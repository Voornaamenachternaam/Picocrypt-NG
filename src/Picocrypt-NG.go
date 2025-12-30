// Package main implements Picocrypt NG v2.00, a secure file encryption tool.
//
// Picocrypt NG v2.00
// Copyright (c) Picocrypt NG developers
// Released under GPL-3.0-only
// https://github.com/Picocrypt-NG/Picocrypt-NG
//
// ~ In cryptography we trust ~
package main

import (
        "archive/zip"
        "bytes"
        "crypto/cipher"
        "crypto/hmac"
        "crypto/rand"
        "crypto/subtle"
        "errors"
        "flag"
        "fmt"
        "hash"
        "image"
        "image/color"
        "io"
        "math"
        "math/big"
        "os"
        "path/filepath"
        "regexp"
        "strconv"
        "strings"
        "time"

        "github.com/Picocrypt/dialog"
        "github.com/Picocrypt/giu"
        "github.com/Picocrypt/imgui-go"
        "github.com/Picocrypt/infectious"
        "github.com/Picocrypt/serpent"
        "github.com/Picocrypt/zxcvbn-go"
        "golang.org/x/crypto/argon2"
        "golang.org/x/crypto/blake2b"
        "golang.org/x/crypto/chacha20"
        "golang.org/x/crypto/hkdf"
        "golang.org/x/crypto/sha3"
)

// Constants
const KiB = 1 << 10
const MiB = 1 << 20
const GiB = 1 << 30
const TiB = 1 << 40

var WHITE = color.RGBA{0xff, 0xff, 0xff, 0xff}
var RED = color.RGBA{0xff, 0x00, 0x00, 0xff}
var GREEN = color.RGBA{0x00, 0xff, 0x00, 0xff}
var YELLOW = color.RGBA{0xff, 0xff, 0x00, 0xff}
var TRANSPARENT = color.RGBA{0x00, 0x00, 0x00, 0x00}

// Generic variables
var window *giu.MasterWindow
var version = "v2.02"
var dpi float32
var mode string
var working bool
var scanning bool

// Popup modals
var modalId int
var showPassgen bool
var showKeyfile bool
var showOverwrite bool
var showProgress bool

// Input and output files
var inputFile string
var inputFileOld string
var outputFile string
var onlyFiles []string
var onlyFolders []string
var allFiles []string
var inputLabel = "Drop files and folders into this window"

// Password and confirm password
var password string
var cpassword string
var passwordStrength int
var passwordState = giu.InputTextFlagsPassword
var passwordStateLabel = "Show"

// Password generator
var passgenLength int32 = 32
var passgenUpper bool
var passgenLower bool
var passgenNums bool
var passgenSymbols bool
var passgenCopy bool

// Keyfile variables
var keyfile bool
var keyfiles []string
var keyfileOrdered bool
var keyfileLabel = "None selected"

// Comments variables
var comments string
var commentsLabel = "Comments:"
var commentsDisabled bool

// Advanced options
var paranoid bool
var reedsolo bool
var deniability bool
var recursively bool
var split bool
var splitSize string
var splitUnits = []string{"KiB", "MiB", "GiB", "TiB", "Total"}
var splitSelected int32 = 1
var recombine bool
var compress bool
var delete bool
var autoUnzip bool
var sameLevel bool
var keep bool
var kept bool

// Status variables
var startLabel = "Start"
var mainStatus = "Ready"
var mainStatusColor = WHITE
var popupStatus string
var requiredFreeSpace int64

// Progress variables
var progress float32
var progressInfo string
var speed float64
var eta string
var canCancel bool

// Reed-Solomon encoders
var rs1, rsErr1 = infectious.NewFEC(1, 3)
var rs5, rsErr2 = infectious.NewFEC(5, 15)
var rs16, rsErr3 = infectious.NewFEC(16, 48)
var rs24, rsErr4 = infectious.NewFEC(24, 72)
var rs32, rsErr5 = infectious.NewFEC(32, 96)
var rs64, rsErr6 = infectious.NewFEC(64, 192)
var rs128, rsErr7 = infectious.NewFEC(128, 136)
var fastDecode bool

// Compression variables and passthrough
var compressDone int64
var compressTotal int64
var compressStart time.Time

type compressorProgress struct {
        io.Reader
}

func (p *compressorProgress) Read(data []byte) (int, error) {
        if !working {
                return 0, io.EOF
        }
        read, err := p.Reader.Read(data)
        compressDone += int64(read)
        progress, speed, eta = statify(compressDone, compressTotal, compressStart)
        if compress {
                popupStatus = fmt.Sprintf("Compressing at %.2f MiB/s (ETA: %s)", speed, eta)
        } else {
                popupStatus = fmt.Sprintf("Combining at %.2f MiB/s (ETA: %s)", speed, eta)
        }
        giu.Update()
        return read, err
}

type encryptedZipWriter struct {
        _w      io.Writer
        _cipher *chacha20.Cipher
}

func (ezw *encryptedZipWriter) Write(data []byte) (n int, err error) {
        dst := make([]byte, len(data))
        ezw._cipher.XORKeyStream(dst, data)
        return ezw._w.Write(dst)
}

type encryptedZipReader struct {
        _r      io.Reader
        _cipher *chacha20.Cipher
}

func (ezr *encryptedZipReader) Read(data []byte) (n int, err error) {
        src := make([]byte, len(data))
        n, err = ezr._r.Read(src)
        if err == nil && n > 0 {
                dst := make([]byte, n)
                ezr._cipher.XORKeyStream(dst, src[:n])
                if copy(data, dst) != n {
                        panic(errors.New("built-in copy() function failed"))
                }
        }
        return n, err
}

func onClickStartButton() {
        // Start button should be disabled if these conditions are true; don't do anything if so
        if (len(keyfiles) == 0 && password == "") || (mode == "encrypt" && password != cpassword) {
                return
        }

        if keyfile && keyfiles == nil {
                mainStatus = "Please select your keyfiles"
                mainStatusColor = RED
                giu.Update()
                return
        }
        tmp, err := strconv.Atoi(splitSize)
        if split && (splitSize == "" || err != nil || tmp <= 0) {
                mainStatus = "Invalid chunk size"
                mainStatusColor = RED
                giu.Update()
                return
        }

        // Check if output file already exists
        _, err = os.Stat(outputFile)

        // Check if any split chunks already exist
        if split {
                names, err2 := filepath.Glob(outputFile + ".*")
                if err2 != nil {
                        panic(err2)
                }
                if len(names) > 0 {
                        err = nil
                } else {
                        err = os.ErrNotExist
                }
        }

        // If files already exist, show the overwrite modal
        if err == nil && !recursively {
                showOverwrite = true
                modalId++
                giu.Update()
        } else { // Nothing to worry about, start working
                showProgress = true
                fastDecode = true
                canCancel = true
                modalId++
                giu.Update()
                if !recursively {
                        go func() {
                                work()
                                working = false
                                showProgress = false
                                giu.Update()
                        }()
                } else {
                        // Store variables as they will be cleared
                        oldPassword := password
                        oldKeyfile := keyfile
                        oldKeyfiles := keyfiles
                        oldKeyfileOrdered := keyfileOrdered
                        oldKeyfileLabel := keyfileLabel
                        oldComments := comments
                        oldParanoid := paranoid
                        oldReedsolo := reedsolo
                        oldDeniability := deniability
                        oldSplit := split
                        oldSplitSize := splitSize
                        oldSplitSelected := splitSelected
                        oldDelete := delete
                        files := allFiles
                        go func() {
                                for _, file := range files {
                                        // Simulate dropping the file
                                        onDrop([]string{file})

                                        // Restore variables and options
                                        password = oldPassword
                                        cpassword = oldPassword
                                        keyfile = oldKeyfile
                                        keyfiles = oldKeyfiles
                                        keyfileOrdered = oldKeyfileOrdered
                                        keyfileLabel = oldKeyfileLabel
                                        comments = oldComments
                                        paranoid = oldParanoid
                                        reedsolo = oldReedsolo
                                        if mode != "decrypt" {
                                                deniability = oldDeniability
                                        }
                                        split = oldSplit
                                        splitSize = oldSplitSize
                                        splitSelected = oldSplitSelected
                                        delete = oldDelete

                                        work()
                                        if !working {
                                                resetUI()
                                                cancel(nil, nil)
                                                showProgress = false
                                                giu.Update()
                                                return
                                        }
                                }
                                working = false
                                showProgress = false
                                giu.Update()
                        }()
                }
        }
}

// The main user interface
func draw() {
        giu.SingleWindow().Flags(524351).Layout(
                giu.Custom(func() {
                        if giu.IsKeyReleased(giu.KeyEnter) {
                                onClickStartButton()
                                return
                        }
                        if showPassgen {
                                giu.PopupModal("Generate password:##"+strconv.Itoa(modalId)).Flags(6).Layout(
                                        giu.Row(
                                                giu.Label("Length:"),
                                                giu.SliderInt(&passgenLength, 12, 64).Size(giu.Auto),
                                        ),
                                        giu.Checkbox("Uppercase", &passgenUpper),
                                        giu.Checkbox("Lowercase", &passgenLower),
                                        giu.Checkbox("Numbers", &passgenNums),
                                        giu.Checkbox("Symbols", &passgenSymbols),
                                        giu.Checkbox("Copy to clipboard", &passgenCopy),
                                        giu.Row(
                                                giu.Button("Cancel").Size(100, 0).OnClick(func() {
                                                        giu.CloseCurrentPopup()
                                                        showPassgen = false
                                                }),
                                                giu.Style().SetDisabled(!passgenUpper && !passgenLower && !passgenNums && !passgenSymbols).To(
                                                        giu.Button("Generate").Size(100, 0).OnClick(func() {
                                                                password = genPassword()
                                                                cpassword = password
                                                                passwordStrength = zxcvbn.PasswordStrength(password, nil).Score

                                                                giu.CloseCurrentPopup()
                                                                showPassgen = false
                                                        }),
                                                ),
                                        ),
                                ).Build()
                                giu.OpenPopup("Generate password:##" + strconv.Itoa(modalId))
                                giu.Update()
                        }

                        if showKeyfile {
                                giu.PopupModal("Manage keyfiles:##"+strconv.Itoa(modalId)).Flags(70).Layout(
                                        giu.Label("Drag and drop your keyfiles here"),
                                        giu.Custom(func() {
                                                if mode != "decrypt" {
                                                        giu.Checkbox("Require correct order", &keyfileOrdered).Build()
                                                        giu.Tooltip("Ordering of keyfiles will matter").Build()
                                                } else if keyfileOrdered {
                                                        giu.Label("Correct ordering is required").Build()
                                                }
                                        }),
                                        giu.Custom(func() {
                                                if len(keyfiles) > 0 {
                                                        giu.Separator().Build()
                                                }
                                                for _, i := range keyfiles {
                                                        giu.Label(filepath.Base(i)).Build()
                                                }
                                        }),
                                        giu.Row(
                                                giu.Button("Clear").Size(100, 0).OnClick(func() {
                                                        keyfiles = nil
                                                        if keyfile {
                                                                keyfileLabel = "Keyfiles required"
                                                        } else {
                                                                keyfileLabel = "None selected"
                                                        }
                                                        modalId++
                                                        giu.Update()
                                                }),
                                                giu.Tooltip("Remove all keyfiles"),

                                                giu.Button("Done").Size(100, 0).OnClick(func() {
                                                        giu.CloseCurrentPopup()
                                                        showKeyfile = false
                                                }),
                                        ),
                                ).Build()
                                giu.OpenPopup("Manage keyfiles:##" + strconv.Itoa(modalId))
                                giu.Update()
                        }

                        if showOverwrite {
                                giu.PopupModal("Warning:##"+strconv.Itoa(modalId)).Flags(6).Layout(
                                        giu.Label("Output already exists. Overwrite?"),
                                        giu.Row(
                                                giu.Button("No").Size(100, 0).OnClick(func() {
                                                        giu.CloseCurrentPopup()
                                                        showOverwrite = false
                                                }),
                                                giu.Button("Yes").Size(100, 0).OnClick(func() {
                                                        giu.CloseCurrentPopup()
                                                        showOverwrite = false

                                                        showProgress = true
                                                        fastDecode = true
                                                        canCancel = true
                                                        modalId++
                                                        giu.Update()
                                                        go func() {
                                                                work()
                                                                working = false
                                                                showProgress = false
                                                                giu.Update()
                                                        }()
                                                }),
                                        ),
                                ).Build()
                                giu.OpenPopup("Warning:##" + strconv.Itoa(modalId))
                                giu.Update()
                        }

                        if showProgress {
                                giu.PopupModal("Progress:##"+strconv.Itoa(modalId)).Flags(6|1<<0).Layout(
                                        giu.Dummy(0, 0),
                                        giu.Row(
                                                giu.ProgressBar(progress).Size(210, 0).Overlay(progressInfo),
                                                giu.Style().SetDisabled(!canCancel).To(
                                                        giu.Button(func() string {
                                                                if working {
                                                                        return "Cancel"
                                                                }
                                                                return "..."
                                                        }()).Size(58, 0).OnClick(func() {
                                                                working = false
                                                                canCancel = false
                                                        }),
                                                ),
                                        ),
                                        giu.Label(popupStatus),
                                ).Build()
                                giu.OpenPopup("Progress:##" + strconv.Itoa(modalId))
                                giu.Update()
                        }
                }),

                giu.Row(
                        giu.Label(inputLabel),
                        giu.Custom(func() {
                                bw, _ := giu.CalcTextSize("Clear")
                                p, _ := giu.GetWindowPadding()
                                bw += p * 2
                                giu.Dummy((bw+p)/-dpi, 0).Build()
                                giu.SameLine()
                                giu.Style().SetDisabled((len(allFiles) == 0 && len(onlyFiles) == 0) || scanning).To(
                                        giu.Button("Clear").Size(bw/dpi, 0).OnClick(resetUI),
                                        giu.Tooltip("Clear all input files and reset UI state"),
                                ).Build()
                        }),
                ),

                giu.Separator(),
                giu.Style().SetDisabled((len(allFiles) == 0 && len(onlyFiles) == 0) || scanning).To(
                        giu.Label("Password:"),
                        giu.Row(
                                giu.Button(passwordStateLabel).Size(54, 0).OnClick(func() {
                                        if passwordState == giu.InputTextFlagsPassword {
                                                passwordState = giu.InputTextFlagsNone
                                                passwordStateLabel = "Hide"
                                        } else {
                                                passwordState = giu.InputTextFlagsPassword
                                                passwordStateLabel = "Show"
                                        }
                                        giu.Update()
                                }),
                                giu.Tooltip("Toggle the visibility of password entries"),

                                giu.Button("Clear").Size(54, 0).OnClick(func() {
                                        password = ""
                                        cpassword = ""
                                        giu.Update()
                                }),
                                giu.Tooltip("Clear the password entries"),

                                giu.Button("Copy").Size(54, 0).OnClick(func() {
                                        giu.Context.GetPlatform().SetClipboard(password)
                                        giu.Update()
                                }),
                                giu.Tooltip("Copy the password into your clipboard"),

                                giu.Button("Paste").Size(54, 0).OnClick(func() {
                                        tmp := giu.Context.GetPlatform().GetClipboard()
                                        password = tmp
                                        if mode != "decrypt" {
                                                cpassword = tmp
                                        }
                                        passwordStrength = zxcvbn.PasswordStrength(password, nil).Score
                                        giu.Update()
                                }),
                                giu.Tooltip("Paste a password from your clipboard"),

                                giu.Style().SetDisabled(mode == "decrypt").To(
                                        giu.Button("Create").Size(54, 0).OnClick(func() {
                                                showPassgen = true
                                                modalId++
                                                giu.Update()
                                        }),
                                ),
                                giu.Tooltip("Generate a cryptographically secure password"),
                        ),
                        giu.Row(
                                giu.InputText(&password).Flags(passwordState).Size(302/dpi).OnChange(func() {
                                        passwordStrength = zxcvbn.PasswordStrength(password, nil).Score
                                        giu.Update()
                                }),
                                giu.Custom(func() {
                                        c := giu.GetCanvas()
                                        p := giu.GetCursorScreenPos()
                                        col := color.RGBA{
                                                uint8(0xc8 - 31*passwordStrength),
                                                uint8(0x4c + 31*passwordStrength), 0x4b, 0xff,
                                        }
                                        if password == "" || mode == "decrypt" {
                                                col = TRANSPARENT
                                        }
                                        path := p.Add(image.Pt(
                                                int(math.Round(-20*float64(dpi))),
                                                int(math.Round(12*float64(dpi))),
                                        ))
                                        c.PathArcTo(path, 6*dpi, -math.Pi/2, math.Pi*(.4*float32(passwordStrength)-.1), -1)
                                        c.PathStroke(col, false, 2)
                                }),
                        ),

                        giu.Dummy(0, 0),
                        giu.Style().SetDisabled(password == "" || mode == "decrypt").To(
                                giu.Label("Confirm password:"),
                                giu.Row(
                                        giu.InputText(&cpassword).Flags(passwordState).Size(302/dpi),
                                        giu.Custom(func() {
                                                c := giu.GetCanvas()
                                                p := giu.GetCursorScreenPos()
                                                col := color.RGBA{0x4c, 0xc8, 0x4b, 0xff}
                                                if cpassword != password {
                                                        col = color.RGBA{0xc8, 0x4c, 0x4b, 0xff}
                                                }
                                                if password == "" || cpassword == "" || mode == "decrypt" {
                                                        col = TRANSPARENT
                                                }
                                                path := p.Add(image.Pt(
                                                        int(math.Round(-20*float64(dpi))),
                                                        int(math.Round(12*float64(dpi))),
                                                ))
                                                c.PathArcTo(path, 6*dpi, 0, 2*math.Pi, -1)
                                                c.PathStroke(col, false, 2)
                                        }),
                                ),
                        ),

                        giu.Dummy(0, 0),
                        giu.Style().SetDisabled(mode == "decrypt" && !keyfile && !deniability).To(
                                giu.Row(
                                        giu.Label("Keyfiles:"),
                                        giu.Button("Edit").Size(54, 0).OnClick(func() {
                                                showKeyfile = true
                                                modalId++
                                                giu.Update()
                                        }),
                                        giu.Tooltip("Manage keyfiles to use for "+(func() string {
                                                if mode != "decrypt" {
                                                        return "encryption"
                                                }
                                                return "decryption"
                                        }())),

                                        giu.Style().SetDisabled(mode == "decrypt").To(
                                                giu.Button("Create").Size(54, 0).OnClick(func() {
                                                        f := dialog.File().Title("Choose where to save the keyfile")
                                                        f.SetStartDir(func() string {
                                                                if len(onlyFiles) > 0 {
                                                                        return filepath.Dir(onlyFiles[0])
                                                                }
                                                                return filepath.Dir(onlyFolders[0])
                                                        }())
                                                        f.SetInitFilename("keyfile-" + strconv.Itoa(int(time.Now().Unix())) + ".bin")
                                                        file, err := f.Save()
                                                        if file == "" || err != nil {
                                                                return
                                                        }

                                                        fout, err := os.Create(file)
                                                        if err != nil {
                                                                mainStatus = "Failed to create keyfile"
                                                                mainStatusColor = RED
                                                                giu.Update()
                                                                return
                                                        }
                                                        data := make([]byte, 32)
                                                        if n, err := rand.Read(data); err != nil || n != 32 {
                                                                panic(errors.New("fatal crypto/rand error"))
                                                        }
                                                        n, err := fout.Write(data)
                                                        if err != nil || n != 32 {
                                                                fout.Close()
                                                                panic(errors.New("failed to write full keyfile"))
                                                        }
                                                        if err := fout.Close(); err != nil {
                                                                panic(err)
                                                        } else {
                                                                mainStatus = "Ready"
                                                                mainStatusColor = WHITE
                                                                giu.Update()
                                                                return
                                                        }
                                                }),
                                                giu.Tooltip("Generate a cryptographically secure keyfile"),
                                        ),
                                        giu.Style().SetDisabled(true).To(
                                                giu.InputText(&keyfileLabel).Size(giu.Auto),
                                        ),
                                ),
                        ),
                ),

                giu.Separator(),
                giu.Style().SetDisabled(mode != "decrypt" && ((len(keyfiles) == 0 && password == "") || (password != cpassword)) || deniability).To(
                        giu.Style().SetDisabled(mode == "decrypt" && (comments == "" || comments == "Comments are corrupted")).To(
                                giu.Label(commentsLabel),
                                giu.InputText(&comments).Size(giu.Auto).Flags(func() giu.InputTextFlags {
                                        if commentsDisabled {
                                                return giu.InputTextFlagsReadOnly
                                        } else if deniability {
                                                comments = ""
                                        }
                                        return giu.InputTextFlagsNone
                                }()),
                                giu.Custom(func() {
                                        if !commentsDisabled {
                                                giu.Tooltip("Note: comments are not encrypted!").Build()
                                        }
                                }),
                        ),
                ),
                giu.Style().SetDisabled((len(keyfiles) == 0 && password == "") || (mode == "encrypt" && password != cpassword)).To(
                                   }
                                        i++
                                }
                        } else {
                                if err := os.Remove(inputFile); err != nil {
                                        panic(err)
                                }
                                if deniability {
                                        if err := os.Remove(strings.TrimSuffix(inputFile, ".tmp")); err != nil {
                                                panic(err)
                                        }
                                }
                        }
                } else {
                        for _, i := range onlyFiles {
                                if err := os.Remove(i); err != nil {
                                        panic(err)
                                }
                        }
                        for _, i := range onlyFolders {
                                if err := os.RemoveAll(i); err != nil {
                                        panic(err)
                                }
                        }
                }
        }
        if mode == "decrypt" && deniability {
                os.Remove(inputFile)
        }

        if mode == "decrypt" && !kept && autoUnzip {
                showProgress = true
                popupStatus = "Unzipping..."
                giu.Update()

                if err := unpackArchive(outputFile); err != nil {
                        mainStatus = "Auto unzipping failed!"
                        mainStatusColor = RED
                        giu.Update()
                        return
                }

                if err := os.Remove(outputFile); err != nil {
                        panic(err)
                }
        }

        // All done, reset the UI
        oldKept := kept
        resetUI()
        kept = oldKept

        // If the user chose to keep a corrupted/modified file, let them know
        if kept {
                mainStatus = "The input file was modified. Please be careful"
                mainStatusColor = YELLOW
        } else {
                mainStatus = "Completed"
                mainStatusColor = GREEN
        }
}

// If the OS denies reading or writing to a file
func accessDenied(s string) {
        mainStatus = s + " access denied by operating system"
        mainStatusColor = RED
}

// If there isn't enough disk space
func insufficientSpace(fin *os.File, fout *os.File) {
        fin.Close()
        fout.Close()
        mainStatus = "Insufficient disk space"
        mainStatusColor = RED
}

// If corruption is detected during decryption
func broken(fin *os.File, fout *os.File, message string, keepOutput bool) {
        fin.Close()
        fout.Close()
        mainStatus = message
        mainStatusColor = RED

        // Clean up files since decryption failed
        if recombine {
                os.Remove(inputFile)
        }
        if !keepOutput {
                os.Remove(outputFile)
        }
}

// Stop working if user hits "Cancel"
func cancel(fin *os.File, fout *os.File) {
        fin.Close()
        fout.Close()
        mainStatus = "Operation cancelled by user"
        mainStatusColor = WHITE
}

// Reset the UI to a clean state with nothing selected or checked
func resetUI() {
        imgui.ClearActiveID()
        mode = ""

        inputFile = ""
        inputFileOld = ""
        outputFile = ""
        onlyFiles = nil
        onlyFolders = nil
        allFiles = nil
        inputLabel = "Drop files and folders into this window"

        password = ""
        cpassword = ""
        passwordState = giu.InputTextFlagsPassword
        passwordStateLabel = "Show"

        passgenLength = 32
        passgenUpper = true
        passgenLower = true
        passgenNums = true
        passgenSymbols = true
        passgenCopy = true

        keyfile = false
        keyfiles = nil
        keyfileOrdered = false
        keyfileLabel = "None selected"

        comments = ""
        commentsLabel = "Comments:"
        commentsDisabled = false

        paranoid = false
        reedsolo = false
        deniability = false
        recursively = false
        split = false
        splitSize = ""
        splitSelected = 1
        recombine = false
        compress = false
        delete = false
        autoUnzip = false
        sameLevel = false
        keep = false
        kept = false

        startLabel = "Start"
        mainStatus = "Ready"
        mainStatusColor = WHITE
        popupStatus = ""
        requiredFreeSpace = 0

        progress = 0
        progressInfo = ""
        giu.Update()
}

// Reed-Solomon encoder
func rsEncode(rs *infectious.FEC, data []byte) []byte {
        res := make([]byte, rs.Total())
        rs.Encode(data, func(s infectious.Share) {
                res[s.Number] = s.Data[0]
        })
        return res
}

// Reed-Solomon decoder
func rsDecode(rs *infectious.FEC, data []byte) ([]byte, error) {
        // If fast decode, just return the first 128 bytes
        if rs.Total() == 136 && fastDecode {
                return data[:128], nil
        }

        tmp := make([]infectious.Share, rs.Total())
        for i := range rs.Total() {
                tmp[i].Number = i
                tmp[i].Data = append(tmp[i].Data, data[i])
        }
        res, err := rs.Decode(nil, tmp)

        // Force decode the data but return the error as well
        if err != nil {
                if rs.Total() == 136 {
                        return data[:128], err
                }
                return data[:rs.Total()/3], err
        }

        // No issues, return the decoded data
        return res, nil
}

// PKCS#7 pad (for use with Reed-Solomon)
func pad(data []byte) []byte {
        padLen := 128 - len(data)%128
        padding := bytes.Repeat([]byte{byte(padLen)}, padLen)
        return append(data, padding...)
}

// PKCS#7 unpad
func unpad(data []byte) []byte {
        padLen := int(data[127])
        return data[:128-padLen]
}

// Generate a cryptographically secure password
func genPassword() string {
        chars := ""
        if passgenUpper {
                chars += "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        }
        if passgenLower {
                chars += "abcdefghijklmnopqrstuvwxyz"
        }
        if passgenNums {
                chars += "1234567890"
        }
        if passgenSymbols {
                chars += "-=_+!@#$^&()?<>"
        }
        tmp := make([]byte, passgenLength)
        for i := range int(passgenLength) {
                j, _ := rand.Int(rand.Reader, big.NewInt(int64(len(chars))))
                tmp[i] = chars[j.Int64()]
        }
        if passgenCopy {
                giu.Context.GetPlatform().SetClipboard(string(tmp))
        }
        return string(tmp)
}

// Convert done, total, and starting time to progress, speed, and ETA
func statify(done int64, total int64, start time.Time) (float32, float64, string) {
        progress := float32(done) / float32(total)
        elapsed := float64(time.Since(start)) / float64(MiB) / 1000
        speed := float64(done) / elapsed / float64(MiB)
        eta := int(math.Floor(float64(total-done) / (speed * float64(MiB))))
        return float32(math.Min(float64(progress), 1)), speed, timeify(eta)
}

// Convert seconds to HH:MM:SS
func timeify(seconds int) string {
        hours := int(math.Floor(float64(seconds) / 3600))
        seconds %= 3600
        minutes := int(math.Floor(float64(seconds) / 60))
        seconds %= 60
        hours = int(math.Max(float64(hours), 0))
        minutes = int(math.Max(float64(minutes), 0))
        seconds = int(math.Max(float64(seconds), 0))
        return fmt.Sprintf("%02d:%02d:%02d", hours, minutes, seconds)
}

// Convert bytes to KiB, MiB, etc.
func sizeify(size int64) string {
        if size >= int64(TiB) {
                return fmt.Sprintf("%.2f TiB", float64(size)/float64(TiB))
        } else if size >= int64(GiB) {
                return fmt.Sprintf("%.2f GiB", float64(size)/float64(GiB))
        } else if size >= int64(MiB) {
                return fmt.Sprintf("%.2f MiB", float64(size)/float64(MiB))
        } else {
                return fmt.Sprintf("%.2f KiB", float64(size)/float64(KiB))
        }
}

func unpackArchive(zipPath string) error {
        reader, err := zip.OpenReader(zipPath)
        if err != nil {
                return err
        }
        defer reader.Close()

        var totalSize int64
        for _, f := range reader.File {
                totalSize += int64(f.UncompressedSize64)
        }

        var extractDir string
        if sameLevel {
                extractDir = filepath.Dir(zipPath)
        } else {
                extractDir = filepath.Join(filepath.Dir(zipPath), strings.TrimSuffix(filepath.Base(zipPath), ".zip"))
        }

        var done int64
        startTime := time.Now()

        for _, f := range reader.File {
                if strings.Contains(f.Name, "..") {
                        return errors.New("potentially malicious zip item path")
                }
                outPath := filepath.Join(extractDir, f.Name)

                // Make directory if current entry is a folder
                if f.FileInfo().IsDir() {
                        if err := os.MkdirAll(outPath, 0700); err != nil {
                                return err
                        }
                }
        }

        for i, f := range reader.File {
                if strings.Contains(f.Name, "..") {
                        return errors.New("potentially malicious zip item path")
                }

                // Already handled above
                if f.FileInfo().IsDir() {
                        continue
                }

                outPath := filepath.Join(extractDir, f.Name)

                // Otherwise create necessary parent directories
                if err := os.MkdirAll(filepath.Dir(outPath), 0700); err != nil {
                        return err
                }

                // Open the file inside the archive
                fileInArchive, err := f.Open()
                if err != nil {
                        return err
                }
                defer fileInArchive.Close()

                dstFile, err := os.Create(outPath)
                if err != nil {
                        return err
                }

                // Read from zip in chunks to update progress
                buffer := make([]byte, MiB)
                for {
                        n, readErr := fileInArchive.Read(buffer)
                        if n > 0 {
                                _, writeErr := dstFile.Write(buffer[:n])
                                if writeErr != nil {
                                        dstFile.Close()
                                        os.Remove(dstFile.Name())
                                        return writeErr
                                }

                                done += int64(n)
                                progress, speed, eta = statify(done, totalSize, startTime)
                                progressInfo = fmt.Sprintf("%d/%d", i+1, len(reader.File))
                                popupStatus = fmt.Sprintf("Unpacking at %.2f MiB/s (ETA: %s)", speed, eta)
                                giu.Update()
                        }
                        if readErr != nil {
                                if readErr == io.EOF {
                                        break
                                }
                                dstFile.Close()
                                return readErr
                        }
                }
                dstFile.Close()
        }

        return nil
}

func main() {
        if rsErr1 != nil || rsErr2 != nil || rsErr3 != nil || rsErr4 != nil || rsErr5 != nil || rsErr6 != nil || rsErr7 != nil {
                panic(errors.New("rs failed to init"))
        }
        // Create the main window
        window = giu.NewMasterWindow("Picocrypt NG "+version[1:], 318, 507, giu.MasterWindowFlagsNotResizable)

        // Start the dialog module
        dialog.Init()

        // Set callbacks
        window.SetDropCallback(onDrop)
        window.SetCloseCallback(func() bool {
                return !working && !showProgress
        })

        // Set universal DPI
        dpi = giu.Context.GetPlatform().GetContentScale()

        // Simulate dropping command line arguments
        flag.Parse()
        if flag.NArg() > 0 {
                onDrop(flag.Args())
        }

        // Start the UI
        window.Run(draw)
}
