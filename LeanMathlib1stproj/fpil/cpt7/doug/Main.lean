import Doug
import Doug.Basic
import Doug.Config

namespace Doug

inductive Entry where
  | file : String → Entry
  | dir : String → Entry

def Entry.isHidden : Entry → Bool
  | .file name => name.startsWith "."
  | .dir  name => name.startsWith "."

def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name =>
      let pathIsDir ← path.isDir
      -- IO.eprintln s!"Debug: \"{name}\" is a {if pathIsDir then "directory" else "file"}" -- Debug: print result of isDir
      pure ∘ some $ if pathIsDir then .dir name else .file name

partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  let cfg ← currentConfig
  match ← toEntry path with
  | none => pure ()
  | some entry => if cfg.showHidden || !entry.isHidden then match entry with
      | (.file name) => showFileName name
      | (.dir  name) => showDirName  name
                        let contents ← path.readDir
                        withReader (·.inDirectory)
                          (doList contents.toList fun d =>
                            dirTree d.path)

def DirFromArgs (args : List String) : Except Unit (Option System.FilePath) := do
  /- - if there is not the `--` separator,
       then the first argument after flags (should it exist)
       is the directory path and cannot start with '-' (cwd if none given);
     - if the `--` separator exists, the rest of the arguments should be joined
       as a space separated string, and regarded as the path (error if none given).
  -/
  if args.contains "--" then
    let afterSeparator := (args.dropWhile (· != "--")).drop 1
    if afterSeparator.isEmpty then
      throw ()  -- error if no path given after --
    let pathStr := " ".intercalate afterSeparator
    let path := System.FilePath.mk pathStr
    return (some path)
  else
    return (args.dropWhile (·.startsWith "-")).head?.map System.FilePath.mk

end Doug

open Doug in
def main (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match DirFromArgs args with
  | Except.ok argDir =>
      IO.eprintln s!"Debug: passed path argument is {argDir}"
      -- todo: check if directory exists, and whether it's relative
      let startDir := argDir.getD cwd
      IO.eprintln s!"Debug: start directory is {startDir}"
      match configFromArgs (args.takeWhile fun str => str.startsWith "-" && str != "--") with
      | some config =>
          match config with
          | {printHelp := true} => IO.println usage
          | _ => (dirTree startDir).run config
          pure 0
      | none =>
          IO.eprintln s!"Didn't understand argument(s) {" ".intercalate args}\n"
          IO.eprintln usage
          pure 1
  | Except.error _ =>
      IO.eprintln "Error: No directory path provided after '--'"
      IO.eprintln usage
      pure 1

def main_bak : IO Unit :=
  IO.println s!"Hello, doug!"
