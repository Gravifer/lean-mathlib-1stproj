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

-- Helper function to resolve . and .. components manually
def resolvePath (path : System.FilePath) : System.FilePath :=
  let components := path.components
  let resolved := components.foldl (fun acc component =>
    match component with
    | "." => acc  -- Skip current directory
    | ".." => if acc.isEmpty then acc else acc.pop  -- Go up one directory
    | comp => acc.push comp
  ) #[]
  let pathStr := String.intercalate (toString System.FilePath.pathSeparator) resolved.toList
  System.FilePath.mk pathStr

open Doug in
def main (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match DirFromArgs args with
  | Except.ok argDir =>
      -- IO.eprintln s!"Debug: (cwd: {cwd}) passed path argument is {argDir}"
      -- Determine the start directory: cwd, relative to cwd, or absolute
      let startDir ← match argDir with
        | none => pure cwd  -- No directory specified, use cwd
        | some path =>
            let normalizedPath := (if path.isAbsolute then path else cwd.join path).normalize
            -- IO.eprintln s!"Debug: trying to resolve {normalizedPath}"
            -- Try to get the canonical/real path to resolve . and .. components
            pure $ resolvePath normalizedPath

      -- Check if the directory exists
      let dirValid ← startDir.isDir
      -- IO.eprintln s!"Debug: start directory is {startDir}"
      if dirValid then
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
      else
        IO.eprintln s!"Error: '{startDir}' does not exist or is not a directory"
        pure 2
  | Except.error _ =>
      IO.eprintln "Error: No directory path provided after '--'"
      IO.eprintln usage
      pure 3

def main_bak : IO Unit :=
  IO.println s!"Hello, doug!"
