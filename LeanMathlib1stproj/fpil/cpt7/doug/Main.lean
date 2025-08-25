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

end Doug

open Doug in
def main (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match configFromArgs args with
  | some config =>
      match config with
      | {printHelp := true} => IO.println usage
      | _ => (dirTree cwd).run config
      pure 0
  | none =>
      IO.eprintln s!"Didn't understand argument(s) {" ".intercalate args}\n"
      IO.eprintln usage
      pure 1

def main_bak : IO Unit :=
  IO.println s!"Hello, doug!"
