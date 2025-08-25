namespace Doug

  def usage : String :=
    "Usage: doug [--ascii] [--all]
  Options:
  \t-a --all  \tShow hidden items
  \t-A --ascii\tUse ASCII characters to display the directory structure
  \t-h --help \tPrint this help message (ignores other flags)"

  structure Config where
    useASCII   : Bool := false
    showHidden : Bool := false
    printHelp  : Bool := false
    currentPrefix : String := ""

  def configFromArgs (args : List String) : Option Config :=
    args.foldlM processArg {} where
      processArg (config : Config) : String -> Option Config
      | "-A" | "--ascii" => some $ if config.printHelp then config else {config with useASCII   := true}
      | "-a" | "--all"   => some $ if config.printHelp then config else {config with showHidden := true}
      | "-h" | "--help"  => some $ {printHelp := true} -- * purge all other options
      | _ => none

  def Config.preFile (cfg : Config) :=
    if cfg.useASCII then "|--" else "├──"

  def Config.preDir (cfg : Config) :=
    if cfg.useASCII then "|  " else "│  "

  def Config.fileName (cfg : Config) (file : String) : String :=
    s!"{cfg.currentPrefix}{cfg.preFile} {file}"

  def Config.dirName (cfg : Config) (dir : String) : String :=
    s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"

  def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ (cfg.currentPrefix/-.set 0 ' '-/)}

  abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α

  -- def ConfigIO (α : Type) : Type :=
  --   Config → IO α

  instance : Monad ConfigIO where
    pure x := fun _ => pure x
    bind result next := fun cfg => do
      let v ← result cfg
      next v cfg

  def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
    action cfg

  def currentConfig : ConfigIO Config :=
    fun cfg => pure cfg

  def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
    fun cfg => action (change cfg)

  def runIO (action : IO α) : ConfigIO α :=
    fun _ => action

  def showFileName (file : String) : ConfigIO Unit := do
    let cfg ← currentConfig
    IO.println $ cfg.fileName file

  def showDirName (dir : String) : ConfigIO Unit := do
    let cfg ← currentConfig
    IO.println $ cfg.dirName  dir

end Doug
