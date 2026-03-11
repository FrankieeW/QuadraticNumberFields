import Batteries.Tactic.Lint
import Lake.CLI.Main

open Lean Core Batteries.Tactic.Lint

open Lake

/-- Returns the root modules of `lean_exe` or `lean_lib` default targets in the Lake workspace. -/
def resolveDefaultRootModules : IO (Array Name) := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"
  let defaultTargetModules := workspace.root.defaultTargets.flatMap fun target =>
    if let some lib := workspace.root.findLeanLib? target then
      lib.roots
    else if let some exe := workspace.root.findLeanExe? target then
      #[exe.config.root]
    else
      #[]
  return defaultTargetModules

/-- Run the Batteries environment linter on a given module. -/
unsafe def runLinterOnModule (module : Name) : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe Lean.enableInitializersExecution
  let lintModule := `Batteries.Tactic.Lint
  let env ← importModules #[module, lintModule] {} (trustLevel := 1024) (loadExts := true)
  let ctx := {
    fileName := ""
    fileMap := default
    options := {}
  }
  let state := { env }
  Prod.fst <$> (CoreM.toIO · ctx state) do
    let decls ← getDeclsInPackage module.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
    let results ← lintCore decls linters (inIO := true) (currentModule := module)
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmtResults ←
        formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
          s!"in {module}" (runSlowLinters := true) .medium linters.size
      IO.print (← fmtResults.toString)
      IO.Process.exit 1
    else
      IO.println s!"-- Linting passed for {module}."

/--
Usage: `runLinter [Module.Name]...`

Runs environment linters on the specified modules, or on all root modules of the package's default
targets if no modules are specified.
-/
unsafe def main (args : List String) : IO Unit := do
  let modules ←
    if args.isEmpty then
      resolveDefaultRootModules
    else
      pure <| args.toArray.map String.toName
  for module in modules do
    runLinterOnModule module
  IO.Process.exit 0
