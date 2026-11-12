import Lean.CoreM
import Lean.Replay

open Lean

/-- The pinned LeanChecker replay routine, applied to one exact module name. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [moduleText] := args
    | throw <| IO.userError "Expected one exact module name"
  let moduleName := moduleText.toName
  if moduleName.isAnonymous then
    throw <| IO.userError "The module name must be nonempty"
  initSearchPath (← findSysroot)
  let moduleFile ← findOLean moduleName
  unless ← moduleFile.pathExists do
    throw <| IO.userError s!"Object file does not exist: {moduleFile}"
  let mut files := #[moduleFile]
  let serverFile := OLeanLevel.server.adjustFileName moduleFile
  if ← serverFile.pathExists then
    files := files.push serverFile
    let privateFile := OLeanLevel.private.adjustFileName moduleFile
    if ← privateFile.pathExists then
      files := files.push privateFile
  let parts ← readModuleDataParts files
  if h : parts.size = 0 then
    throw <| IO.userError "The module has no data parts"
  else
    let (moduleData, _) := parts[0]
    let (_, state) ← importModulesCore moduleData.imports |>.run
    let environment ← finalizeImport state moduleData.imports {} 0 false false (isModule := true)
    let mut constants := {}
    for name in parts[parts.size - 1].1.constNames, info in parts[parts.size - 1].1.constants do
      constants := constants.insert name info
    discard <| environment.toKernelEnv.replay constants
    environment.freeRegions
    IO.println s!"replaying {moduleText} (exact module)"
    return 0
