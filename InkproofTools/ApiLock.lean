/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

open Lean Meta

namespace InkproofTools.ApiLock

/-- Last name components of declarations Lean derives from a public declaration. They change only
when that declaration does, which its own line already records. -/
private def derivedSuffixes : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ibelow", "noConfusion",
   "noConfusionType", "inj", "injEq", "sizeOf_spec", "ctorIdx", "ctorElim", "ctorElimType",
   "eq_def", "eq_unfold", "congr_simp", "induct", "mutual_induct", "induct_unfolding", "fun_cases"]

private def isDerivedName (n : Name) : Bool :=
  match n with
  | .str _ s => derivedSuffixes.contains s || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
  | _ => false

private def isApi (env : Environment) (n : Name) : MetaM Bool := do
  if n.isInternalDetail || isPrivateName n || isDerivedName n then return false
  if isAuxRecursor env n || isNoConfusion env n || (← isMatcher n) then return false
  return true

private def kind (env : Environment) (n : Name) : ConstantInfo → MetaM String
  | .axiomInfo _ => pure "axiom"
  | .thmInfo _ => pure "theorem"
  | .opaqueInfo _ => pure "opaque"
  | .quotInfo _ => pure "quot"
  | .recInfo _ => pure "recursor"
  | .ctorInfo _ => pure "constructor"
  | .inductInfo _ =>
    pure <| if isClass env n then "class" else if isStructure env n then "structure" else "inductive"
  | .defnInfo _ => do
    if ← isInstance n then return "instance"
    if (env.getProjectionFnInfo? n).isSome then return "field"
    return "def"

/-- Collapses a pretty-printed type to one line, so each declaration is exactly one line. -/
private def oneLine (s : String) : String :=
  " ".intercalate (s.splitToList Char.isWhitespace |>.filter (!·.isEmpty))

/-- The public API of every module whose name starts with one of `roots`, except modules with an
`Internal` component, which no consumer may import: one line per public declaration giving its
kind, name and type, sorted by name. -/
def apiLines (roots : Array Name) : MetaM (Array String) := do
  let env ← getEnv
  let inScope (n : Name) : Bool :=
    (env.getModuleIdxFor? n >>= (env.allImportedModuleNames[·.toNat]?)).any
      fun m => roots.any (·.isPrefixOf m) && !m.components.contains `Internal
  let mut lines : Array (Name × String) := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless inScope n do continue
    unless ← isApi env n do continue
    let ty ← withOptions (fun o => o.set `format.width (100000 : Nat) |>.set `pp.fullNames true) do
      ppExpr ci.type
    lines := lines.push (n, s!"{← kind env n ci} {n} : {oneLine (toString ty)}")
  return lines.qsort (fun a b => a.1.toString < b.1.toString) |>.map (·.2)

/-- Lean resolves a module through the first search-path entry holding a directory named after its
root, so a namespace split over several packages is only found in one of them. Mirrors each such
directory into `tmp`, one symlink per file (the root module's own file included), and puts `tmp` first on the search path. -/
private def mergeSplitRoots (tmp : System.FilePath) : IO Unit := do
  let sp ← searchPathRef.get
  let mut seen : Std.HashMap String (Array System.FilePath) := {}
  for entry in sp.eraseDups do
    unless ← entry.isDir do continue
    for child in ← entry.readDir do
      if ← child.path.isDir then
        seen := seen.alter child.fileName (some <| ·.getD #[] |>.push child.path)
  let mut merged := false
  for (name, dirs) in seen do
    unless dirs.size > 1 do continue
    merged := true
    for dir in dirs do
      let rootFiles ← (dir.parent.getD ".").readDir
      let own := rootFiles.filter (·.fileName.startsWith s!"{name}.") |>.map (·.path)
      for file in own ++ (← dir.walkDir) do
        if ← file.isDir then continue
        let dest := if file.parent == dir.parent then tmp / file.fileName.getD ""
          else tmp / name / (file.toString.drop (dir.toString.length + 1)).toString
        if let some parent := dest.parent then IO.FS.createDirAll parent
        if ← dest.pathExists then continue
        let child ← IO.Process.output { cmd := "ln", args := #["-s", file.toString, dest.toString] }
        if child.exitCode != 0 then throw <| IO.userError s!"cannot link {file}: {child.stderr}"
  if merged then searchPathRef.set (tmp :: sp)

/-- Imports `roots` and prints their API lines. -/
def run (roots : Array Name) : IO Unit := do
  initSearchPath (← findSysroot)
  IO.FS.withTempDir fun tmp => do
    mergeSplitRoots tmp
    unsafe enableInitializersExecution
    let env ← importModules (roots.map ({ module := · })) {} (loadExts := true)
    let ctx : Core.Context := { fileName := "<api-lock>", fileMap := default }
    let (lines, _) ← (apiLines roots).run' |>.toIO ctx { env }
    for line in lines do IO.println line

end InkproofTools.ApiLock
