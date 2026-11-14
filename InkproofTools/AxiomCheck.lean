/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

open Lean

namespace InkproofTools.AxiomCheck

/-- The problems with the declarations of the modules whose names start with `root`: an axiom
declared outside `axiomsModule` (or any axiom, if there is none), a declaration depending on an
axiom that is neither Lean's own nor declared in `axiomsModule`, or no declarations at all, which
would make the check pass vacuously. -/
def violations (env : Environment) (root : Name) (axiomsModule : Option Name := none) :
    CoreM (Array String) := do
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).bind (env.allImportedModuleNames[·.toNat]?)
  let mut listed : NameSet := ({} : NameSet).insert `propext |>.insert `Classical.choice
    |>.insert `Quot.sound
  let mut library : Array Name := #[]
  let mut problems : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless (moduleOf n).any root.isPrefixOf do continue
    library := library.push n
    if ci matches .axiomInfo _ then
      if moduleOf n != axiomsModule then
        problems := problems.push <| match axiomsModule with
          | some m => s!"axiom {n} is declared outside {m}"
          | none => s!"axiom {n} is declared, but none are allowed"
      else
        listed := listed.insert n
  if library.isEmpty then
    return #[s!"no declarations in modules under {root}; the check would pass vacuously"]
  for n in library do
    for a in ← collectAxioms n do
      unless listed.contains a do
        problems := problems.push s!"{n} depends on axiom {a}, which is not allowed"
  return problems

/-- Fails if `violations` finds anything. Call it from a `run_cmd` in a module that imports the
library. -/
def check (root : Name) (axiomsModule : Option Name := none) : CoreM Unit := do
  let problems ← violations (← getEnv) root axiomsModule
  unless problems.isEmpty do
    throwError "axiom check failed for {root}:\n{"\n".intercalate problems.toList}"

end InkproofTools.AxiomCheck
