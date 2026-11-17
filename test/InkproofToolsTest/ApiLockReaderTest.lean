/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofTools.ApiLock
import InkproofTools.ApiLock.Reader
import InkproofToolsTest.ApiLockFixture

/-! The reader recovers exactly the theorems the writer wrote, from the fixture's own output. -/

open Lean Meta InkproofTools.ApiLock

/-- Fails unless `cond`. -/
private def expect (cond : Bool) (msg : String) : MetaM Unit :=
  unless cond do throwError msg

run_meta do
  let lines ← apiLines #[`InkproofToolsTest.ApiLockFixture]
  let thms := lines.filterMap parseTheorem
  expect (thms.map (·.name) == #["Fixture.total_line", "Fixture.total_nil"])
    s!"theorems read back: {thms.map (·.name)}"
  expect (lines.size > thms.size + 5) "fixture lacks non-theorem declarations"
  for line in lines do
    let isThm := line.startsWith "theorem "
    expect (isThm == (parseTheorem line).isSome) s!"kind misread: {line}"
    if let some t := parseTheorem line then
      expect (line == theoremLine t.name t.statement) s!"line does not round-trip: {line}"
  let some line := lines.find? (·.startsWith "theorem Fixture.total_line ")
    | throwError "missing theorem line"
  expect ((parseTheorem line).map (·.statement) == some "∀ (n : Nat), Fixture.total [Fixture.Shape.line n] = n")
    "statement with an inner colon misread"
  expect (declares line "total_line" ["Fixture"]) "relative name not found"
  expect (declares line "Fixture.total_line")  "full name not found"
  expect (declares line "total_line" ["Other", "Fixture"] == false) "wrong namespace accepted"
  expect (!declares "def Fixture.total_line : Nat" "Fixture.total_line") "non-theorem accepted"
