/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! Reads the lines `api-lock` writes. Imports only Lean core, so a browser build can link it. -/

namespace InkproofTools.ApiLock

/-- A theorem's full name and its statement, as written on its line. -/
structure Theorem where
  name : String
  statement : String
  deriving Repr, BEq

/-- The line `api-lock` writes for a theorem. -/
def theoremLine (name statement : String) : String :=
  "theorem " ++ name ++ " : " ++ statement

private def theoremTag : List Char := "theorem ".toList

private def dropPrefix : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | p :: ps, c :: cs => if p == c then dropPrefix ps cs else none
  | _ :: _, [] => none

/-- Splits at the first `" : "`. A name never contains a space, so that is where the name ends. -/
private def splitAtColon : List Char → Option (List Char × List Char)
  | ' ' :: ':' :: ' ' :: rest => some ([], rest)
  | c :: cs => (splitAtColon cs).map fun (a, b) => (c :: a, b)
  | [] => none

/-- The theorem a line declares, or `none` if the line declares anything else. -/
def parseTheorem (line : String) : Option Theorem := do
  let rest ← dropPrefix theoremTag line.toList
  let (name, statement) ← splitAtColon rest
  some { name := String.ofList name, statement := String.ofList statement }

/-- The full name of `name` written inside `namespaces`. -/
def qualify (namespaces : List String) (name : String) : String :=
  match namespaces with
  | [] => name
  | _ => ".".intercalate namespaces ++ "." ++ name

/-- The full names a theorem written as `name` inside `namespaces` (outermost first) may stand for:
Lean tries the name in the innermost namespace first, then each enclosing one, then the root. -/
def candidates (namespaces : List String) (name : String) : List String :=
  (List.range (namespaces.length + 1)).reverse.map fun k => qualify (namespaces.take k) name

/-- Whether the line declares the theorem `name`, written in full or relative to `namespaces`. -/
def declares (line name : String) (namespaces : List String := []) : Bool :=
  match parseTheorem line with
  | some thm => (candidates namespaces name).contains thm.name
  | none => false

private def isNameEnd (c : Char) : Bool :=
  c.isWhitespace || c == ':' || c == '(' || c == '{' || c == '[' || c == '⦃'

private def dropOptional (p : String) (cs : List Char) : List Char :=
  (dropPrefix p.toList cs).getD cs

/-- The rest after the `]` that closes a bracket opened `depth` levels deep. -/
private def skipBracketed : Nat → List Char → Option (List Char)
  | _, [] => none
  | d, ']' :: cs => if d == 0 then some cs else skipBracketed (d - 1) cs
  | d, '[' :: cs => skipBracketed (d + 1) cs
  | d, _ :: cs => skipBracketed d cs

/-- Drops up to `fuel` leading `@[...]` blocks and the whitespace after each. An unterminated block
is left alone. -/
private def skipAttributes : Nat → List Char → List Char
  | 0, cs => cs
  | n + 1, cs =>
    match dropPrefix "@[".toList cs with
    | some rest =>
      match skipBracketed 0 rest with
      | some after => skipAttributes n (after.dropWhile Char.isWhitespace)
      | none => cs
    | none => cs

private def theoremNameOf (cs : List Char) : Option String := do
  let rest ← dropPrefix theoremTag (dropOptional "protected " (dropOptional "private " cs))
  let name := rest.takeWhile (!isNameEnd ·)
  if name.isEmpty then none else some (String.ofList name)

/-- The name a line of Lean source declares as a theorem, after any indentation, attributes and a
`private` or `protected` modifier. The name ends at whitespace, a colon or the first binder, so binders and a
statement on a later line do not matter. -/
def sourceTheoremName (line : String) : Option String :=
  let cs := line.toList.dropWhile Char.isWhitespace
  theoremNameOf (skipAttributes cs.length cs)

/-- Whether a line of Lean source declares the theorem `name`, written in full or relative to
`namespaces`. Unlike `declares`, which reads `API.lock` lines, the name may be followed by binders or
nothing at all. -/
def declaresInSource (line name : String) (namespaces : List String := []) : Bool :=
  match sourceTheoremName line with
  | some n => (candidates namespaces name).contains n
  | none => false

/-- Whether a line of Lean source, read inside `namespaces` (outermost first), declares the theorem
with the full name `fullName`: a declaration takes the name it is written with in the namespaces it
is inside. -/
def declaresInSourceAt (line fullName : String) (namespaces : List String) : Bool :=
  match sourceTheoremName line with
  | some n => qualify namespaces n == fullName
  | none => false

/-- Outside any namespace a name is its own full name. -/
theorem qualify_nil (name : String) : qualify [] name = name := rfl

/-- Inside namespaces, the full name is the namespaces and the name joined by dots. -/
theorem qualify_of_ne_nil (namespaces : List String) (name : String) (h : namespaces ≠ []) :
    qualify namespaces name = ".".intercalate namespaces ++ "." ++ name := by
  cases namespaces with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- The candidates are the name qualified by each prefix of the namespaces. -/
theorem mem_candidates (namespaces : List String) (name full : String) :
    full ∈ candidates namespaces name ↔
      ∃ k, k ≤ namespaces.length ∧ qualify (namespaces.take k) name = full := by
  simp only [candidates, List.mem_map, List.mem_reverse, List.mem_range]
  constructor
  · rintro ⟨k, hk, e⟩; exact ⟨k, by omega, e⟩
  · rintro ⟨k, hk, e⟩; exact ⟨k, by omega, e⟩

/-- Outside any namespace the only candidate is the name itself. -/
theorem candidates_nil (name : String) : candidates [] name = [name] := rfl

private theorem splitAtColon_cons (c : Char) (t : List Char) (hc : c ≠ ' ') :
    splitAtColon (c :: t) = (splitAtColon t).map fun (a, b) => (c :: a, b) := by
  cases t <;> simp [splitAtColon, hc]

private theorem splitAtColon_append (n s : List Char) (h : ' ' ∉ n) :
    splitAtColon (n ++ ' ' :: ':' :: ' ' :: s) = some (n, s) := by
  induction n with
  | nil => simp [splitAtColon]
  | cons c cs ih =>
    have hc : c ≠ ' ' := fun e => h (e ▸ List.mem_cons_self)
    have hcs : ' ' ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, splitAtColon_cons c _ hc, ih hcs]
    rfl

private theorem dropPrefix_append (p cs : List Char) : dropPrefix p (p ++ cs) = some cs := by
  induction p with
  | nil => rfl
  | cons c ps ih => simp [dropPrefix, ih]

/-- Reading back what `theoremLine` writes gives the theorem, for any name without a space. -/
theorem parseTheorem_theoremLine (name statement : String) (h : ' ' ∉ name.toList) :
    parseTheorem (theoremLine name statement) = some ⟨name, statement⟩ := by
  have hl : (theoremLine name statement).toList =
      theoremTag ++ (name.toList ++ ' ' :: ':' :: ' ' :: statement.toList) := by
    simp only [theoremLine, theoremTag, String.toList_append, List.append_assoc]
    rfl
  simp only [parseTheorem, hl, dropPrefix_append]
  simp only [bind, Option.bind]
  rw [splitAtColon_append _ _ h]
  simp

private theorem dropPrefix_some (p cs r : List Char) (h : dropPrefix p cs = some r) : cs = p ++ r := by
  induction p generalizing cs with
  | nil => simp [dropPrefix] at h; simp [h]
  | cons c ps ih =>
    match cs, h with
    | d :: ds, h =>
      simp only [dropPrefix] at h
      split at h
      · rename_i e; simp at e; simp [← e, ih ds h]
      · simp at h

private theorem splitAtColon_some (cs a b : List Char) (h : splitAtColon cs = some (a, b)) :
    cs = a ++ ' ' :: ':' :: ' ' :: b := by
  fun_induction splitAtColon cs generalizing a with
  | case1 rest => simp at h; simp [h]
  | case2 c cs hne ih =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨a', b'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    simp [ih a' h1]
  | case3 => simp at h

/-- Only the line `theoremLine` writes reads back as a theorem. -/
theorem eq_theoremLine_of_parseTheorem (line : String) (thm : Theorem) (h : parseTheorem line = some thm) :
    line = theoremLine thm.name thm.statement := by
  unfold parseTheorem at h
  cases hr : dropPrefix theoremTag line.toList with
  | none => simp [hr] at h
  | some rest =>
    cases hs : splitAtColon rest with
    | none => simp [hr, hs] at h
    | some ns =>
      obtain ⟨n, s⟩ := ns
      simp only [hr, hs, bind, Option.bind, Option.some.injEq] at h
      subst h
      have h1 := dropPrefix_some _ _ _ hr
      have h2 := splitAtColon_some _ _ _ hs
      rw [← String.toList_inj]
      simp only [theoremLine, String.toList_append, String.toList_ofList]
      rw [h1, h2]
      simp [theoremTag]

theorem declares_iff (line name : String) (namespaces : List String) :
    declares line name namespaces = true ↔
      ∃ thm, parseTheorem line = some thm ∧ thm.name ∈ candidates namespaces name := by
  unfold declares
  cases parseTheorem line <;> simp

/-- A theorem is found by its name relative to any prefix of the namespaces it was declared in. -/
theorem declares_relative (line name : String) (namespaces : List String) (k : Nat) (thm : Theorem)
    (h : parseTheorem line = some thm) (hk : k ≤ namespaces.length)
    (hn : thm.name = qualify (namespaces.take k) name) : declares line name namespaces = true := by
  rw [declares_iff]
  refine ⟨thm, h, ?_⟩
  simp only [candidates, List.mem_map, List.mem_reverse, List.mem_range]
  exact ⟨k, by omega, hn.symm⟩

/-- A theorem is found by its full name. -/
theorem declares_full (line name : String) (namespaces : List String) (thm : Theorem)
    (h : parseTheorem line = some thm) (hn : thm.name = name) : declares line name namespaces = true :=
  declares_relative line name namespaces 0 thm h (Nat.zero_le _) (by simp [qualify, hn])

theorem declaresInSource_iff (line name : String) (namespaces : List String) :
    declaresInSource line name namespaces = true ↔
      ∃ n, sourceTheoremName line = some n ∧ n ∈ candidates namespaces name := by
  unfold declaresInSource
  cases sourceTheoremName line <;> simp

theorem declaresInSourceAt_iff (line fullName : String) (namespaces : List String) :
    declaresInSourceAt line fullName namespaces = true ↔
      ∃ n, sourceTheoremName line = some n ∧ qualify namespaces n = fullName := by
  unfold declaresInSourceAt
  cases sourceTheoremName line <;> simp

private theorem skipAttributes_theorem (fuel : Nat) (r : List Char) :
    skipAttributes fuel (theoremTag ++ r) = theoremTag ++ r := by
  cases fuel <;> simp [skipAttributes, theoremTag, dropPrefix]

private theorem skipBracketed_zero (a rest : List Char) (h : ∀ c ∈ a, c ≠ '[' ∧ c ≠ ']') :
    skipBracketed 0 (a ++ ']' :: rest) = some rest := by
  induction a with
  | nil => simp [skipBracketed]
  | cons c cs ih =>
    obtain ⟨h1, h2⟩ := h c List.mem_cons_self
    have := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [List.cons_append]
    unfold skipBracketed
    split <;> simp_all

private theorem theoremNameOf_theorem (name tail : String) (hn : name ≠ "")
    (hf : ∀ d ∈ name.toList, isNameEnd d = false)
    (ht : ∀ c ∈ tail.toList.head?, isNameEnd c = true) :
    theoremNameOf (theoremTag ++ (name.toList ++ tail.toList)) = some name := by
  have htw : name.toList.takeWhile (!isNameEnd ·) = name.toList := by
    generalize name.toList = l at hf
    induction l with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.takeWhile, hf d List.mem_cons_self, Bool.not_false, List.cons.injEq, true_and]
      exact ih (fun e he => hf e (List.mem_cons_of_mem _ he))
  have hstop : (tail.toList).takeWhile (!isNameEnd ·) = [] := by
    cases h : tail.toList with
    | nil => rfl
    | cons c cs => have := ht c (by simp [h]); simp [List.takeWhile, this]
  have hne : name.toList ≠ [] := fun h => hn (by rw [← String.toList_inj]; simpa using h)
  have hp : ∀ q, q = "private " ∨ q = "protected " →
      dropOptional q (theoremTag ++ (name.toList ++ tail.toList)) = theoremTag ++ (name.toList ++ tail.toList) := by
    rintro q (rfl | rfl) <;> simp [dropOptional, theoremTag, dropPrefix]
  unfold theoremNameOf
  rw [hp "private " (Or.inl rfl), hp "protected " (Or.inr rfl)]
  simp only [bind, Option.bind, dropPrefix_append]
  simp [List.takeWhile_append, htw, hstop, hne]

private theorem dropWhile_theorem (r : List Char) :
    (theoremTag ++ r).dropWhile Char.isWhitespace = theoremTag ++ r := by
  simp [theoremTag, Char.isWhitespace]

private theorem skipAttributes_attribute (n : Nat) (attrs rest : List Char)
    (ha : ∀ c ∈ attrs, c ≠ '[' ∧ c ≠ ']') :
    skipAttributes (n + 1) ('@' :: '[' :: (attrs ++ ']' :: rest)) =
      skipAttributes n (rest.dropWhile Char.isWhitespace) := by
  have := skipBracketed_zero attrs rest ha
  simp [skipAttributes, dropPrefix, this]

/-- A theorem is still found behind an attribute block whose contents have no brackets. -/
theorem sourceTheoremName_attribute (attrs name tail : String) (hn : name ≠ "")
    (ha : ∀ c ∈ attrs.toList, c ≠ '[' ∧ c ≠ ']')
    (hf : ∀ d ∈ name.toList, isNameEnd d = false)
    (ht : ∀ c ∈ tail.toList.head?, isNameEnd c = true) :
    sourceTheoremName ("@[" ++ attrs ++ "] theorem " ++ name ++ tail) = some name := by
  have hl : ("@[" ++ attrs ++ "] theorem " ++ name ++ tail).toList =
      '@' :: '[' :: (attrs.toList ++ ']' :: ' ' :: (theoremTag ++ (name.toList ++ tail.toList))) := by
    simp only [String.toList_append, List.append_assoc]
    rfl
  unfold sourceTheoremName
  simp only []
  rw [hl, List.dropWhile_cons_of_neg (by simp [Char.isWhitespace])]
  rw [List.length_cons, skipAttributes_attribute _ _ _ ha, List.dropWhile_cons_of_pos (by simp [Char.isWhitespace]),
    dropWhile_theorem, skipAttributes_theorem, theoremNameOf_theorem name tail hn hf ht]

/-- An unindented `theorem` line declares the name up to the first whitespace, colon or binder. -/
theorem sourceTheoremName_theorem (name tail : String) (hn : name ≠ "")
    (hf : ∀ d ∈ name.toList, isNameEnd d = false)
    (ht : ∀ c ∈ tail.toList.head?, isNameEnd c = true) :
    sourceTheoremName ("theorem " ++ name ++ tail) = some name := by
  have hl : ("theorem " ++ name ++ tail).toList = theoremTag ++ (name.toList ++ tail.toList) := by
    simp only [String.toList_append, List.append_assoc]
    rfl
  unfold sourceTheoremName
  simp only []
  rw [hl, dropWhile_theorem, skipAttributes_theorem, theoremNameOf_theorem name tail hn hf ht]

end InkproofTools.ApiLock
