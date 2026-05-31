import Mathlib.Tactic.TypeStar

/-!
# DRS Syntax: Discourse Representation Structures
@cite{kamp-reyle-1993} @cite{muskens-1996}

Pure syntactic representation of DRS expressions with structural
operations — no semantic imports, no interpretation.

## Definitions

- `DRS`: recursive syntax for DRS boxes, conditions, and connectives
- `adr K`: active discourse referents (drefs introduced by `K`)
- `occurs u K`: whether dref `u` occurs in `K`
- `acc u K`: drefs accessible from `u`'s occurrence in `K`
- `isFree u K`: `u` occurs in `K` but is not accessible
- `isProper K`: no free referents (@cite{muskens-1996}, p. 171)

## Design

This module is the pure-syntax layer of the four-layer dynamic
semantics architecture:

```
DynProp.lean       ← semantic algebra (DRS S, dseq, test, ...)
DynamicTy2.lean    ← compositional layer (Dref, AssignmentStructure)
DRS.lean       ← DRS syntax (this file)
Accessibility.lean ← interpretation bridge (DRS → DRS)
```

`DRS` has no dependency on the semantic algebra (`DRS S`) or
compositional types (`Dref`, `Assign`). Interpretation is defined
in `Accessibility.lean` via `interp : DRS → DRS (Assign E)`.
-/

-- ════════════════════════════════════════════════════════════════
-- § 1. DRS Syntax
-- ════════════════════════════════════════════════════════════════

/-- Syntactic representation of DRS expressions.

Dref indices are natural numbers. Relation symbols are identified
by natural number indices; their arity is implicit in the dref list. -/
inductive DRS where
  /-- Atomic condition: relation R applied to drefs -/
  | atom (rel : Nat) (drefs : List Nat) : DRS
  /-- Identity condition: u₁ is u₂ -/
  | is (u v : Nat) : DRS
  /-- Negation: not K -/
  | neg (K : DRS) : DRS
  /-- Disjunction: K₁ or K₂ -/
  | disj (K₁ K₂ : DRS) : DRS
  /-- Implication: K₁ ⇒ K₂ -/
  | impl (K₁ K₂ : DRS) : DRS
  /-- Box: [u₁,...,uₙ | γ₁,...,γₘ] -/
  | box (newDrefs : List Nat) (conds : List DRS) : DRS
  /-- Sequencing: K₁ ; K₂ -/
  | seq (K₁ K₂ : DRS) : DRS
  deriving Repr

namespace DRS

-- ════════════════════════════════════════════════════════════════
-- § 2. Active Discourse Referents
-- ════════════════════════════════════════════════════════════════

/-- Active discourse referents: the drefs *introduced* by `K`.

`adr([u₁,...,uₙ | γ₁,...,γₘ]) = {u₁,...,uₙ}`
`adr(K₁ ; K₂) = adr(K₁) ∪ adr(K₂)`

Conditions (atoms, negation, disjunction, implication) introduce no drefs. -/
def adr : DRS → List Nat
  | .atom _ _ => []
  | .is _ _ => []
  | .neg _ => []
  | .disj _ _ => []
  | .impl _ _ => []
  | .box newDrefs _ => newDrefs
  | .seq K₁ K₂ => adr K₁ ++ adr K₂

-- ════════════════════════════════════════════════════════════════
-- § 3. Occurrence and Accessibility
-- ════════════════════════════════════════════════════════════════

/-- Whether dref `u` occurs anywhere in expression `K`. -/
def occurs (u : Nat) : DRS → Bool
  | .atom _ drefs => drefs.contains u
  | .is v w => u == v || u == w
  | .neg K => occurs u K
  | .disj K₁ K₂ => occurs u K₁ || occurs u K₂
  | .impl K₁ K₂ => occurs u K₁ || occurs u K₂
  | .box newDrefs conds => newDrefs.contains u || occursAny u conds
  | .seq K₁ K₂ => occurs u K₁ || occurs u K₂
where
  occursAny (u : Nat) : List DRS → Bool
    | [] => false
    | c :: cs => occurs u c || occursAny u cs

/-- Accessible drefs from an occurrence of `u` in `K`.

Defined by structural recursion following @cite{muskens-1996} pp. 170–171:
- Atomic: no drefs are accessible
- Negation: accessibility passes through
- Disjunction/implication: accessibility from the branch containing `u`,
  with antecedent drefs accessible in the consequent
- Box: new drefs are accessible, plus accessibility from the condition containing `u`
- Sequencing: drefs from `K₁` are accessible in `K₂` -/
def acc (u : Nat) : DRS → List Nat
  | .atom _ _ => []
  | .is _ _ => []
  | .neg K => acc u K
  | .disj K₁ K₂ =>
    if occurs u K₁ then acc u K₁ else acc u K₂
  | .impl K₁ K₂ =>
    if occurs u K₁ then acc u K₁
    else acc u K₂ ++ adr K₁
  | .box newDrefs conds =>
    match accFind u conds with
    | some r => r ++ newDrefs
    | none => newDrefs
  | .seq K₁ K₂ =>
    if occurs u K₁ then acc u K₁
    else acc u K₂ ++ adr K₁
where
  /-- Find the first condition containing `u` and return its accessible drefs. -/
  accFind (u : Nat) : List DRS → Option (List Nat)
    | [] => none
    | c :: cs => if occurs u c then some (acc u c) else accFind u cs

/-- Collect all dref indices mentioned anywhere in `K`. -/
def allOccurring : DRS → List Nat
  | .atom _ drefs => drefs
  | .is v w => [v, w]
  | .neg K => allOccurring K
  | .disj K₁ K₂ => allOccurring K₁ ++ allOccurring K₂
  | .impl K₁ K₂ => allOccurring K₁ ++ allOccurring K₂
  | .box newDrefs conds => newDrefs ++ allOccurringList conds
  | .seq K₁ K₂ => allOccurring K₁ ++ allOccurring K₂
where
  allOccurringList : List DRS → List Nat
    | [] => []
    | c :: cs => allOccurring c ++ allOccurringList cs

/-- A dref `u` is *free* in `K` if it occurs in `K` but is not
among the drefs accessible from its position. -/
def isFree (u : Nat) (K : DRS) : Bool :=
  occurs u K && !(acc u K).contains u

/-- *Local* properness: no referent is free at its first occurrence.

**Unsound for cross-disjunction binding**: it conflates accessibility across
disjunction branches, so e.g. `[u | P u] ∨ [| Q u]` passes even though `u` is
free in the second disjunct. For the soundness-certified check (which
`proposition_1` proves equivalent to closed weakest-preconditions) use
`DRS.isProper` (`= allBound []`) in `Boxes/Accessibility.lean`. -/
def locallyProper (K : DRS) : Bool :=
  (allOccurring K).all (λ u => !(isFree u K))

-- ════════════════════════════════════════════════════════════════
-- § 4. Discourse-referent renaming
-- ════════════════════════════════════════════════════════════════

/-- Rename discourse referent `old` to `new`, stopping at any box that re-binds
`old` (capture-avoidance on the `old` side). The caller must ensure `new` is
accessible at the substitution site so the renamed occurrences are not captured
by an inner binder — exactly the licensing condition when a presupposition binds
to an accessible antecedent (@cite{van-der-sandt-1992}). -/
def rename (old new : Nat) : DRS → DRS
  | .atom r ds => .atom r (ds.map fun d => if d == old then new else d)
  | .is u v => .is (if u == old then new else u) (if v == old then new else v)
  | .neg K => .neg (rename old new K)
  | .disj K₁ K₂ => .disj (rename old new K₁) (rename old new K₂)
  | .impl K₁ K₂ => .impl (rename old new K₁) (rename old new K₂)
  | .box ds cs =>
      if ds.contains old then .box ds cs
      else .box ds (renameList old new cs)
  | .seq K₁ K₂ => .seq (rename old new K₁) (rename old new K₂)
where
  renameList (old new : Nat) : List DRS → List DRS
    | [] => []
    | c :: cs => rename old new c :: renameList old new cs

private theorem map_rename_self (a : Nat) (ds : List Nat) :
    ds.map (fun d => if d == a then a else d) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [List.map_cons, ih]; split <;> simp_all

mutual
/-- Renaming a referent to itself is the identity. -/
@[simp] theorem rename_self (a : Nat) (K : DRS) : rename a a K = K := by
  match K with
  | .atom r ds => simp only [rename, map_rename_self]
  | .is u v => simp only [rename]; congr 1 <;> (split <;> simp_all)
  | .neg K => simp only [rename, rename_self a K]
  | .disj K₁ K₂ => simp only [rename, rename_self a K₁, rename_self a K₂]
  | .impl K₁ K₂ => simp only [rename, rename_self a K₁, rename_self a K₂]
  | .box ds cs =>
      simp only [rename]
      split
      · rfl
      · rw [renameList_self a cs]
  | .seq K₁ K₂ => simp only [rename, rename_self a K₁, rename_self a K₂]
theorem renameList_self (a : Nat) (cs : List DRS) :
    rename.renameList a a cs = cs := by
  match cs with
  | [] => rfl
  | c :: cs => simp only [rename.renameList, rename_self a c, renameList_self a cs]
end

/-- A box's own discourse referents are accessible from any occurrence inside it.
This is the general form of the parasitic-accessibility fact: referents
introduced in an outer (belief) box are visible from an embedded (desire)
sub-box. -/
theorem box_drefs_subset_acc (u : Nat) (ds : List Nat) (cs : List DRS) :
    ds ⊆ acc u (.box ds cs) := by
  simp only [acc]
  cases acc.accFind u cs with
  | none => exact List.Subset.refl ds
  | some r => exact List.subset_append_right r ds

/-- `occurs` distributes over sequencing. -/
@[simp] theorem occurs_seq (u : Nat) (K₁ K₂ : DRS) :
    occurs u (.seq K₁ K₂) = (occurs u K₁ || occurs u K₂) := rfl

/-- `occurs` sees through negation. -/
@[simp] theorem occurs_neg (u : Nat) (K : DRS) : occurs u (.neg K) = occurs u K := rfl

/-- Active discourse referents distribute over sequencing. -/
@[simp] theorem adr_seq (K₁ K₂ : DRS) : adr (.seq K₁ K₂) = adr K₁ ++ adr K₂ := rfl

-- ════════════════════════════════════════════════════════════════
-- § 5. Verification Examples
-- ════════════════════════════════════════════════════════════════

/-- "A man adores a woman" as a syntactic DRS.

`[u₁ u₂ | man u₁, woman u₂, u₁ adores u₂]`

Using relation indices: 0 = man, 1 = woman, 2 = adores. -/
def exManAdoresWoman : DRS :=
  .box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]]

/-- The example DRS is proper: all drefs (1, 2) are introduced by the box. -/
example : locallyProper exManAdoresWoman = true := by decide

/-- "If a farmer owns a donkey, he beats it" as a syntactic DRS.

`[u₁ u₂ | farmer u₁, donkey u₂, u₁ owns u₂] ⇒ [| u₁ beats u₂]`

Using relation indices: 0 = farmer, 1 = donkey, 2 = owns, 3 = beats. -/
def exDonkey : DRS :=
  .impl
    (.box [1, 2] [.atom 0 [1], .atom 1 [2], .atom 2 [1, 2]])
    (.box [] [.atom 3 [1, 2]])

/-- The donkey sentence is proper: drefs 1, 2 are introduced in the
antecedent and accessible in the consequent. -/
example : locallyProper exDonkey = true := by decide

/-- "He₁ stinks" (with no antecedent) is NOT proper: dref 1 is free. -/
def exFree : DRS := .box [] [.atom 0 [1]]

example : locallyProper exFree = false := by decide

end DRS
