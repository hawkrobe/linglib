import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Finite.Basic

/-!
# Rules of exponence
[kiparsky-1973] [halle-marantz-1993] [stump-2001]

A **rule of exponence** pairs an exponent with an applicability
condition on contexts. Rules are preordered by applicability-set
inclusion ([kiparsky-1973]'s Elsewhere Condition), and Elsewhere
selection is minimality in this order: the most specific applicable
rule is the one with the smallest domain.

Framework engines (the containment hierarchy, DM vocabulary items,
nanosyntax spellout) specialize `Ctx` and connect to this core through
`toRule` maps and winner theorems in their own files.

## Main declarations

* `Rule` — an exponent with its applicability condition
* `Rule.applySet` — a rule's applicability set; `r ≤ s` iff
  `r.applySet ⊆ s.applySet`
* `IsElsewhereWinner` — a `≤`-minimal applicable rule in a vocabulary
* `Coherent` — equivalent rules share an exponent; with
  `IsElsewhereWinner.exponent_eq`, comparable winners then select one
  exponent, and `exists_isElsewhereWinner` provides a winner whenever
  some rule applies
-/

namespace Morphology.Exponence

variable {Ctx F : Type*}

/-- A **rule of exponence**: an exponent paired with the condition on
contexts under which the rule applies. Framework engines specialize
`Ctx` and recover applicability from intensional specifications
(thresholds, feature bundles, stored trees). -/
structure Rule (Ctx : Type*) (F : Type*) where
  /-- The exponent the rule inserts. -/
  exponent : F
  /-- The contexts in which the rule applies. -/
  Applies : Ctx → Prop

namespace Rule

/-- The set of contexts a rule applies in. -/
def applySet (r : Rule Ctx F) : Set Ctx := {c | r.Applies c}

@[simp] theorem mem_applySet {r : Rule Ctx F} {c : Ctx} :
    c ∈ r.applySet ↔ r.Applies c :=
  Iff.rfl

/-- Rules are preordered by applicability-set inclusion: `r ≤ s` when
`r` applies in a subset of the contexts `s` applies in, i.e. `r` is at
least as specific as `s`. Only a preorder — rules with the same
applicability but different exponents are equivalent, not equal. -/
instance : Preorder (Rule Ctx F) := .lift applySet

theorem le_def {r s : Rule Ctx F} : r ≤ s ↔ r.applySet ⊆ s.applySet :=
  Iff.rfl

/-- Derived Pāṇinian specificity, unfolded: `r ≤ s` iff `s` applies
wherever `r` does. -/
theorem le_iff {r s : Rule Ctx F} :
    r ≤ s ↔ ∀ ⦃c⦄, r.Applies c → s.Applies c :=
  Iff.rfl

end Rule

/-- An **Elsewhere winner** for vocabulary `v` at context `c`: a
`≤`-minimal applicable member of `v` — no applicable rule in `v` is
strictly more specific. -/
def IsElsewhereWinner (v : List (Rule Ctx F)) (c : Ctx) (r : Rule Ctx F) : Prop :=
  Minimal (fun s => s ∈ v ∧ s.Applies c) r

/-- A winner is at least as specific as any applicable member of the
vocabulary that is at least as specific as it. -/
theorem IsElsewhereWinner.le_of_le {v : List (Rule Ctx F)} {c : Ctx}
    {r s : Rule Ctx F} (hr : IsElsewhereWinner v c r) (hs : s ∈ v)
    (happ : s.Applies c) (h : s ≤ r) : r ≤ s :=
  Minimal.le_of_le hr ⟨hs, happ⟩ h

/-! ### Selection: existence, coherence, uniqueness -/

/-- Comparable Elsewhere winners at the same context are equivalent. -/
theorem IsElsewhereWinner.antisymmRel {v : List (Rule Ctx F)} {c : Ctx}
    {r s : Rule Ctx F} (hr : IsElsewhereWinner v c r)
    (hs : IsElsewhereWinner v c s) (h : s ≤ r ∨ r ≤ s) :
    AntisymmRel (· ≤ ·) r s := by
  rcases h with h | h
  · exact ⟨hr.le_of_le hs.1.1 hs.1.2 h, h⟩
  · exact ⟨h, hs.le_of_le hr.1.1 hr.1.2 h⟩

/-- A **coherent** vocabulary assigns equivalent rules the same
exponent, so the exponent descends to the antisymmetrization of the
specificity preorder ([caha-2009]-style antihomophony, stated
order-theoretically). -/
def Coherent (v : List (Rule Ctx F)) : Prop :=
  ∀ r ∈ v, ∀ s ∈ v, AntisymmRel (· ≤ ·) r s → r.exponent = s.exponent

/-- Over a coherent vocabulary, comparable winners select the same
exponent: Elsewhere selection is well defined up to incomparability. -/
theorem IsElsewhereWinner.exponent_eq {v : List (Rule Ctx F)} {c : Ctx}
    {r s : Rule Ctx F} (hv : Coherent v) (hr : IsElsewhereWinner v c r)
    (hs : IsElsewhereWinner v c s) (h : s ≤ r ∨ r ≤ s) :
    r.exponent = s.exponent :=
  hv r hr.1.1 s hs.1.1 (hr.antisymmRel hs h)

/-- A vocabulary with an applicable rule has an Elsewhere winner. -/
theorem exists_isElsewhereWinner {v : List (Rule Ctx F)} {c : Ctx}
    (h : ∃ r ∈ v, r.Applies c) : ∃ r, IsElsewhereWinner v c r :=
  (v.finite_toSet.subset fun _ hr => hr.1).exists_minimal h

end Morphology.Exponence
