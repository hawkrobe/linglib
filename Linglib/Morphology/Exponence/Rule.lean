import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Finite.Basic

/-!
# Rules of exponence
[kiparsky-1973] [halle-marantz-1993] [stump-2001]

A **rule of exponence** pairs an exponent with an applicability
condition on contexts. `RuleLike` is the interface every framework
engine's carrier implements: an exponent projection and an
applicability set, ordered by set inclusion ([kiparsky-1973]'s
Elsewhere Condition). Elsewhere selection is minimality in this order —
the most specific applicable rule has the smallest domain.

`Rule Ctx F` is the free carrier. Framework engines (the containment
hierarchy, DM vocabulary items, nanosyntax spellout) implement
`RuleLike` on their own intensional carriers (thresholds, feature
bundles, stored trees) and install `RuleLike.toPreorder` as the
carrier's order, so the selection theorems apply to the native type
with no wrapper.

## Main declarations

* `Rule` — an exponent with its applicability condition
* `RuleLike` — the exponent-plus-applicability interface;
  `RuleLike.toPreorder` lifts applicability-set inclusion to a preorder
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

/-- Carriers whose values expone: an exponent projection and an
applicability set, à la `SetLike` minus injectivity. Distinct rules may
share an applicability set while carrying different exponents, so there
is no `coe_injective` and the induced order is only a preorder
(`toPreorder`), never a partial order. Framework engines instantiate
this on their intensional carriers and derive Elsewhere selection over
the native type. -/
class RuleLike (R : Type*) (Ctx F : outParam Type*) where
  /-- The exponent a rule inserts. -/
  exponent : R → F
  /-- The set of contexts a rule applies in. -/
  applySet : R → Set Ctx

namespace RuleLike

variable {R : Type*} [RuleLike R Ctx F]

/-- A rule applies at a context when the context is in its
applicability set. -/
def Applies (r : R) (c : Ctx) : Prop := c ∈ applySet (F := F) r

/-- The preorder a carrier opts into: applicability-set inclusion. Not a
global instance — each engine installs it (or a defeq order) on its own
carrier. -/
@[reducible] def toPreorder : Preorder R := Preorder.lift (applySet (F := F))

end RuleLike

/-- The free carrier exposes its fields as the interface. -/
instance : RuleLike (Rule Ctx F) Ctx F := ⟨Rule.exponent, Rule.applySet⟩

variable {R : Type*} [Preorder R] [RuleLike R Ctx F]

/-- An **Elsewhere winner** for vocabulary `v` at context `c`: a
`≤`-minimal applicable member of `v` — no applicable rule in `v` is
strictly more specific. -/
def IsElsewhereWinner (v : List R) (c : Ctx) (r : R) : Prop :=
  Minimal (fun s => s ∈ v ∧ RuleLike.Applies (F := F) s c) r

/-- A winner is at least as specific as any applicable member of the
vocabulary that is at least as specific as it. -/
theorem IsElsewhereWinner.le_of_le {v : List R} {c : Ctx} {r s : R}
    (hr : IsElsewhereWinner v c r) (hs : s ∈ v)
    (happ : RuleLike.Applies (F := F) s c) (h : s ≤ r) : r ≤ s :=
  Minimal.le_of_le hr ⟨hs, happ⟩ h

/-! ### Selection: existence, coherence, uniqueness -/

/-- Comparable Elsewhere winners at the same context are equivalent. -/
theorem IsElsewhereWinner.antisymmRel {v : List R} {c : Ctx} {r s : R}
    (hr : IsElsewhereWinner v c r) (hs : IsElsewhereWinner v c s)
    (h : s ≤ r ∨ r ≤ s) : AntisymmRel (· ≤ ·) r s := by
  rcases h with h | h
  · exact ⟨hr.le_of_le hs.1.1 hs.1.2 h, h⟩
  · exact ⟨h, hs.le_of_le hr.1.1 hr.1.2 h⟩

/-- A **coherent** vocabulary assigns equivalent rules the same
exponent, so the exponent descends to the antisymmetrization of the
specificity preorder ([caha-2009]-style antihomophony, stated
order-theoretically). -/
def Coherent (v : List R) : Prop :=
  ∀ r ∈ v, ∀ s ∈ v, AntisymmRel (· ≤ ·) r s →
    RuleLike.exponent (F := F) r = RuleLike.exponent (F := F) s

/-- Over a coherent vocabulary, comparable winners select the same
exponent: Elsewhere selection is well defined up to incomparability. -/
theorem IsElsewhereWinner.exponent_eq {v : List R} {c : Ctx} {r s : R}
    (hv : Coherent v) (hr : IsElsewhereWinner v c r)
    (hs : IsElsewhereWinner v c s) (h : s ≤ r ∨ r ≤ s) :
    RuleLike.exponent (F := F) r = RuleLike.exponent (F := F) s :=
  hv r hr.1.1 s hs.1.1 (hr.antisymmRel hs h)

/-- A vocabulary with an applicable rule has an Elsewhere winner. -/
theorem exists_isElsewhereWinner {v : List R} {c : Ctx}
    (h : ∃ r ∈ v, RuleLike.Applies (F := F) r c) : ∃ r, IsElsewhereWinner v c r :=
  (v.finite_toSet.subset fun _ hr => hr.1).exists_minimal h

end Morphology.Exponence
