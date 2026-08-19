import Linglib.Semantics.Dynamic.Update
import Linglib.Semantics.Intensional.Index
import Linglib.Semantics.Dynamic.Possibility
import Linglib.Semantics.Tense.Compositional

/-!
# Dynamic tense as eliminative update of static tense
[veltman-1996] [groenendijk-stokhof-veltman-1996] [de-groote-2006] [charlow-2021] [heim-1982]

`dynPAST`/`dynPRES`/`dynFUT` are the dynamic-context-update counterparts
of the static `PAST`/`PRES`/`FUT` operators in `Tense/Compositional.lean`.
Each is the spine's test filter `lift (test ·)` at the tense cell
(`Tense/Defs.lean`) between two dref lookups — so the static and dynamic
operators are *the same cell*, lifted from a state-level predicate to a
context-level filter, and the temporal algebra (partition, contradiction,
chaining) is the cells' Boolean algebra (`Core.Order.holds_or_holds₃`,
`Core.Order.not_holds_and_holds`) through the generic filter algebra of
`Update.lean` (`lift_test_cover₃`, `lift_test_disjoint`).

Contexts are level-0 states over `Index.Possibility` — the
world coordinate is the current evaluation index, drefs are indices.

## Theoretical anchor

- [heim-1982] principle (A) — file change for a static condition is
  intersection with the satisfaction set — is the prototype "static
  condition lifts to context filter"; [veltman-1996] formalizes it as
  the *test*, and [groenendijk-stokhof-veltman-1996] generalize to
  eliminative updates (`CCP.IsEliminative`).
- [de-groote-2006] recovers static readings from dynamic ones by the
  trivial continuation; [charlow-2021] recasts the lift monadically.
  The `dynPAST = lift (test (holds past · ·))` factoring below is the
  tense fragment of that lift.

## Main results

- `dynPAST_iff_PAST_with_true` (and PRES/FUT): a context entry survives
  the dynamic filter iff the static operator holds at its
  event/reference indices — the "wrapper actually wraps" check.
- `temporal_partition`, the contradictory-pair lemmas, and
  `dynPAST_transitive`: the temporal algebra, derived from the cells'
  Boolean algebra through the spine's filter algebra.

Sibling of `Tense/Compositional.lean` (the static operators) and
`Mood/Dynamic.lean` (the parallel pattern for SUBJ/IND). Used by
`Studies/Mendes2025.lean`'s analysis of the Subordinate Future.
-/

namespace Tense

open Core.Order (holds)
open _root_.Intensional (Index)
open DynamicSemantics
open DynamicSemantics.Update (test closure)

variable {W Time : Type*} [LinearOrder Time]

/-- Dynamic PAST: the spine's test filter at the `past` cell. A context
    entry survives iff its event-variable index precedes its
    reference-variable index in time. -/
def dynPAST (eventVar refVar : ℕ) :
    Set (Index.Possibility W Time) →
      Set (Index.Possibility W Time) :=
  lift (test fun p =>
    holds past (p.assignment eventVar).time (p.assignment refVar).time)

/-- Dynamic PRES: the test filter at the `present` cell. -/
def dynPRES (eventVar refVar : ℕ) :
    Set (Index.Possibility W Time) →
      Set (Index.Possibility W Time) :=
  lift (test fun p =>
    holds present (p.assignment eventVar).time (p.assignment refVar).time)

/-- Dynamic FUT: the test filter at the `future` cell. -/
def dynFUT (eventVar refVar : ℕ) :
    Set (Index.Possibility W Time) →
      Set (Index.Possibility W Time) :=
  lift (test fun p =>
    holds future (p.assignment eventVar).time (p.assignment refVar).time)

variable (e r : ℕ) (c : Set (Index.Possibility W Time))
  (p : Index.Possibility W Time)

/-! ### Membership characterizations -/

@[simp] theorem mem_dynPAST :
    p ∈ dynPAST e r c ↔
      p ∈ c ∧ (p.assignment e).time < (p.assignment r).time := by
  simp [dynPAST, mem_lift_test]

@[simp] theorem mem_dynPRES :
    p ∈ dynPRES e r c ↔
      p ∈ c ∧ (p.assignment e).time = (p.assignment r).time := by
  simp [dynPRES, mem_lift_test]

@[simp] theorem mem_dynFUT :
    p ∈ dynFUT e r c ↔
      p ∈ c ∧ (p.assignment r).time < (p.assignment e).time := by
  simp [dynFUT, mem_lift_test]

/-! ### Static realization: dynamic IS the eliminative update of static

For each tense, the static operator (with the trivial propositional
payload `fun _ => True`) holds at the entry's event/reference indices iff
the dynamic filter retains the entry — the [de-groote-2006] sense in
which static and dynamic tense are the same operator at different
layers. -/

theorem dynPAST_iff_PAST_with_true :
    p ∈ dynPAST e r c ↔
      p ∈ c ∧ PAST (fun _ => True) (p.assignment e) (p.assignment r) := by
  simp

theorem dynPRES_iff_PRES_with_true :
    p ∈ dynPRES e r c ↔
      p ∈ c ∧ PRES (fun _ => True) (p.assignment e) (p.assignment r) := by
  simp

theorem dynFUT_iff_FUT_with_true :
    p ∈ dynFUT e r c ↔
      p ∈ c ∧ FUT (fun _ => True) (p.assignment e) (p.assignment r) := by
  simp

/-! ### Temporal algebra (cell algebra through the filter algebra) -/

/-- PAST ∪ PRES ∪ FUT = identity: `lift_test_cover₃` at the cells' cover
`past ⊔ present ⊔ future = ⊤`. -/
theorem temporal_partition (v₁ v₂ : ℕ) :
    dynPAST v₁ v₂ c ∪ dynPRES v₁ v₂ c ∪ dynFUT v₁ v₂ c = c := by
  unfold dynPAST dynPRES dynFUT
  exact lift_test_cover₃ _ _ _
    (fun p => Core.Order.holds_or_holds₃
      (s := past) (t := present) (u := future) (by decide)
      (p.assignment v₁).time (p.assignment v₂).time) c

/-- PAST and FUT are contradictory on the same variables:
`lift_test_disjoint` at the disjoint cells `past ⊓ future = ⊥`. -/
theorem dynPAST_dynFUT_empty (v₁ v₂ : ℕ) :
    dynPAST v₁ v₂ (dynFUT v₁ v₂ c) = ∅ := by
  unfold dynPAST dynFUT
  exact lift_test_disjoint _ _
    (fun p h₂ h₁ => Core.Order.not_holds_and_holds
      (s := past) (t := future) (by decide) _ _ ⟨h₁, h₂⟩) c

/-- PAST and PRES are contradictory on the same variables. -/
theorem dynPAST_dynPRES_empty (v₁ v₂ : ℕ) :
    dynPAST v₁ v₂ (dynPRES v₁ v₂ c) = ∅ := by
  unfold dynPAST dynPRES
  exact lift_test_disjoint _ _
    (fun p h₂ h₁ => Core.Order.not_holds_and_holds
      (s := past) (t := present) (by decide) _ _ ⟨h₁, h₂⟩) c

/-- PRES and FUT are contradictory on the same variables. -/
theorem dynPRES_dynFUT_empty (v₁ v₂ : ℕ) :
    dynPRES v₁ v₂ (dynFUT v₁ v₂ c) = ∅ := by
  unfold dynPRES dynFUT
  exact lift_test_disjoint _ _
    (fun p h₂ h₁ => Core.Order.not_holds_and_holds
      (s := present) (t := future) (by decide) _ _ ⟨h₁, h₂⟩) c

/-- Chained PAST constraints compose: e < r ∧ r < s → e < s. -/
theorem dynPAST_transitive (e r s : ℕ)
    (h : p ∈ dynPAST r s (dynPAST e r c)) :
    (p.assignment e).time < (p.assignment s).time := by
  rw [mem_dynPAST, mem_dynPAST] at h
  exact lt_trans h.1.2 h.2

end Tense
