import Linglib.Semantics.Dynamic.Update
import Linglib.Semantics.Intensional.WorldTimeIndex
import Linglib.Semantics.Tense.Compositional

/-!
# Dynamic tense as eliminative update of static tense
[veltman-1996] [groenendijk-stokhof-veltman-1996] [de-groote-2006] [charlow-2021] [heim-1982]

`dynPAST`/`dynPRES`/`dynFUT` are the dynamic-context-update counterparts
of the static `PAST`/`PRES`/`FUT` operators in `Tense/Compositional.lean`.
Each is the spine's test filter `lift (test ·)` at the static temporal-
relation kernel (`precedes`/`coincides`/`follows`) between two dref
lookups — so the static and dynamic operators are *the same temporal
constraint*, lifted from a state-level predicate to a context-level
filter, and the temporal algebra (partition, contradiction, chaining) is
inherited from the generic filter algebra of `Update.lean`
(`lift_test_cover₃`, `lift_test_disjoint`) at the kernel facts of
`Tense/Compositional.lean`.

Contexts are level-0 states over `WorldTimeIndex.Possibility` — the
world coordinate is the current evaluation index, drefs are indices.

## Theoretical anchor

- [heim-1982] principle (A) — file change for a static condition is
  intersection with the satisfaction set — is the prototype "static
  condition lifts to context filter"; [veltman-1996] formalizes it as
  the *test*, and [groenendijk-stokhof-veltman-1996] generalize to
  eliminative updates (`CCP.IsEliminative`).
- [de-groote-2006] recovers static readings from dynamic ones by the
  trivial continuation; [charlow-2021] recasts the lift monadically.
  The `dynPAST = lift (test (precedes · ·))` factoring below is the
  tense fragment of that lift.

## Main results

- `dynPAST_iff_PAST_with_true` (and PRES/FUT): a context entry survives
  the dynamic filter iff the static operator holds at its
  event/reference indices — the "wrapper actually wraps" check.
- `temporal_partition`, the contradictory-pair lemmas, and
  `dynPAST_transitive`: the temporal algebra, derived from the kernel
  facts through the spine's filter algebra.

Sibling of `Tense/Compositional.lean` (the static kernel) and
`Mood/Dynamic.lean` (the parallel pattern for SUBJ/IND). Used by
`Studies/Mendes2025.lean`'s analysis of the Subordinate Future.
-/

namespace Tense

open _root_.Intensional (WorldTimeIndex)
open DynamicSemantics
open DynamicSemantics.Update (test closure)

variable {W Time : Type*}

/--
Dynamic PAST: the spine's test filter at the static `precedes` relation
between two dref lookups. A context entry survives iff its event-variable
index precedes its reference-variable index in time.
-/
def dynPAST [LT Time] (eventVar refVar : ℕ) :
    Set (WorldTimeIndex.Possibility W Time) →
      Set (WorldTimeIndex.Possibility W Time) :=
  lift (test fun p => precedes (p.assignment eventVar) (p.assignment refVar))

/-- Dynamic PRES: the test filter at `coincides`. -/
def dynPRES (eventVar refVar : ℕ) :
    Set (WorldTimeIndex.Possibility W Time) →
      Set (WorldTimeIndex.Possibility W Time) :=
  lift (test fun p => coincides (p.assignment eventVar) (p.assignment refVar))

/-- Dynamic FUT: the test filter at `follows`. -/
def dynFUT [LT Time] (eventVar refVar : ℕ) :
    Set (WorldTimeIndex.Possibility W Time) →
      Set (WorldTimeIndex.Possibility W Time) :=
  lift (test fun p => follows (p.assignment eventVar) (p.assignment refVar))

variable (e r : ℕ) (c : Set (WorldTimeIndex.Possibility W Time))
  (p : WorldTimeIndex.Possibility W Time)

/-! ### Membership characterizations -/

@[simp] theorem mem_dynPAST [LT Time] :
    p ∈ dynPAST e r c ↔ p ∈ c ∧ precedes (p.assignment e) (p.assignment r) :=
  mem_lift_test

@[simp] theorem mem_dynPRES :
    p ∈ dynPRES e r c ↔ p ∈ c ∧ coincides (p.assignment e) (p.assignment r) :=
  mem_lift_test

@[simp] theorem mem_dynFUT [LT Time] :
    p ∈ dynFUT e r c ↔ p ∈ c ∧ follows (p.assignment e) (p.assignment r) :=
  mem_lift_test

/-! ### Static realization: dynamic IS the eliminative update of static

For each tense, the static operator (with the trivial propositional
payload `fun _ => True`) holds at the entry's event/reference indices iff
the dynamic filter retains the entry — the [de-groote-2006] sense in
which static and dynamic tense are the same operator at different
layers. -/

theorem dynPAST_iff_PAST_with_true [LT Time] :
    p ∈ dynPAST e r c ↔
      p ∈ c ∧ PAST (fun _ => True) (p.assignment e) (p.assignment r) :=
  ⟨fun h => ⟨(mem_lift_test.mp h).1, (mem_lift_test.mp h).2, trivial⟩,
   fun ⟨hc, hp, _⟩ => mem_lift_test.mpr ⟨hc, hp⟩⟩

theorem dynPRES_iff_PRES_with_true :
    p ∈ dynPRES e r c ↔
      p ∈ c ∧ PRES (fun _ => True) (p.assignment e) (p.assignment r) :=
  ⟨fun h => ⟨(mem_lift_test.mp h).1, (mem_lift_test.mp h).2, trivial⟩,
   fun ⟨hc, hp, _⟩ => mem_lift_test.mpr ⟨hc, hp⟩⟩

theorem dynFUT_iff_FUT_with_true [LT Time] :
    p ∈ dynFUT e r c ↔
      p ∈ c ∧ FUT (fun _ => True) (p.assignment e) (p.assignment r) :=
  ⟨fun h => ⟨(mem_lift_test.mp h).1, (mem_lift_test.mp h).2, trivial⟩,
   fun ⟨hc, hp, _⟩ => mem_lift_test.mpr ⟨hc, hp⟩⟩

/-! ### Temporal algebra (kernel facts through the filter algebra) -/

/-- PAST ∪ PRES ∪ FUT = identity: `lift_test_cover₃` at the kernel's
`precedes_or_coincides_or_follows`. -/
theorem temporal_partition [LinearOrder Time] (v₁ v₂ : ℕ) :
    dynPAST v₁ v₂ c ∪ dynPRES v₁ v₂ c ∪ dynFUT v₁ v₂ c = c := by
  unfold dynPAST dynPRES dynFUT
  exact lift_test_cover₃ _ _ _
    (fun p => precedes_or_coincides_or_follows
      (p.assignment v₁) (p.assignment v₂)) c

/-- PAST and FUT are contradictory on the same variables:
`lift_test_disjoint` at the kernel's `not_precedes_and_follows`. -/
theorem dynPAST_dynFUT_empty [Preorder Time] (v₁ v₂ : ℕ) :
    dynPAST v₁ v₂ (dynFUT v₁ v₂ c) = ∅ := by
  unfold dynPAST dynFUT
  exact lift_test_disjoint _ _
    (fun p h₂ h₁ => not_precedes_and_follows _ _ ⟨h₁, h₂⟩) c

/-- PAST and PRES are contradictory on the same variables. -/
theorem dynPAST_dynPRES_empty [Preorder Time] (v₁ v₂ : ℕ) :
    dynPAST v₁ v₂ (dynPRES v₁ v₂ c) = ∅ := by
  unfold dynPAST dynPRES
  exact lift_test_disjoint _ _
    (fun p h₂ h₁ => not_precedes_and_coincides _ _ ⟨h₁, h₂⟩) c

/-- PRES and FUT are contradictory on the same variables. -/
theorem dynPRES_dynFUT_empty [Preorder Time] (v₁ v₂ : ℕ) :
    dynPRES v₁ v₂ (dynFUT v₁ v₂ c) = ∅ := by
  unfold dynPRES dynFUT
  exact lift_test_disjoint _ _
    (fun p h₂ h₁ => not_coincides_and_follows _ _ ⟨h₁, h₂⟩) c

/-- Chained PAST constraints compose: e < r ∧ r < s → e < s. -/
theorem dynPAST_transitive [Preorder Time] (e r s : ℕ)
    (h : p ∈ dynPAST r s (dynPAST e r c)) :
    (p.assignment e).time < (p.assignment s).time :=
  lt_trans (mem_lift_test.mp (mem_lift_test.mp h).1).2 (mem_lift_test.mp h).2

end Tense
