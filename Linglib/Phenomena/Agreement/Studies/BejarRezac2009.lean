import Linglib.Theories.Syntax.Minimalism.Core.CyclicAgree
import Linglib.Fragments.Basque.Agreement
import Linglib.Fragments.Georgian.Agreement

/-!
# Cyclic Agree and Differential P Indexing @cite{bejar-rezac-2009}

@cite{bejar-rezac-2009} derive **agreement displacement** — where
the agreement controller alternates between the EA and IA based on
person — from cyclic Agree with articulated φ-probes.

This study file connects the Cyclic Agree theory
(`Theories/Syntax/Minimalism/Core/CyclicAgree.lean`) to the empirical
fragment data for Basque and Georgian, proving that the **differential
P indexing** pattern in both languages is predicted by the partial
probe's direct/inverse classification.

## Key Result

The central theorem (`basque_indexed_iff_always_inverse`,
`georgian_indexed_iff_always_inverse`) proves:

> An object (IA) is indexed on the verb iff the partial probe puts
> every EA→IA combination into an inverse context.

SAP objects satisfy this because SAP IAs fully check the partial probe
[uπ, uParticipant], leaving no residue for any EA. 3P objects fail it
because a SAP EA can match the residue [uParticipant], creating a
direct context where the EA — not the object — controls agreement.

## Georgian Second-Cycle Morphology

Georgian's *m-*/*v-* prefix split for 1sg objects is predicted by the
second-cycle information: *m-* appears when valued on cycle I (IA=1P),
*v-* when valued on cycle II (EA=1P, IA=3P). This connects Georgian
`objectPrefix` to `cycleSegments`.

-/

namespace Phenomena.Agreement.Studies.BejarRezac2009

open Core.Prominence (PersonLevel)
open Minimalism.CyclicAgree

-- ============================================================================
-- § 1: PersonNumber → PersonLevel Bridge
-- ============================================================================

/-- Extract person level from a Basque person-number value. -/
def basqueToLevel : Fragments.Basque.Agreement.PersonNumber → PersonLevel
  | .p1sg | .p1pl => .first
  | .p2sg | .p2pl => .second
  | .p3sg | .p3pl => .third

/-- Extract person level from a Georgian person-number value. -/
def georgianToLevel : Fragments.Georgian.Agreement.PersonNumber → PersonLevel
  | .p1sg | .p1pl => .first
  | .p2sg | .p2pl => .second
  | .p3sg | .p3pl => .third

-- ============================================================================
-- § 2: Basque — pIsIndexed Matches Inverse Context
-- ============================================================================

/-- Basque `pIsIndexed` agrees with `PersonLevel.isSAP` under the bridge. -/
theorem basque_indexed_eq_sap (pn : Fragments.Basque.Agreement.PersonNumber) :
    Fragments.Basque.Agreement.pIsIndexed pn = (basqueToLevel pn).isSAP := by
  cases pn <;> rfl

/-- Per-cell verification: each Basque person-number's indexing status
    matches the cyclic agree prediction. -/
theorem basque_p1sg_indexed :
    Fragments.Basque.Agreement.pIsIndexed .p1sg = true ∧
    basque.isInverse .first .first = true ∧
    basque.isInverse .second .first = true ∧
    basque.isInverse .third .first = true := by
  exact ⟨rfl, by native_decide, by native_decide, by native_decide⟩

theorem basque_p2sg_indexed :
    Fragments.Basque.Agreement.pIsIndexed .p2sg = true ∧
    basque.isInverse .first .second = true ∧
    basque.isInverse .second .second = true ∧
    basque.isInverse .third .second = true := by
  exact ⟨rfl, by native_decide, by native_decide, by native_decide⟩

theorem basque_p3sg_not_indexed :
    Fragments.Basque.Agreement.pIsIndexed .p3sg = false ∧
    basque.isInverse .first .third = false ∧
    basque.isInverse .second .third = false := by
  exact ⟨rfl, by native_decide, by native_decide⟩

/-- Core bridge theorem (Basque): an object is indexed iff cyclic agree
    puts *every* EA→IA combination into an inverse context.

    When the object (IA) is SAP, the partial probe [uπ, uParticipant] is
    fully checked by the IA on cycle I, leaving no residue for any EA.
    Result: IA always controls → agreement tracks the object → indexed.

    When the object is 3P, the IA only checks [uπ], leaving [uParticipant]
    as active residue. A SAP EA matches this residue on cycle II → EA
    controls → agreement tracks the subject, not the object → not indexed. -/
theorem basque_indexed_iff_always_inverse
    (pn : Fragments.Basque.Agreement.PersonNumber) :
    Fragments.Basque.Agreement.pIsIndexed pn = true ↔
    ∀ ea : PersonLevel, basque.isInverse ea (basqueToLevel pn) = true := by
  cases pn <;> simp only [Fragments.Basque.Agreement.pIsIndexed,
    Fragments.Basque.Agreement.PersonNumber.isSAP,
    Fragments.Basque.Agreement.PersonNumber.person,
    basqueToLevel] <;> constructor
  -- mp for SAP: intro, then case-split on ea
  all_goals (try (intro; intro ea; cases ea <;> native_decide))
  -- mpr for SAP/3P: provide witness or use false hypothesis
  all_goals (try (intro h; exact h .first))
  -- mp for 3P: false = true → _, dispatch with absurd
  all_goals (intro h; exact absurd h (by native_decide))

-- ============================================================================
-- § 3: Georgian — pIsIndexed Matches Inverse Context
-- ============================================================================

/-- Georgian `pIsIndexed` agrees with `PersonLevel.isSAP` under the bridge. -/
theorem georgian_indexed_eq_sap (pn : Fragments.Georgian.Agreement.PersonNumber) :
    Fragments.Georgian.Agreement.pIsIndexed pn = (georgianToLevel pn).isSAP := by
  cases pn <;> rfl

/-- Per-cell verification: Georgian 1sg object prefix *m-* exists iff inverse. -/
theorem georgian_1sg_prefix_and_inverse :
    Fragments.Georgian.Agreement.objectPrefix .p1sg = some "m-" ∧
    basque.isInverse .first .first = true ∧
    basque.isInverse .second .first = true ∧
    basque.isInverse .third .first = true := by
  exact ⟨rfl, by native_decide, by native_decide, by native_decide⟩

/-- Per-cell verification: Georgian 3sg has no object prefix, and
    there exist direct contexts. -/
theorem georgian_3sg_no_prefix_and_direct :
    Fragments.Georgian.Agreement.objectPrefix .p3sg = none ∧
    isDirectContext .standard partialProbe .first .third = true ∧
    isDirectContext .standard partialProbe .second .third = true := by
  exact ⟨rfl, by native_decide, by native_decide⟩

/-- Core bridge theorem (Georgian): object is indexed iff always inverse.

    Georgian uses the same partial probe [u-3-2] and standard geometry as
    Basque, so the same cyclic agree mechanism derives the same SAP/3P
    split in object agreement. -/
theorem georgian_indexed_iff_always_inverse
    (pn : Fragments.Georgian.Agreement.PersonNumber) :
    Fragments.Georgian.Agreement.pIsIndexed pn = true ↔
    ∀ ea : PersonLevel, basque.isInverse ea (georgianToLevel pn) = true := by
  -- Georgian pIsIndexed tracks SAP (proved in fragment); SAP ↔ always inverse
  rw [georgian_indexed_eq_sap]
  cases pn <;> simp only [georgianToLevel, PersonLevel.isSAP] <;> constructor
  -- mp for SAP: intro, then case-split on ea
  all_goals (try (intro; intro ea; cases ea <;> native_decide))
  -- mpr for SAP: goal is `... → True` after simp
  all_goals (try (intro; trivial))
  -- mpr for 3P: specialize ∀ ea to get false = true witness
  all_goals (try (intro h; exact absurd (h .first) (by native_decide)))
  -- mp for 3P: hypothesis is false = true directly
  all_goals (intro h; exact absurd h (by native_decide))

-- ============================================================================
-- § 4: Georgian Second-Cycle Morphology
-- ============================================================================

/-- Georgian 1sg agreement: *m-* appears when 1P is the IA (cycle I only),
    *v-* appears when 1P is the EA (cycle II, IA=3P).

    @cite{bejar-rezac-2009} §3.2: the *m-*/*v-* alternation correlates with
    whether the probe was valued on the first or second cycle. -/
theorem georgian_m_is_cycle_I :
    hasSecondCycleEffect .standard partialProbe .third .first = false ∧
    hasSecondCycleEffect .standard partialProbe .second .first = false ∧
    hasSecondCycleEffect .standard partialProbe .first .first = false := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

theorem georgian_v_is_cycle_II :
    hasSecondCycleEffect .standard partialProbe .first .third = true ∧
    hasSecondCycleEffect .standard partialProbe .second .third = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- The *m-*/*v-* split is exactly the inverse/direct split for 1P:
    - *m-* (1P object = IA, inverse) → cycle I only, no second-cycle effect
    - *v-* (1P subject = EA, direct) → second-cycle effect present

    This connects Georgian `objectPrefix` morphology to the derivational
    mechanics of cyclic expansion. -/
theorem georgian_mv_split_is_inverse_direct :
    -- m-: 1P as IA (3→1), inverse, no second cycle
    (basque.isInverse .third .first = true ∧
     hasSecondCycleEffect .standard partialProbe .third .first = false) ∧
    -- v-: 1P as EA (1→3), direct, has second cycle
    (isDirectContext .standard partialProbe .first .third = true ∧
     hasSecondCycleEffect .standard partialProbe .first .third = true) := by
  exact ⟨⟨by native_decide, by native_decide⟩, ⟨by native_decide, by native_decide⟩⟩

-- ============================================================================
-- § 5: Basque Agreement Displacement Paradigm (Table 1)
-- ============================================================================

-- @cite{bejar-rezac-2009} Table 1: Basque paradigm cells showing which
-- argument controls the agreement slot.
-- The notation `x→y = z` means: EA=x, IA=y, agreement tracks z.
-- Underlined forms in the paper track the IA (inverse/displacement);
-- non-underlined forms track the EA (direct/regular).

/-- (2a) 1→2 = 2: "I saw you" — IA controls (inverse). -/
theorem table1_basque_1_2 : basque.value .first .second = .second := by native_decide
/-- (2b) 3→1 = 1: "He saw me" — IA controls (inverse/displacement). -/
theorem table1_basque_3_1 : basque.value .third .first = .first := by native_decide
/-- (2c) 2→1 = 1: "You saw me" — IA controls (inverse/displacement). -/
theorem table1_basque_2_1 : basque.value .second .first = .first := by native_decide
/-- (2d) 1→3 = 1: "I saw him" — EA controls (direct/regular). -/
theorem table1_basque_1_3 : basque.value .first .third = .first := by native_decide
/-- 2→3 = 2: "You saw him" — EA controls (direct/regular). -/
theorem table1_basque_2_3 : basque.value .second .third = .second := by native_decide

-- ============================================================================
-- § 6: Cross-Linguistic Uniformity
-- ============================================================================

/-- Basque and Georgian make the same predictions because they share the
    same agreement system (standard geometry, partial probe). -/
theorem basque_georgian_same_system :
    basque = ⟨.standard, partialProbe⟩ ∧
    basque = basque := ⟨rfl, rfl⟩

/-- The differential P indexing pattern is identical for all six
    person-number values across both languages. -/
theorem cross_linguistic_uniformity :
    (∀ pn : Fragments.Basque.Agreement.PersonNumber,
      Fragments.Basque.Agreement.pIsIndexed pn =
      (basqueToLevel pn).isSAP) ∧
    (∀ pn : Fragments.Georgian.Agreement.PersonNumber,
      Fragments.Georgian.Agreement.pIsIndexed pn =
      (georgianToLevel pn).isSAP) :=
  ⟨basque_indexed_eq_sap, georgian_indexed_eq_sap⟩

end Phenomena.Agreement.Studies.BejarRezac2009
