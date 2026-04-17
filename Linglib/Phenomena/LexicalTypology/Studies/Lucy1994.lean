import Linglib.Fragments.Mayan.Yukatek.Operators

/-!
# Lucy 1994: The role of semantic value in lexical comparison

@cite{lucy-1994}

@cite{lucy-1994} argues that the right way to identify lexical
classes is *morpho-distributional*, not denotational. Yucatek's
"spatial" verbs are his test case: a notional set assembled by English
intuition fails to coincide with any morphologically defined Yucatek
class. What the morphology *does* deliver is a different, three-way
classification of roots by salience profile, derivable from which
transitiviser the root requires:

| Required transitiviser | Salience class           | Examples                              |
|------------------------|--------------------------|---------------------------------------|
| `=t` (affective)       | agent-salient            | síit' "jump", ¢'iib "write"           |
| `=∅` (zero)            | agent-patient salient    | kuč "carry", p'is "measure", lo'š "punch" |
| `=s` (causative)       | patient-salient          | kíim "die", háan "cease", lúub' "fall", 'ok "enter" |

Crucially, Lucy's "motion" roots (`luub`, `ok`, etc.) do not form a
unified class — they pattern with other state-change verbs as
patient-salient. What *does* form a unified class is the **positional**
roots (čin "bend", kul "sit", etc.), distinguished by their derivation
via `-tal` (allomorph `-lah`) for the positional inchoative.

Here we recast the salience cut as a derived equivalence on roots
under the operator inventory in `Fragments/Mayan/Yukatek/Operators.lean`:
two roots have the same salience class iff the same operator(s) apply
to them. The 3-way classification then *falls out* of (B&K-G feature
signature) × (operator applicability conditions) — it is not stipulated.

The structural theorem `salienceClass_from_signature` makes this
precise: salience class depends only on the feature signature, not on
the specific root identity. The per-root checks then degenerate to
finite signature lookups.
-/

namespace Phenomena.LexicalTypology.Studies.Lucy1994

open Semantics.Verb.Roots
open Morphology.Derivation
open Fragments.Mayan.Yukatek.Roots
open Fragments.Mayan.Yukatek.Operators

-- ════════════════════════════════════════════════════
-- § 1. Salience Classes (re-exported from Theory)
-- ════════════════════════════════════════════════════

/-! `SalienceClass` and `classOfSignature` live in
    `Theories/Semantics/Verb/Roots/SalienceClass.lean`. This file
    provides the full @cite{lucy-1994} analysis on top of them:
    operator-orbit characterizations and per-root sanity checks.

    Local short alias `predictedClass = Root.predictedSalience`. -/

/-- A root's predicted salience class. Alias for
    `Root.predictedSalience` (`SalienceClass.lean`). -/
abbrev predictedClass (r : Root) : Option SalienceClass :=
  r.predictedSalience

theorem class_depends_only_on_signature
    (r₁ r₂ : Root) (h : r₁.featureSignature = r₂.featureSignature) :
    predictedClass r₁ = predictedClass r₂ :=
  predictedSalience_depends_only_on_signature r₁ r₂ h

-- ════════════════════════════════════════════════════
-- § 4. Predicted Class Agrees with Operator Orbit
-- ════════════════════════════════════════════════════

/-- The `=t`-only orbit characterises agent-salient roots. -/
theorem agent_iff_orbit_t (r : Root) :
    predictedClass r = some .agent ↔ inventory.orbit r = ["=t"] := by
  unfold predictedClass classOfSignature inventory Inventory.orbit
    affectiveT zeroDeriv causativeS positionalTal Root.featureSignature
  simp only [List.filter_cons, List.filter_nil]
  cases hs : r.hasState <;> cases hm : r.hasManner <;>
    cases hr : r.hasResult <;> cases hc : r.hasCause <;> simp_all

/-- The `=∅`-only orbit characterises agent-patient salient roots. -/
theorem agentPatient_iff_orbit_zero (r : Root) :
    predictedClass r = some .agentPatient ↔ inventory.orbit r = ["=∅"] := by
  unfold predictedClass classOfSignature inventory Inventory.orbit
    affectiveT zeroDeriv causativeS positionalTal Root.featureSignature
  simp only [List.filter_cons, List.filter_nil]
  cases hs : r.hasState <;> cases hm : r.hasManner <;>
    cases hr : r.hasResult <;> cases hc : r.hasCause <;> simp_all

/-- The `=s`-only orbit characterises patient-salient roots. -/
theorem patient_iff_orbit_s (r : Root) :
    predictedClass r = some .patient ↔ inventory.orbit r = ["=s"] := by
  unfold predictedClass classOfSignature inventory Inventory.orbit
    affectiveT zeroDeriv causativeS positionalTal Root.featureSignature
  simp only [List.filter_cons, List.filter_nil]
  cases hs : r.hasState <;> cases hm : r.hasManner <;>
    cases hr : r.hasResult <;> cases hc : r.hasCause <;> simp_all

/-- The `-tal`-only orbit characterises positional roots. -/
theorem positional_iff_orbit_tal (r : Root) :
    predictedClass r = some .positional ↔ inventory.orbit r = ["-tal"] := by
  unfold predictedClass classOfSignature inventory Inventory.orbit
    affectiveT zeroDeriv causativeS positionalTal Root.featureSignature
  simp only [List.filter_cons, List.filter_nil]
  cases hs : r.hasState <;> cases hm : r.hasManner <;>
    cases hr : r.hasResult <;> cases hc : r.hasCause <;> simp_all

-- ════════════════════════════════════════════════════
-- § 5. Per-Root Sanity Checks
-- ════════════════════════════════════════════════════

theorem siit_agent : predictedClass siit = some .agent := rfl
theorem tziib_agent : predictedClass tziib = some .agent := rfl

theorem kuc_agentPatient : predictedClass kuc = some .agentPatient := rfl
theorem pis_agentPatient : predictedClass pis = some .agentPatient := rfl
theorem los_agentPatient : predictedClass los = some .agentPatient := rfl

theorem kiim_patient : predictedClass kiim = some .patient := rfl
theorem haan_patient : predictedClass haan = some .patient := rfl
theorem luub_patient : predictedClass luub = some .patient := rfl
theorem ok_patient : predictedClass ok = some .patient := rfl

theorem cin_positional : predictedClass cin = some .positional := rfl
theorem kul_positional : predictedClass kul = some .positional := rfl

-- ════════════════════════════════════════════════════
-- § 6. The "Motion Verbs" Non-Class
-- ════════════════════════════════════════════════════

/-- @cite{lucy-1994}'s central typological point: "motion" verbs
    (`luub` "fall", `ok` "enter") are not in their own salience class
    — they pattern with other patient-salient state-change roots.
    Concretely: their predicted class is the same as `kiim` "die". -/
theorem motion_roots_not_separate_class :
    predictedClass luub = predictedClass kiim ∧
    predictedClass ok = predictedClass kiim :=
  ⟨rfl, rfl⟩

/-- Conversely, positional roots *do* form a unified class
    distinguishable from any "motion" or state-change root: their
    predicted class differs from every patient-salient root's. -/
theorem positional_distinct_from_motion :
    predictedClass cin ≠ predictedClass luub := by decide

-- ════════════════════════════════════════════════════
-- § 7. Closure Robustness
-- ════════════════════════════════════════════════════

/-- The class predicted from a root's *closed* feature signature
    (`bkgRules` applied to the base entailments). -/
def closedPredictedClass (r : Root) : Option SalienceClass :=
  classOfSignature r.closedFeatureSignature

/-- Closure under `bkgRules` does not change the Lucy 1994 salience
    classification: agent / agentPatient / patient classes ignore the
    `state` field, and the positional class requires `result = false`,
    which closure does not affect (`closedFeatureSignature_result`).
    The only way closure can flip `state` from `false` to `true` is if
    the base set has a `becomesState` atom (so `result = true`) — in
    which case the positional arm is already excluded by `result`. -/
theorem predictedClass_closure_invariant (r : Root) :
    closedPredictedClass r = predictedClass r := by
  unfold closedPredictedClass predictedClass classOfSignature
  rw [closedFeatureSignature_manner, closedFeatureSignature_result,
      closedFeatureSignature_cause, closedFeatureSignature_state_eq]
  rcases hm : r.featureSignature.manner with _ | _ <;>
    rcases hr : r.featureSignature.result with _ | _ <;>
    rcases hc : r.featureSignature.cause with _ | _ <;>
    rcases hs : r.featureSignature.state with _ | _ <;>
    simp_all

end Phenomena.LexicalTypology.Studies.Lucy1994
