import Linglib.Fragments.Mayan.Yukatek.Operators
import Linglib.Fragments.Mayan.Yukatek.VerbClasses
import Linglib.Theories.Semantics.Verb.Roots.SalienceClass

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

/-! Each of the four orbit characterisations follows the same
    pattern: unfold the orbit and the named class predicates, then
    case-split on the four B&K-G feature bits and let `simp_all`
    discharge each cell of the 16-row truth table. The local macro
    `lucy_orbit` packages this so the four theorems differ only in
    which class label appears on the LHS. -/

local macro "lucy_orbit " r:term : tactic =>
  `(tactic|
    (unfold predictedClass Root.predictedSalience classOfSignature
       inventory Inventory.orbit
       affectiveT zeroDeriv causativeS positionalTal
       Root.IsAgentSalient Root.IsAgentPatientSalient
       Root.IsPatientSalient Root.IsPositional
       FeatureSignature.IsAgentSalient FeatureSignature.IsAgentPatientSalient
       FeatureSignature.IsPatientSalient FeatureSignature.IsPositional
       Root.featureSignature
     simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
     cases hm : ($r).hasManner <;> cases hr : ($r).hasResult <;>
       cases hs : ($r).hasState <;> cases hc : ($r).hasCause <;> simp_all))

/-- The `=t`-only orbit characterises agent-salient roots. -/
theorem agent_iff_orbit_t (r : Root) :
    predictedClass r = some .agent ↔ inventory.orbit r = ["=t"] := by
  lucy_orbit r

/-- The `=∅`-only orbit characterises agent-patient salient roots. -/
theorem agentPatient_iff_orbit_zero (r : Root) :
    predictedClass r = some .agentPatient ↔ inventory.orbit r = ["=∅"] := by
  lucy_orbit r

/-- The `=s`-only orbit characterises patient-salient roots. -/
theorem patient_iff_orbit_s (r : Root) :
    predictedClass r = some .patient ↔ inventory.orbit r = ["=s"] := by
  lucy_orbit r

/-- The `-tal`-only orbit characterises positional roots. -/
theorem positional_iff_orbit_tal (r : Root) :
    predictedClass r = some .positional ↔ inventory.orbit r = ["-tal"] := by
  lucy_orbit r

/-- An empty orbit characterises roots outside @cite{lucy-1994}'s
    diagnostic gap (`(¬manner, ¬result)` rows that lack the positional
    configuration `state ∧ ¬cause`). -/
theorem none_iff_orbit_empty (r : Root) :
    predictedClass r = none ↔ inventory.orbit r = [] := by
  lucy_orbit r

/-- **Orbit-as-classifier.** Two roots have the same operator orbit
    under @cite{lucy-1994}'s diagnostic inventory iff they have the
    same predicted salience class. The 4 named-class iff-theorems are
    special cases. -/
theorem orbit_eq_iff_predictedClass_eq (r₁ r₂ : Root) :
    inventory.orbit r₁ = inventory.orbit r₂ ↔
      predictedClass r₁ = predictedClass r₂ := by
  unfold predictedClass Root.predictedSalience classOfSignature
    inventory Inventory.orbit
    affectiveT zeroDeriv causativeS positionalTal
    Root.IsAgentSalient Root.IsAgentPatientSalient
    Root.IsPatientSalient Root.IsPositional
    FeatureSignature.IsAgentSalient FeatureSignature.IsAgentPatientSalient
    FeatureSignature.IsPatientSalient FeatureSignature.IsPositional
    Root.featureSignature
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
  cases r₁.hasManner <;> cases r₁.hasResult <;>
    cases r₁.hasState <;> cases r₁.hasCause <;>
    cases r₂.hasManner <;> cases r₂.hasResult <;>
      cases r₂.hasState <;> cases r₂.hasCause <;> simp_all

-- ════════════════════════════════════════════════════
-- § 5. Per-Root Sanity Checks
-- ════════════════════════════════════════════════════

/-! Agent-salient. -/
theorem siit_agent  : predictedClass siit  = some .agent := rfl
theorem tziib_agent : predictedClass tziib = some .agent := rfl
theorem miis_agent  : predictedClass miis  = some .agent := rfl
theorem cheh_agent  : predictedClass cheh  = some .agent := rfl
theorem paak_agent  : predictedClass paak  = some .agent := rfl

/-! Agent-patient salient. -/
theorem kuc_agentPatient : predictedClass kuc = some .agentPatient := rfl
theorem pis_agentPatient : predictedClass pis = some .agentPatient := rfl
theorem los_agentPatient : predictedClass los = some .agentPatient := rfl

/-! Patient-salient. -/
theorem kiim_patient      : predictedClass kiim      = some .patient := rfl
theorem haanCease_patient : predictedClass haanCease = some .patient := rfl
theorem luub_patient      : predictedClass luub      = some .patient := rfl
theorem ok_patient        : predictedClass ok        = some .patient := rfl
theorem ah_patient        : predictedClass ah        = some .patient := rfl
theorem wen_patient       : predictedClass wen       = some .patient := rfl
theorem siih_patient      : predictedClass siih      = some .patient := rfl
theorem tuub_patient      : predictedClass tuub      = some .patient := rfl
theorem kaah_patient      : predictedClass kaah      = some .patient := rfl
theorem chuun_patient     : predictedClass chuun     = some .patient := rfl
theorem chenCease_patient : predictedClass chenCease = some .patient := rfl
theorem hoop_patient      : predictedClass hoop      = some .patient := rfl
theorem heel_patient      : predictedClass heel      = some .patient := rfl
theorem paat_patient      : predictedClass paat      = some .patient := rfl

/-! Motion roots — pattern as patient-salient (Lucy's central point). -/
theorem maan_patient : predictedClass maan = some .patient := rfl
theorem taal_patient : predictedClass taal = some .patient := rfl
theorem bin_patient  : predictedClass bin  = some .patient := rfl
theorem naak_patient : predictedClass naak = some .patient := rfl
theorem liik_patient : predictedClass liik = some .patient := rfl

/-! Positional. -/
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
  unfold closedPredictedClass predictedClass Root.predictedSalience
    classOfSignature
  rw [closedFeatureSignature_manner, closedFeatureSignature_result,
      closedFeatureSignature_cause, closedFeatureSignature_state_eq]
  rcases hm : r.featureSignature.manner with _ | _ <;>
    rcases hr : r.featureSignature.result with _ | _ <;>
    rcases hc : r.featureSignature.cause with _ | _ <;>
    rcases hs : r.featureSignature.state with _ | _ <;>
    simp_all

-- ════════════════════════════════════════════════════
-- § 8. Bridge to Bohnemeyer's 5-Way Verb Stem Classes
-- ════════════════════════════════════════════════════

/-! @cite{bohnemeyer-2004} refines @cite{lucy-1994}'s 4-way salience
    cut into a 5-way stem classification (`active`, `inactive`,
    `inchoative`, `positional`, `transitiveActive`). The mapping is
    `VerbStemClass.toSalienceClass` in `VerbClasses.lean`. The agent /
    patient / agent-patient classes correspond one-to-one; Lucy's
    `positional` covers both Bohnemeyer's `inchoative` and `positional`.

    The per-root theorems below check that for each Yukatek root in
    `Roots.lean`, Lucy's predicted class agrees with the Bohnemeyer
    stem-class label converted via `toSalienceClass`. -/

open Fragments.Mayan.Yukatek (VerbStemClass)

/-- Agent-salient Lucy roots map to Bohnemeyer's `active` stem class. -/
theorem siit_lucy_agrees_active :
    predictedClass siit = some (VerbStemClass.active.toSalienceClass) := rfl

theorem tziib_lucy_agrees_active :
    predictedClass tziib = some (VerbStemClass.active.toSalienceClass) := rfl

/-- Agent-patient salient Lucy roots map to Bohnemeyer's
    `transitiveActive`. -/
theorem kuc_lucy_agrees_transitiveActive :
    predictedClass kuc =
      some (VerbStemClass.transitiveActive.toSalienceClass) := rfl

theorem pis_lucy_agrees_transitiveActive :
    predictedClass pis =
      some (VerbStemClass.transitiveActive.toSalienceClass) := rfl

theorem los_lucy_agrees_transitiveActive :
    predictedClass los =
      some (VerbStemClass.transitiveActive.toSalienceClass) := rfl

/-- Patient-salient Lucy roots map to Bohnemeyer's `inactive`. -/
theorem kiim_lucy_agrees_inactive :
    predictedClass kiim = some (VerbStemClass.inactive.toSalienceClass) := rfl

theorem haanCease_lucy_agrees_inactive :
    predictedClass haanCease = some (VerbStemClass.inactive.toSalienceClass) := rfl

theorem luub_lucy_agrees_inactive :
    predictedClass luub = some (VerbStemClass.inactive.toSalienceClass) := rfl

theorem ok_lucy_agrees_inactive :
    predictedClass ok = some (VerbStemClass.inactive.toSalienceClass) := rfl

/-- Positional Lucy roots map to Bohnemeyer's `positional` (and would
    equally map to `inchoative` per `inchoative_positional_collapse_under_lucy`). -/
theorem cin_lucy_agrees_positional :
    predictedClass cin =
      some (VerbStemClass.positional.toSalienceClass) := rfl

theorem kul_lucy_agrees_positional :
    predictedClass kul =
      some (VerbStemClass.positional.toSalienceClass) := rfl

end Phenomena.LexicalTypology.Studies.Lucy1994
