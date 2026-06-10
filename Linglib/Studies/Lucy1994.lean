import Linglib.Fragments.Mayan.Yukatek.Operators
import Linglib.Fragments.Mayan.Yukatek.VerbClasses
import Linglib.Semantics.Lexical.Roots.SalienceClass

/-!
# Lucy 1994: The role of semantic value in lexical comparison

[lucy-1994]

[lucy-1994] argues that the right way to identify lexical
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

The structural theorem `class_depends_only_on_signature` makes this
precise: salience class depends only on the feature signature, not on
the specific root identity. The per-root checks then degenerate to
finite signature lookups.
-/

namespace Lucy1994

open Morphology.Derivation
open Yukatek.Roots
open Yukatek.Operators

/-! ### Salience classes (re-exported from theory) -/

/-! `SalienceClass` and `classOfSignature` live in
    `Semantics/Lexical/Roots/SalienceClass.lean`. This file
    provides the full [lucy-1994] analysis on top of them:
    operator-applicability characterizations and per-root sanity checks.

    Local short alias `predictedClass = Root.predictedSalience`. -/

/-- A root's predicted salience class. Alias for
    `Root.predictedSalience` (`SalienceClass.lean`). -/
abbrev predictedClass (r : Root) : Option SalienceClass :=
  r.predictedSalience

theorem class_depends_only_on_signature
    (r₁ r₂ : Root) (h : r₁.featureSignature = r₂.featureSignature) :
    predictedClass r₁ = predictedClass r₂ :=
  predictedSalience_depends_only_on_signature r₁ r₂ h

/-! ### Predicted class agrees with operator applicability -/

/-! Both `predictedClass` and the inventory's applicability profile
    factor through the root's feature signature, a `Finset LexKind`
    drawn from a 16-element fintype. Each characterisation therefore
    reduces — after rewriting the profile to signature level
    (`applicableNames_eq_profile`) and generalising the signature — to
    a statement over all signatures that `decide` checks. The local
    macro `lucy_applicable` packages the reduction. -/

/-- The inventory's applicability profile as a function of the feature
    signature. The four operator conditions are pairwise disjoint
    (`classes_pairwise_disjoint`), so at most one name appears. -/
private theorem applicableNames_eq_profile (r : Root) :
    inventory.applicableNames r =
      (if r.featureSignature.IsAgentSalient then ["=t"] else []) ++
      (if r.featureSignature.IsAgentPatientSalient then ["=∅"] else []) ++
      (if r.featureSignature.IsPatientSalient then ["=s"] else []) ++
      (if r.featureSignature.IsPositional then ["-tal"] else []) := by
  simp only [inventory, Inventory.applicableNames, affectiveT, zeroDeriv,
    causativeS, positionalTal, List.filter_cons, List.filter_nil,
    decide_eq_true_eq, Root.IsAgentSalient, Root.IsAgentPatientSalient,
    Root.IsPatientSalient, Root.IsPositional]
  generalize r.featureSignature = s
  revert s
  decide

local macro "lucy_applicable " r:term : tactic =>
  `(tactic|
    (rw [applicableNames_eq_profile]
     unfold predictedClass Root.predictedSalience
     generalize ($r).featureSignature = s
     revert s
     decide))

/-- The `=t`-only applicability profile characterises agent-salient roots. -/
theorem agent_iff_applicable_t (r : Root) :
    predictedClass r = some .agent ↔ inventory.applicableNames r = ["=t"] := by
  lucy_applicable r

/-- The `=∅`-only applicability profile characterises agent-patient salient roots. -/
theorem agentPatient_iff_applicable_zero (r : Root) :
    predictedClass r = some .agentPatient ↔ inventory.applicableNames r = ["=∅"] := by
  lucy_applicable r

/-- The `=s`-only applicability profile characterises patient-salient roots. -/
theorem patient_iff_applicable_s (r : Root) :
    predictedClass r = some .patient ↔ inventory.applicableNames r = ["=s"] := by
  lucy_applicable r

/-- The `-tal`-only applicability profile characterises positional roots. -/
theorem positional_iff_applicable_tal (r : Root) :
    predictedClass r = some .positional ↔ inventory.applicableNames r = ["-tal"] := by
  lucy_applicable r

/-- An empty applicability profile characterises roots in [lucy-1994]'s
    diagnostic gap (the no-manner, no-result signatures other than the
    pure positional configuration `{.state}`). -/
theorem none_iff_applicable_empty (r : Root) :
    predictedClass r = none ↔ inventory.applicableNames r = [] := by
  lucy_applicable r

/-- **Applicability-as-classifier.** Two roots have the same applicability profile
    under [lucy-1994]'s diagnostic inventory iff they have the
    same predicted salience class. The 4 named-class iff-theorems are
    special cases. -/
theorem applicableNames_eq_iff_predictedClass_eq (r₁ r₂ : Root) :
    inventory.applicableNames r₁ = inventory.applicableNames r₂ ↔
      predictedClass r₁ = predictedClass r₂ := by
  rw [applicableNames_eq_profile, applicableNames_eq_profile]
  unfold predictedClass Root.predictedSalience
  generalize r₁.featureSignature = s₁
  generalize r₂.featureSignature = s₂
  revert s₁ s₂
  decide

/-! ### Per-root sanity checks -/

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

/-! ### The "motion verbs" non-class -/

/-- [lucy-1994]'s central typological point: "motion" verbs
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

/-! ### Closure robustness -/

/-- The class predicted from a root's *closed* feature signature
    (the collocational closure `FeatureSignature.close` of the derived
    signature). -/
def closedPredictedClass (r : Root) : Option SalienceClass :=
  classOfSignature r.closedFeatureSignature

/-- For cause-free roots, collocational closure does not change the
    Lucy 1994 salience classification: the only closure edge that can
    fire is result→state, the agent / agentPatient / patient arms
    ignore `.state` membership, and a base that gains `.state` from
    closure carries `.result` and so is already excluded from the
    positional arm. The hypothesis is necessary: a root carrying
    `.cause` but not `.result` is unclassified at base yet
    patient-salient after closure, since the cause→result closure edge
    introduces `.result`. -/
theorem predictedClass_closure_invariant (r : Root) (h : ¬ r.HasCause) :
    closedPredictedClass r = predictedClass r := by
  unfold Root.HasCause at h
  unfold closedPredictedClass predictedClass Root.predictedSalience
    Root.closedFeatureSignature
  revert h
  generalize r.featureSignature = s
  revert s
  decide

/-! ### Bridge to Bohnemeyer's 5-way verb stem classes -/

/-! [bohnemeyer-2004] refines [lucy-1994]'s 4-way salience
    cut into a 5-way stem classification (`active`, `inactive`,
    `inchoative`, `positional`, `transitiveActive`). The mapping is
    `VerbStemClass.toSalienceClass` in `VerbClasses.lean`. The agent /
    patient / agent-patient classes correspond one-to-one; Lucy's
    `positional` covers both Bohnemeyer's `inchoative` and `positional`.

    The per-root theorems below check that for each Yukatek root in
    `Roots.lean`, Lucy's predicted class agrees with the Bohnemeyer
    stem-class label converted via `toSalienceClass`. -/

open Yukatek (VerbStemClass)

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

end Lucy1994
