import Linglib.Semantics.Lexical.Roots.Typology

/-!
# Lexical Salience Classes

[lucy-1994]'s classification of verbal roots by which argument(s) the
underived root form makes "salient" (default case-role assignment at
the propositional level): a 3-way salience cut (agent, agent-patient,
patient, by required transitiviser) plus the separately-derived
positional class, systematized here as one enum. The characterization
of each class by B&K-G feature signature is a cross-framework
reconstruction ([lucy-1994] predates the feature vocabulary of
[beavers-koontz-garboden-2020]), not Lucy's own formulation.

This file lifts the classification out of any specific empirical
study so that other Fragment / Theory modules can refer to it
(e.g., the Yukatek 5-way verb stem classification, which refines
this cut). The full [lucy-1994] analysis — operator applicability,
motion-roots-non-class theorem, per-root verifications — lives in
`Studies/Lucy1994.lean`.
-/

/-- Salience classification of verbal roots ([lucy-1994]): the 3-way
    transitiviser cut plus the positional class. "Salience" is shorthand
    for "default case-role assignment at the propositional level" — *not*
    a substantive feature `[±agent]` written into the root. -/
inductive SalienceClass where
  /-- Underived intransitive whose argument is the agent. -/
  | agent
  /-- Underived transitive — both arguments lexically salient. -/
  | agentPatient
  /-- Underived intransitive whose argument is the patient. -/
  | patient
  /-- Stative root (positional / configurational). -/
  | positional
  deriving DecidableEq, Repr

/-! ### Named class predicates

Named structural conditions characterising membership in each
[lucy-1994] salience class. These predicates are language-independent:
the same conditions characterise the class in any inventory whose
transitivisers respect the diagnostic. They appear directly as the
`applies` field of each Yukatek operator in
`Fragments/Mayan/Yukatek/Operators.lean`, making the
operator-applicability ↔ salience-class connection true *by
construction* rather than only provable per-case. -/

namespace FeatureSignature

/-- Agent-salient: manner without result (intransitive activity that
    requires =t to transitivise; [lucy-1994]). -/
def IsAgentSalient (s : FeatureSignature) : Prop :=
  .manner ∈ s ∧ .result ∉ s

instance (s : FeatureSignature) : Decidable s.IsAgentSalient :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Agent-patient salient: manner *and* result (already lexically
    transitive; [lucy-1994]). -/
def IsAgentPatientSalient (s : FeatureSignature) : Prop :=
  .manner ∈ s ∧ .result ∈ s

instance (s : FeatureSignature) : Decidable s.IsAgentPatientSalient :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Patient-salient: result without manner (intransitive change-of-state
    that requires =s to transitivise; [lucy-1994]). -/
def IsPatientSalient (s : FeatureSignature) : Prop :=
  .manner ∉ s ∧ .result ∈ s

instance (s : FeatureSignature) : Decidable s.IsPatientSalient :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Positional: pure stative root — state without manner, result, or
    cause (requires `-tal` for the inchoative; [lucy-1994]). -/
def IsPositional (s : FeatureSignature) : Prop :=
  s = {.state}

instance (s : FeatureSignature) : Decidable s.IsPositional :=
  inferInstanceAs (Decidable (_ = _))

end FeatureSignature

/-! Per-root convenience versions, lifted via `featureSignature`. -/

namespace Root

/-- Agent-salient root (cf. `FeatureSignature.IsAgentSalient`). -/
def IsAgentSalient (r : Root) : Prop :=
  r.featureSignature.IsAgentSalient

instance (r : Root) : Decidable r.IsAgentSalient :=
  inferInstanceAs (Decidable (FeatureSignature.IsAgentSalient _))

/-- Agent-patient salient root. -/
def IsAgentPatientSalient (r : Root) : Prop :=
  r.featureSignature.IsAgentPatientSalient

instance (r : Root) : Decidable r.IsAgentPatientSalient :=
  inferInstanceAs (Decidable (FeatureSignature.IsAgentPatientSalient _))

/-- Patient-salient root. -/
def IsPatientSalient (r : Root) : Prop :=
  r.featureSignature.IsPatientSalient

instance (r : Root) : Decidable r.IsPatientSalient :=
  inferInstanceAs (Decidable (FeatureSignature.IsPatientSalient _))

/-- Positional root. -/
def IsPositional (r : Root) : Prop :=
  r.featureSignature.IsPositional

instance (r : Root) : Decidable r.IsPositional :=
  inferInstanceAs (Decidable (FeatureSignature.IsPositional _))

end Root

/-! ### Salience classifier -/

/-- Map a B&K-G feature signature to its salience class
    ([lucy-1994]) by dispatching on the four named predicates, which
    align with operator applicability conditions in
    `Fragments/Mayan/Yukatek/Operators.lean`. The positional arm
    requires the pure-state signature: positional roots are stative
    configurations (orientation, posture, location) with no causing
    event. -/
def classOfSignature (s : FeatureSignature) : Option SalienceClass :=
  if s.IsAgentSalient then some .agent
  else if s.IsAgentPatientSalient then some .agentPatient
  else if s.IsPatientSalient then some .patient
  else if s.IsPositional then some .positional
  else none

/-- A root's predicted salience class is `classOfSignature` of its
    feature signature. -/
def Root.predictedSalience (r : Root) : Option SalienceClass :=
  classOfSignature r.featureSignature

/-- Two roots with the same B&K-G feature signature get the same
    salience class. -/
theorem predictedSalience_depends_only_on_signature
    (r₁ r₂ : Root) (h : r₁.featureSignature = r₂.featureSignature) :
    r₁.predictedSalience = r₂.predictedSalience := by
  unfold Root.predictedSalience
  rw [h]

/-! ### Pairwise disjointness of class predicates -/

/-- The four named predicates are pairwise disjoint: at most one fires
    on any given signature. (They are *jointly* not exhaustive — the
    no-manner-no-result signatures other than `{state}` fall outside
    all four; see `classOfSignature_eq_none_iff`.) -/
theorem classes_pairwise_disjoint :
    ∀ s : FeatureSignature,
      ¬ (s.IsAgentSalient ∧ s.IsAgentPatientSalient) ∧
      ¬ (s.IsAgentSalient ∧ s.IsPatientSalient) ∧
      ¬ (s.IsAgentSalient ∧ s.IsPositional) ∧
      ¬ (s.IsAgentPatientSalient ∧ s.IsPatientSalient) ∧
      ¬ (s.IsAgentPatientSalient ∧ s.IsPositional) ∧
      ¬ (s.IsPatientSalient ∧ s.IsPositional) := by
  decide

/-- `classOfSignature s = none` iff `s` falls outside all four named
    predicates. Characterises the gap in the diagnostic: the
    no-manner-no-result signatures other than pure `{state}` are
    unclassified by Lucy's Yukatek diagnostic. -/
theorem classOfSignature_eq_none_iff :
    ∀ s : FeatureSignature,
      classOfSignature s = none ↔
        ¬ s.IsAgentSalient ∧ ¬ s.IsAgentPatientSalient ∧
        ¬ s.IsPatientSalient ∧ ¬ s.IsPositional := by
  decide
