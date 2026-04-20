import Linglib.Theories.Semantics.Verb.Roots.Closure

/-!
# Lexical Salience Classes

@cite{lucy-1994}

A 4-way classification of verbal roots by which argument(s) the
underived root form makes "salient" (in @cite{lucy-1994}'s sense:
default case-role assignment at the propositional level). The four
classes — agent, agent-patient, patient, positional — are derivable
from the B&K-G feature signature alone.

This file lifts the classification out of any specific empirical
study so that other Fragment / Theory modules can refer to it
(e.g., the Yukatek 5-way verb stem classification, which refines
this 4-way cut). The full @cite{lucy-1994} analysis — operator
orbits, motion-roots-non-class theorem, per-root verifications —
lives in `Phenomena/LexicalTypology/Studies/Lucy1994.lean`.
-/

namespace Semantics.Verb.Roots

/-- The 4-way salience classification of verbal roots
    (@cite{lucy-1994}). "Salience" is shorthand for "default case-role
    assignment at the propositional level" — *not* a substantive feature
    `[±agent]` written into the root. -/
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

-- ════════════════════════════════════════════════════
-- § 1. Named Class Predicates
-- ════════════════════════════════════════════════════

/-! Named structural conditions characterising membership in each
    @cite{lucy-1994} salience class. These predicates are language-
    independent: the same conditions characterise the class in any
    inventory whose transitivisers respect the diagnostic. They appear
    directly as the `applies` field of each Yukatek operator in
    `Fragments/Mayan/Yukatek/Operators.lean`, making the
    operator-applicability ↔ salience-class connection true *by
    construction* rather than only provable per-case. -/

/-- Agent-salient: manner without result (intransitive activity that
    requires =t to transitivise; @cite{lucy-1994}). -/
def FeatureSignature.IsAgentSalient (s : FeatureSignature) : Prop :=
  s.manner = true ∧ s.result = false

instance (s : FeatureSignature) : Decidable s.IsAgentSalient := by
  unfold FeatureSignature.IsAgentSalient; infer_instance

/-- Agent-patient salient: manner *and* result (already lexically
    transitive; @cite{lucy-1994}). -/
def FeatureSignature.IsAgentPatientSalient (s : FeatureSignature) : Prop :=
  s.manner = true ∧ s.result = true

instance (s : FeatureSignature) : Decidable s.IsAgentPatientSalient := by
  unfold FeatureSignature.IsAgentPatientSalient; infer_instance

/-- Patient-salient: result without manner (intransitive change-of-state
    that requires =s to transitivise; @cite{lucy-1994}). -/
def FeatureSignature.IsPatientSalient (s : FeatureSignature) : Prop :=
  s.manner = false ∧ s.result = true

instance (s : FeatureSignature) : Decidable s.IsPatientSalient := by
  unfold FeatureSignature.IsPatientSalient; infer_instance

/-- Positional: pure stative root — state without manner, result, or
    cause (requires `-tal` for the inchoative; @cite{lucy-1994}). -/
def FeatureSignature.IsPositional (s : FeatureSignature) : Prop :=
  s.state = true ∧ s.manner = false ∧ s.result = false ∧ s.cause = false

instance (s : FeatureSignature) : Decidable s.IsPositional := by
  unfold FeatureSignature.IsPositional; infer_instance

/-! Per-root convenience versions, lifted via `featureSignature`. -/

/-- Agent-salient root (lifted to roots; cf. `FeatureSignature.IsAgentSalient`). -/
def Root.IsAgentSalient (r : Root) : Prop :=
  r.featureSignature.IsAgentSalient

instance (r : Root) : Decidable r.IsAgentSalient := by
  unfold Root.IsAgentSalient; infer_instance

/-- Agent-patient salient root. -/
def Root.IsAgentPatientSalient (r : Root) : Prop :=
  r.featureSignature.IsAgentPatientSalient

instance (r : Root) : Decidable r.IsAgentPatientSalient := by
  unfold Root.IsAgentPatientSalient; infer_instance

/-- Patient-salient root. -/
def Root.IsPatientSalient (r : Root) : Prop :=
  r.featureSignature.IsPatientSalient

instance (r : Root) : Decidable r.IsPatientSalient := by
  unfold Root.IsPatientSalient; infer_instance

/-- Positional root. -/
def Root.IsPositional (r : Root) : Prop :=
  r.featureSignature.IsPositional

instance (r : Root) : Decidable r.IsPositional := by
  unfold Root.IsPositional; infer_instance

-- ════════════════════════════════════════════════════
-- § 2. Salience Classifier
-- ════════════════════════════════════════════════════

/-- Map a B&K-G feature signature to its salience class
    (@cite{lucy-1994}). The arms align with operator applicability
    conditions in `Fragments/Mayan/Yukatek/Operators.lean`:

    | (state, manner, result, cause) | predicted class    |
    |--------------------------------|--------------------|
    | (_, true, false, _)            | agent              |
    | (_, true, true, _)             | agentPatient       |
    | (_, false, true, _)            | patient            |
    | (true, false, false, false)    | positional         |
    | otherwise                      | none               |

    The positional row requires `cause = false`: positional roots are
    pure stative configurations (orientation, posture, location) with
    no causing event. The four arms equivalently dispatch on the four
    named predicates `IsAgentSalient`, `IsAgentPatientSalient`,
    `IsPatientSalient`, `IsPositional` — see `classOfSignature_eq_dispatch`. -/
def classOfSignature (s : FeatureSignature) : Option SalienceClass :=
  match s.manner, s.result, s.state, s.cause with
  | true,  false, _,    _     => some .agent
  | true,  true,  _,    _     => some .agentPatient
  | false, true,  _,    _     => some .patient
  | false, false, true, false => some .positional
  | false, false, _,    _     => none

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

-- ════════════════════════════════════════════════════
-- § 3. Equivalence with Predicate Dispatch
-- ════════════════════════════════════════════════════

/-- The `classOfSignature` table is equivalent to dispatching on the
    four named predicates. Establishes that the classifier really *is*
    the disjunction of the named conditions — not an arbitrary table. -/
theorem classOfSignature_eq_dispatch (s : FeatureSignature) :
    classOfSignature s =
      (if s.IsAgentSalient        then some .agent
       else if s.IsAgentPatientSalient then some .agentPatient
       else if s.IsPatientSalient  then some .patient
       else if s.IsPositional      then some .positional
       else none) := by
  obtain ⟨st, m, r, c⟩ := s
  unfold classOfSignature FeatureSignature.IsAgentSalient
    FeatureSignature.IsAgentPatientSalient FeatureSignature.IsPatientSalient
    FeatureSignature.IsPositional
  cases m <;> cases r <;> cases st <;> cases c <;> simp_all

-- ════════════════════════════════════════════════════
-- § 4. Pairwise Disjointness of Class Predicates
-- ════════════════════════════════════════════════════

/-- The four named predicates are pairwise disjoint: at most one fires
    on any given signature. (They are *jointly* not exhaustive — the
    ⟨false, false, _, _⟩ rows that the positional arm doesn't catch
    fall outside all four; see `classOfSignature_eq_none_iff`.) -/
theorem classes_pairwise_disjoint (s : FeatureSignature) :
    ¬ (s.IsAgentSalient ∧ s.IsAgentPatientSalient) ∧
    ¬ (s.IsAgentSalient ∧ s.IsPatientSalient) ∧
    ¬ (s.IsAgentSalient ∧ s.IsPositional) ∧
    ¬ (s.IsAgentPatientSalient ∧ s.IsPatientSalient) ∧
    ¬ (s.IsAgentPatientSalient ∧ s.IsPositional) ∧
    ¬ (s.IsPatientSalient ∧ s.IsPositional) := by
  obtain ⟨st, m, r, c⟩ := s
  cases m <;> cases r <;> cases st <;> cases c <;>
    decide

/-- `classOfSignature s = none` iff `s` falls outside all four named
    predicates. Characterises the gap in the diagnostic: the
    `(¬manner, ¬result)` rows that lack the positional configuration
    (state ∧ ¬cause) are unclassified by Lucy's Yukatek diagnostic. -/
theorem classOfSignature_eq_none_iff (s : FeatureSignature) :
    classOfSignature s = none ↔
      ¬ s.IsAgentSalient ∧ ¬ s.IsAgentPatientSalient ∧
      ¬ s.IsPatientSalient ∧ ¬ s.IsPositional := by
  obtain ⟨st, m, r, c⟩ := s
  cases m <;> cases r <;> cases st <;> cases c <;>
    decide

end Semantics.Verb.Roots
