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
    no causing event. -/
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

end Semantics.Verb.Roots
