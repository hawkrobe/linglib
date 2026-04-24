/-!
# Empathy
@cite{kuno-1987}

Empathy in the sense of @cite{kuno-1987}: the speaker's identification with
an event participant. Empathy is a graded notion — the speaker can identify
more or less strongly with a given participant — and it cross-cuts person,
animacy, and discourse role.

## Why a separate primitive

Empathy is *not* an attitude in the propositional sense (Sells's `self`),
nor is it discourse participation (Sells's `source`). It is a third
perspectival relation: the speaker's affective alignment with a participant.
In Romance, dative clitics tend to encode empathy
(@cite{charnavel-mateu-2015}); in Japanese, transferring verbs *yaru/kureru*
lexically alternate by speaker-empathy (@cite{kuno-1987} p. 246).

This file provides the minimal primitive. Frameworks that *use* empathy
(e.g., @cite{charnavel-mateu-2015}'s antilogophoricity hierarchy) live
in their own files and import this one.
-/

namespace Features.Empathy

/-- A binary empathy property. The speaker either identifies with the
    referent or does not. This is the simplest possible primitive;
    graded variants (the Empathy Hierarchy of @cite{kuno-1987} ch. 5) can
    be added when downstream consumers need them. -/
def IsEmpathyLocus (p : Prop) : Prop := p

/-- Kuno's *Speech-Act Empathy Hierarchy* (@cite{kuno-1987} p. 207):
    speaker > addressee > third person, in terms of empathy default.
    Captured here as a coarse three-level enum; the *application* of this
    hierarchy to specific syntactic positions (e.g., dative clitic =
    empathy locus, per @cite{charnavel-mateu-2015}) is downstream. -/
inductive EmpathyDefault : Type where
  /-- Speaker — empathy is automatic. -/
  | speaker
  /-- Addressee — empathy is highly accessible. -/
  | addressee
  /-- Third person — empathy must be linguistically marked. -/
  | thirdPerson
  deriving DecidableEq, Repr, Inhabited

/-- Numeric rank for the empathy default hierarchy. -/
def EmpathyDefault.rank : EmpathyDefault → Nat
  | .speaker     => 2
  | .addressee   => 1
  | .thirdPerson => 0

theorem EmpathyDefault.hierarchy :
    EmpathyDefault.speaker.rank > EmpathyDefault.addressee.rank ∧
    EmpathyDefault.addressee.rank > EmpathyDefault.thirdPerson.rank := by decide

end Features.Empathy
