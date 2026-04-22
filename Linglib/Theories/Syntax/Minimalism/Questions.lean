import Linglib.Theories.Syntax.Minimalism.Polarity
import Linglib.Theories.Syntax.Minimalism.ClauseSpine
import Linglib.Core.Mood.ClauseType

/-!
# Question Syntax: ForceP, FinP, PolP
@cite{rizzi-1997} @cite{holmberg-2016}

Syntactic projections involved in question formation.

## Clause Structure for Polar Questions

@cite{rizzi-1997}'s split-CP and @cite{holmberg-2016}'s PolP analysis
give the following structure for a polar question:

    [ForceP Force⁰[+Q] [FinP Fin⁰[+finite] [PolP Pol⁰[uPol] [TP ...]]]]

- **ForceP**: Clause-typing head. Force⁰ bears [+Q] for interrogatives,
  [-Q] for declaratives. Corresponds to `Cat.Force` and `FeatureVal.q`.
- **FinP**: Finiteness head. Fin⁰ bears [±finite]. Corresponds to `Cat.Fin`
  and `FeatureVal.finite`.
- **PolP**: Polarity head. Pol⁰ bears valued [±Pol] in declaratives,
  unvalued [uPol] in polar questions. Corresponds to `Cat.Pol` and
  `FeatureVal.pol`. See `Minimalism.Polarity` for the Agree infrastructure.

## Connection to Semantic Questions

`Interfaces.SyntaxSemantics.LeftPeriphery` defines `WHFeature` (±WH on C) —
the semantic clause-typing feature. The syntactic `FeatureVal.q` corresponds
to the semantic `WHFeature`:
- `FeatureVal.q true` ↔ `WHFeature.plusWH`
- `FeatureVal.q false` ↔ `WHFeature.minusWH`

## Connection to ClauseType

A clause's `Core.Mood.ClauseType` (force × mood) is determined by
the syntactic projections:
- Force⁰[+Q] → `IllocutionaryMood.interrogative`
- Force⁰[-Q] → `IllocutionaryMood.declarative`
- Mood is determined lower (by T/Fin morphology), not by ForceP.
-/

namespace Minimalism.Questions

open Minimalism
open Core.Mood (ClauseType GramMood IllocutionaryMood)

/-- The Q-feature on Force⁰: [+Q] for interrogatives, [-Q] for declaratives. -/
inductive QFeature where
  | plusQ   -- interrogative
  | minusQ  -- declarative
  deriving DecidableEq, Repr

/-- Map the Q-feature to a `FeatureVal` for the Agree system. -/
def QFeature.toFeatureVal : QFeature → FeatureVal
  | .plusQ  => .q true
  | .minusQ => .q false

/-- Map the Q-feature to illocutionary force. -/
def QFeature.toForce : QFeature → IllocutionaryMood
  | .plusQ  => .interrogative
  | .minusQ => .declarative

/-- The clause spine for a polar question: V ... T ... Pol ... Fin ... Force.

    This is the full IP-to-CP spine with the projections relevant to
    @cite{holmberg-2016}'s analysis. The Pol head is between T and Fin. -/
def polarQuestionSpine : ClauseSpine :=
  ⟨[.V, .v, .Voice, .T, .Pol, .Neg, .Fin, .Force], by decide⟩

/-- A declarative spine has the same projections. -/
def declarativeSpine : ClauseSpine :=
  ⟨[.V, .v, .Voice, .T, .Pol, .Neg, .Fin, .Force], by decide⟩

/-- PolP is projected in both declaratives and polar questions. -/
theorem polP_always_projected :
    polarQuestionSpine.projects .Pol = true ∧
    declarativeSpine.projects .Pol = true := ⟨rfl, rfl⟩

/-- Derive `ClauseType` from the syntactic features on Force⁰ and T⁰/Fin⁰.

    The Q-feature on Force determines illocutionary force; mood is
    determined by the morphological properties of the verb (indicative
    vs subjunctive), independent of Force. -/
def clauseType (q : QFeature) (m : GramMood) : ClauseType :=
  { force := q.toForce, mood := m }

/-- A polar question with indicative mood. -/
theorem polar_question_is_interrogative_indicative :
    clauseType .plusQ .indicative = ClauseType.polarQuestion := rfl

/-- A declarative with indicative mood. -/
theorem declarative_is_decl_ind :
    clauseType .minusQ .indicative = ClauseType.declInd := rfl

/-- Force and mood are independently set by different heads. -/
theorem force_from_forceP_mood_from_fin :
    (clauseType .plusQ .indicative).force = .interrogative ∧
    (clauseType .plusQ .subjunctive).force = .interrogative ∧
    (clauseType .plusQ .indicative).mood = .indicative ∧
    (clauseType .plusQ .subjunctive).mood = .subjunctive := ⟨rfl, rfl, rfl, rfl⟩

end Minimalism.Questions
