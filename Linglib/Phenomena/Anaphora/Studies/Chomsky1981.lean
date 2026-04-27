import Linglib.Theories.Syntax.Minimalism.Coreference
import Linglib.Phenomena.Anaphora.Coreference
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Paradigms.AcceptabilityJudgment

/-!
# Chomsky (1981) — Binding Principles A/B/C @cite{chomsky-1981}

*Lectures on Government and Binding*. Foris.

The Government-and-Binding binding theory of @cite{chomsky-1981}
classifies nominal expressions into three types and constrains their
distribution by c-command + a local binding domain:

- **Principle A**: an anaphor must be bound (c-commanded by a coindexed
  antecedent) in its local domain
- **Principle B**: a pronoun must be free (not bound) in its local domain
- **Principle C**: an R-expression must be free everywhere

This file verifies the implementation in
`Theories/Syntax/Minimalism/Coreference.lean` against the empirical
minimal-pair data in `Phenomena/Anaphora/Coreference.lean`.

Companion to `Reinhart1976.lean` (which formalizes the c-command
relation that Principles A/B/C presuppose) and to
`SagWasowBender2003.lean` (the HPSG re-axiomatization that subsumes
Principle C under Principle B).
-/

namespace Chomsky1981

open Paradigms.AcceptabilityJudgment
open Minimalism.Coreference
open Phenomena.Anaphora.Coreference

/-- Coverage of a `PhenomenonData` set under Minimalist binding theory.

    Stated `Prop`-valued (with a `Decidable` instance) because the
    underlying `grammaticalForCoreference` predicate is `Prop`-valued. -/
def capturesCoreferenceData (phenom : PhenomenonData) : Prop :=
  ∀ p ∈ phenom.pairs,
    grammaticalForCoreference p.grammatical ∧ ¬ grammaticalForCoreference p.ungrammatical

instance (phenom : PhenomenonData) : Decidable (capturesCoreferenceData phenom) := by
  unfold capturesCoreferenceData; infer_instance

/-- Minimalism captures `reflexiveCoreferenceData`. -/
theorem captures_reflexive_coreference :
    capturesCoreferenceData reflexiveCoreferenceData := by
  decide

/-- Minimalism captures `complementaryDistributionData`. -/
theorem captures_complementary_distribution :
    capturesCoreferenceData complementaryDistributionData := by
  decide

/-- Minimalism captures `pronominalDisjointReferenceData`. -/
theorem captures_pronominal_disjoint_reference :
    capturesCoreferenceData pronominalDisjointReferenceData := by
  decide

private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev mary := Fragments.English.Nouns.mary.toWordSg
private abbrev they := Fragments.English.Pronouns.they.toWord
private abbrev sees := Fragments.English.Predicates.Verbal.see.toWord3sg
private abbrev see := Fragments.English.Predicates.Verbal.see.toWordPl
private abbrev himself := Fragments.English.Pronouns.himself.toWord
private abbrev herself := Fragments.English.Pronouns.herself.toWord
private abbrev themselves := Fragments.English.Pronouns.themselves.toWord
private abbrev them := Fragments.English.Pronouns.them.toWord
private abbrev eachOther := Fragments.English.Pronouns.eachOther.toWord

/-- Per-pair verification of reflexive binding judgments. -/
theorem reflexive_pairs_captured :
    (grammaticalForCoreference [john, sees, himself] ∧
     ¬ grammaticalForCoreference [himself, sees, john]) ∧
    (grammaticalForCoreference [mary, sees, herself] ∧
     ¬ grammaticalForCoreference [herself, sees, mary]) ∧
    (grammaticalForCoreference [they, see, themselves] ∧
     ¬ grammaticalForCoreference [themselves, see, them]) ∧
    (grammaticalForCoreference [john, sees, himself] ∧
     ¬ grammaticalForCoreference [john, sees, herself]) ∧
    (grammaticalForCoreference [they, see, themselves] ∧
     ¬ grammaticalForCoreference [they, see, himself]) := by
  decide

/-- Reciprocal binding: plural antecedent required, singular blocked. -/
theorem reciprocal_plural_antecedent :
    grammaticalForCoreference [they, see, eachOther] ∧
    ¬ grammaticalForCoreference [john, sees, eachOther] := by
  decide

end Chomsky1981
