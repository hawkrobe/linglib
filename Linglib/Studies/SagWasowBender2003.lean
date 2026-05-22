import Linglib.Theories.Syntax.HPSG.Coreference
import Linglib.Phenomena.Anaphora.Coreference
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Paradigms.AcceptabilityJudgment

/-!
# Sag, Wasow & Bender (2003) — HPSG Binding Theory @cite{sag-wasow-bender-2003}

*Syntactic Theory: A Formal Introduction* (2nd ed.), Ch. 7.

The HPSG binding theory of @cite{sag-wasow-bender-2003} reduces the
Chomskyan three-way classification (anaphor / pronoun / R-expression →
Principles A/B/C) to two principles based on the `MODE` feature:

- **Principle A**: `[MODE ana]` must be outranked on ARG-ST by a coindexed element
- **Principle B**: `[MODE ref]` must NOT be outranked on ARG-ST by a coindexed element

Both pronouns and R-expressions are `[MODE ref]`, so Principle B subsumes
Principle C. See `Theories/Syntax/HPSG/Coreference.lean` for the
implementation; this file verifies it against the empirical minimal-pair
data in `Phenomena/Anaphora/Coreference.lean` via the
`Paradigms.AcceptabilityJudgment` contract.
-/

namespace SagWasowBender2003

open Paradigms.AcceptabilityJudgment
open HPSG.Coreference
open Phenomena.Anaphora.Coreference

/-- Coverage of a `PhenomenonData` set under HPSG binding. -/
def capturesCoreferenceData (phenom : PhenomenonData) : Bool :=
  capturesPhenomenonData grammaticalForCoreference phenom

/-- HPSG captures `reflexiveCoreferenceData`. -/
theorem captures_reflexive_coreference :
    capturesCoreferenceData reflexiveCoreferenceData = true := by
  decide

/-- HPSG captures `complementaryDistributionData`. -/
theorem captures_complementary_distribution :
    capturesCoreferenceData complementaryDistributionData = true := by
  decide

/-- HPSG captures `pronominalDisjointReferenceData`. -/
theorem captures_pronominal_disjoint_reference :
    capturesCoreferenceData pronominalDisjointReferenceData = true := by
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
    -- Pair 1: john sees himself vs himself sees john
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [himself, sees, john] = false) ∧
    -- Pair 2: mary sees herself vs herself sees mary
    (grammaticalForCoreference [mary, sees, herself] = true ∧
     grammaticalForCoreference [herself, sees, mary] = false) ∧
    -- Pair 3: they see themselves vs themselves see them
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [themselves, see, them] = false) ∧
    -- Pair 4: agreement - john sees himself vs john sees herself
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [john, sees, herself] = false) ∧
    -- Pair 5: agreement - they see themselves vs they see himself
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [they, see, himself] = false) := by
  decide

/-- Reciprocal binding: plural antecedent required, singular blocked.
    (Pairs 1–2 of `reciprocalCoreferenceData` use 5-word coordinated
    sentences that exceed the simple clause parser.) -/
theorem reciprocal_plural_antecedent :
    grammaticalForCoreference [they, see, eachOther] = true ∧
    grammaticalForCoreference [john, sees, eachOther] = false := by
  decide

end SagWasowBender2003
