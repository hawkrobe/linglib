import Linglib.Theories.Syntax.Minimalism.Coreference
import Linglib.Phenomena.Anaphora.Coreference
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Bridge: Minimalist Coreference Theory to Anaphora Phenomena

Connects Minimalist binding theory (c-command, locality) to the empirical
coreference data in `Phenomena.Anaphora.Coreference`.

## Main results

- `captures_reflexive_coreference`: Minimalism correctly predicts reflexive binding
- `captures_complementary_distribution`: Minimalism captures complementary distribution
- `captures_pronominal_disjoint_reference`: Minimalism captures disjoint reference
- `reflexive_pairs_captured`: Per-pair verification
-/

namespace MinimalismCoreference

open Minimalism.Phenomena.Coreference
open Phenomena.Anaphora.Coreference

/-- Check if Minimalism correctly predicts a minimal pair for coreference.

    Grammatical sentence should pass, ungrammatical should fail. -/
def capturesCoreferenceMinimalPair (pair : MinimalPair) : Prop :=
  grammaticalForCoreference pair.grammatical ∧
  ¬ grammaticalForCoreference pair.ungrammatical

instance (pair : MinimalPair) : Decidable (capturesCoreferenceMinimalPair pair) := by
  unfold capturesCoreferenceMinimalPair; infer_instance

/-- Check all pairs in a PhenomenonData -/
def capturesCoreferenceData (phenom : PhenomenonData) : Prop :=
  ∀ p ∈ phenom.pairs, capturesCoreferenceMinimalPair p

instance (phenom : PhenomenonData) : Decidable (capturesCoreferenceData phenom) := by
  unfold capturesCoreferenceData; infer_instance

/-- Minimalism captures reflexiveCoreferenceData -/
theorem captures_reflexive_coreference :
    capturesCoreferenceData reflexiveCoreferenceData := by
  native_decide

/-- Minimalism captures complementaryDistributionData -/
theorem captures_complementary_distribution :
    capturesCoreferenceData complementaryDistributionData := by
  native_decide

/-- Minimalism captures pronominalDisjointReferenceData -/
theorem captures_pronominal_disjoint_reference :
    capturesCoreferenceData pronominalDisjointReferenceData := by
  native_decide

private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev mary := Fragments.English.Nouns.mary.toWordSg
private abbrev they := Fragments.English.Pronouns.they.toWord
private abbrev sees := Fragments.English.Predicates.Verbal.see.toWord3sg
private abbrev see := Fragments.English.Predicates.Verbal.see.toWordPl
private abbrev himself := Fragments.English.Pronouns.himself.toWord
private abbrev herself := Fragments.English.Pronouns.herself.toWord
private abbrev themselves := Fragments.English.Pronouns.themselves.toWord
private abbrev him := Fragments.English.Pronouns.him.toWord
private abbrev them := Fragments.English.Pronouns.them.toWord
private abbrev eachOther := Fragments.English.Pronouns.eachOther.toWord

/-- Check each pair individually for reflexiveCoreferenceData -/
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
  native_decide

/-- Minimalism captures the parseable reciprocal pair: plural antecedent
    required, singular antecedent blocked. -/
theorem reciprocal_plural_antecedent :
    grammaticalForCoreference [they, see, eachOther] ∧
    ¬ grammaticalForCoreference [john, sees, eachOther] := by
  native_decide

end MinimalismCoreference
