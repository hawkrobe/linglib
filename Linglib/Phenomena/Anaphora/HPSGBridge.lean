import Linglib.Theories.Syntax.HPSG.Coreference
import Linglib.Phenomena.Anaphora.Coreference

/-!
# Bridge: HPSG Coreference Theory to Anaphora Phenomena

Connects HPSG binding theory (o-command, LOCAL domains) to the empirical
coreference data in `Phenomena.Anaphora.Coreference`.

## Main results

- `captures_reflexive_coreference`: HPSG correctly predicts reflexive binding
- `captures_complementary_distribution`: HPSG captures complementary distribution
- `captures_pronominal_disjoint_reference`: HPSG captures disjoint reference
- `reflexive_pairs_captured`: Per-pair verification
-/

namespace Phenomena.Anaphora.HPSGBridge

open HPSG.Coreference

/-- Check if HPSG correctly predicts a minimal pair for coreference.

    Grammatical sentence should pass, ungrammatical should fail. -/
def capturesCoreferenceMinimalPair (pair : MinimalPair) : Bool :=
  grammaticalForCoreference pair.grammatical &&
  !grammaticalForCoreference pair.ungrammatical

/-- Check all pairs in a PhenomenonData -/
def capturesCoreferenceData (phenom : PhenomenonData) : Bool :=
  phenom.pairs.all capturesCoreferenceMinimalPair

/-- HPSG captures reflexiveCoreferenceData -/
theorem captures_reflexive_coreference :
    capturesCoreferenceData reflexiveCoreferenceData = true := by
  native_decide

/-- HPSG captures complementaryDistributionData -/
theorem captures_complementary_distribution :
    capturesCoreferenceData complementaryDistributionData = true := by
  native_decide

/-- HPSG captures pronominalDisjointReferenceData -/
theorem captures_pronominal_disjoint_reference :
    capturesCoreferenceData pronominalDisjointReferenceData = true := by
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

/-- Check each pair individually for reflexiveCoreferenceData -/
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
  native_decide

end Phenomena.Anaphora.HPSGBridge
