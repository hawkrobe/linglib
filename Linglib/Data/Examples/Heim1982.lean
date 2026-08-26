import Linglib.Data.Examples.Schema

/-!
# `Heim1982` — typed example data

Auto-generated from `Linglib/Data/Examples/Heim1982.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heim1982.Examples`.
-/

namespace Heim1982.Examples

open Data.Examples

def indefinite_persists : LinguisticExample :=
  { id := "heim1982_indefinite_persists"
    source := ⟨"heim-1982", "Ch. I (9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A dog came in. It lay down under the table."
    discourseSegments := ["A dog came in.", "It lay down under the table."]
    glossedTokens := []
    translation := "A dog came in. It lay down under the table."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "none")]
    comment := "Strawson's challenge to Russell's analysis of indefinites (Ch. I §1.1): the pronoun is read as bound by the same variable as the indefinite."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def universal_blocks : LinguisticExample :=
  { id := "heim1982_universal_blocks"
    source := ⟨"heim-1982", "Ch. I (16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every dog came in. It lay down under the table."
    discourseSegments := ["Every dog came in.", "It lay down under the table."]
    glossedTokens := []
    translation := "Every dog came in. It lay down under the table."
    context := "No referent for 'it' fixed independently of the preceding sentence."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "universal"), ("context", "none")]
    comment := "Neither (16) nor (17) permits a reading where 'it' is bound by the quantified NP of the preceding sentence: an unembedded sentence is a scope island."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def negative_blocks : LinguisticExample :=
  { id := "heim1982_negative_blocks"
    source := ⟨"heim-1982", "Ch. I (17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No dog came in. It lay down under the table."
    discourseSegments := ["No dog came in.", "It lay down under the table."]
    glossedTokens := []
    translation := "No dog came in. It lay down under the table."
    context := "No referent for 'it' fixed independently of the preceding sentence."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "negative_quant"), ("context", "none")]
    comment := "See (16)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def most_blocks : LinguisticExample :=
  { id := "heim1982_most_blocks"
    source := ⟨"heim-1982", ""⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most men walked in. He sat down."
    discourseSegments := ["Most men walked in.", "He sat down."]
    glossedTokens := []
    translation := "Most men walked in. He sat down."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "proportional_quant"), ("context", "none")]
    comment := "Not among the dissertation's examples; its 'most' data concern the proportion problem (Ch. I (32)–(33)). Retained for KeshetAbney2024."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def conditional_antecedent : LinguisticExample :=
  { id := "heim1982_conditional_antecedent"
    source := ⟨"heim-1982", ""⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a man walks in, he sits down. He orders coffee."
    discourseSegments := ["If a man walks in, he sits down.", "He orders coffee."]
    glossedTokens := []
    translation := "If a man walks in, he sits down. He orders coffee."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "conditional_antecedent")]
    comment := "Not among the dissertation's examples; the prediction follows from rule (III) leaving the domain of the file unchanged."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def standard_negation_blocks : LinguisticExample :=
  { id := "heim1982_standard_negation_blocks"
    source := ⟨"heim-1982", ""⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't see a bird. It was singing."
    discourseSegments := ["John didn't see a bird.", "It was singing."]
    glossedTokens := []
    translation := "John didn't see a bird. It was singing."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "negation")]
    comment := "Not among the dissertation's examples; the prediction follows from rule (IV) leaving the domain of the file unchanged. Retained for KeshetAbney2024."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def definite_reference : LinguisticExample :=
  { id := "heim1982_definite_reference"
    source := ⟨"heim-1982", "Ch. III (2) of §5.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a cat behind you. The cat is hungry."
    discourseSegments := ["There is a cat behind you.", "The cat is hungry."]
    glossedTokens := []
    translation := "There is a cat behind you. The cat is hungry."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "none")]
    comment := "The first sentence adds a card with the entry 'is a cat'; the definite is then licensed by both the Novelty-Familiarity and the Descriptive-Content Condition (§5.1)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def conditional_donkey : LinguisticExample :=
  { id := "heim1982_conditional_donkey"
    source := ⟨"heim-1982", "Ch. I (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a man owns a donkey, he beats it."
    discourseSegments := []
    glossedTokens := []
    translation := "If a man owns a donkey, he beats it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("donkey_configuration", "conditional")]
    comment := "The indefinites in the antecedent are read with universal force."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def relative_donkey : LinguisticExample :=
  { id := "heim1982_relative_donkey"
    source := ⟨"heim-1982", "Ch. I (3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man who owns a donkey beats it."
    discourseSegments := []
    glossedTokens := []
    translation := "Every man who owns a donkey beats it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("donkey_configuration", "relative_clause")]
    comment := "'every' binds the variable of 'a donkey' inside its restrictive term."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def soldier_gun : LinguisticExample :=
  { id := "heim1982_soldier_gun"
    source := ⟨"heim-1982", "Ch. II (6)/(6a) of §5.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every soldier has a gun. He will shoot."
    discourseSegments := ["Every soldier has a gun.", "He will shoot."]
    glossedTokens := []
    translation := "Every soldier has a gun. He will shoot."
    context := ""
    judgment := .unacceptable
    alternatives := [("Someone has a gun. He will shoot.", .acceptable)]
    readings := []
    paperFeatures := [("antecedent_type", "universal"), ("context", "none")]
    comment := "A scope constraint, not a coindexing constraint: it distinguishes universals from indefinites and names (Ch. II §5.2)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cat_door : LinguisticExample :=
  { id := "heim1982_cat_door"
    source := ⟨"heim-1982", "Ch. II (3) of §3.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A cat was at the door. It wanted to be fed."
    discourseSegments := ["A cat was at the door.", "It wanted to be fed."]
    glossedTokens := []
    translation := "A cat was at the door. It wanted to be fed."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "none")]
    comment := "Text-level truth comes out right, but the Ch. II truth definition assigns no truth value to the second sentence on its own — the motivation for evaluating sentences against files (Ch. III §3.2)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def woman_dog : LinguisticExample :=
  { id := "heim1982_woman_dog"
    source := ⟨"heim-1982", "Ch. III (5) of §2.5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A woman was bitten by a dog. She hit him."
    discourseSegments := ["A woman was bitten by a dog.", "She hit him."]
    glossedTokens := []
    translation := "A woman was bitten by a dog. She hit him."
    context := "Uttered against a file in whose domain neither 1 nor 2 occurs."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "none")]
    comment := "The text requires 1, 2 novel in the initial file although its second sentence, Ch. III (4), requires them familiar: felicity conditions project step by step (§2.5)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def woman_dog_definite : LinguisticExample :=
  { id := "heim1982_woman_dog_definite"
    source := ⟨"heim-1982", "Ch. III (4) of §3.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is a woman. He is a dog. She was bitten by him."
    discourseSegments := ["She is a woman.", "He is a dog.", "She was bitten by him."]
    glossedTokens := []
    translation := "She is a woman. He is a dog. She was bitten by him."
    context := "Uttered against a true file in whose domain both 1 and 2 occur."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "definite"), ("context", "none")]
    comment := "Same satisfaction conditions as 'A woman was bitten by a dog', but under criterion (C) the individuals must fit cards 1 and 2 (§3.2)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def pretzel : LinguisticExample :=
  { id := "heim1982_pretzel"
    source := ⟨"heim-1982", "Ch. III (2) of §4.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone bought a pretzel and ate it."
    discourseSegments := []
    glossedTokens := []
    translation := "Everyone bought a pretzel and ate it."
    context := "Uttered when an empty file obtains."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "nuclear_scope")]
    comment := "Felicitous although 'it₂' needs card 2: the card is introduced by 'a pretzel₂' in an intermediate file, so quantified file change must proceed in steps (§4.1)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def flea_collar : LinguisticExample :=
  { id := "heim1982_flea_collar"
    source := ⟨"heim-1982", "Ch. III (7) of §4.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a cat is well cared for, it always has a flea collar."
    discourseSegments := []
    glossedTokens := []
    translation := "If a cat is well cared for, it always has a flea collar."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "nuclear_scope")]
    comment := "'a flea collar' has narrow-scope existential force without a construal rule of Existential Closure: rule (III) existentially closes the nuclear scope (§4.3)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def dog_bite : LinguisticExample :=
  { id := "heim1982_dog_bite"
    source := ⟨"heim-1982", "Ch. III (3) of §5.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Watch out, the dog will bite you."
    discourseSegments := []
    glossedTokens := []
    translation := "Watch out, the dog will bite you."
    context := "Said to the addressee walking up a driveway: no previous discourse, no dog in sight, no reason to believe a dog lives there."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "definite"), ("context", "accommodation")]
    comment := "Hawkins's immediate situation use; a novel definite rendered felicitous by accommodating a card 'is a dog somewhere close by' (§5.2)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def king_of_france : LinguisticExample :=
  { id := "heim1982_king_of_france"
    source := ⟨"heim-1982", "Ch. III (10) of §5.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary didn't have lunch with the king of France (because France doesn't have a king)."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary didn't have lunch with the king of France (because France doesn't have a king)."
    context := "The because-clause denies that France has a king."
    judgment := .acceptable
    alternatives := []
    readings := [("narrow scope (local accommodation)", .acceptable), ("existence implied (global accommodation)", .acceptable)]
    paperFeatures := [("antecedent_type", "definite"), ("context", "negation")]
    comment := "Accommodation inside the auxiliary file of the negation yields the narrow-scope reading; accommodating the initial file instead implies a king of France and is the preferred option without the because-clause (§5.2)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [indefinite_persists, universal_blocks, negative_blocks, most_blocks, conditional_antecedent, standard_negation_blocks, definite_reference, conditional_donkey, relative_donkey, soldier_gun, cat_door, woman_dog, woman_dog_definite, pretzel, flea_collar, dog_bite, king_of_france]

end Heim1982.Examples
