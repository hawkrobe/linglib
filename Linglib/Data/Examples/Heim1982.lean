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
    source := ⟨"karttunen-1976", "UNVERIFIED indefinite establishes a discourse referent"⟩
    reportedIn := some ⟨"heim-1982", "UNVERIFIED Ch I"⟩
    language := "stan1293"
    primaryText := "A man walked in. He sat down."
    discourseSegments := ["A man walked in.", "He sat down."]
    glossedTokens := []
    translation := "A man walked in. He sat down."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "indefinite"), ("context", "none")]
    comment := "Migrated from Phenomena/Anaphora/CrossSentential.lean indefinitePersists. The classic discourse-referent example: the indefinite 'a man' licenses cross-sentential 'he'. Karttunen's 'Discourse Referents' first circulated as a 1969 COLING paper; the canonical incollection version is Karttunen 1976. Discussed throughout Heim 1982."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def universal_blocks : LinguisticExample :=
  { id := "heim1982_universal_blocks"
    source := ⟨"karttunen-1976", "UNVERIFIED universal quantifier blocks discourse reference"⟩
    reportedIn := some ⟨"heim-1982", "UNVERIFIED Ch I"⟩
    language := "stan1293"
    primaryText := "Every man walked in. He sat down."
    discourseSegments := ["Every man walked in.", "He sat down."]
    glossedTokens := []
    translation := "Every man walked in. He sat down."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "universal"), ("context", "none")]
    comment := "Migrated from Phenomena/Anaphora/CrossSentential.lean universalBlocks. A universally quantified antecedent does not introduce an accessible discourse referent for cross-sentential 'he'. Karttunen 1969 COLING origin; canonical version Karttunen 1976. Discussed throughout Heim 1982."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def negative_blocks : LinguisticExample :=
  { id := "heim1982_negative_blocks"
    source := ⟨"karttunen-1976", "UNVERIFIED negative quantifier blocks discourse reference"⟩
    reportedIn := some ⟨"heim-1982", "UNVERIFIED Ch I"⟩
    language := "stan1293"
    primaryText := "No man walked in. He sat down."
    discourseSegments := ["No man walked in.", "He sat down."]
    glossedTokens := []
    translation := "No man walked in. He sat down."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "negative_quant"), ("context", "none")]
    comment := "Migrated from Phenomena/Anaphora/CrossSentential.lean negativeBlocks. A negative quantifier does not introduce an accessible discourse referent. Karttunen 1969 COLING origin; canonical version Karttunen 1976. Discussed throughout Heim 1982."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def most_blocks : LinguisticExample :=
  { id := "heim1982_most_blocks"
    source := ⟨"heim-1982", "UNVERIFIED proportional quantifier blocks discourse reference"⟩
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
    comment := "Migrated from Phenomena/Anaphora/CrossSentential.lean mostBlocks. Proportional quantifiers pattern with universals in not introducing an accessible discourse referent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def conditional_antecedent : LinguisticExample :=
  { id := "heim1982_conditional_antecedent"
    source := ⟨"heim-1982", "UNVERIFIED indefinite in if-clause does not persist"⟩
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
    comment := "Migrated from Phenomena/Anaphora/CrossSentential.lean conditionalAntecedent. The indefinite inside the if-clause binds 'he' within the conditional but does not persist into subsequent discourse."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def standard_negation_blocks : LinguisticExample :=
  { id := "heim1982_standard_negation_blocks"
    source := ⟨"heim-1982", "UNVERIFIED negation blocks discourse reference"⟩
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
    comment := "Migrated from Phenomena/Anaphora/CrossSentential.lean standardNegationBlocks. An indefinite under single negation does not introduce an accessible discourse referent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def definite_reference : LinguisticExample :=
  { id := "heim1982_definite_reference"
    source := ⟨"heim-1982", "UNVERIFIED definites introduce accessible referents"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The man walked in. He sat down."
    discourseSegments := ["The man walked in.", "He sat down."]
    glossedTokens := []
    translation := "The man walked in. He sat down."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent_type", "definite"), ("context", "none")]
    comment := "Migrated from Phenomena/Anaphora/CrossSentential.lean definiteReference. Definites also support cross-sentential anaphora; under the Novelty-Familiarity Condition they require a familiar index."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def conditional_donkey : LinguisticExample :=
  { id := "heim1982_conditional_donkey"
    source := ⟨"heim-1982", "UNVERIFIED conditional donkey sentence"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a farmer owns a donkey, he beats it."
    discourseSegments := []
    glossedTokens := []
    translation := "If a farmer owns a donkey, he beats it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strong/universal", .acceptable), ("weak/existential", .acceptable), ("bound", .acceptable)]
    paperFeatures := [("donkey_configuration", "conditional")]
    comment := "Migrated from Phenomena/Anaphora/DonkeyAnaphora.lean conditionalDonkey. The conditional variant of the Geach donkey sentence; the indefinites in the antecedent acquire universal force over the conditional."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [indefinite_persists, universal_blocks, negative_blocks, most_blocks, conditional_antecedent, standard_negation_blocks, definite_reference, conditional_donkey]

end Heim1982.Examples
