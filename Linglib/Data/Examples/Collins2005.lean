import Linglib.Data.Examples.Schema

/-!
# `Collins2005` — typed example data

Auto-generated from `Linglib/Data/Examples/Collins2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Collins2005.Examples`.
-/

namespace Collins2005.Examples

open Data.Examples

def ex10a : LinguisticExample :=
  { id := "collins2005_ex10a"
    source := ⟨"collins-2005", "UNVERIFIED (10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every letter was signed by its author"
    discourseSegments := []
    glossedTokens := []
    translation := "Every letter was signed by its author"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "c_command"), ("dependency", "bound_variable"), ("licensee_position", "by_phrase")]
    comment := "Migrated from Phenomena/ArgumentStructure/Passive.lean cCommandData. Derived subject 'every letter' binds the pronoun inside the by-phrase: the passive subject c-commands the by-phrase."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10b : LinguisticExample :=
  { id := "collins2005_ex10b"
    source := ⟨"collins-2005", "UNVERIFIED (10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Its author was arrested by every cop"
    discourseSegments := []
    glossedTokens := []
    translation := "Its author was arrested by every cop"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "c_command"), ("dependency", "bound_variable"), ("licensee_position", "subject")]
    comment := "Migrated from Phenomena/ArgumentStructure/Passive.lean cCommandData. Quantifier in the by-phrase cannot bind into the derived subject: the by-phrase does not c-command the subject. Ungrammatical on the bound-variable reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10c : LinguisticExample :=
  { id := "collins2005_ex10c"
    source := ⟨"collins-2005", "UNVERIFIED (10c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No letter was signed by anyone"
    discourseSegments := []
    glossedTokens := []
    translation := "No letter was signed by anyone"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "c_command"), ("dependency", "npi"), ("licensee_position", "by_phrase")]
    comment := "Migrated from Phenomena/ArgumentStructure/Passive.lean cCommandData. Negative derived subject licenses the NPI 'anyone' inside the by-phrase."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10d : LinguisticExample :=
  { id := "collins2005_ex10d"
    source := ⟨"collins-2005", "UNVERIFIED (10d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anyone was fired by no manager"
    discourseSegments := []
    glossedTokens := []
    translation := "Anyone was fired by no manager"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "c_command"), ("dependency", "npi"), ("licensee_position", "subject")]
    comment := "Migrated from Phenomena/ArgumentStructure/Passive.lean cCommandData. Negative quantifier in the by-phrase cannot license an NPI in the derived subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex15a : LinguisticExample :=
  { id := "collins2005_ex15a"
    source := ⟨"collins-2005", "UNVERIFIED (15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The cat was let out"
    discourseSegments := []
    glossedTokens := []
    translation := "The cat was let out"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "particle"), ("has_dp_object", "false")]
    comment := "Migrated from Phenomena/ArgumentStructure/Passive.lean particleData. Passive of a particle verb: the particle stays with the verb inside the smuggled PartP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex16a : LinguisticExample :=
  { id := "collins2005_ex16a"
    source := ⟨"collins-2005", "UNVERIFIED (16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The cat was let out the dog"
    discourseSegments := []
    glossedTokens := []
    translation := "The cat was let out the dog"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "particle"), ("has_dp_object", "true")]
    comment := "Migrated from Phenomena/ArgumentStructure/Passive.lean particleData. No post-particle DP object survives in the passive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex16b : LinguisticExample :=
  { id := "collins2005_ex16b"
    source := ⟨"collins-2005", "UNVERIFIED (16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The cat was let the dog out"
    discourseSegments := []
    glossedTokens := []
    translation := "The cat was let the dog out"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "particle"), ("has_dp_object", "true")]
    comment := "Migrated from Phenomena/ArgumentStructure/Passive.lean (module docstring, ex 16b). No DP object can intercalate between verb and particle in the passive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex23a : LinguisticExample :=
  { id := "collins2005_ex23a"
    source := ⟨"collins-2005", "UNVERIFIED (23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has kicked the ball"
    discourseSegments := []
    glossedTokens := []
    translation := "John has kicked the ball"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "aux_selection"), ("aux", "have"), ("complement_form", "past_participle")]
    comment := "Migrated from Phenomena/ArgumentStructure/Passive.lean auxiliaryData. Perfect 'have' c-selects a participial complement (PartP)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex23b : LinguisticExample :=
  { id := "collins2005_ex23b"
    source := ⟨"collins-2005", "UNVERIFIED (23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ball was kicked"
    discourseSegments := []
    glossedTokens := []
    translation := "The ball was kicked"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "aux_selection"), ("aux", "be"), ("complement_form", "past_participle")]
    comment := "Migrated from Phenomena/ArgumentStructure/Passive.lean auxiliaryData. Passive 'be' likewise requires a participial complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex23c : LinguisticExample :=
  { id := "collins2005_ex23c"
    source := ⟨"collins-2005", "UNVERIFIED (23c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has kicking the ball"
    discourseSegments := []
    glossedTokens := []
    translation := "John has kicking the ball"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "aux_selection"), ("aux", "have"), ("complement_form", "present_participle")]
    comment := "Migrated from Phenomena/ArgumentStructure/Passive.lean auxiliaryData. Perfect 'have' rejects a present-participle complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex23d : LinguisticExample :=
  { id := "collins2005_ex23d"
    source := ⟨"collins-2005", "UNVERIFIED (23d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ball was kick"
    discourseSegments := []
    glossedTokens := []
    translation := "The ball was kick"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "aux_selection"), ("aux", "be"), ("complement_form", "bare_stem")]
    comment := "Migrated from Phenomena/ArgumentStructure/Passive.lean auxiliaryData. Passive 'be' rejects a bare-stem complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex10a, ex10b, ex10c, ex10d, ex15a, ex16a, ex16b, ex23a, ex23b, ex23c, ex23d]

end Collins2005.Examples
