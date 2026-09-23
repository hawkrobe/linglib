module

public import Linglib.Data.Examples.Schema

/-!
# `DaviesDubinsky2003` — typed example data

Auto-generated from `Linglib/Data/Examples/DaviesDubinsky2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DaviesDubinsky2003.Examples`.
-/

@[expose] public section

namespace DaviesDubinsky2003.Examples

open Data.Examples

def ex52a_write : LinguisticExample :=
  { id := "daviesdubinsky2003_ex52a_write"
    source := ⟨"davies-dubinsky-2003", "(52a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you write those essays about?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "write"), ("creation", "yes"), ("object", "definite")]
    comment := "A verb of creation licenses extraction from a definite result nominal."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex52a_read : LinguisticExample :=
  { id := "daviesdubinsky2003_ex52a_read"
    source := ⟨"davies-dubinsky-2003", "(52a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you read those essays about?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "read"), ("creation", "no"), ("object", "definite")]
    comment := "Marked ?? in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex52b_write : LinguisticExample :=
  { id := "daviesdubinsky2003_ex52b_write"
    source := ⟨"davies-dubinsky-2003", "(52b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you write essays about?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "write"), ("creation", "yes"), ("object", "indefinite")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex52b_read : LinguisticExample :=
  { id := "daviesdubinsky2003_ex52b_read"
    source := ⟨"davies-dubinsky-2003", "(52b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you read essays about?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "read"), ("creation", "no"), ("object", "indefinite")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex53a_tell : LinguisticExample :=
  { id := "daviesdubinsky2003_ex53a_tell"
    source := ⟨"davies-dubinsky-2003", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you tell those jokes about?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "tell"), ("creation", "yes"), ("object", "definite")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex53a_hear : LinguisticExample :=
  { id := "daviesdubinsky2003_ex53a_hear"
    source := ⟨"davies-dubinsky-2003", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you hear those jokes about?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "hear"), ("creation", "no"), ("object", "definite")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex53b_tell : LinguisticExample :=
  { id := "daviesdubinsky2003_ex53b_tell"
    source := ⟨"davies-dubinsky-2003", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you tell jokes about?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "tell"), ("creation", "yes"), ("object", "indefinite")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex53b_hear : LinguisticExample :=
  { id := "daviesdubinsky2003_ex53b_hear"
    source := ⟨"davies-dubinsky-2003", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you hear jokes about?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "hear"), ("creation", "no"), ("object", "indefinite")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex54a_paint : LinguisticExample :=
  { id := "daviesdubinsky2003_ex54a_paint"
    source := ⟨"davies-dubinsky-2003", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you paint that portrait of?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "paint"), ("creation", "yes"), ("object", "definite")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex54a_see : LinguisticExample :=
  { id := "daviesdubinsky2003_ex54a_see"
    source := ⟨"davies-dubinsky-2003", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you see that portrait of?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "see"), ("creation", "no"), ("object", "definite")]
    comment := "Marked ?? in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex54b_paint : LinguisticExample :=
  { id := "daviesdubinsky2003_ex54b_paint"
    source := ⟨"davies-dubinsky-2003", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you paint a portrait of?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "paint"), ("creation", "yes"), ("object", "indefinite")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex54b_see : LinguisticExample :=
  { id := "daviesdubinsky2003_ex54b_see"
    source := ⟨"davies-dubinsky-2003", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you see a portrait of?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("verb", "see"), ("creation", "no"), ("object", "indefinite")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex52a_write, ex52a_read, ex52b_write, ex52b_read, ex53a_tell, ex53a_hear, ex53b_tell, ex53b_hear, ex54a_paint, ex54a_see, ex54b_paint, ex54b_see]

end DaviesDubinsky2003.Examples
