import Linglib.Data.Examples.Schema

/-!
# `Beaver2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Beaver2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beaver2004.Examples`.
-/

namespace Beaver2004.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "beaver2004_1"
    source := ⟨"beaver-2004", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane likes Mary. She often brings her flowers. She chats with her for ages."
    discourseSegments := []
    glossedTokens := []
    translation := "Jane likes Mary. She often brings her flowers. She chats with her for ages."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("In (1c), she = Jane and her = Mary", .acceptable)]
    paperFeatures := [("transition", "continue")]
    comment := "BFP's worked example: sixteen candidate resolutions of (1c), filtered and ranked; the continuation wins."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "beaver2004_2"
    source := ⟨"beaver-2004", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary likes tennis. She plays Jim quite often. He used to play doubles with Mary."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary likes tennis. She plays Jim quite often. He used to play doubles with Mary."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := [("He = Jim and the two Marys corefer", .marginal)]
    paperFeatures := [("phenomenon", "rule 1 violation")]
    comment := "BFP filters out the coreferential reading (Rule 1); demoting PRO-TOP below FAM-DEF recovers it, and the production tableau explains the awkwardness: the speaker would have pronominalized Mary."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "beaver2004_5"
    source := ⟨"beaver-2004", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane likes Mary. She often visits her for tea. The woman is a compulsive tea drinker."
    discourseSegments := []
    glossedTokens := []
    translation := "Jane likes Mary. She often visits her for tea. The woman is a compulsive tea drinker."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("She = Jane, her = Mary; the woman = Jane", .acceptable)]
    paperFeatures := [("phenomenon", "definite description resolution")]
    comment := "PRO-TOP fails for every candidate of (5c), so FAM-DEF and COHERE decide: the definite resolves to the topic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "beaver2004_8"
    source := ⟨"beaver-2004", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane likes Mary. She often goes around for tea with her. She chats with the young woman for ages."
    discourseSegments := []
    glossedTokens := []
    translation := "Jane likes Mary. She often goes around for tea with her. She chats with the young woman for ages."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("She = Jane, the young woman = Mary", .acceptable)]
    paperFeatures := [("transition", "continue")]
    comment := "The parallel-subject reading wins; the crossed reading violates PRO-TOP and ALIGN."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "beaver2004_9"
    source := ⟨"beaver-2004", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is happy. Mary gave her a present. She smiled."
    discourseSegments := []
    glossedTokens := []
    translation := "Jane is happy. Mary gave her a present. She smiled."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("She = Jane, the topic, not the previous subject Mary", .acceptable)]
    paperFeatures := [("transition", "continue")]
    comment := "Neither parallelism nor subjecthood of the antecedent decides: COHERE keeps the topic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "beaver2004_12"
    source := ⟨"beaver-2004", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is happy. She was congratulated by Freda, and Mary gave her a present."
    discourseSegments := []
    glossedTokens := []
    translation := "Jane is happy. She was congratulated by Freda, and Mary gave her a present."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("her = Jane", .acceptable)]
    paperFeatures := [("transition", "retain")]
    comment := "Jane stays topic but leaves subject position: only ALIGN is violated."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "beaver2004_14"
    source := ⟨"beaver-2004", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is happy. Mary gave her a present. She smiled at her."
    discourseSegments := []
    glossedTokens := []
    translation := "Jane is happy. Mary gave her a present. She smiled at her."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("She = Mary, her = Jane", .acceptable)]
    paperFeatures := [("transition", "smooth shift")]
    comment := "Both pronouns force an anaphoric reading whose topic was non-topical subject before: ALIGN decides."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16 : LinguisticExample :=
  { id := "beaver2004_16"
    source := ⟨"beaver-2004", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is happy. Mary gave her a present. Somebody unwrapped it."
    discourseSegments := []
    glossedTokens := []
    translation := "Jane is happy. Mary gave her a present. Somebody unwrapped it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("it = the present", .acceptable)]
    paperFeatures := [("transition", "rough shift")]
    comment := "The only agreeing resolution shifts the topic to the present, in non-subject position."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "beaver2004_23"
    source := ⟨"beaver-2004", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A great refinement among armorial signets was to reproduce not only the coat-of-arms but the correct tinctures; they were repeated in colour on the reverse side and the crystal would then be set in the gold bezel."
    discourseSegments := []
    glossedTokens := []
    translation := "A great refinement among armorial signets was to reproduce not only the coat-of-arms but the correct tinctures; they were repeated in colour on the reverse side and the crystal would then be set in the gold bezel."
    context := "Corpus example from museum-object descriptions."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "rule 1 violation")]
    comment := "The topic continues via a bridging description while a less salient entity is pronominalized; felicitous, supporting defeasible PRO-TOP over an absolute Rule 1."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24 : LinguisticExample :=
  { id := "beaver2004_24"
    source := ⟨"beaver-2004", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John went to his favorite music store to buy a piano. He had frequented the store for many years. He was excited to be going to the store to actually buy a piano. It was the biggest music store in the area. It had just the kind of piano that he wanted. It was closing just as John arrived."
    discourseSegments := []
    glossedTokens := []
    translation := "John went to his favorite music store to buy a piano. He had frequented the store for many years. He was excited to be going to the store to actually buy a piano. It was the biggest music store in the area. It had just the kind of piano that he wanted. It was closing just as John arrived."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "text coherence")]
    comment := "The coherent variant of the Grosz-Sidner text pair: one COHERE violation in the whole-text tableau."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25 : LinguisticExample :=
  { id := "beaver2004_25"
    source := ⟨"beaver-2004", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John went to his favorite music store to buy a piano. It was a store John had frequented for many years. He was excited to be going to the store to actually buy a piano. It was the biggest music store in the area. He knew that it had just the kind of piano that he wanted. It was closing just as John arrived."
    discourseSegments := []
    glossedTokens := []
    translation := "John went to his favorite music store to buy a piano. It was a store John had frequented for many years. He was excited to be going to the store to actually buy a piano. It was the biggest music store in the area. He knew that it had just the kind of piano that he wanted. It was closing just as John arrived."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "text coherence")]
    comment := "The jerky variant: multiple PRO-TOP, FAM-DEF and ALIGN violations accumulate in the whole-text tableau."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_28 : LinguisticExample :=
  { id := "beaver2004_28"
    source := ⟨"beaver-2004", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred was eating. He saw Jim. HE winked."
    discourseSegments := []
    glossedTokens := []
    translation := "Fred was eating. He saw Jim. HE winked."
    context := "The speaker wants to convey that Jim winked."
    judgment := .acceptable
    alternatives := []
    readings := [("Stressed HE = Jim (switch reference)", .acceptable)]
    paperFeatures := [("phenomenon", "stressed pronoun")]
    comment := "Unstressed he is bidirectionally optimal for Fred, so BLOCK gives the stressed form the complementary, topic-shifting reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_5, ex_8, ex_9, ex_12, ex_14, ex_16, ex_23, ex_24, ex_25, ex_28]

end Beaver2004.Examples
