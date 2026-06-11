import Linglib.Data.Examples.Schema

/-!
# `Partee2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Partee2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Partee2010.Examples`.
-/

namespace Partee2010.Examples

open Data.Examples

def ex_10a : LinguisticExample :=
  { id := "partee2010_10a"
    source := ⟨"partee-2010", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A fake gun is not a gun."
    discourseSegments := []
    glossedTokens := [("A", "INDEF"), ("fake", "fake"), ("gun", "gun"), ("is", "be.PRS.3SG"), ("not", "NEG"), ("a", "INDEF"), ("gun", "gun")]
    translation := "A fake gun is not a gun."
    context := "Cited as an apparently-true privative entailment (the prima facie evidence for the privative class)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee §2. Paired with (10b): if 'gun' excludes fake guns (the privative analysis), why is (10b) well-formed?"
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_10b : LinguisticExample :=
  { id := "partee2010_10b"
    source := ⟨"partee-2010", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is that gun real or fake?"
    discourseSegments := []
    glossedTokens := [("Is", "be.PRS.3SG"), ("that", "DEM"), ("gun", "gun"), ("real", "real"), ("or", "or"), ("fake", "fake")]
    translation := "Is that gun real or fake?"
    context := "The 'gun puzzle': for this question to be well-formed, 'gun' must include both real and fake guns. Direct evidence that the noun's denotation coerces to include the adjective's extension."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee §2 ex. (10b). The motivating puzzle: traditional privative analysis predicts 'gun' ∩ 'fake gun' = ∅, but (10b) presupposes 'gun' covers both. Resolved in §4 via NVP-licensed coercion of 'gun' to 'gun*'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_11a : LinguisticExample :=
  { id := "partee2010_11a"
    source := ⟨"nowak-2000", "(11a)"⟩
    reportedIn := some ⟨"partee-2010", "(11a)"⟩
    language := "poli1260"
    primaryText := "Kelnerki rozmawiały o przystojnym chłopcu."
    discourseSegments := []
    glossedTokens := [("Kelnerki", "waitress.NOM.PL"), ("rozmawiały", "talk.PST.3PL.F"), ("o", "about"), ("przystojnym", "handsome.LOC.SG.M"), ("chłopcu", "boy.LOC.SG")]
    translation := "The waitresses talked about a handsome boy."
    context := "Unmarked NP-internal word order; Adj+N adjacent within the PP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §3 ex. (11a); Nowak 2000. Baseline for the split construction in (11b)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_11b : LinguisticExample :=
  { id := "partee2010_11b"
    source := ⟨"nowak-2000", "(11b)"⟩
    reportedIn := some ⟨"partee-2010", "(11b)"⟩
    language := "poli1260"
    primaryText := "O przystojnym kelnerki rozmawiały chłopcu."
    discourseSegments := []
    glossedTokens := [("O", "about"), ("przystojnym", "handsome.LOC.SG.M"), ("kelnerki", "waitress.NOM.PL"), ("rozmawiały", "talk.PST.3PL.F"), ("chłopcu", "boy.LOC.SG")]
    translation := "The waitresses talked about a handsome BOY."
    context := "NP-split: preposition + adjective in sentence-initial position, head noun sentence-final. Topic-focus structure highlights the noun."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §3 ex. (11b); Nowak 2000. The split-NP construction central to Partee's argument: intersective 'przystojny' splits cleanly. Compare with (14b) where non-subsective 'były' cannot split."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_13b : LinguisticExample :=
  { id := "partee2010_13b"
    source := ⟨"nowak-2000", "(13b)"⟩
    reportedIn := some ⟨"partee-2010", "(13b)"⟩
    language := "poli1260"
    primaryText := "Do doliny weszliśmy rozległej."
    discourseSegments := []
    glossedTokens := [("Do", "to"), ("doliny", "valley.GEN.SG"), ("weszliśmy", "enter.PST.1PL"), ("rozległej", "large.GEN.SG.F")]
    translation := "We entered a LARGE valley."
    context := "NP-split with intersective adjective 'rozległy' (large). The split succeeds, as expected for intersective Adj+N."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §3 ex. (13b); Nowak 2000. Intersective member of the splittable class (15a/c)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_14b : LinguisticExample :=
  { id := "partee2010_14b"
    source := ⟨"nowak-2000", "(14b)"⟩
    reportedIn := some ⟨"partee-2010", "(14b)"⟩
    language := "poli1260"
    primaryText := "Z prezydentem rozmawiała byłym."
    discourseSegments := []
    glossedTokens := [("Z", "with"), ("prezydentem", "president.INS.SG"), ("rozmawiała", "talk.PST.3SG.F"), ("byłym", "former.INS.SG.M")]
    translation := "She talked with the FORMER president."
    context := "Attempted NP-split with non-subsective modal adjective 'były' (former). The split is ungrammatical."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §3 ex. (14b); Nowak 2000. Critical negative datum: non-subsective adjectives cannot split. This is the empirical contrast that motivates the 3-class hierarchy: the splitting diagnostic distinguishes subsective (including former privatives) from non-subsective, NOT privative from non-privative."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def biedny_ambiguity : LinguisticExample :=
  { id := "partee2010_biedny_ambiguity"
    source := ⟨"nowak-2000", "(15b),(16a)"⟩
    reportedIn := some ⟨"partee-2010", "(15b),(16a)"⟩
    language := "poli1260"
    primaryText := "biedny"
    discourseSegments := []
    glossedTokens := [("biedny", "poor.NOM.SG.M")]
    translation := "poor / pitiful (lexically ambiguous)"
    context := "Polish 'biedny' is lexically ambiguous between an intersective reading 'not rich' (15b: can split in NP-split construction) and a non-subsective reading 'pitiful' (16a: cannot split). The splitting diagnostic tracks the READING, not the lexical form."
    judgment := .acceptable
    alternatives := []
    readings := [("intersective 'not rich'", .acceptable), ("non-subsective 'pitiful'", .unacceptable)]
    paperFeatures := []
    comment := "Partee 2010 §3 exs. (15b) and (16a); Nowak 2000. The single most precise empirical claim in the paper: the same lexical item splits or fails to split depending on its semantic class. This refutes any attempt to assimilate splitting to a morphological or lexical feature of the adjective. The `readings` field captures the discrimination at the reading level — the discrimination cannot be encoded at the class level alone."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_17b : LinguisticExample :=
  { id := "partee2010_17b"
    source := ⟨"partee-2010", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't care whether that fur is fake or real."
    discourseSegments := []
    glossedTokens := [("I", "1SG"), ("don't", "do.PRS.NEG"), ("care", "care"), ("whether", "whether"), ("that", "DEM"), ("fur", "fur"), ("is", "be.PRS.3SG"), ("fake", "fake"), ("or", "or"), ("real", "real")]
    translation := "I don't care whether that fur is fake or real."
    context := "Generalization of the (10b) gun-puzzle to 'fur'. The polar disjunction 'fake or real' presupposes that 'fur' covers both fake and real fur; otherwise 'real' would be redundant. Direct evidence of NVP-licensed coercion of the noun extension."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §4 ex. (17b). Together with (10b), the canonical evidence for noun-extension coercion. The paper notes 'real' would always be redundant without coercion."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_19b : LinguisticExample :=
  { id := "partee2010_19b"
    source := ⟨"kamp-partee-1995", "(19b) in Partee 2010"⟩
    reportedIn := some ⟨"partee-2010", "(19b)"⟩
    language := "stan1293"
    primaryText := "a midget giant (a giant, but an exceptionally small one)"
    discourseSegments := []
    glossedTokens := [("a", "INDEF"), ("midget", "midget"), ("giant", "giant")]
    translation := "a midget giant (a giant, but an exceptionally small one)"
    context := "Test case for HPP (Head Primacy Principle): the head 'giant' fixes the local domain; the modifier 'midget' is interpreted relative to that domain, yielding 'small for a giant'. Compare (19a) 'giant midget' = a midget who is exceptionally large."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §4 ex. (19b); credited to Kamp & Partee 1995. The classical HPP example: identical adjective+noun pairs receive different interpretations depending on which is head, because the head fixes the local domain."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_21b : LinguisticExample :=
  { id := "partee2010_21b"
    source := ⟨"kamp-partee-1995", "(21b) in Partee 2010"⟩
    reportedIn := some ⟨"partee-2010", "(21b)"⟩
    language := "stan1293"
    primaryText := "Knives are sharp."
    discourseSegments := []
    glossedTokens := [("Knives", "knife.PL"), ("are", "be.PRS.3PL"), ("sharp", "sharp")]
    translation := "Knives are sharp."
    context := "Test case for NVP (Non-Vacuity Principle). Generic predication: 'sharp' would be redundant if 'knife' presupposed sharpness; NVP forces a reading where some knives are not sharp, so the generic claim is non-vacuous."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §4 ex. (21b); credited to Kamp & Partee 1995. Demonstrates that NVP applies to simple predicates, not just to Adj+N combinations — the same principle Partee invokes for privative coercion."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_22b : LinguisticExample :=
  { id := "partee2010_22b"
    source := ⟨"partee-2010", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many poets are buried in Amherst?"
    discourseSegments := []
    glossedTokens := [("How", "how"), ("many", "many"), ("poets", "poet.PL"), ("are", "be.PRS.3PL"), ("buried", "bury.PASS.PTCP"), ("in", "in"), ("Amherst", "Amherst")]
    translation := "How many poets are buried in Amherst?"
    context := "Demonstrates context-shift of the noun 'poet' independent of any adjective. With predicate 'buried', 'poets' presupposes dead poets; with 'live in' or similar present-tense, 'poets' presupposes living poets. Shows N's extension is itself adjustable, supporting the coercion mechanism Partee invokes for privatives."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §4 ex. (22b). Closing argument: noun extensions are context-adjustable independently of adjective modification, so the coercion machinery posited for privatives isn't an ad hoc rescue — it's a general property of noun interpretation."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_12a : LinguisticExample :=
  { id := "partee2010_12a"
    source := ⟨"nowak-2000", "(12a)"⟩
    reportedIn := some ⟨"partee-2010", "(12a)"⟩
    language := "poli1260"
    primaryText := "Włamano się do nowego sklepu."
    discourseSegments := []
    glossedTokens := [("Włamano", "break.in-NEUT.SG"), ("się", "REFL"), ("do", "to"), ("nowego", "new.GEN.SG.M"), ("sklepu", "store.GEN.SG")]
    translation := "Someone broke into the new store."
    context := "Unmarked NP-internal order; baseline for the split in (12b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §3 ex. (12a); Nowak 2000. Unsplit baseline for the (12b) split-NP contrast."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_12b : LinguisticExample :=
  { id := "partee2010_12b"
    source := ⟨"nowak-2000", "(12b)"⟩
    reportedIn := some ⟨"partee-2010", "(12b)"⟩
    language := "poli1260"
    primaryText := "Do sklepu włamano się nowego."
    discourseSegments := []
    glossedTokens := [("Do", "to"), ("sklepu", "store.GEN.SG"), ("włamano", "break.in-NEUT.SG"), ("się", "REFL"), ("nowego", "new.GEN.SG.M")]
    translation := "Someone broke into the NEW store."
    context := "NP-split: noun-in-PP sentence-initial, adjective sentence-final. Intersective 'nowy' (new) splits cleanly."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §3 ex. (12b); Nowak 2000. A second splittable intersective adjective, paired with (11b) to show the pattern is not lexically isolated."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_13a : LinguisticExample :=
  { id := "partee2010_13a"
    source := ⟨"nowak-2000", "(13a)"⟩
    reportedIn := some ⟨"partee-2010", "(13a)"⟩
    language := "poli1260"
    primaryText := "Do rozległej weszliśmy doliny."
    discourseSegments := []
    glossedTokens := [("Do", "to"), ("rozległej", "large.GEN.SG.F"), ("weszliśmy", "enter.PST.1PL"), ("doliny", "valley.GEN.SG")]
    translation := "We entered a large VALLEY."
    context := "Alternate split order: preposition + adjective initial, noun final. Pair-mate of (13b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §3 ex. (13a); Nowak 2000. Both orderings of (13) are acceptable splits, demonstrating that the construction does not constrain which element is sentence-final."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_14a : LinguisticExample :=
  { id := "partee2010_14a"
    source := ⟨"nowak-2000", "(14a)"⟩
    reportedIn := some ⟨"partee-2010", "(14a)"⟩
    language := "poli1260"
    primaryText := "Z byłym rozmawiała prezydentem."
    discourseSegments := []
    glossedTokens := [("Z", "with"), ("byłym", "former.INS.SG.M"), ("rozmawiała", "talk.PST.3SG.F"), ("prezydentem", "president.INS.SG")]
    translation := "She talked with the former PRESIDENT."
    context := "Attempted NP-split with non-subsective 'były' (former). Ungrammatical regardless of split order; pair-mate of (14b)."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §3 ex. (14a); Nowak 2000. The ungrammaticality holds for both split orders, ruling out a syntactic explanation tied to which element is sentence-final."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_17a : LinguisticExample :=
  { id := "partee2010_17a"
    source := ⟨"partee-2010", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't care whether that fur is fake fur or real fur."
    discourseSegments := []
    glossedTokens := [("I", "1SG"), ("don't", "do.PRS.NEG"), ("care", "care"), ("whether", "whether"), ("that", "DEM"), ("fur", "fur"), ("is", "be.PRS.3SG"), ("fake", "fake"), ("fur", "fur"), ("or", "or"), ("real", "real"), ("fur", "fur")]
    translation := "I don't care whether that fur is fake fur or real fur."
    context := "Explicit form of the fur disjunction, with both 'fake fur' and 'real fur' as full NPs. The acceptability shows the noun 'fur' uncontroversially covers both extensions."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §4 ex. (17a). The unreduced form makes the coercion visible: 'fur' must be the extension covering both halves of the disjunction."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_19a : LinguisticExample :=
  { id := "partee2010_19a"
    source := ⟨"kamp-partee-1995", "(19a) in Partee 2010"⟩
    reportedIn := some ⟨"partee-2010", "(19a)"⟩
    language := "stan1293"
    primaryText := "a giant midget (a midget, but an exceptionally large one)"
    discourseSegments := []
    glossedTokens := [("a", "INDEF"), ("giant", "giant"), ("midget", "midget")]
    translation := "a giant midget (a midget, but an exceptionally large one)"
    context := "HPP pair-mate of (19b): with 'midget' as head, the local domain is midgets; 'giant' shifts to 'large for a midget'. Same words, opposite interpretations."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §4 ex. (19a); Kamp & Partee 1995. The (19a)/(19b) minimal pair is the canonical demonstration that head choice fixes the local domain — without (19a) as foil, (19b) does not make the HPP point."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_21a : LinguisticExample :=
  { id := "partee2010_21a"
    source := ⟨"kamp-partee-1995", "(21a) in Partee 2010"⟩
    reportedIn := some ⟨"partee-2010", "(21a)"⟩
    language := "stan1293"
    primaryText := "This is a sharp knife."
    discourseSegments := []
    glossedTokens := [("This", "DEM"), ("is", "be.PRS.3SG"), ("a", "INDEF"), ("sharp", "sharp"), ("knife", "knife")]
    translation := "This is a sharp knife."
    context := "Episodic predication mate of the generic (21b). Both can be true together; 'sharp' is not redundant in (21a) because NVP requires the local domain of knives to contain both sharp and non-sharp instances."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §4 ex. (21a); Kamp & Partee 1995. Without (21a) as foil, the NVP analysis of (21b) does not have a contrastive case to anchor."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_22a : LinguisticExample :=
  { id := "partee2010_22a"
    source := ⟨"partee-2010", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many poets are there in Amherst?"
    discourseSegments := []
    glossedTokens := [("How", "how"), ("many", "many"), ("poets", "poet.PL"), ("are", "be.PRS.3PL"), ("there", "EXIST"), ("in", "in"), ("Amherst", "Amherst")]
    translation := "How many poets are there in Amherst?"
    context := "Existential predicate companion of (22b). With 'are there', 'poets' presupposes living poets, contrasting with (22b) where 'are buried' presupposes dead poets. Same noun, context-shifted extension."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Partee 2010 §4 ex. (22a). Required as the live-poets foil for (22b)'s dead-poets reading; the pair demonstrates that the noun-extension shift Partee invokes for privatives is independently attested for ordinary nouns under predicate-driven coercion."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex_10a, ex_10b, ex_11a, ex_11b, ex_13b, ex_14b, biedny_ambiguity, ex_17b, ex_19b, ex_21b, ex_22b, ex_12a, ex_12b, ex_13a, ex_14a, ex_17a, ex_19a, ex_21a, ex_22a]

end Partee2010.Examples
