import Linglib.Theories.Semantics.Gradability.Classification
import Linglib.Theories.Semantics.Composition.Coercion
import Linglib.Phenomena.Gradability.Studies.Kamp1975
import Linglib.Data.Examples.Schema

/-!
# Partee (2010): Privative Adjectives: Subsective plus Coercion
@cite{partee-2010} @cite{kamp-1975} @cite{kamp-partee-1995} @cite{nowak-2000}

In R. Bäuerle, U. Reyle, & T. E. Zimmermann (eds.), *Presuppositions and
Discourse: Essays Offered to Hans Kamp*, 273–292. Brill.

(Circulated as a manuscript since 2001.)

## Overview

@cite{partee-2010} argues that there are **no genuinely privative
adjectives**. What @cite{kamp-1975} classified as "privative" (fake,
counterfeit, fictitious) is actually **subsective** — under coercion of
the noun's denotation.

## Structure of the argument (mirrors the paper)

- **§ 2** (paper): reviews the four-class hierarchy with meaning
  postulates; introduces the gun-real-or-fake puzzle at ex. (10b).
- **§ 3** (paper): Polish NP-split data from @cite{nowak-2000}; shows
  that the split diagnostic crosses the privative/non-privative
  boundary, supporting reclassification.
- **§ 4** (paper): the "no privative adjectives" hypothesis. Coercion
  is **principled**, not arbitrary: it is driven jointly by the
  **Non-Vacuity Principle (NVP)** and the **Head Primacy Principle
  (HPP)** of @cite{kamp-partee-1995} (paper formulae 18 and 20).

## What this file formalises

The licensing infrastructure — NVP, HPP, `LicensedCoercion` — lives in
`Theories/Semantics/Composition/Coercion.lean`. The `RevisedClass`
3-class enum lives in `Theories/Semantics/Gradability/Classification.lean`.
This study file states the two paper-anchored substantive theorems:

1. `privative_admits_licensed_coercion`: every Kamp-privative
   adjective admits an NVP-licensed coercion of any noun whose direct
   application would force vacuity. (Paper § 4.)
2. `fakeAdj_coerces`: the previous theorem instantiated on
   @cite{kamp-1975}'s canonical `fakeAdj` witness — the formal bridge
   showing Partee's reanalysis applies to Kamp's own example.

Both proofs are `sorry`-marked. A faithful proof requires constructing
the minimal NVP-satisfying shift and verifying HPP-locality; this is
non-trivial set-theoretic combinatorics that depends on substrate
(`Set` API around `Property.union`) still being shaped.

## What the paper says but this file does NOT formalise

- The full **NVP-vs-HPP tradeoff calculation** (which principle
  "wins" for each adjective class). The paper's discussion is informal
  prose; encoding it would require a decision procedure over coercion
  contexts. Out of scope here.
- The constitutive-material cases (stone lion, wooden horse,
  velveteen rabbit) — encoded as `LinguisticExample`s only.
- The retired-N gradient (retired professor vs retired CEO) — paper
  flags this as an open empirical question; encoded as examples only.

## Cited examples

Inline `LinguisticExample` values for paper exs. 10, 11, 13, 14, 15,
16, 17, 19, 21, 22 are generated from `Linglib/Data/Examples/Partee2010.json`
via `python3 scripts/gen_examples.py Partee2010` into the marker block
at the end of this file.
-/

namespace Partee2010

open Semantics.Gradability.Classification
open Semantics.Composition.Coercion

variable {W E : Type*}

/-! ### Substantive Partee 2010 claims (sorry-marked) -/

/-- **Partee 2010 § 4 (main claim).** Every Kamp-privative adjective
    admits an NVP-licensed coercion of any noun whose direct
    application yields a vacuous predicate.

    Paper § 4: the privative classification arises only because the
    noun's denotation is held fixed; under the Non-Vacuity Principle
    (`@cite{kamp-partee-1995}` formula 18), the noun coerces to a
    wider extension making `adj N*` non-vacuous within the local
    domain established by the Head Primacy Principle (formula 20).

    Proof open. -/
theorem privative_admits_licensed_coercion
    {adj : AdjMeaning W E} (_hp : isPrivative adj)
    (N : Property W E) (w : W) (_hne : ∃ x, adj N w x) :
    Nonempty (LicensedCoercion N adj w) := by
  -- TODO(NVP): construct shift := λ w' x => N w' x ∨ adj N w' x;
  --   ext_of: trivial Or.inl; satisfies_nvp:
  --   positive extension witnessed by hne; negative extension
  --   non-empty in HPPDomain shift w requires a "small-enough N"
  --   hypothesis or a global non-triviality assumption (paper's
  --   informal "outside its normal bounds" caveat).
  sorry

/-- **Bridge to @cite{kamp-1975}.** Partee 2010's reanalysis applied
    to Kamp's canonical privative witness `Kamp1975.fakeAdj`: even the
    paradigm "fake" adjective admits a licensed coercion. This is the
    formal counterpart to the prose claim "fake gun → fake-gun-allowing
    gun*". Proof reduces to the general claim via `fake_privative`. -/
theorem fakeAdj_coerces
    (N : Property Kamp1975.W2 Kamp1975.E3) (w : Kamp1975.W2)
    (hne : ∃ x, Kamp1975.fakeAdj N w x) :
    Nonempty (LicensedCoercion N Kamp1975.fakeAdj w) :=
  privative_admits_licensed_coercion Kamp1975.fake_privative N w hne

/-! ### Polish NP-splitting (paper § 3, @cite{nowak-2000})

Paper § 3 uses Polish NP-splitting (Nowak 2000) to argue against the
traditional 4-class hierarchy: the split diagnostic crosses the
privative/non-privative boundary, treating former privatives the same
as intersective and subsective adjectives, but rejecting modal
non-subsectives.

@cite{nowak-2000} reports a critical minimal pair on `biedny` 'poor':
the adjective splits in the intersective 'not rich' reading (ex. 15b)
but **not** in the non-subsective 'pitiful' reading (ex. 16a). This is
the key empirical observation that licenses the 3-class collapse: the
splitting diagnostic tracks the reading-level semantic class, not the
lexical form.

The 3-class enum `RevisedClass` in
`Theories/Semantics/Gradability/Classification.lean` encodes the
post-collapse hierarchy. Per @cite{partee-2010} footnote 1 the
hierarchy is subset-ordered, not linear: intersective ⊂ subsective ⊂
unrestricted.

The Polish judgments themselves live as `LinguisticExample` data
generated into the block below. -/

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/Partee2010.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
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

def all : List LinguisticExample := [ex_10a, ex_10b, ex_11a, ex_11b, ex_13b, ex_14b, biedny_ambiguity, ex_17b, ex_19b, ex_21b, ex_22b]

end Examples
-- END GENERATED EXAMPLES

end Partee2010
