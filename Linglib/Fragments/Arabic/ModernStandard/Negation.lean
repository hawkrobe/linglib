import Linglib.Typology.Negation

/-!
# Modern Standard Arabic Negation
@cite{ryding-2005} @cite{benmamoun-2000}

The MSA standard-negation system per @cite{ryding-2005} ch 37
(pp. 641–656) and @cite{benmamoun-2000} ch 6 (pp. 94–109).

## The five-marker inventory

- *laa* لا — co-occurs with imperfective verbs (default present-tense
  reading; Ryding §37.2.1.2). Also: stand-alone "no" (§37.2.1.1);
  negative imperative with jussive (§37.2.1.5); reduplicated for
  "neither…nor"; constituent negation as in *laa rajul-a fii d-daar-i*
  'no man in the house' (Benmamoun §6.1.1, ex. 6, citing Moutaouakil
  1993). The constituent-negation use is unavailable to *lam* and
  *lan* — see Benmamoun §6.1.1 ex. 6b–c.
- *lam* لمْ — co-occurs with past-tense reference; the verb appears
  in the jussive (Ryding §37.2.2; pattern documented at §35.1).
- *lan* لنْ — co-occurs with future-tense reference; the verb
  appears in the subjunctive (Ryding §37.2.3 / §35.2).
- *maa* ما — focal / literary past negation (Ryding §37.2.4;
  Benmamoun §6.4).
- *lays-a* ليس — inflecting verb 'not be'; sister of *kaan-a*; takes
  its complement in the accusative (Ryding §37.1, p. 641). Carries
  full person / number / gender agreement (paradigm at Benmamoun
  §6.3, ex. 25, p. 102): *las-tu* 1SG, *las-ta* 2SG.M, *las-ti* 2SG.F,
  *lays-a* 3SG.M, *lays-at* 3SG.F, *las-tumaa* 2DU, *lays-aa* 3DU.M,
  *lays-ataa* 3DU.F, *las-naa* 1PL, *las-tum* 2PL.M, *las-tunna* 2PL.F,
  *lays-uu* 3PL.M, *las-na* 3PL.F. Restricted to present-tense
  interpretation; cannot co-occur with future or past-inflected verbs
  (Benmamoun §6.3.3, p. 105, citing Fassi Fehri 1993:208 n25).

## Empirical distributional patterns

These are descriptive patterns documented in @cite{benmamoun-2000}
ch 6 (the analytic apparatus — NegP, head movement, feature checking
— is not adopted by this Fragment file):

- **Complementary distribution of tense exponence**: when the negative
  inflects for tense (*lam*, *lan*), the verb cannot also inflect for
  tense (Benmamoun §6.1.2, ex. 7–8): \**ṭ-ṭullaab-u lam ðahab-uu*
  (both tense-marked) is ill-formed.
- **Negative–verb adjacency**: no subject or adverb may intervene
  between *lam* / *lan* and the verb they negate (Benmamoun §6.1.3,
  ex. 12, citing Hassan 1973, Fassi Fehri 1993:164, Moutaouakil
  1993:83, Shlonsky 1997:103).
- **Verbless-sentence restriction**: *laa* / *lam* / *lan* cannot
  occur in verbless (equational) sentences. Negating a past or future
  copular sentence requires inserting *kaan-a* (Benmamoun §6.1.3
  ex. 13–14, citing Fassi Fehri 1993:164 and Moutaouakil 1993:82–88).
- **lays-a's distinctive properties**: unlike the other particles,
  *lays-a* (a) is mobile (can be separated from the predicate by the
  subject), (b) carries agreement, (c) appears in verbless sentences
  with present-tense interpretation (Benmamoun §6.3, p. 102–104).

## Asymmetry

Standard MSA negation has **both symmetric and asymmetric**
constructions (the WALS Ch 113 `.both` value). Symmetric branch:
*laa* + present-tense indicative; *maa* + past-tense indicative.
Asymmetric branch:

- *lam* → jussive, *lan* → subjunctive (Ryding §35.1, §35.2): the
  choice of negative marker conditions a paradigm-internal mood shift
  on an otherwise finite verb (Miestamo's A/Cat — TAM-marking change).
- *lays-a* introduces a finite copular verb where the affirmative
  would be verbless (Ryding §37.1.2 p. 642): the negation introduces
  finiteness where the affirmative has none (Miestamo's A/Fin —
  finiteness change), parallel to Mandarin *méi(yǒu)* in
  @cite{miestamo-2005} pp. 90–91.

Combined, this places MSA in the WALS Ch 113 `.both` cell with the
WALS Ch 114 `.finAndCat` subtype.

**Note on source basis.** MSA (`arb`) is **not in** @cite{miestamo-2005}'s
297-language sample (verified against the index of languages, pp. 470–476)
and **not in** the WALS Ch 113A/114A datasets (which only carry the `aeg`
row for `arz` Egyptian Arabic — classified there as `.symmetric` /
`.nonAssignable`, since Egyptian *ma-…-š* doesn't trigger the mood shifts
MSA's *lam*/*lan* do). The values populated below are therefore a
project-internal extrapolation applying Miestamo's framework to the MSA
data Ryding §37 + Benmamoun ch 6 describe; they should not be cited as
Miestamo's own classification of MSA.

## Out of scope

- N-word / NPI behaviour of *ʾaḥad-un* 'anyone' under negation —
  belongs in `Fragments/Arabic/ModernStandard/PolarityItems.lean` if
  added later.
- Exceptive *ʾillaa*, focal negation, constituent negation beyond the
  *laa rajul-a* pattern noted above — Ryding §37.3 covers these but
  they are not part of WALS Ch 112's "standard sentential negation"
  target.
- The dialectal *ma…š* bipartite negation of Egyptian / Moroccan
  Arabic (Benmamoun ch 5) — belongs in
  `Fragments/Arabic/Egyptian/Negation.lean` if added later.
-/

namespace Arabic.ModernStandard.Negation

open Typology.Negation

/-- The five-marker inventory: *laa* (general / present), *lam* (past),
    *lan* (future), *maa* (focal/literary past), *lays-a* (copular).
    All four particles precede the verb; *lays-a* is itself a verb
    inflecting for person/number/gender. Per Ryding ch 37. -/
def negMarkers : List NegMarkerEntry :=
  [ { form := "laa"
    , gloss := "NEG.IPFV"
    , morphemeType := .particle
    , position := .preverbal }
  , { form := "lam"
    , gloss := "NEG.PST"
    , morphemeType := .particle
    , position := .preverbal }
  , { form := "lan"
    , gloss := "NEG.FUT"
    , morphemeType := .particle
    , position := .preverbal }
  , { form := "maa"
    , gloss := "NEG.PST"
    , morphemeType := .particle
    , position := .preverbal }
  , { form := "lays-a"
    , gloss := "NEG.COP"
    , morphemeType := .auxVerb
    , position := .preverbal }
  ]

/-- Bundled `NegationSystem` (markers + WALS Ch 112A/143A/144A
    datapoints pulled from `Data.WALS` by ISO code `arb`). -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "arb" negMarkers

/-- WALS-typology bundle. The marker classification at `morphemeType`
    privileges the *laa* / *lam* / *lan* / *maa* particles (the
    productive sentential negators on finite verbs) over the verbal
    *lays-a*; the asymmetry comes from the tense/mood-conditioned
    alternation. Per Ryding §37 + Benmamoun ch 6 + the Miestamo
    construction-typology framing in
    `Studies/Miestamo2005.lean`. -/
def negationProfile : NegationProfile :=
  { language := "Arabic (Modern Standard)"
  , iso := "arb"
  , morphemeType := .particle
  , symmetry := .both
  , asymmetrySubtype := .finAndCat
  , negIndefinite := none
  , negMarkers := ["laa", "lam", "lan", "maa", "lays-a"]
  , negIsHead := none
  , enAttested := none }

end Arabic.ModernStandard.Negation
