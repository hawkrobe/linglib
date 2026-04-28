import Linglib.Typology.PolarityMarking
import Linglib.Fragments.Italian.PolarityMarking
import Linglib.Fragments.Spanish.PolarityMarking
import Linglib.Fragments.French.PolarityMarking

/-!
# Garassino & Jacob (2018) @cite{garassino-jacob-2018}

*Polarity focus and non-canonical syntax in Italian, French and Spanish:
Clitic left dislocation and sì che / sí que-constructions.*
In @cite{dimroth-sudhoff-2018}, pp. 227–254. DOI 10.1075/la.249.08gar.

This study file anchors three Fragment entries —
`Fragments.Italian.PolarityMarking.siChe`,
`Fragments.Spanish.PolarityMarking.siQue`, and
`Fragments.French.PolarityMarking.si` — to the chapter that compares them
as Romance polarity-focus (PF) realization strategies.

## Three substantive contributions of the chapter

1. **A typology of PF-marking strategies** in Italian, French and Spanish
   that carves the inventory differently from the
   `Features.InformationStructure.PolarityMarkingStrategy` enum: G&J split
   lexical means (adverbs, affirmative particles, embedded-clause
   structures) from syntactic means (non-focal fronting, cleft family,
   clitic dislocation, *sì che* / *sí que* clefts) — see §1 below for
   the typed constructors.

2. **A corpus result** (Table 1, p. 239) showing complementary distribution
   of polar left-dislocation and *sì che* / *sí que* across the three
   languages in *Direct Europarl*: Italian uses LDs (6 occurrences),
   Spanish uses *sí que* (61 occurrences); the two strategies are
   essentially non-overlapping — see §2 below.

3. **An explicit theoretical commitment to @cite{matic-nikolaeva-2018}'s
   "salient polarity" framework** (footnote 13, p. 236), against the form-
   class encoding that the substrate's `PolarityMarkingStrategy` records.
   See §4 below; the formal statement of the non-equivalence lives in
   `Phenomena/Polarity/Studies/MaticNikolaeva2018.lean`.

## Cross-references

- `Phenomena/Polarity/Studies/MaticNikolaeva2018.lean` — same volume,
  the framework G&J endorse against form-class encoding.
- `Phenomena/Polarity/Studies/TurcoBraunDimroth2014.lean` — earlier
  Germanic-vs-Romance production study G&J cite as their typological
  starting point (their footnote 5, p. 230); the
  `italian_spanish_cognates` theorem squatting at `TBD2014:446` was
  factually a G&J claim and has been relocated here as
  `siChe_siQue_cognates_at_encoding_level`.
- `Fragments/Italian/PolarityMarking.lean::siChe` — the entry whose
  docstring previously hosted G&J's corpus claim as prose; the claim
  now lives below as Lean data.
-/

namespace Phenomena.Polarity.Studies.GarassinoJacob2018

open Typology.PolarityMarking (PolarityMarkingEntry PolarityMarkingStrategy
  PolarityMarkingEnv)
open Fragments.Italian.PolarityMarking (siChe)
open Fragments.Spanish.PolarityMarking (siQue)
open Fragments.French.PolarityMarking (si)

/-! ## §1 G&J's PF-marking strategy taxonomy

G&J carve the Romance inventory into 8 strategies, organized as
*lexical* (§2.1: adverbs, particles, embedded clauses, elliptic
embedding) vs *syntactic* (§2.2: fronting, clefts, dislocation) plus
the *sì che* / *sí que* construction analyzed separately in §2.3.

This is **not the same carving** as `PolarityMarkingStrategy`. The
substrate enum collapses several of these into `.polarityReversal`,
following the Blühdorn/TBD2014 form-class tradition. G&J's taxonomy
is finer-grained and cuts on syntactic structure rather than discourse
function. Both encodings are kept; the divergence is the point. -/
inductive GJStrategy where
  /-- Lexical adverbs of truth/certainty/fact: It. *davvero*,
      Fr. *vraiment*, Sp. *de veras*, *de hecho* — @cite{garassino-jacob-2018}
      §2.1 ¶1, p. 230. -/
  | lexicalAdverb
  /-- Bare affirmative polarity particle: It. *sì*, Sp. *sí*, Fr. *bien*,
      Sp. *ya* — §2.1 ¶2, p. 230. -/
  | affirmativePolarityParticle
  /-- Embedded-clause structure with full matrix speech-act verb:
      It. *ti assicuro che*, Sp. *te digo que*, Fr. *je t'assure que* —
      §2.1 ¶3, p. 231 (examples 5–7). -/
  | embeddedClauseStructure
  /-- Elliptic embedding with adjective-only matrix: It. *certo che*,
      Sp. *claro que*, Fr. *bien sûr que* — §2.1 ¶4, p. 231 (examples 8–10). -/
  | ellipticEmbedding
  /-- Non-focal fronting (typical of Spanish, marginal in Italian):
      *Algo debe saber* — §2.2, p. 232 (examples 11–13). -/
  | nonFocalFronting
  /-- Cleft-family construction with stressed semantically-empty matrix
      verb: Fr. *c'est ce qu'elle fait* — §2.2, p. 233 (example 14). -/
  | faireCleft
  /-- Clitic dislocation (LD / RD) into a PF-supporting structure —
      §2.2 ¶ on dislocation, examples 15–16; §2.4, examples 21–22. -/
  | cliticDislocation
  /-- *Sì che* / *sí que* cleft-or-cleft-like construction — §2.3,
      examples 17–19. -/
  | siQueClass
  deriving DecidableEq, Repr

/-- A G&J taxonomy entry: paradigm form + which substrate strategy the
    Fragment file encodes for this entry (when one exists). -/
structure GJStrategyDatum where
  /-- The G&J strategy class. -/
  gjStrategy : GJStrategy
  /-- Representative Italian / French / Spanish example surface form. -/
  exampleForm : String
  /-- Whether this G&J strategy is *available* in Italian, French, Spanish
      per @cite{garassino-jacob-2018} §2 prose — ordered (it, fr, sp). -/
  availability : Bool × Bool × Bool

def davveroDatum : GJStrategyDatum where
  gjStrategy := .lexicalAdverb
  exampleForm := "davvero"
  availability := (true, true, true)

def siParticleDatum : GJStrategyDatum where
  gjStrategy := .affirmativePolarityParticle
  exampleForm := "sì / sí / bien"
  availability := (true, true, true)

def tiAssicuroDatum : GJStrategyDatum where
  gjStrategy := .embeddedClauseStructure
  exampleForm := "ti assicuro che"
  availability := (true, true, true)

def certoCheDatum : GJStrategyDatum where
  gjStrategy := .ellipticEmbedding
  exampleForm := "certo che / claro que / bien sûr que"
  availability := (true, true, true)

def algoDatum : GJStrategyDatum where
  gjStrategy := .nonFocalFronting
  exampleForm := "algo debe saber"
  -- Italian = true (marginally attested per G&J p. 232: "typical of Spanish,
  -- but is also (more rarely) attested in Italian and Catalan"). The
  -- Bool encoding records grammatical availability; rarity is a separate
  -- claim documented here in prose.
  availability := (true, false, true)

def faireDatum : GJStrategyDatum where
  gjStrategy := .faireCleft
  exampleForm := "c'est ce qu'elle fait"
  availability := (false, true, false)

def dislocationDatum : GJStrategyDatum where
  gjStrategy := .cliticDislocation
  exampleForm := "la soluzione gliela troviamo"
  availability := (true, true, true)

def siCheDatum : GJStrategyDatum where
  gjStrategy := .siQueClass
  exampleForm := "sì che / sí que"
  availability := (true, false, true)  -- Italian + Spanish, not French (fn 11)

def gjAllStrategies : List GJStrategyDatum :=
  [davveroDatum, siParticleDatum, tiAssicuroDatum, certoCheDatum,
   algoDatum, faireDatum, dislocationDatum, siCheDatum]

/-- The four lexical strategies (§2.1) are available in all three
    languages; the chapter's lexical-means inventory is genuinely
    pan-Romance. -/
theorem lexical_means_pan_romance :
    davveroDatum.availability = (true, true, true) ∧
    siParticleDatum.availability = (true, true, true) ∧
    tiAssicuroDatum.availability = (true, true, true) ∧
    certoCheDatum.availability = (true, true, true) := by decide

/-- The syntactic strategies (§2.2–2.3) split asymmetrically across the
    three languages, with each language licensing a different subset.
    This is the structural correlate of G&J's observation that
    "Spanish appears to be, so to speak, more Germanic than Romance"
    in PF marking (§4, p. 250). Non-focal fronting is *marginally*
    attested in Italian per G&J p. 232 — encoded as available
    (Bool collapses primary vs marginal). -/
theorem syntactic_strategies_split_asymmetrically :
    algoDatum.availability = (true, false, true) ∧  -- It marginal, Sp typical, Fr none
    faireDatum.availability = (false, true, false) ∧  -- French faire-clefts
    siCheDatum.availability = (true, false, true) := by decide  -- It + Sp, not Fr

/-- French does **not** license the *sì che* / *sí que* class — G&J fn 11
    (p. 234): "French *si*, unlike the corresponding forms in Spanish and
    Italian, is limited to dialogical contexts." -/
theorem french_lacks_siQueClass :
    siCheDatum.availability.2.1 = false := rfl

/-! ## §2 Corpus result (Table 1, p. 239)

Distribution of polar CDs (clitic left-dislocations with PF reading) and
*sì che* / *sí que* constructions in *Direct Europarl*. Italian sample
2.3M words, French 2.5M, Spanish 2.8M. Verified from the PDF. -/

/-- One row of @cite{garassino-jacob-2018} Table 1. `siQueCount = none`
    encodes the chapter's "NA" entry for French. -/
structure GJCorpusDatum where
  language : String  -- "Italian", "French", "Spanish"
  corpusSizeMillionWords : String  -- "2.3", "2.5", "2.8" — kept as label
  polarLDCount : Nat
  siQueCount : Option Nat
  deriving DecidableEq, Repr

def italianRow : GJCorpusDatum where
  language := "Italian"
  corpusSizeMillionWords := "2.3"
  polarLDCount := 6
  siQueCount := some 0

def frenchRow : GJCorpusDatum where
  language := "French"
  corpusSizeMillionWords := "2.5"
  polarLDCount := 4
  siQueCount := none  -- NA per Table 1

def spanishRow : GJCorpusDatum where
  language := "Spanish"
  corpusSizeMillionWords := "2.8"
  polarLDCount := 0
  siQueCount := some 61

def gjTable1 : List GJCorpusDatum := [italianRow, frenchRow, spanishRow]

/-- The central corpus claim of @cite{garassino-jacob-2018} (§3 Conclusions,
    p. 250): Italian and Spanish exhibit **complementary distribution** for
    the two PF-marking strategies — Italian uses LDs (6 / 0), Spanish uses
    *sí que* (0 / 61). -/
theorem italian_spanish_complementary_distribution :
    italianRow.polarLDCount > 0 ∧ italianRow.siQueCount = some 0 ∧
    spanishRow.polarLDCount = 0 ∧ spanishRow.siQueCount = some 61 := by
  refine ⟨?_, rfl, rfl, rfl⟩
  decide

-- Italian *sì che* zero-count is one conjunct of the theorem above;
-- G&J p. 239 attribute the gap to register effects ("Italian *sì che*
-- structures are perceived by native speakers as more typical of the
-- spoken language or generally of more informal registers").

/-! ## §3 Cognacy at the substrate-encoding level

@cite{garassino-jacob-2018} §2.3 (p. 234) and the broader Romance
literature (@cite{bernini-1995}, @cite{batllori-hernanz-2013},
@cite{poletto-zanuttini-2013}) treat *sì che* and *sí que* as cognate
constructions: an affirmative-polarity particle followed by a
complementizer introducing an embedded clause carrying the asserted
proposition.

The substrate-level cognacy theorem below records that the two Fragment
entries agree on every substrate field. **Crucially, this is cognacy at
the encoding level only.** §2's corpus theorem above shows the two
constructions diverge in actual usage frequency: Spanish *sí que*
appears 61× in Direct Europarl, Italian *sì che* zero times. Both
"the constructions are formally cognate" and "they are pragmatically
divergent" can hold, and G&J's chapter is precisely the documentation
that they do.

(Relocated from `TurcoBraunDimroth2014.lean:446`; the cognacy claim
chronologically anchors on Bernini 1995 / Batllori-Hernanz 2013 /
G&J 2018, not TBD 2014.) -/
theorem siChe_siQue_cognates_at_encoding_level :
    siChe.strategy = siQue.strategy ∧
    siChe.environments = siQue.environments := ⟨rfl, rfl⟩

/-! ## §4 G&J's framework position (footnote 13, p. 236)

G&J explicitly endorse @cite{matic-nikolaeva-2018}'s rejection of the
form-class encoding of polarity focus. Footnote 13 reads, verbatim:

> This view is similar to the one presented by Matić & Nikolaeva (this
> volume), according to whom PF (or salient polarity as they prefer to
> name this specific type of emphasis) is not directly encoded by certain
> linguistic forms in a given language but can be pragmatically conveyed
> by different structures under appropriate (contextual) conditions.

This is in tension with the substrate's `PolarityMarkingStrategy` enum,
which assigns each entry a single `.polarityReversal` / `.particle` /
`.verumFocus` strategy class as if it were a fixed form-meaning property.
The contradiction is recorded at the substrate's def-site
(`Features/InformationStructure.lean::PolarityMarkingStrategy` docstring)
and formalized in `Phenomena/Polarity/Studies/MaticNikolaeva2018.lean`. -/

/-! ## §5 Surface-class lumping caveat (footnote 11, p. 234)

G&J fn 11 distinguishes French *si* from the *sì che* / *sí que* class:

> Si exists in French as an affirmative particle expressing positive
> polarity in a contrastive way; … However, French *si*, unlike the
> corresponding forms in Spanish and Italian, is limited to dialogical
> contexts, where it is used to answer a preceding opposite turn.

So the cross-linguistic lumping under `PolarityMarkingStrategy.polarityReversal`
of French *si*, Italian *sì*, and Spanish *sí* records a shared functional
role only — the surface category differs (French = response particle,
Italian + Spanish = clause-initial cleft-like construction). The substrate
flag in `PolarityMarkingStrategy` docstring records this caveat. The
`french_lacks_siQueClass` theorem in §1 above proves the corresponding
data-level claim. -/

end Phenomena.Polarity.Studies.GarassinoJacob2018
