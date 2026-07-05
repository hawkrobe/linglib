import Linglib.Syntax.Minimalist.LeftPeriphery
import Linglib.Features.QParticleLayer
import Linglib.Fragments.HindiUrdu.Particles
import Linglib.Fragments.Japanese.Particles
import Linglib.Fragments.English.QuestionParticles

/-!
# Dayal (2025): Three-layer cartography for clause-typing
[dayal-2025] [mccloskey-2006] [zu-2018]
[bhatt-dayal-2020]

Veneeta Dayal (2025), *Linguistic Inquiry* 56(4):663–712, develops the
three-layer split `[SAP [PerspP [CP ...]]]` of the interrogative left
periphery and derives cross-linguistic clause-typing variation, the
responsive/rogative split, and McCloskey-style quasi-subordination from it.

## Main declarations

* `ClauseTyping`: the two orthogonal clause-typing parameters (§§4.3–4.4),
  polar wh-complementizer and delayed typing.
* `simplex_subordination_matches_complementizer`,
  `neutral_decl_matches_delay`: the per-parameter typological projections
  over the English/Italian/Hindi-Urdu sample.
* `cross_linguistic_shiftiness_predicted`: Hindi-Urdu *kya:* shiftiness
  (§3.2) derived by the same `allowsQuasiSub` account as McCloskey's
  English data.
* `theory_predicts_embedding`: the `SelectionClass` apparatus checked
  against the §1.2 English embedding judgments.
* `layerOf`, `layers_derived`, `particle_layer_predicts_embedding`: the
  CP / PerspP / SAP particle classifier (§1.3), read off embedding
  distribution.

## Implementation notes

Rival analyses of the same facts: Rizzi-style `Force⁰[+Q]` typing lives in
`Syntax/Minimalist/Questions.lean`, Holmberg's `PolP` locus in
`Studies/Holmberg2016.lean`, and the Speas–Tenny seat-of-knowledge matrix
in `Studies/SpeasTenny2003.lean`. Both Dayal and Speas–Tenny predict the
Newari conjunct/disjunct flip (§5.2, via [zu-2018]), which the paper reads
as matrix perspective shift only, leaving open whether PerspP is Zu's
SentienceP.
-/

namespace Dayal2025

open Minimalist.LeftPeriphery
open Features (QParticleLayer)
open HindiUrdu.Particles (kya)
open Japanese.Particles (ka kke)
open English.QuestionParticles (quick)

/-! ### Clause-typing typology

Two orthogonal parameters govern polar-question syntax. Whether the
language has a dedicated wh-complementizer for polar questions (English
*whether*, Italian *se*; Hindi-Urdu has none) governs simplex-polar
subordination (§4.4, ex. 70–71). Whether clause-typing may be delayed past
C to PerspP (Italian and Hindi-Urdu, ex. 66) or is forced at the earliest
opportunity (English) governs whether a rising declarative can be a
neutral question (§4.3, ex. 63b). English and Italian share the first
parameter but differ on the second, so the two must not be collapsed. -/

/-- A language's clause-typing profile for polar questions. -/
structure ClauseTyping where
  /-- Has a dedicated polar wh-complementizer (English *whether*,
  Italian *se*). -/
  hasPolarComplementizer : Bool
  /-- Clause-typing may be delayed past C to PerspP; forced-early languages
  type at C immediately. -/
  delayedTyping : Bool
  deriving DecidableEq, Repr

/-- Per-language polar-question syntax: simplex-polar distribution and
neutral rising declaratives. A simplex polar is the nucleus alone
(*p?* rather than *p or not (p)?*). -/
structure PolarSyntaxDatum where
  language : String
  typing : ClauseTyping
  /-- Simplex polar in matrix position? -/
  matrixOk : Bool
  /-- Simplex polar in quasi-subordination? -/
  quasiSubOk : Bool
  /-- Simplex polar in subordination? -/
  subordinationOk : Bool
  /-- Can a rising declarative be a neutral (unbiased) question? -/
  neutralDeclOk : Bool
  deriving DecidableEq, Repr

def english_polar : PolarSyntaxDatum :=
  { language := "English"
  , typing := { hasPolarComplementizer := true, delayedTyping := false }
  , matrixOk := true, quasiSubOk := true, subordinationOk := true
  , neutralDeclOk := false }

def italian_polar : PolarSyntaxDatum :=
  { language := "Italian"
  , typing := { hasPolarComplementizer := true, delayedTyping := true }
  , matrixOk := true, quasiSubOk := true, subordinationOk := true
  , neutralDeclOk := true }

/-- Hindi-Urdu: no wh-complementizer, so simplex polars cannot be
subordinated (ex. 70–71); typing is delayed, so rising declaratives can be
neutral. -/
def hindi_urdu_polar : PolarSyntaxDatum :=
  { language := "Hindi-Urdu"
  , typing := { hasPolarComplementizer := false, delayedTyping := true }
  , matrixOk := true, quasiSubOk := true, subordinationOk := false
  , neutralDeclOk := true }

def allPolarSyntaxData : List PolarSyntaxDatum :=
  [english_polar, italian_polar, hindi_urdu_polar]

/-- Simplex-polar subordination tracks the complementizer parameter. -/
theorem simplex_subordination_matches_complementizer :
    ∀ d ∈ allPolarSyntaxData,
      d.subordinationOk = d.typing.hasPolarComplementizer := by decide

/-- Neutral rising declaratives track the delayed-typing parameter: forced
early typing leaves only the biased reading (English); delayable typing
admits the neutral question (Italian, Hindi-Urdu). -/
theorem neutral_decl_matches_delay :
    ∀ d ∈ allPolarSyntaxData,
      d.neutralDeclOk = d.typing.delayedTyping := by decide

/-! ### Hindi-Urdu shiftiness (§3.2, ex. 39–41)

Hindi-Urdu *kya:* under attitude predicates patterns with McCloskey's
English embedded inversion: blocked under a bare responsive, licensed
under negation or questioning. -/

/-- Cross-linguistic shiftiness data. -/
structure CrossLingShiftinessDatum where
  language : String
  verb : String
  sentence : String
  negated : Bool
  questioned : Bool
  quasiSubOk : Bool
  deriving DecidableEq, Repr

/-- Hindi-Urdu: "want to know" (rogative) freely takes *kya:* (ex. 39a). -/
def hindi_urdu_want_to_know : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: ca:h-na: (want to know)"
  , sentence := "anu ja:nna: ca:hti: hai [ki (kya:) tum cai piyoge↑]"
  , negated := false, questioned := false, quasiSubOk := true }

/-- Hindi-Urdu: bare "know" (responsive) rejects *kya:* (ex. 39b). -/
def hindi_urdu_know_bare : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: (know)"
  , sentence := "*anu ja:nti: hai [ki (kya:) tum cai piyoge↑]"
  , negated := false, questioned := false, quasiSubOk := false }

/-- Hindi-Urdu: "nobody knows" + *kya:* → OK (negation, ex. 41a). -/
def hindi_urdu_know_negated : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: (know)"
  , sentence := "koii nahii jaanta [ki kya: TiTo sTa:lin-se mile the↑]"
  , negated := true, questioned := false, quasiSubOk := true }

/-- Hindi-Urdu: "does anyone know" + *kya:* → OK (questioning, ex. 41b). -/
def hindi_urdu_know_questioned : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: (know)"
  , sentence := "kisii-ko bhi maalum hai [ki (kya:) TiTo sTa:lin-se mile the↑]"
  , negated := false, questioned := true, quasiSubOk := true }

def allCrossLingShiftinessData : List CrossLingShiftinessDatum :=
  [hindi_urdu_want_to_know, hindi_urdu_know_bare,
   hindi_urdu_know_negated, hindi_urdu_know_questioned]

/-- English: bare responsive *remember* rejects embedded inversion
([mccloskey-2006]). -/
def remember_bare : CrossLingShiftinessDatum :=
  { language := "English", verb := "remember"
  , sentence := "*I remember [was Henry a communist↑]"
  , negated := false, questioned := false, quasiSubOk := false }

/-- English: negated *remember* licenses embedded inversion — McCloskey's
judgment is marginal ("?"), encoded here as licensed. -/
def remember_negated : CrossLingShiftinessDatum :=
  { language := "English", verb := "remember"
  , sentence := "?I don't remember [was Henry a communist↑]"
  , negated := true, questioned := false, quasiSubOk := true }

/-- English: questioned *remember* licenses embedded inversion
([mccloskey-2006]). -/
def remember_questioned : CrossLingShiftinessDatum :=
  { language := "English", verb := "remember"
  , sentence := "Does Sue remember [was Henry a communist↑]"
  , negated := false, questioned := true, quasiSubOk := true }

/-! ### Verification against empirical embedding data

The `SelectionClass` apparatus checked against the paper's §1.2
classification of English attitude predicates: rogatives split three ways
by the largest structure they take (CP / PerspP / SAP); responsives and
uninterrogatives take none of the larger structures. -/

/-- Embedding judgment for an English attitude predicate (§1.2). -/
structure EmbeddingDatum where
  verb : String
  /-- "V whether/who..." -/
  subordination : Bool
  /-- "V [did S leave↑]" (embedded inversion + matrix intonation) -/
  quasiSubordination : Bool
  /-- 'V, "Did S leave?"' -/
  quotation : Bool
  deriving DecidableEq, Repr

-- Rogative predicates (embed only interrogatives)

def investigate_d : EmbeddingDatum :=
  { verb := "investigate"
  , subordination := true, quasiSubordination := false, quotation := false }

def depend_on_d : EmbeddingDatum :=
  { verb := "depend on"
  , subordination := true, quasiSubordination := false, quotation := false }

def wonder_d : EmbeddingDatum :=
  { verb := "wonder"
  , subordination := true, quasiSubordination := true, quotation := false }

def ask_d : EmbeddingDatum :=
  { verb := "ask"
  , subordination := true, quasiSubordination := true, quotation := true }

-- Responsive predicates (embed both declaratives and interrogatives)

def know_d : EmbeddingDatum :=
  { verb := "know"
  , subordination := true, quasiSubordination := false, quotation := false }

/-- Predicate of Relevance: responsive but resists question-to-proposition
reduction ([elliott-etal-2017]). The reduction-resistance is a separate
property — see `Elliott2017`. -/
def care_d : EmbeddingDatum :=
  { verb := "care"
  , subordination := true, quasiSubordination := false, quotation := false }

/-- Predicate of Relevance ([elliott-etal-2017]). -/
def matter_d : EmbeddingDatum :=
  { verb := "matter"
  , subordination := true, quasiSubordination := false, quotation := false }

-- Uninterrogative predicates (declaratives only)

def believe_d : EmbeddingDatum :=
  { verb := "believe"
  , subordination := false, quasiSubordination := false, quotation := false }

def allEmbeddingData : List EmbeddingDatum :=
  [investigate_d, depend_on_d, wonder_d, ask_d, know_d, care_d, matter_d, believe_d]

/-- Quasi-subordination implies subordination: the §1.2 classification is
cumulative — each larger-structure class also takes the smaller ones. -/
theorem quasi_sub_implies_sub :
    ∀ d ∈ allEmbeddingData,
      d.quasiSubordination = true → d.subordination = true := by decide

/-- Quotation implies quasi-subordination among the interrogative-selecting
predicates sampled here (per §1.2; *say* takes interrogative quotations
without quasi-subordinating, but is not interrogative-selecting). -/
theorem quotation_implies_quasi_sub :
    ∀ d ∈ allEmbeddingData,
      d.quotation = true → d.quasiSubordination = true := by decide

/-- The substrate classifier extended with [elliott-etal-2017]'s predicates
of relevance (*care*, *matter*), which classify as responsive. -/
def classify : String → SelectionClass
  | "care"   => .responsive
  | "matter" => .responsive
  | v        => classifyVerb v

/-- The theory correctly predicts all embedding judgments from the data. -/
theorem theory_predicts_embedding :
    ∀ d ∈ allEmbeddingData,
      allowsEmbedding (classify d.verb) .subordination false false
        = d.subordination ∧
      allowsEmbedding (classify d.verb) .quasiSubordination false false
        = d.quasiSubordination ∧
      allowsEmbedding (classify d.verb) .quotation false false
        = d.quotation := by decide

/-- Shiftiness predictions match McCloskey's data for *remember*
(responsive). -/
theorem shiftiness_predicted :
    allowsQuasiSub .responsive remember_bare.negated remember_bare.questioned
      = remember_bare.quasiSubOk ∧
    allowsQuasiSub .responsive remember_negated.negated remember_negated.questioned
      = remember_negated.quasiSubOk ∧
    allowsQuasiSub .responsive remember_questioned.negated remember_questioned.questioned
      = remember_questioned.quasiSubOk := by decide

/-! ### Cross-linguistic predictions -/

/-- Hindi-Urdu shiftiness follows the same derivation as English:
responsive predicates reject quasi-sub in bare form, allow it under
negation/questioning. -/
theorem cross_linguistic_shiftiness_predicted :
    ∀ d ∈ allCrossLingShiftinessData,
      allowsQuasiSub (classifyCrossLingVerb d.verb) d.negated d.questioned
        = d.quasiSubOk := by decide

/-! ### The three-layer classifier for question particles

The cartography's defining correlation as a classifier: a question
particle's left-peripheral layer is read off its embedding distribution —
subordinated-licensed → CP (clause-typing); subordinated-excluded but
quasi-subordinated-licensed → PerspP; quasi-subordinated-excluded but
matrix-licensed → SAP (§1.3). [bhatt-dayal-2020]'s ForceP location for
Hindi-Urdu *kya:* is recast here as PerspP (a terminological change by the
paper's own fn. 3).

| Layer  | Language    | Particle    | Distribution         |
|--------|-------------|-------------|----------------------|
| CP     | Japanese    | *ka*        | matrix + subord + QS |
| PerspP | Hindi-Urdu  | *kya:*      | matrix + QS, no sub  |
| SAP    | Japanese    | *kke*       | matrix + quotation   |
| SAP    | English     | *quick(ly)* | matrix + quotation   |
-/

/-- A question particle's layer, read off its embedding distribution.
    Defined for question particles only — Japanese *koto* (a declarative
    complementizer, the *ka* contrast of ex. 15) is outside the intended
    domain. -/
def layerOf (p : Particle) : Option QParticleLayer :=
  if p.LicensedInEmbed .subordinated then some .cp
  else if p.LicensedInEmbed .quasiSubordinated then some .perspP
  else if p.LicensedInEmbed .matrix then some .sap
  else none

/-- The classifier's intended domain: the question particles this study
    classifies. Membership is a claim about what the particle *does*
    (question-forming), not about its distribution. -/
def qParticles : List Particle := [ka, kya, kke, quick]

/-- The four representative layer assignments, derived from the fragments'
    embedding facets: *ka* CP, *kya:* PerspP (recasting
    [bhatt-dayal-2020]'s ForceP), *kke* SAP ([sauerland-yatsushiro-2017]),
    *quick* SAP (ex. 18–19). -/
theorem layers_derived :
    layerOf ka = some .cp ∧
    layerOf kya = some .perspP ∧
    layerOf kke = some .sap ∧
    layerOf quick = some .sap := by decide

/-- Every particle in the classifier's domain receives a layer. -/
theorem qParticles_layered : ∀ p ∈ qParticles, (layerOf p).isSome := by decide

/-- Q-particle embedding follows from which left-peripheral layer they occupy:
    CP-layer particles are licensed in subordination, PerspP- and SAP-layer
    particles are not, and SAP-layer particles are excluded even from
    quasi-subordination. Stated over `layerOf`, which derives the layer from
    the embedding facet, so this is the kernel-checked converse guarantee for
    the study's particle sample. -/
theorem particle_layer_predicts_embedding :
    ∀ p ∈ qParticles,
      (layerOf p = some .cp → p.LicensedInEmbed .subordinated) ∧
      (layerOf p = some .perspP → ¬ p.LicensedInEmbed .subordinated) ∧
      (layerOf p = some .sap → ¬ p.LicensedInEmbed .quasiSubordinated) := by
  decide

end Dayal2025
