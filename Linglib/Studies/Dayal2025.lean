import Linglib.Syntax.Minimalist.LeftPeriphery
import Linglib.Features.QParticleLayer
import Linglib.Fragments.HindiUrdu.Particles
import Linglib.Fragments.Japanese.Particles
import Linglib.Fragments.English.QuestionParticles

/-!
# Dayal (2025): Three-layer cartography for clause-typing
[dayal-2025] [mccloskey-2006] [zu-2018]
[bhatt-dayal-2020]

Veneeta Dayal (2025), *Linguistic Inquiry* 56(4):663-712. Develops the
three-layer cartographic split `[SAP [PerspP [CP ...]]]` and uses it to
account for cross-linguistic clause-typing variation, the responsive/
rogative split, and McCloskey-style quasi-subordination.

This study file is the canonical home for:

1. **Clause-typing typology** (§4.4): forced-CP vs delayed-PerspP variation
   across English/Italian/Hindi-Urdu.
2. **Hindi-Urdu shiftiness** (§3.2): the McCloskey parallel for Hindi-Urdu
   *jaanna:*.
3. **Newari conjunct/disjunct** (§5.2): the perspective-shift evidence
   from Newari person marking.
4. **Left-Periphery bridge**: the verification of the LeftPeriphery
   `SelectionClass` apparatus against the English embedding data (§5)
   and the cross-linguistic shiftiness data.

## Cross-framework relations

- **Rizzi 1997 / `Syntax/Minimalist/Questions.lean`** places
  clause-typing at `Force⁰[+Q]`; Dayal places it at `C` with a downstream
  `PerspP` shift. The disagreement is real and not currently formalized as
  a bridge theorem. See `Syntax/Minimalist/Questions.lean`.
- **Holmberg 2016 / `Studies/Holmberg2016.lean`**
  places the polar-Q-typing locus at `PolP` (via the
  `Features/AnsweringSystem.lean` typological parameter). Holmberg's
  analysis competes with Dayal's for the same matrix-polar facts.
- **Speas-Tenny / `Studies/SpeasTenny2003.lean`** derives
  `SpeasTenny2003.seatOfKnowledge` from a 2×2 feature matrix; Dayal places SoK
  in PerspP with PRO. Both predict the Newari conjunct/disjunct flip; the bridge
  theorem `SpeasTenny2003.seatOfKnowledge ↔ PerspP-PRO over Newari` is
  unformalized.
-/

namespace Dayal2025

open Minimalist.LeftPeriphery
open Features (QParticleLayer)
open HindiUrdu.Particles (kya)
open Japanese.Particles (ka kke)
open English.QuestionParticles (quick)

-- ============================================================================
-- §1. Clause-typing typology (Dayal 2025 §4.4)
-- ============================================================================

/-- How a language handles clause-typing for polar questions. The contrast
    is the cartographic locus of `[+Q]`-typing, not a difference in feature
    inventory. CP-typed languages license simplex polars in subordination
    via a wh-complementizer (English `whether`, Italian `se`); PerspP-typed
    languages route polar questions through a higher PerspP layer that does
    not embed under canonical responsive predicates. -/
inductive ClauseTypingStrategy where
  /-- Clause-typing locus is `C` (English `whether`, Italian `se`). -/
  | cpTyped
  /-- Clause-typing locus is `PerspP` (Hindi-Urdu rising intonation). -/
  | perspPTyped
  deriving DecidableEq, Repr

/-- Structural projection: which clause-typing strategies license simplex
    polar questions in subordination. CP-typed languages do (the wh-
    complementizer is the embedding selector); PerspP-typed languages do
    not (PerspP is too high to be selected by canonical responsive verbs).
    `delayed_blocks_simplex_subordination` below derives from this
    projection together with the Fragment data, rather than holding
    vacuously over a 1-element sample. -/
def ClauseTypingStrategy.licensesSimplexSubordination :
    ClauseTypingStrategy → Bool
  | .cpTyped     => true
  | .perspPTyped => false

/-- Data on simplex polar question embedding across languages.
    A simplex polar question is just the nucleus *p* (no "or not"). -/
structure SimplexPolarDatum where
  language : String
  clauseTyping : ClauseTypingStrategy
  /-- Simplex polar in matrix? -/
  matrixOk : Bool
  /-- Simplex polar in quasi-subordination? -/
  quasiSubOk : Bool
  /-- Simplex polar in subordination? -/
  subordinationOk : Bool
  deriving Repr

def english_simplex : SimplexPolarDatum :=
  { language := "English", clauseTyping := .cpTyped
  , matrixOk := true, quasiSubOk := true, subordinationOk := true }

def italian_simplex : SimplexPolarDatum :=
  { language := "Italian", clauseTyping := .cpTyped
  , matrixOk := true, quasiSubOk := true, subordinationOk := true }

/-- Hindi-Urdu: simplex polar questions require PerspP (rising intonation
    activates [+WH] at PerspP level). No wh-complementizer → cannot
    clause-type at C. (Dayal 2025: ex (70)–(71); UNVERIFIED page numbers.) -/
def hindi_urdu_simplex : SimplexPolarDatum :=
  { language := "Hindi-Urdu", clauseTyping := .perspPTyped
  , matrixOk := true, quasiSubOk := true, subordinationOk := false }

def allSimplexPolarData : List SimplexPolarDatum :=
  [english_simplex, italian_simplex, hindi_urdu_simplex]

/-- The Fragment data is consistent with the structural projection: every
    PerspP-typed language in the sample lacks simplex-polar subordination.
    Unlike a 1-direction stipulation, this connects per-language data to a
    typed projection on `ClauseTypingStrategy`. -/
theorem simplex_subordination_matches_projection :
    ∀ d ∈ allSimplexPolarData,
      d.subordinationOk = d.clauseTyping.licensesSimplexSubordination := by
  intro d hd
  simp only [allSimplexPolarData, List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> rfl

/-- Corollary: PerspP-typed languages cannot subordinate simplex polars.
    Now derived from the structural projection, not from the data alone. -/
theorem perspPTyped_blocks_simplex_subordination :
    ∀ d ∈ allSimplexPolarData,
      d.clauseTyping = .perspPTyped → d.subordinationOk = false := by
  intro d hd hp
  rw [simplex_subordination_matches_projection d hd, hp]
  rfl

-- ============================================================================
-- §2. Declarative questions and bias (Dayal 2025 §4.3)
-- ============================================================================

/-- Whether declarative questions in a language are obligatorily biased.
    English: "You drink wine?" is obligatorily biased (speaker expects yes).
    Hindi-Urdu/Italian: rising declaratives can be neutral.
    This follows from whether clause-typing is forced at C (CP-typed) or
    routed through PerspP. (Italian `neutralOk := true` is contested in
    the rising-declarative literature, e.g. Gunlogson 2003 vs Bartels 1999;
    Dayal 2025 makes the specific claim — UNVERIFIED page numbers.) -/
structure DeclarativeQuestionDatum where
  language : String
  /-- Can a rising declarative be a neutral (unbiased) question? -/
  neutralOk : Bool
  /-- Is a rising declarative always biased? -/
  obligatorilyBiased : Bool
  clauseTyping : ClauseTypingStrategy
  deriving Repr

def english_decl_q : DeclarativeQuestionDatum :=
  { language := "English"
  , neutralOk := false, obligatorilyBiased := true
  , clauseTyping := .cpTyped }

def hindi_urdu_decl_q : DeclarativeQuestionDatum :=
  { language := "Hindi-Urdu"
  , neutralOk := true, obligatorilyBiased := false
  , clauseTyping := .perspPTyped }

def italian_decl_q : DeclarativeQuestionDatum :=
  { language := "Italian"
  , neutralOk := true, obligatorilyBiased := false
  , clauseTyping := .cpTyped }

def allDeclQData : List DeclarativeQuestionDatum :=
  [english_decl_q, hindi_urdu_decl_q, italian_decl_q]

-- ============================================================================
-- §3. Hindi-Urdu shiftiness (Dayal 2025 §3.2, ex (39)–(41))
-- ============================================================================

/-- Cross-linguistic shiftiness data. Parallels McCloskey's English data.
    Hindi-Urdu *kya:* shows the same pattern as English embedded inversion:
    blocked under bare responsive, licensed under negation/questioning. -/
structure CrossLingShiftinessDatum where
  language : String
  verb : String
  sentence : String
  negated : Bool
  questioned : Bool
  quasiSubOk : Bool
  deriving Repr

/-- Hindi-Urdu: "want to know" (rogative) freely takes *kya:*
    (Dayal 2025: ex (39a)). -/
def hindi_urdu_want_to_know : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: ca:h-na: (want to know)"
  , sentence := "anu ja:nna: ca:hti: hai [ki (kya:) tum cai piyoge↑]"
  , negated := false, questioned := false, quasiSubOk := true }

/-- Hindi-Urdu: "know" (responsive) rejects *kya:* (Dayal 2025: ex (39b)). -/
def hindi_urdu_know_bare : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: (know)"
  , sentence := "*anu ja:nti: hai [ki (kya:) tum cai piyoge↑]"
  , negated := false, questioned := false, quasiSubOk := false }

/-- Hindi-Urdu: "nobody knows" + *kya:* → OK (negation, Dayal 2025: ex (41a)). -/
def hindi_urdu_know_negated : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: (know)"
  , sentence := "koii nahii jaanta [ki kya: TiTo sTa:lin-se mile the↑]"
  , negated := true, questioned := false, quasiSubOk := true }

/-- Hindi-Urdu: "does anyone know" + *kya:* → OK (questioning,
    Dayal 2025: ex (41b)). -/
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

/-- English: negated *remember* licenses embedded inversion
    ([mccloskey-2006]). -/
def remember_negated : CrossLingShiftinessDatum :=
  { language := "English", verb := "remember"
  , sentence := "I don't remember [was Henry a communist↑]"
  , negated := true, questioned := false, quasiSubOk := true }

/-- English: questioned *remember* licenses embedded inversion
    ([mccloskey-2006]). -/
def remember_questioned : CrossLingShiftinessDatum :=
  { language := "English", verb := "remember"
  , sentence := "Does Sue remember [was Henry a communist↑]"
  , negated := false, questioned := true, quasiSubOk := true }

/-- Hindi-Urdu shiftiness parallels English: bare responsive blocks quasi-sub,
    negation and questioning license it. -/
theorem hindi_urdu_shiftiness_parallels_english :
    hindi_urdu_know_bare.quasiSubOk = false ∧
    hindi_urdu_know_negated.quasiSubOk = true ∧
    hindi_urdu_know_questioned.quasiSubOk = true := by
  simp [hindi_urdu_know_bare, hindi_urdu_know_negated, hindi_urdu_know_questioned]

-- ============================================================================
-- §4. Newari conjunct/disjunct marking (Dayal 2025 §5.2, [zu-2018])
-- ============================================================================

/-- Newari uses conjunct vs disjunct verb forms sensitive to whether the
    subject is coindexed with the perspectival center (Seat of Knowledge).
    - Declaratives: conjunct = 1st person subject (SoK = speaker)
    - Interrogatives: conjunct = 2nd person subject (SoK = addressee)
    This provides independent evidence for perspective shift in questions
    (canonical Newari conjunct/disjunct pattern; Zu 2018 reanalyses as
    perspective shift). -/
structure ConjunctDisjunctDatum where
  language : String
  clauseType : String  -- "declarative" or "interrogative"
  conjunctPerson : String  -- which person gets conjunct marking
  deriving Repr

def newari_declarative : ConjunctDisjunctDatum :=
  { language := "Newari", clauseType := "declarative"
  , conjunctPerson := "1st" }

def newari_interrogative : ConjunctDisjunctDatum :=
  { language := "Newari", clauseType := "interrogative"
  , conjunctPerson := "2nd" }

def allConjunctDisjunctData : List ConjunctDisjunctDatum :=
  [newari_declarative, newari_interrogative]

-- ============================================================================
-- §5. Verification against empirical embedding data
-- ============================================================================

/-- Embedding judgment for an English attitude predicate
    ([dayal-2025]: §§1–3). -/
structure EmbeddingDatum where
  verb : String
  /-- "V whether/who..." -/
  subordination : Bool
  /-- "V [did S leave↑]" (embedded inversion + matrix intonation) -/
  quasiSubordination : Bool
  /-- 'V, "Did S leave?"' -/
  quotation : Bool
  deriving Repr

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

/-- Quasi-subordination implies subordination ([dayal-2025]). -/
-- UNVERIFIED: ex (20)
theorem quasi_sub_implies_sub :
    ∀ d ∈ allEmbeddingData,
      d.quasiSubordination = true → d.subordination = true := by
  intro d hd hq
  simp [allEmbeddingData] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [investigate_d, depend_on_d, wonder_d, ask_d, know_d, care_d, matter_d, believe_d]

/-- Quotation implies quasi-subordination ([dayal-2025]). -/
-- UNVERIFIED: ex (20)
theorem quotation_implies_quasi_sub :
    ∀ d ∈ allEmbeddingData,
      d.quotation = true → d.quasiSubordination = true := by
  intro d hd hq
  simp [allEmbeddingData] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [investigate_d, depend_on_d, wonder_d, ask_d, know_d, care_d, matter_d, believe_d]

/-- Classify each empirical embedding datum. -/
def classifyVerb : String → SelectionClass
  | "investigate" => .rogativeCP
  | "depend on"   => .rogativeCP
  | "wonder"      => .rogativePerspP
  | "ask"         => .rogativeSAP
  | "know"        => .responsive
  | "care"        => .responsive
  | "matter"      => .responsive
  | "believe"     => .uninterrogative
  | _             => .uninterrogative

/-- The theory correctly predicts all embedding judgments from the data. -/
theorem theory_predicts_embedding :
    ∀ d ∈ allEmbeddingData,
      allowsEmbedding (classifyVerb d.verb) .subordination false false
        = d.subordination ∧
      allowsEmbedding (classifyVerb d.verb) .quasiSubordination false false
        = d.quasiSubordination ∧
      allowsEmbedding (classifyVerb d.verb) .quotation false false
        = d.quotation := by
  intro d hd
  simp only [allEmbeddingData, List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Shiftiness predictions match McCloskey's data for *remember* (responsive). -/
theorem shiftiness_predicted :
    allowsQuasiSub .responsive remember_bare.negated remember_bare.questioned
      = remember_bare.quasiSubOk ∧
    allowsQuasiSub .responsive remember_negated.negated remember_negated.questioned
      = remember_negated.quasiSubOk ∧
    allowsQuasiSub .responsive remember_questioned.negated remember_questioned.questioned
      = remember_questioned.quasiSubOk := by
  simp [allowsQuasiSub, perspPConsistent, effectiveKnowledge, entailsKnowledge,
        remember_bare, remember_negated, remember_questioned]

-- ============================================================================
-- §6. Cross-linguistic predictions
-- ============================================================================

/-- Classify Hindi-Urdu verbs from the cross-linguistic shiftiness data. -/
def classifyCrossLingVerb : String → SelectionClass
  | "ja:n-na: ca:h-na: (want to know)" => .rogativePerspP
  | "ja:n-na: (know)"                  => .responsive
  | _                                  => .responsive

/-- Hindi-Urdu shiftiness follows the same derivation as English:
    responsive predicates reject quasi-sub in bare form, allow under
    negation/questioning. The theory predicts ALL cross-linguistic data. -/
theorem cross_linguistic_shiftiness_predicted :
    ∀ d ∈ allCrossLingShiftinessData,
      allowsQuasiSub (classifyCrossLingVerb d.verb) d.negated d.questioned
        = d.quasiSubOk := by
  intro d hd
  simp [allCrossLingShiftinessData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [allowsQuasiSub, perspPConsistent, effectiveKnowledge, entailsKnowledge,
          classifyCrossLingVerb,
          hindi_urdu_want_to_know, hindi_urdu_know_bare,
          hindi_urdu_know_negated, hindi_urdu_know_questioned]

/-! ### The three-layer classifier for question particles

The cartography's defining correlation as a classifier: a question
particle's left-peripheral layer is read off its embedding distribution —
subordinated-licensed → CP (clause-typing); subordinated-excluded but
quasi-subordinated-licensed → PerspP; quasi-subordinated-excluded but
matrix-licensed → SAP. [bhatt-dayal-2020]'s ForceP location for Hindi-Urdu
*kya:* is recast here as PerspP.

| Layer  | Language    | Particle    | Distribution         |
|--------|-------------|-------------|----------------------|
| CP     | Japanese    | *ka*        | matrix + subord + QS |
| PerspP | Hindi-Urdu  | *kya:*      | matrix + QS, no sub  |
| SAP    | Japanese    | *kke*       | matrix + quotation   |
| SAP    | English     | *quick(ly)* | matrix only          |
-/

/-- A question particle's layer, read off its embedding distribution.
    Defined for question particles only — Japanese *koto* (a declarative
    complementizer) is outside the intended domain. -/
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
    *quick* SAP. -/
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

-- ============================================================================
-- §7. Cross-layer agreement
-- ============================================================================

open English.Predicates.Verbal

/-- The structurally derived classification matches the manually-assigned
    string-based classification for all verbs in the embedding data. -/
theorem derived_class_matches_manual :
    deriveSelectionClass English.Predicates.Verbal.know
      = classifyVerb "know" ∧
    deriveSelectionClass English.Predicates.Verbal.wonder
      = classifyVerb "wonder" ∧
    deriveSelectionClass English.Predicates.Verbal.ask
      = classifyVerb "ask" ∧
    deriveSelectionClass English.Predicates.Verbal.investigate
      = classifyVerb "investigate" ∧
    deriveSelectionClass English.Predicates.Verbal.believe
      = classifyVerb "believe" := by
  decide

/-- String-based classification matches field-based derivation. -/
theorem classifyVerb_agrees_with_selectionClass :
    classifyVerb "know"
      = fieldSelectionClass English.Predicates.Verbal.know ∧
    classifyVerb "wonder"
      = fieldSelectionClass English.Predicates.Verbal.wonder ∧
    classifyVerb "ask"
      = fieldSelectionClass English.Predicates.Verbal.ask ∧
    classifyVerb "investigate"
      = fieldSelectionClass English.Predicates.Verbal.investigate ∧
    classifyVerb "depend on"
      = fieldSelectionClass English.Predicates.Verbal.depend_on ∧
    classifyVerb "believe"
      = fieldSelectionClass English.Predicates.Verbal.believe := by
  decide

end Dayal2025
