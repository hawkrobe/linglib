/-
# Cross-Linguistic Data on the Interrogative Left Periphery

Empirical data on how question formation and embedding vary across languages,
following Dayal (2025). The three-point left-peripheral structure
[SAP [PerspP [CP ...]]] predicts systematic variation in:

1. **Q-particles**: which layer they realize (CP vs PerspP vs SAP)
2. **Simplex polar questions**: whether they require overt clause-typing
3. **Declarative questions**: whether they are obligatorily biased
4. **Shiftiness**: whether responsive predicates shift under negation/questioning

## Languages covered

- English, Hindi-Urdu, Japanese, Italian, Newari

## References

- Dayal, V. (2025). The Interrogative Left Periphery. Linguistic Inquiry 56(4).
- Bhatt, R. & V. Dayal (2020). Polar question particles: Hindi-Urdu kya:.
- McCloskey, J. (2006). Questions and questioning in a local English.
- Miyagawa, S. (2012). Agreements that occur mainly in the main clause.
- Zu, X. (2018). Discourse participants and the structural representation of context.
-/

namespace Phenomena.Questions.Typology

-- ============================================================================
-- A. Q-particle typology (Dayal 2025: §1.3)
-- ============================================================================

/-- Where in the left periphery a Q-particle resides. -/
inductive QParticleLayer where
  | cp      -- Clause-typing particle: obligatory in subordinated interrogatives
  | perspP  -- Polar question particle (PQP): matrix + quasi-subordinated, not subordinated
  | sap     -- Meta question particle (MQP): matrix + quotation only
  deriving DecidableEq, Repr, BEq

/-- A Q-particle datum. -/
structure QParticleDatum where
  language : String
  form : String
  layer : QParticleLayer
  /-- Appears in matrix questions? -/
  inMatrix : Bool
  /-- Appears in subordinated interrogatives? -/
  inSubordinated : Bool
  /-- Appears in quasi-subordinated interrogatives? -/
  inQuasiSub : Bool
  /-- Appears in quotations? -/
  inQuotation : Bool
  deriving Repr

-- Japanese ka: clause-typing particle (CP)
-- Obligatory in subordinated, optional in matrix (Dayal 2025: §1.1, §1.3)
def japanese_ka : QParticleDatum :=
  { language := "Japanese", form := "ka"
  , layer := .cp
  , inMatrix := true, inSubordinated := true
  , inQuasiSub := true, inQuotation := true }

-- Hindi-Urdu kya:: polar question particle (PQP, PerspP layer)
-- Matrix + quasi-subordinated, NOT subordinated (Bhatt & Dayal 2020)
def hindi_urdu_kya : QParticleDatum :=
  { language := "Hindi-Urdu", form := "kya:"
  , layer := .perspP
  , inMatrix := true, inSubordinated := false
  , inQuasiSub := true, inQuotation := false }

-- Japanese kke: meta question particle (MQP, SAP layer)
-- Matrix + quotation only (Sauerland & Yatsushiro 2017)
def japanese_kke : QParticleDatum :=
  { language := "Japanese", form := "kke"
  , layer := .sap
  , inMatrix := true, inSubordinated := false
  , inQuasiSub := false, inQuotation := true }

-- English quick/quickly: MQP-like adverb (SAP layer)
-- Only matrix questions, ungrammatical in embedded position (Dayal 2025: (19))
def english_quick : QParticleDatum :=
  { language := "English", form := "quick/quickly"
  , layer := .sap
  , inMatrix := true, inSubordinated := false
  , inQuasiSub := false, inQuotation := false }

def allQParticleData : List QParticleDatum :=
  [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick]

-- Key generalization: distribution follows from left-peripheral layer
-- CP particles can appear wherever CP appears (everywhere)
-- PerspP particles where PerspP appears (matrix + quasi-sub)
-- SAP particles where SAP appears (matrix + quotation)

/-- CP-layer particles appear in subordinated position. -/
theorem cp_particles_in_subordination :
    ∀ d ∈ allQParticleData,
      d.layer = .cp → d.inSubordinated = true := by
  intro d hd _
  simp [allQParticleData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp_all [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick]

/-- PerspP-layer particles do NOT appear in subordinated position. -/
theorem perspP_particles_not_in_subordination :
    ∀ d ∈ allQParticleData,
      d.layer = .perspP → d.inSubordinated = false := by
  intro d hd _
  simp [allQParticleData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp_all [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick]

/-- SAP-layer particles do NOT appear in quasi-subordinated position. -/
theorem sap_particles_not_in_quasi_sub :
    ∀ d ∈ allQParticleData,
      d.layer = .sap → d.inQuasiSub = false := by
  intro d hd _
  simp [allQParticleData] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp_all [japanese_ka, hindi_urdu_kya, japanese_kke, english_quick]

-- ============================================================================
-- B. Clause-typing variation (Dayal 2025: §4.4)
-- ============================================================================

/-- How a language handles clause-typing for polar questions at CP. -/
inductive ClauseTypingStrategy where
  | forced       -- Clause-typing forced at CP (English, Italian: whether/se)
  | delayed      -- Clause-typing delayed to PerspP (Hindi-Urdu: no wh-complementizer)
  deriving DecidableEq, Repr, BEq

/-- Data on simplex polar question embedding across languages.
    A simplex polar question is just the nucleus *p* (no "or not").
    Hindi-Urdu: simplex polars in matrix/quasi-sub but NOT subordination.
    English/Italian: simplex polars in all three positions (via whether/se). -/
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
  { language := "English", clauseTyping := .forced
  , matrixOk := true, quasiSubOk := true, subordinationOk := true }

def italian_simplex : SimplexPolarDatum :=
  { language := "Italian", clauseTyping := .forced
  , matrixOk := true, quasiSubOk := true, subordinationOk := true }

-- Hindi-Urdu: simplex polar questions require PerspP (rising intonation activates
-- +WH at PerspP level). No wh-complementizer → cannot clause-type at CP.
-- Dayal 2025: (70)–(71)
def hindi_urdu_simplex : SimplexPolarDatum :=
  { language := "Hindi-Urdu", clauseTyping := .delayed
  , matrixOk := true, quasiSubOk := true, subordinationOk := false }

def allSimplexPolarData : List SimplexPolarDatum :=
  [english_simplex, italian_simplex, hindi_urdu_simplex]

/-- Delayed clause-typing languages cannot subordinate simplex polars. -/
theorem delayed_blocks_simplex_subordination :
    ∀ d ∈ allSimplexPolarData,
      d.clauseTyping = .delayed → d.subordinationOk = false := by
  intro d hd _
  simp [allSimplexPolarData] at hd
  rcases hd with rfl | rfl | rfl <;>
    simp_all [english_simplex, italian_simplex, hindi_urdu_simplex]

-- ============================================================================
-- C. Declarative questions and bias (Dayal 2025: §4.3)
-- ============================================================================

/-- Whether declarative questions in a language are obligatorily biased.
    English: "You drink wine?" is obligatorily biased (speaker expects yes).
    Hindi-Urdu/Italian: "a:p shara:b pi:te hai?" / "Bevi il vino?" can be neutral.
    This follows from whether clause-typing is forced at CP. -/
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
  , clauseTyping := .forced }

def hindi_urdu_decl_q : DeclarativeQuestionDatum :=
  { language := "Hindi-Urdu"
  , neutralOk := true, obligatorilyBiased := false
  , clauseTyping := .delayed }

def italian_decl_q : DeclarativeQuestionDatum :=
  { language := "Italian"
  , neutralOk := true, obligatorilyBiased := false
  , clauseTyping := .forced }

def allDeclQData : List DeclarativeQuestionDatum :=
  [english_decl_q, hindi_urdu_decl_q, italian_decl_q]

-- ============================================================================
-- D. Hindi-Urdu shiftiness (Dayal 2025: §3.2, (39)–(41))
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

-- Hindi-Urdu: "want to know" (rogative) freely takes kya: (Dayal 2025: (39a))
def hindi_urdu_want_to_know : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: ca:h-na: (want to know)"
  , sentence := "anu ja:nna: ca:hti: hai [ki (kya:) tum cai piyoge↑]"
  , negated := false, questioned := false, quasiSubOk := true }

-- Hindi-Urdu: "know" (responsive) rejects kya: (Dayal 2025: (39b))
def hindi_urdu_know_bare : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: (know)"
  , sentence := "*anu ja:nti: hai [ki (kya:) tum cai piyoge↑]"
  , negated := false, questioned := false, quasiSubOk := false }

-- Hindi-Urdu: "nobody knows" + kya: → OK (negation, Dayal 2025: (41a))
def hindi_urdu_know_negated : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: (know)"
  , sentence := "koii nahii jaanta [ki kya: TiTo sTa:lin-se mile the↑]"
  , negated := true, questioned := false, quasiSubOk := true }

-- Hindi-Urdu: "does anyone know" + kya: → OK (questioning, Dayal 2025: (41b))
def hindi_urdu_know_questioned : CrossLingShiftinessDatum :=
  { language := "Hindi-Urdu", verb := "ja:n-na: (know)"
  , sentence := "kisii-ko bhi maalum hai [ki (kya:) TiTo sTa:lin-se mile the↑]"
  , negated := false, questioned := true, quasiSubOk := true }

def allCrossLingShiftinessData : List CrossLingShiftinessDatum :=
  [hindi_urdu_want_to_know, hindi_urdu_know_bare,
   hindi_urdu_know_negated, hindi_urdu_know_questioned]

/-- Hindi-Urdu shiftiness parallels English: bare responsive blocks quasi-sub,
    negation and questioning license it. -/
theorem hindi_urdu_shiftiness_parallels_english :
    hindi_urdu_know_bare.quasiSubOk = false ∧
    hindi_urdu_know_negated.quasiSubOk = true ∧
    hindi_urdu_know_questioned.quasiSubOk = true := by
  simp [hindi_urdu_know_bare, hindi_urdu_know_negated, hindi_urdu_know_questioned]

-- ============================================================================
-- E. Newari conjunct/disjunct marking (Dayal 2025: §5.2, Zu 2018)
-- ============================================================================

/-- Newari uses conjunct vs disjunct verb forms sensitive to whether the subject
    is coindexed with the perspectival center (Seat of Knowledge).
    - Declaratives: conjunct = 1st person subject (SoK = speaker)
    - Interrogatives: conjunct = 2nd person subject (SoK = addressee)
    This provides independent evidence for perspective shift in questions. -/
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

end Phenomena.Questions.Typology
