/-!
# Cross-Linguistic Question Typology (Dayal 2025)

Theory-neutral cross-linguistic data on question formation and embedding,
following Dayal (2025). Covers:

1. **Clause-typing variation**: forced (English, Italian) vs delayed (Hindi-Urdu)
2. **Simplex polar questions**: subordination restricted by clause-typing strategy
3. **Declarative questions**: bias conditioned by clause-typing
4. **Shiftiness**: responsive predicates shift under negation/questioning
5. **Conjunct/disjunct marking**: Newari person-sensitive verb morphology

Q-particle data classified by left-peripheral layer (which imports from
Theories/) lives in `Questions.TypologyBridge`.

## Languages covered

- English, Hindi-Urdu, Japanese, Italian, Newari

## References

- Dayal, V. (2025). The Interrogative Left Periphery. Linguistic Inquiry 56(4).
- Bhatt, R. & V. Dayal (2020). Polar question particles: Hindi-Urdu kya:.
- McCloskey, J. (2006). Questions and questioning in a local English.
- Zu, X. (2018). Discourse participants and the structural representation of context.
-/

namespace Phenomena.Questions.Typology

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
