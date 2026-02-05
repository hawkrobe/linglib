/-
# Embedding of Interrogatives under Attitude Predicates

Empirical data on which predicates embed which types of interrogative clauses,
following Dayal (2025). The key contrast is between subordination (standard
embedding), quasi-subordination (embedded inversion + matrix intonation), and
quotation.

## Core observations (Dayal 2025: §§1–3)

1. Rogative predicates (wonder, ask, investigate) embed interrogatives;
   responsive predicates (know) embed both declaratives and interrogatives
2. Only a subset of rogatives allow embedded inversion (quasi-subordination)
3. Responsive predicates allow quasi-subordination only when negated or questioned
   ("shiftiness", McCloskey 2006)

## References

- Dayal, V. (2025). The Interrogative Left Periphery. Linguistic Inquiry 56(4).
- McCloskey, J. (2006). Questions and questioning in a local English.
- Grimshaw, J. (1979). Complement selection and the lexicon.
-/

namespace Phenomena.Questions.Embedding

-- ============================================================================
-- Embedding types (theory-neutral description)
-- ============================================================================

/-- The structurally distinct ways an interrogative clause can be embedded. -/
inductive EmbedType where
  | subordination      -- "knows whether S left" / "knows who S saw"
  | quasiSubordination -- "wants to know [did S leave↑]" (embedded inversion)
  | quotation          -- asked, "Did S leave?" (full quotation)
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- Embedding predicate data
-- ============================================================================

/-- Embedding judgment for a predicate. -/
structure EmbeddingDatum where
  verb : String
  /-- "V whether/who ..." -/
  subordination : Bool
  /-- "V [did S leave↑]" (embedded inversion + matrix intonation) -/
  quasiSubordination : Bool
  /-- 'V, "Did S leave?"' -/
  quotation : Bool
  /-- Does it also embed declarative complements? -/
  embedsDeclarative : Bool
  deriving Repr

-- Rogative predicates (embed only interrogatives)

def investigate_d : EmbeddingDatum :=
  { verb := "investigate"
  , subordination := true, quasiSubordination := false
  , quotation := false, embedsDeclarative := false }

def depend_on_d : EmbeddingDatum :=
  { verb := "depend on"
  , subordination := true, quasiSubordination := false
  , quotation := false, embedsDeclarative := false }

def wonder_d : EmbeddingDatum :=
  { verb := "wonder"
  , subordination := true, quasiSubordination := true
  , quotation := false, embedsDeclarative := false }

def ask_d : EmbeddingDatum :=
  { verb := "ask"
  , subordination := true, quasiSubordination := true
  , quotation := true, embedsDeclarative := false }

-- Responsive predicates (embed both declaratives and interrogatives)

def know_d : EmbeddingDatum :=
  { verb := "know"
  , subordination := true, quasiSubordination := false
  , quotation := false, embedsDeclarative := true }

-- Uninterrogative predicates (declaratives only)

def believe_d : EmbeddingDatum :=
  { verb := "believe"
  , subordination := false, quasiSubordination := false
  , quotation := false, embedsDeclarative := true }

def allEmbeddingData : List EmbeddingDatum :=
  [investigate_d, depend_on_d, wonder_d, ask_d, know_d, believe_d]

-- ============================================================================
-- Key generalizations
-- ============================================================================

/-- Quasi-subordination implies subordination (Dayal 2025: (20)). -/
theorem quasi_sub_implies_sub :
    ∀ d ∈ allEmbeddingData,
      d.quasiSubordination = true → d.subordination = true := by
  intro d hd hq
  simp [allEmbeddingData] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [investigate_d, depend_on_d, wonder_d, ask_d, know_d, believe_d]

/-- Quotation implies quasi-subordination (Dayal 2025: (20)). -/
theorem quotation_implies_quasi_sub :
    ∀ d ∈ allEmbeddingData,
      d.quotation = true → d.quasiSubordination = true := by
  intro d hd hq
  simp [allEmbeddingData] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [investigate_d, depend_on_d, wonder_d, ask_d, know_d, believe_d]

-- ============================================================================
-- Shiftiness data (McCloskey 2006, Dayal 2025: §3.2)
-- ============================================================================

/-- Context-dependent quasi-subordination judgment. -/
structure ShiftinessDatum where
  verb : String
  sentence : String
  negated : Bool
  questioned : Bool
  quasiSubOk : Bool
  deriving Repr

def remember_bare : ShiftinessDatum :=
  { verb := "remember"
  , sentence := "*I remember [was Henry a communist↑]"
  , negated := false, questioned := false, quasiSubOk := false }

def remember_negated : ShiftinessDatum :=
  { verb := "remember"
  , sentence := "I don't remember [was Henry a communist↑]"
  , negated := true, questioned := false, quasiSubOk := true }

def remember_questioned : ShiftinessDatum :=
  { verb := "remember"
  , sentence := "Does Sue remember [was Henry a communist↑]"
  , negated := false, questioned := true, quasiSubOk := true }

def forget_quasi_sub : ShiftinessDatum :=
  { verb := "forget"
  , sentence := "I have forgotten [did Ann get A's↑]"
  , negated := false, questioned := false, quasiSubOk := true }

def allShiftinessData : List ShiftinessDatum :=
  [remember_bare, remember_negated, remember_questioned, forget_quasi_sub]

end Phenomena.Questions.Embedding
