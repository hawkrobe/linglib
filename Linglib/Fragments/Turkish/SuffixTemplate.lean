import Linglib.Fragments.Turkish.TAM
import Linglib.Fragments.Turkish.VowelHarmony

/-!
# Turkish Suffix Template
@cite{goksel-kerslake-2005}

Turkish is strictly suffixing (@cite{goksel-kerslake-2005} Ch 6). Suffixes
attach in a fixed order determined by a **positional template**.

## Verbal template (Ch 6, 8, 13)

  Root -> Voice -> Negation -> TAM -> Copula -> Agreement -> Question

## Nominal template (Ch 6, 8, 14)

  Root -> Derivational -> Plural -> Possessive -> Case

## Key properties

1. **Strict ordering**: suffixes from later slots never precede earlier ones
2. **At most one per slot**: each slot filled at most once (voice can stack:
   e.g., *yap-tır-ıl-* 'be made to do' = CAUS + PASS)
3. **Monoexponential**: each suffix realizes a single morphosyntactic feature
   (WALS F21A: monoexponential case)
-/

namespace Fragments.Turkish.SuffixTemplate

/-- Verbal suffix slots, ordered innermost to outermost.
    @cite{goksel-kerslake-2005} Ch 6, 8, 13. -/
inductive VerbSlot where
  | voice         -- causative -DIr, passive -(I)l, reflexive -(I)n, reciprocal -(I)ş
  | negation      -- -mA
  | tam           -- -DI, -mIş, -(I)r, -Iyor, -(y)AcAK, -sA, -(y)A, -mAlI
  | copula        -- compound tense: -DI, -mIş, -(y)sA
  | agreement     -- person/number
  | question      -- mI
  deriving DecidableEq, BEq, Repr

/-- Nominal suffix slots, ordered innermost to outermost.
    @cite{goksel-kerslake-2005} Ch 6, 8, 14. -/
inductive NounSlot where
  | derivational  -- denominal/deadjectival suffixes
  | plural        -- -lAr
  | possessive    -- -(I)m, -(I)n, -(s)I, etc.
  | case          -- -(y)I, -(y)A, -DA, -DAn, -(n)In, zero
  deriving DecidableEq, BEq, Repr

def VerbSlot.rank : VerbSlot → Nat
  | .voice => 0 | .negation => 1 | .tam => 2
  | .copula => 3 | .agreement => 4 | .question => 5

def NounSlot.rank : NounSlot → Nat
  | .derivational => 0 | .plural => 1 | .possessive => 2 | .case => 3

-- ============================================================================
-- § Ordering verification
-- ============================================================================

theorem voice_before_neg : VerbSlot.voice.rank < VerbSlot.negation.rank := by native_decide
theorem neg_before_tam : VerbSlot.negation.rank < VerbSlot.tam.rank := by native_decide
theorem tam_before_cop : VerbSlot.tam.rank < VerbSlot.copula.rank := by native_decide
theorem cop_before_agr : VerbSlot.copula.rank < VerbSlot.agreement.rank := by native_decide
theorem agr_before_q : VerbSlot.agreement.rank < VerbSlot.question.rank := by native_decide

theorem plural_before_poss : NounSlot.plural.rank < NounSlot.possessive.rank := by native_decide
theorem poss_before_case : NounSlot.possessive.rank < NounSlot.case.rank := by native_decide

/-- Negation cannot follow TAM (reversed order). -/
theorem neg_not_after_tam :
    ¬(VerbSlot.tam.rank < VerbSlot.negation.rank) := by native_decide

/-- Case cannot precede possessive (reversed order). -/
theorem case_not_before_poss :
    ¬(NounSlot.case.rank < NounSlot.possessive.rank) := by native_decide

/-- Voice suffixes can stack (two voice entries at rank 0 is well-formed).
    Example: *yap-tır-ıl-* (do-CAUS-PASS). -/
theorem voice_stacking_ok :
    VerbSlot.voice.rank ≤ VerbSlot.voice.rank := Nat.le_refl _

-- ============================================================================
-- § Cross-file bridges: TAM and negation fill template slots
-- ============================================================================

/-- All 8 TAM categories fill the .tam slot (slot rank 2). -/
theorem tam_entries_fill_tam_slot :
    TAM.entries.length = 8 ∧ VerbSlot.tam.rank = 2 := ⟨by native_decide, rfl⟩

/-- Negation (-mA-) occupies slot rank 1, strictly before TAM (slot rank 2).
    This matches the surface order: gel-**me**-**di** (stem-NEG-PST). -/
theorem negation_precedes_tam :
    VerbSlot.negation.rank < VerbSlot.tam.rank := by native_decide

/-- The question particle mI fills the outermost verbal slot (rank 5).
    It follows agreement, yielding: gel-di-**m** **mi**? (come-PST-1SG Q). -/
theorem question_is_outermost :
    VerbSlot.question.rank = 5 ∧
    ∀ s : VerbSlot, s.rank ≤ VerbSlot.question.rank := by
  constructor
  · rfl
  · intro s; cases s <;> simp [VerbSlot.rank] <;> omega

-- ============================================================================
-- § End-to-end: VH resolves TAM suffix vowels
-- ============================================================================

open VowelHarmony in
/-- The archiphonemic I in progressive -Iyor resolves to 4 surface vowels
    depending on stem harmony. This connects VowelHarmony to TAM:
    - back+unround stem (kol): -ıyor (resolveI true false = ı)
    - front+unround stem (gel): -iyor (resolveI false false = i)
    - back+round stem (kol): -uyor (resolveI true true = u)
    - front+round stem (göz): -üyor (resolveI false true = ü) -/
theorem progressive_I_resolution :
    resolveI true  false = ı_vowel ∧
    resolveI false false = i_vowel ∧
    resolveI true  true  = u_vowel ∧
    resolveI false true  = ü_vowel := ⟨rfl, rfl, rfl, rfl⟩

open VowelHarmony in
/-- The archiphonemic A in future -(y)AcAK resolves to a/e by palatal harmony.
    back stem (kol): -(y)acak; front stem (gel): -(y)ecek. -/
theorem future_A_resolution :
    resolveA true  = a_vowel ∧
    resolveA false = e_vowel := ⟨rfl, rfl⟩

end Fragments.Turkish.SuffixTemplate
