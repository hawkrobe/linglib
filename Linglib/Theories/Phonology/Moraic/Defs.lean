import Linglib.Theories.Phonology.Syllable.Defs
import Linglib.Theories.Phonology.ProsodicWord

/-!
# Moraic Phonology

Moraic representations following @cite{hayes-1989}: the mora (μ) as the
fundamental unit of prosodic structure. Segments associate to morae, morae
associate to syllables. This replaces the segmental prosodic tier (X theory,
CV theory) with a prosodic tier whose elements directly encode weight.

Key design decisions from @cite{hayes-1989}:
- Onset consonants are **non-moraic** (universally)
- Short consonants are underlyingly moraless; coda consonants may receive
  a mora via **Weight by Position** (language-specific)
- Long vowels link to two morae; geminates link one segment to two morae
- Glides are moraless (zero morae)

The moraic tier σ → μ → segment replaces the `List Segment` representation
in `Syllable.Defs`, which is essentially a segmental (X-theory) view.

@cite{hayes-1989}
-/

namespace Theories.Phonology.Moraic

open Theories.Phonology (Segment Feature)
open Theories.Phonology.Syllable (Syllable SyllWeight SyllabifiedForm)

-- ============================================================================
-- § 1: Moraic Segment — a segment with its mora count
-- ============================================================================

/-- A segment's underlying moraic specification.

    Following @cite{hayes-1989}:
    - 0 morae: glides, onset consonants
    - 1 mora: short vowels, short consonants (when moraic by WBP)
    - 2 morae: long vowels, geminates, long syllabic consonants -/
inductive MoraCount where
  | zero   -- glides: no mora
  | one    -- short vowels, moraic coda consonants: one mora
  | two    -- long vowels, geminates: two morae
  deriving DecidableEq, Repr

def MoraCount.toNat : MoraCount → Nat
  | .zero => 0
  | .one  => 1
  | .two  => 2

/-- Increment a mora count by one (capped at two). -/
def MoraCount.succ : MoraCount → MoraCount
  | .zero => .one
  | .one  => .two
  | .two  => .two

-- ============================================================================
-- § 2: Moraic Syllable
-- ============================================================================

/-- A segment on the moraic tier, carrying its mora count.

    This captures the association between the segmental and prosodic tiers:
    the segment `seg` is linked to `morae` morae dominated by a syllable node. -/
structure MoraicSeg where
  seg   : Segment
  morae : MoraCount

/-- A syllable in moraic theory.

    Following @cite{hayes-1989}: the syllable node σ directly dominates morae,
    which in turn dominate segments. Onset consonants adjoin directly to σ
    without intervening morae (they are weight-irrelevant).

    The split between `onset` (non-moraic) and `moraic` (mora-bearing) segments
    is the structural core of moraic theory — it is this split that derives the
    onset deletion asymmetry. -/
structure MoraicSyllable where
  /-- Onset consonants: directly adjoined to σ, no mora. -/
  onset  : List Segment
  /-- Mora-bearing segments: nucleus vowels and (optionally) coda consonants.
      Ordered left to right; nucleus segments precede coda segments. -/
  moraic : List MoraicSeg

/-- A moraic form: a word parsed into moraic syllables. -/
structure MoraicForm where
  syllables : List MoraicSyllable

-- ============================================================================
-- § 3: Weight by Position — language-specific moraic structure
-- ============================================================================

/-- Language-specific parameters for moraic structure assignment.

    Following @cite{hayes-1989}, Rule (10): moraic structure is partly
    language-specific. The key parameter is Weight by Position: whether coda
    consonants receive a mora. Languages like Latin have WBP (CVC = heavy);
    languages like Lardil lack it (CVC = light). -/
structure MoraicParams where
  /-- Does this language assign morae to coda consonants? -/
  wbp : Bool

-- ============================================================================
-- § 4: Syllabification — deriving moraic structure from params + segments
-- ============================================================================

/-- Assign moraic structure to a `Syllable` according to `MoraicParams`.

    Following @cite{hayes-1989}, §2: the moraic structure assignment rules are:
    1. Nucleus segments receive one mora each
    2. Coda consonants receive a mora iff WBP is active
    3. Onset consonants are non-moraic

    This is the key function that **derives** moraic syllables from the
    existing segmental `Syllable` representation + language-specific params,
    rather than stipulating mora counts by hand. -/
def syllableToMoraic (params : MoraicParams) (σ : Syllable) : MoraicSyllable :=
  let nucleusMoraic := σ.nucleus.map (λ s => ⟨s, .one⟩)
  let codaMoraic := σ.coda.map (λ s => ⟨s, if params.wbp then .one else .zero⟩)
  ⟨σ.onset, nucleusMoraic ++ codaMoraic⟩

/-- Convert an entire `SyllabifiedForm` to a `MoraicForm`. -/
def syllabifiedToMoraic (params : MoraicParams) (sf : SyllabifiedForm) : MoraicForm :=
  ⟨sf.syllables.map (syllableToMoraic params)⟩

-- ============================================================================
-- § 5: Mora Counting
-- ============================================================================

/-- Total mora count of a moraic syllable. -/
def MoraicSyllable.moraCount (σ : MoraicSyllable) : Nat :=
  σ.moraic.foldl (· + ·.morae.toNat) 0

/-- Total mora count of a moraic form. -/
def MoraicForm.totalMorae (f : MoraicForm) : Nat :=
  f.syllables.foldl (· + ·.moraCount) 0

-- ============================================================================
-- § 6: Bridge to Syllable.SyllWeight and ProsodicWord
-- ============================================================================

/-- Convert moraic syllable to `SyllWeight` by extracting the mora count.

    This is lossless: `σ.toSyllWeight.morae = σ.moraCount` by definition.
    No classification into light/heavy/superheavy bins — the exact mora
    count passes through. -/
def MoraicSyllable.toSyllWeight (σ : MoraicSyllable) : SyllWeight :=
  ⟨σ.moraCount⟩

/-- Convert a moraic form to a `PrWd` (prosodic word) weight profile.

    This connects moraic representations to the prosodic word layer,
    enabling minimal word constraints, metrical parsing, and stress
    assignment to operate on moraically-derived weight profiles. -/
def MoraicForm.toPrWd (f : MoraicForm) : Theories.Phonology.ProsodicWord.PrWd :=
  ⟨f.syllables.map MoraicSyllable.toSyllWeight⟩

-- ============================================================================
-- § 7: Bridge Theorems
-- ============================================================================

/-- Helper: folding mora counts over a list of segments all mapped to the same
    `MoraCount` equals `init + length * moraCount`. -/
theorem foldl_morae_map (mc : MoraCount) (xs : List Segment) (init : Nat) :
    (xs.map (λ s => (⟨s, mc⟩ : MoraicSeg))).foldl (· + ·.morae.toNat) init =
    init + xs.length * mc.toNat := by
  induction xs generalizing init with
  | nil => simp [List.map]
  | cons _ xs ih =>
    simp only [List.map, List.foldl, List.length_cons]
    rw [ih, Nat.add_mul]; omega

/-- **General bridge**: `syllableToMoraic` with WBP produces the same mora count
    as `Syllable.moraCount codaMoraic=true`. Fully general over all syllables. -/
theorem syllableToMoraic_moraCount_wbp (σ : Syllable) :
    (syllableToMoraic { wbp := true } σ).moraCount = σ.moraCount true := by
  simp only [syllableToMoraic, MoraicSyllable.moraCount, Syllable.moraCount,
    ite_true, List.foldl_append]
  rw [foldl_morae_map, foldl_morae_map]
  simp [MoraCount.toNat]

/-- **General bridge**: `syllableToMoraic` without WBP produces the same mora count
    as `Syllable.moraCount codaMoraic=false`. -/
theorem syllableToMoraic_moraCount_no_wbp (σ : Syllable) :
    (syllableToMoraic { wbp := false } σ).moraCount = σ.moraCount false := by
  simp only [syllableToMoraic, MoraicSyllable.moraCount, Syllable.moraCount,
    Bool.false_eq_true, ite_false, List.foldl_append]
  rw [foldl_morae_map, foldl_morae_map]
  simp [MoraCount.toNat]

/-- **General bridge**: moraic weight classification agrees with segmental weight
    classification for WBP languages. This connects `MoraicSyllable.toSyllWeight`
    to `Syllable.weight` — two independently defined weight functions that
    must agree for the moraic theory to be consistent with the segmental view. -/
theorem syllableToMoraic_weight_wbp (σ : Syllable) :
    (syllableToMoraic { wbp := true } σ).toSyllWeight = σ.weight true := by
  unfold MoraicSyllable.toSyllWeight Syllable.weight
  congr 1; exact syllableToMoraic_moraCount_wbp σ

/-- General bridge for non-WBP languages. -/
theorem syllableToMoraic_weight_no_wbp (σ : Syllable) :
    (syllableToMoraic { wbp := false } σ).toSyllWeight = σ.weight false := by
  unfold MoraicSyllable.toSyllWeight Syllable.weight
  congr 1; exact syllableToMoraic_moraCount_no_wbp σ

/-- `syllableToMoraic` preserves CV = light regardless of WBP. -/
theorem syllableToMoraic_cv_light (params : MoraicParams) (o n : Segment) :
    (syllableToMoraic params ⟨[o], [n], []⟩).toSyllWeight = .light := by
  simp only [syllableToMoraic, MoraicSyllable.toSyllWeight,
    MoraicSyllable.moraCount, MoraCount.toNat, List.map, List.append_nil,
    List.foldl]

/-- A CV syllable (one monomoraic vowel, no coda) is light. -/
theorem cv_moraic_light (v : Segment) :
    (MoraicSyllable.mk [] [⟨v, .one⟩]).toSyllWeight = .light := rfl

/-- A CVV syllable (one bimoraic vowel) is heavy. -/
theorem cvv_moraic_heavy (v : Segment) :
    (MoraicSyllable.mk [] [⟨v, .two⟩]).toSyllWeight = .heavy := rfl

/-- A CVC syllable with WBP (coda has one mora) is heavy. -/
theorem cvc_wbp_heavy (v c₁ c₂ : Segment) :
    (MoraicSyllable.mk [c₁] [⟨v, .one⟩, ⟨c₂, .one⟩]).toSyllWeight = .heavy := rfl

/-- A CVC syllable without WBP (coda has zero morae) is light. -/
theorem cvc_no_wbp_light (v c₁ c₂ : Segment) :
    (MoraicSyllable.mk [c₁] [⟨v, .one⟩, ⟨c₂, .zero⟩]).toSyllWeight = .light := rfl

/-- A CVVC syllable (long vowel + moraic coda) is superheavy. -/
theorem cvvc_superheavy (v c₁ c₂ : Segment) :
    (MoraicSyllable.mk [c₁] [⟨v, .two⟩, ⟨c₂, .one⟩]).toSyllWeight = .superheavy := rfl

/-- Geminate: one segment linked to two morae, straddling a syllable boundary.
    The first half contributes its mora(e) to the coda of σ₁. -/
theorem geminate_makes_heavy (v seg : Segment) :
    (MoraicSyllable.mk [] [⟨v, .one⟩, ⟨seg, .one⟩]).toSyllWeight = .heavy := rfl

/-- The moraic minimal word: `satisfiesMinWord` checks ≥ 2 morae by default.
    This connects moraic representations to PrWd's bimoraic minimum. -/
theorem moraic_minword (f : MoraicForm) :
    f.toPrWd.satisfiesMinWord = decide (f.toPrWd.moraCount ≥ 2) := rfl

/-- **Round-trip fidelity**: `toSyllWeight.morae` recovers the exact mora count.
    No bounds needed — `SyllWeight` is now a `Nat` wrapper, not a lossy enum. -/
theorem toSyllWeight_morae_faithful (σ : MoraicSyllable) :
    σ.toSyllWeight.morae = σ.moraCount := rfl

end Theories.Phonology.Moraic
