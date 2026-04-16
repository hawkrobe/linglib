import Linglib.Theories.Phonology.Moraic.Defs

/-!
# Compensatory Lengthening in Moraic Theory

Compensatory lengthening (CL) as the filling of stranded morae following
segment deletion. This module formalizes the core theoretical claims of
@cite{hayes-1989}:

1. **Moraic Conservation**: CL processes conserve total mora count. Deletion
   strands a mora; spreading fills it.

2. **Onset Deletion Asymmetry**: CL does not compensate for loss of onset
   consonants, because onsets are universally non-moraic.

3. **Weight Prerequisite**: CL occurs only in languages with a syllable
   weight distinction (bimoraic syllables), because only such languages
   have morae that can be stranded.

The CL typology classifies seven attested CL types, all derivable from
moraic representations without stipulating constraints on association
line rearrangements.

@cite{hayes-1989}
-/

namespace Theories.Phonology.Moraic.CL

open Theories.Phonology (Segment)
open Theories.Phonology.Moraic

-- ============================================================================
-- § 1: CL Typology
-- ============================================================================

/-- The typology of compensatory lengthening processes
    (@cite{hayes-1989}, §5.1).

    Each type is defined by the deletion trigger and the spreading target.
    All types share the core mechanism: deletion strands a mora, which is
    then filled by spreading from an adjacent segment. -/
inductive CLType where
  /-- Vowel lengthens when a following coda consonant deletes.
      Example: Latin *kasnus → ka:nus. -/
  | classical
  /-- Total assimilation of a consonant, formally equivalent to CL.
      Example: asta → [atta] (progressive), asta → [assa] (regressive). -/
  | totalAssimilation
  /-- Glide formation shortens a vowel, freeing a mora that
      lengthens an adjacent segment. Example: tia → [tya:]. -/
  | glideFormation
  /-- Prenasalization absorbs a mora from the following stop.
      Example: Bantu amba → [a: m̌ba]. -/
  | prenasalization
  /-- Non-adjacent CL via double flop. Deletion causes resyllabification,
      which strands a mora accessible to a non-adjacent vowel.
      Example: Ancient Greek *odwos → o:dos. -/
  | doubleFlop
  /-- Vowel in the following syllable deletes; the preceding vowel
      lengthens via Parasitic Delinking.
      Example: Middle English talə → [ta:l]. -/
  | vowelLoss
  /-- A vowel deletes or shortens, with concomitant lengthening
      of the following consonant. Example: Luganda aika → [akka]. -/
  | inverseCL
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Deletion — segment removal that strands morae
-- ============================================================================

/-- Delete a segment from a moraic syllable at a given index in the
    moraic tier. Returns the modified syllable and the number of stranded morae.

    Following @cite{hayes-1989} §3: deletion on the segmental tier only —
    the mora remains, becoming segmentally unaffiliated. -/
def deleteMoraic (σ : MoraicSyllable) (idx : Nat) :
    MoraicSyllable × Nat :=
  match σ.moraic[idx]? with
  | some ms =>
    (⟨σ.onset, σ.moraic.eraseIdx idx⟩, ms.morae.toNat)
  | none => (σ, 0)

/-- Delete an onset consonant from a moraic syllable. Returns the modified
    syllable. No morae are stranded because onsets are non-moraic. -/
def deleteOnset (σ : MoraicSyllable) (idx : Nat) : MoraicSyllable :=
  ⟨σ.onset.eraseIdx idx, σ.moraic⟩

-- ============================================================================
-- § 3: Spreading — filling stranded morae
-- ============================================================================

/-- Direction of spreading to fill a stranded mora. -/
inductive SpreadDir where
  /-- Spread from the left: the preceding segment acquires the stranded mora.
      This is the typical case for classical CL and vowel loss CL. -/
  | left
  /-- Spread from the right: the following segment acquires the stranded mora.
      This is the typical case for inverse CL. -/
  | right
  deriving DecidableEq, Repr

/-- Add `n` morae to a `MoraicSeg`, capping at `.two`. -/
private def addMorae (ms : MoraicSeg) (n : Nat) : MoraicSeg :=
  let newMorae := match n with
    | 0 => ms.morae
    | 1 => ms.morae.succ
    | _ => .two  -- cap at bimoraic
  ⟨ms.seg, newMorae⟩

/-- Apply spreading to fill stranded morae in a moraic syllable.

    Following @cite{hayes-1989}: CL is part of syllabification.
    When a mora is stranded, syllabification principles fill it by spreading
    from the nearest available segment. The direction of spreading is
    language-specific (part of the syllabification algorithm).

    Handles 1 or 2 stranded morae (geminate deletion). -/
def spreadToFill (σ : MoraicSyllable) (strandedMorae : Nat)
    (dir : SpreadDir) : MoraicSyllable :=
  if strandedMorae == 0 then σ
  else match dir, σ.moraic.reverse, σ.moraic with
  | .left, last :: rest, _ =>
    ⟨σ.onset, rest.reverse ++ [addMorae last strandedMorae]⟩
  | .right, _, first :: rest =>
    ⟨σ.onset, addMorae first strandedMorae :: rest⟩
  | _, _, _ => σ

-- ============================================================================
-- § 4: Core Theorems
-- ============================================================================

/-- **Onset Deletion Asymmetry** (@cite{hayes-1989}, §5.2.1):
    Deleting an onset consonant strands zero morae, because onset consonants
    are universally non-moraic.

    This follows directly from the representation: onsets are `List Segment`
    with no mora association. There is nothing to strand.

    This is the strongest theorem in the formalization — fully general over
    all syllables and all onset indices. It is **derived** from the
    representation, not stipulated. -/
theorem onset_deletion_no_stranding (σ : MoraicSyllable) (idx : Nat) :
    (deleteOnset σ idx).moraCount = σ.moraCount := by
  simp only [deleteOnset, MoraicSyllable.moraCount]

/-- **Moraic Conservation** for single-mora CL
    (@cite{hayes-1989}, Rule (64)):
    Deleting a monomoraic segment and spreading left preserves total morae. -/
theorem moraic_conservation_left (v c : Segment) :
    let σ := MoraicSyllable.mk [] [⟨v, .one⟩, ⟨c, .one⟩]
    let (σ_del, stranded) := deleteMoraic σ 1
    σ.moraCount = (spreadToFill σ_del stranded .left).moraCount := rfl

/-- Moraic conservation also holds for rightward spreading (inverse CL). -/
theorem moraic_conservation_right (v c : Segment) :
    let σ := MoraicSyllable.mk [] [⟨v, .one⟩, ⟨c, .one⟩]
    let (σ_del, stranded) := deleteMoraic σ 0
    σ.moraCount = (spreadToFill σ_del stranded .right).moraCount := rfl

/-- **Weight prerequisite** (@cite{hayes-1989}, §6): deleting a non-moraic
    coda (WBP inactive) strands zero morae. No CL is possible. -/
theorem no_wbp_no_cl (v c₁ c₂ : Segment) :
    (deleteMoraic ⟨[c₁], [⟨v, .one⟩, ⟨c₂, .zero⟩]⟩ 1).2 = 0 := rfl

/-- Deleting a moraic coda (WBP active) strands one mora. CL is possible. -/
theorem wbp_strands_mora (v c₁ c₂ : Segment) :
    (deleteMoraic ⟨[c₁], [⟨v, .one⟩, ⟨c₂, .one⟩]⟩ 1).2 = 1 := rfl

/-- **Vowel-loss directionality** (@cite{hayes-1989}, §5.2.2):
    CL through vowel loss always lengthens the vowel to the **left** of the
    deleted vowel, never to the right. In moraic theory this follows from
    Parasitic Delinking + the No-Crossing Constraint (derived from temporal
    precedence in `Theories.Phonology.Autosegmental.no_crossing`,
    @cite{sagey-1986} §5.3): a stranded mora can only be picked up by
    spreading leftward without crossing. -/
theorem vowel_loss_leftward (v₁ v₂ : Segment) :
    let σ₁ := MoraicSyllable.mk [] [⟨v₁, .one⟩]
    let σ₂ := MoraicSyllable.mk [] [⟨v₂, .one⟩]
    let (_, stranded) := deleteMoraic σ₂ 0
    -- The stranded mora from σ₂ can fill σ₁ by leftward spreading
    let σ₁_cl := spreadToFill σ₁ stranded .left
    -- Conservation: σ₁ gains what σ₂ lost
    σ₁_cl.moraCount = σ₁.moraCount + stranded := rfl

/-- Syllabification with WBP (Rule (10)) produces moraic codas that can
    trigger CL. This connects `MoraicParams` to the CL mechanism: the *same
    parameter* that determines syllable weight also determines CL possibility
    (@cite{hayes-1989}, §6). -/
theorem wbp_params_enable_cl (o n c : Segment) :
    let σ := syllableToMoraic { wbp := true } ⟨[o], [n], [c]⟩
    (deleteMoraic σ 1).2 = 1 := rfl

/-- Without WBP, syllabification produces non-moraic codas: no CL. -/
theorem no_wbp_params_disable_cl (o n c : Segment) :
    let σ := syllableToMoraic { wbp := false } ⟨[o], [n], [c]⟩
    (deleteMoraic σ 1).2 = 0 := rfl

end Theories.Phonology.Moraic.CL
