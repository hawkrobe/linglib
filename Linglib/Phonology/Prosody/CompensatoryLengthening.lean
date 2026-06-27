import Linglib.Phonology.Prosody.Syllable

/-!
# Compensatory lengthening

Compensatory lengthening (CL) as the re-association of a stranded mora,
following [hayes-1989]. Because a `Mora` is a node that *survives* the deletion
of the segment it dominated (`Mora.stranded`), the core claims hold **by
construction** rather than by stipulation:

* **Onset-deletion asymmetry** — onsets are not on the mora spine, so deleting
  one strands no μ and cannot feed CL (`deleteOnset_strandedCount`), unlike
  coda deletion (`strand`).
* **Moraic conservation** — onset deletion, stranding a segment, and
  re-associating its μ are each length-preserving on the spine, so the weight
  is invariant (`deleteOnset_moraCount`, `strand_moraCount`, `spread_moraCount`).

The empirical CL types (Latin *kasnus → ka:nus*, etc.) are exercised in
`Studies/Hayes1989`.
-/

namespace Prosody.CL

open Phonology (Segment)

/-! ### The CL typology -/

/-- The seven attested compensatory-lengthening types ([hayes-1989]). Each is a
    deletion trigger plus a spreading target; all share the mechanism *deletion
    strands a mora, which is then re-associated to an adjacent segment*. -/
inductive CLType where
  /-- Vowel lengthens when a following coda consonant deletes (Latin
      *kasnus → ka:nus*). -/
  | classical
  /-- Total consonant assimilation, formally equivalent to CL (*asta → atta*). -/
  | totalAssimilation
  /-- Glide formation frees a mora that lengthens a neighbour (*tia → tya:*). -/
  | glideFormation
  /-- Prenasalization absorbs a mora from the following stop (Bantu
      *amba → a:mba*). -/
  | prenasalization
  /-- Non-adjacent CL via double flop: deletion resyllabifies, stranding a mora
      a non-adjacent vowel picks up (Ancient Greek *odwos → o:dos*). -/
  | doubleFlop
  /-- A following vowel deletes; the preceding vowel lengthens by Parasitic
      Delinking (Middle English *talə → ta:l*). -/
  | vowelLoss
  /-- A vowel shortens, lengthening the following consonant (Luganda
      *aika → akka*). -/
  | inverseCL
  deriving DecidableEq, Repr

/-! ### Stranding and spreading -/

/-- Delete the segment dominated by mora `i`, leaving the μ node **stranded**
    (it survives, dominating nothing). The mora count is unchanged — this is the
    engine of compensatory lengthening. -/
def strand (σ : Syllable) (i : Nat) : Syllable :=
  ⟨σ.onset, σ.morae.set i Mora.stranded⟩

/-- Delete an onset segment. Onsets are not on the mora spine, so the weight is
    untouched. -/
def deleteOnset (σ : Syllable) (i : Nat) : Syllable :=
  ⟨σ.onset.eraseIdx i, σ.morae⟩

/-- The number of stranded (segmentally unaffiliated) morae. -/
def strandedCount (σ : Syllable) : Nat :=
  σ.morae.countP fun μ => μ.dominates.isEmpty

/-- Direction of spreading to fill a stranded mora. -/
inductive SpreadDir where
  | left
  | right
  deriving DecidableEq, Repr

/-- Re-link stranded morae left-to-right, each one taking the melody (`mel`) of
    the nearest non-stranded mora to its left. -/
def relink : List Segment → List Mora → List Mora
  | _,   []      => []
  | mel, μ :: ms =>
    if μ.dominates.isEmpty then ⟨mel⟩ :: relink mel ms
    else μ :: relink μ.dominates ms

theorem relink_length (mel : List Segment) (ms : List Mora) :
    (relink mel ms).length = ms.length := by
  induction ms generalizing mel with
  | nil => rfl
  | cons μ ms ih => simp only [relink]; split <;> simp [ih]

/-- Re-associate each stranded mora to the melody of its nearest non-stranded
    neighbour on the given side. Length-preserving on the mora spine, so weight
    is conserved (`spread_moraCount`). -/
def spread (σ : Syllable) (dir : SpreadDir) : Syllable :=
  match dir with
  | .left  => ⟨σ.onset, relink [] σ.morae⟩
  | .right => ⟨σ.onset, (relink [] σ.morae.reverse).reverse⟩

/-! ### The onset-deletion asymmetry -/

/-- **Onset-deletion asymmetry** ([hayes-1989]): deleting an onset segment
    strands *no* mora — onsets are not on the mora spine — so it cannot feed
    compensatory lengthening. Contrast `strand`, which leaves a stranded μ
    behind (exercised on concrete syllables in `Studies/Hayes1989`). The
    asymmetry is in the *stranded* count, not the mora count: in moraic theory
    *both* onset and coda deletion preserve the total weight (next section),
    but only coda deletion produces a stranded μ to lengthen. -/
theorem deleteOnset_strandedCount (σ : Syllable) (i : Nat) :
    strandedCount (deleteOnset σ i) = strandedCount σ := rfl

/-! ### Moraic conservation by construction -/

/-- Onset deletion preserves the weight (it never touches the spine). -/
theorem deleteOnset_moraCount (σ : Syllable) (i : Nat) :
    (deleteOnset σ i).moraCount = σ.moraCount := rfl

/-- Stranding a segment preserves the weight — the μ node survives, dominating
    nothing, so the mora *count* is unchanged. This is what makes conservation
    hold by construction rather than by arithmetic bookkeeping. -/
theorem strand_moraCount (σ : Syllable) (i : Nat) :
    (strand σ i).moraCount = σ.moraCount := by
  simp [strand, Syllable.moraCount]

/-- Spreading (re-associating stranded morae) is length-preserving on the
    spine, so the weight is invariant. -/
theorem spread_moraCount (σ : Syllable) (dir : SpreadDir) :
    (spread σ dir).moraCount = σ.moraCount := by
  cases dir <;>
    simp [spread, Syllable.moraCount, relink_length, List.length_reverse]

end Prosody.CL
