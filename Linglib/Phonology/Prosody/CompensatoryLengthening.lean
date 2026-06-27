import Linglib.Phonology.Prosody.Syllable

/-!
# Compensatory lengthening

We model compensatory lengthening (CL) — the lengthening of one segment to
"compensate" for the loss of another — as the re-association of a stranded mora,
following [hayes-1989].

A `Mora` is an autosegmental node that *survives* the deletion of the segment it
dominated, becoming `Mora.stranded` (dominating nothing). Because the μ node
persists, the two central claims of moraic CL theory hold **by construction**
rather than by stipulation: deleting a non-moraic onset strands nothing, and so
cannot feed CL, while re-associating a stranded μ preserves the mora count, and
hence the weight. CL comes in two localities: *tautosyllabic*, where the
stranded μ re-links within its own syllable (Latin *kasnus → ka:nus*), and
*heterosyllabic*, where it crosses a boundary onto a neighbouring vowel (Middle
English *talə → ta:l*).

## Main definitions

* `CLType` — the seven attested CL types, with `CLType.locality` classifying
  each as tautosyllabic or heterosyllabic.
* `strand`, `deleteOnset` — segment deletion that strands a coda μ, versus onset
  deletion, which strands nothing.
* `spread` — tautosyllabic re-association of a syllable's stranded morae.
* `migrateLeft` — heterosyllabic re-association across a syllable boundary.

## Main statements

* `deleteOnset_strandedCount` — the onset-deletion asymmetry: onset deletion
  strands no μ, so it cannot feed CL.
* `strand_moraCount`, `spread_moraCount`, `migrateLeft_conserves` — moraic
  conservation: re-association preserves a syllable's mora count, and the total
  weight across a boundary.

The empirical CL derivations are exercised in `Studies/Hayes1989`.
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

/-- Whether a CL type re-associates the stranded μ within one syllable or moves
    it across a syllable boundary — i.e. which mechanism (`spread` vs
    `migrateLeft`) realizes it. -/
inductive Locality where
  | tautosyllabic
  | heterosyllabic
  deriving DecidableEq, Repr

/-- The locality of each attested CL type. Vowel loss and the double flop strand
    a μ that a *non-adjacent* (next-syllable) vowel picks up; the rest re-link
    within the deletion's own syllable. -/
def CLType.locality : CLType → Locality
  | .vowelLoss | .doubleFlop => .heterosyllabic
  | .classical | .totalAssimilation | .glideFormation
  | .prenasalization | .inverseCL => .tautosyllabic

/-! ### Stranding and spreading (tautosyllabic) -/

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
private def relink : List Segment → List Mora → List Mora
  | _,   []      => []
  | mel, μ :: ms =>
    if μ.dominates.isEmpty then ⟨mel⟩ :: relink mel ms
    else μ :: relink μ.dominates ms

private theorem relink_length (mel : List Segment) (ms : List Mora) :
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

/-! ### Heterosyllabic compensatory lengthening -/

/-- Heterosyllabic CL (`Locality.heterosyllabic`): deleting `right`'s nucleus
    strands a μ that re-associates onto `left`, lengthening it — Middle English
    *talə → ta:l*, the Ancient Greek double flop. One μ leaves `right` and joins
    `left` (the lengthening μ copies `left`'s final melody), so weight is
    conserved across the boundary rather than within one syllable. -/
def migrateLeft (left right : Syllable) : Syllable × Syllable :=
  (⟨left.onset, left.morae ++ [left.morae.getLastD Mora.stranded]⟩,
   ⟨right.onset, right.morae.dropLast⟩)

/-- **Moraic conservation across a syllable boundary**: the μ stranded in
    `right` is exactly the μ gained by `left`, so the total weight is unchanged.
    The tautosyllabic analogue of `strand_moraCount`/`spread_moraCount`. -/
theorem migrateLeft_conserves (left right : Syllable) (h : right.morae ≠ []) :
    (migrateLeft left right).1.moraCount + (migrateLeft left right).2.moraCount
      = left.moraCount + right.moraCount := by
  have hlen : 1 ≤ right.morae.length := by
    cases hm : right.morae with
    | nil => exact absurd hm h
    | cons a as => simp
  simp [migrateLeft, Syllable.moraCount, List.length_dropLast]
  omega

end Prosody.CL
