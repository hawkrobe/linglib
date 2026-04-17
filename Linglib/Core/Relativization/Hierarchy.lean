import Linglib.Core.Relativization.Basic

/-!
# Accessibility Hierarchy: Ordering and Contiguity
@cite{keenan-comrie-1977}

Defines the rank function and contiguity predicate for the Accessibility
Hierarchy. Mirrors `Core.Case.Hierarchy` for Blake's case hierarchy.
-/

namespace Core

-- ============================================================================
-- § 1: Rank
-- ============================================================================

/-- Numeric rank of a position on the Accessibility Hierarchy.
    Higher rank = more accessible = more languages can relativize it. -/
def AHPosition.rank : AHPosition → Nat
  | .subject        => 6
  | .directObject   => 5
  | .indirectObject => 4
  | .oblique        => 3
  | .genitive       => 2
  | .objComparison  => 1

/-- Position p1 is at least as accessible as p2 on the hierarchy. -/
def AHPosition.atLeastAsAccessible (p1 p2 : AHPosition) : Bool :=
  p1.rank >= p2.rank

/-- Position p1 is strictly more accessible than p2. -/
def AHPosition.moreAccessible (p1 p2 : AHPosition) : Bool :=
  p1.rank > p2.rank

/-- All AH positions in descending order of accessibility. -/
def AHPosition.all : List AHPosition :=
  [.subject, .directObject, .indirectObject, .oblique, .genitive, .objComparison]

-- ============================================================================
-- § 2: Contiguity Predicate
-- ============================================================================

/-- Whether a list of AH positions contains at least one position at rank r. -/
private def hasAHRank (positions : List AHPosition) (r : Nat) : Bool :=
  positions.any fun p => p.rank == r

/-- A set of AH positions forms a contiguous segment on the hierarchy:
    for every pair of positions in the set, all intermediate ranks
    are also represented.

    Mirrors `Core.validInventory` for the case hierarchy (@cite{blake-1994}).

    This formalizes HC₂ of @cite{keenan-comrie-1977}: "Any RC-forming
    strategy must apply to a continuous segment of the AH." -/
def contiguousOnAH (positions : List AHPosition) : Bool :=
  positions.all fun p1 =>
    positions.all fun p2 =>
      if p2.rank > p1.rank then
        let lo := p1.rank
        let hi := p2.rank
        List.range hi |>.all fun r =>
          if r > lo && r < hi then hasAHRank positions r
          else true
      else true

/-- A marker's positions form a contiguous segment of the AH. -/
def RelClauseMarker.isContinuous (m : RelClauseMarker) : Bool :=
  contiguousOnAH m.positions

-- ============================================================================
-- § 3: Ordering Theorems
-- ============================================================================

/-- The hierarchy rank is injective — no two positions share a rank.
    Combined with the natural order on ℕ, this makes the AH a total order. -/
theorem ah_rank_injective (a b : AHPosition) (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> simp_all [AHPosition.rank]

/-- All ranks are between 1 and 6. -/
theorem ah_rank_bounded (p : AHPosition) : 1 ≤ p.rank ∧ p.rank ≤ 6 := by
  cases p <;> simp [AHPosition.rank]

/-- Accessibility is reflexive (follows from `≥` on ℕ). -/
theorem ah_reflexive (p : AHPosition) : p.atLeastAsAccessible p = true := by
  simp [AHPosition.atLeastAsAccessible]

/-- Accessibility is transitive (follows from `≥` on ℕ). -/
theorem ah_transitive (a b c : AHPosition)
    (h1 : a.atLeastAsAccessible b = true) (h2 : b.atLeastAsAccessible c = true) :
    a.atLeastAsAccessible c = true := by
  simp [AHPosition.atLeastAsAccessible] at *; omega

-- ============================================================================
-- § 4: Contiguity Examples
-- ============================================================================

/-- The full hierarchy [SU, DO, IO, OBL, GEN, OCOMP] is contiguous. -/
theorem full_ah_contiguous :
    contiguousOnAH AHPosition.all = true := rfl

/-- A single position is trivially contiguous. -/
theorem singleton_contiguous :
    contiguousOnAH [AHPosition.subject] = true := rfl

/-- [SU, DO] is contiguous. -/
theorem su_do_contiguous :
    contiguousOnAH [AHPosition.subject, .directObject] = true := rfl

/-- [IO, OBL, GEN] is contiguous (a non-primary segment). -/
theorem io_obl_gen_contiguous :
    contiguousOnAH [AHPosition.indirectObject, .oblique, .genitive] = true := rfl

/-- [SU, DO, OBL] is NOT contiguous (skips IO at rank 4). -/
theorem su_do_obl_not_contiguous :
    contiguousOnAH [AHPosition.subject, .directObject, .oblique] = false := rfl

-- ============================================================================
-- § 5: Primary Relativization Constraint (General Proof)
-- ============================================================================


/-- BEq agrees with propositional equality for AH positions. -/
private theorem ah_beq_iff (a b : AHPosition) :
    (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

/-- Nat BEq equality implies propositional equality. -/
private theorem nat_beq_to_eq {n m : Nat} (h : (n == m) = true) : n = m := by
  cases n <;> cases m <;> simp_all [BEq.beq]

/-- If `hasAHRank` finds a position at rank `a.rank`, that position is `a`
    (since rank is injective). -/
private theorem hasAHRank_implies_any
    (positions : List AHPosition) (a : AHPosition)
    (h : hasAHRank positions a.rank = true) :
    positions.any (· == a) = true := by
  unfold hasAHRank at h
  rw [List.any_eq_true] at h ⊢
  obtain ⟨b, hb_mem, hb_rank⟩ := h
  have hrank : b.rank = a.rank := nat_beq_to_eq hb_rank
  have heq : b = a := ah_rank_injective b a hrank
  exact ⟨a, heq ▸ hb_mem, by rw [ah_beq_iff]⟩

/-- If `contiguousOnAH positions = true` and `p1`, `p2` are both in the list
    with `p1.rank < p2.rank`, then every intermediate rank `r` with
    `p1.rank < r < p2.rank` is represented in the list. -/
private theorem contiguous_intermediate
    (positions : List AHPosition)
    (h_contig : contiguousOnAH positions = true)
    (p1 p2 : AHPosition)
    (hp1 : positions.any (· == p1) = true)
    (hp2 : positions.any (· == p2) = true)
    (hlt : p1.rank < p2.rank)
    (r : Nat) (hlo : p1.rank < r) (hhi : r < p2.rank) :
    hasAHRank positions r = true := by
  -- Convert List.any to membership
  rw [List.any_eq_true] at hp1 hp2
  obtain ⟨a1, ha1_mem, ha1_eq⟩ := hp1
  obtain ⟨a2, ha2_mem, ha2_eq⟩ := hp2
  rw [ah_beq_iff] at ha1_eq ha2_eq
  -- ha1_eq : a1 = p1, ha2_eq : a2 = p2
  have hp1_mem : p1 ∈ positions := ha1_eq ▸ ha1_mem
  have hp2_mem : p2 ∈ positions := ha2_eq ▸ ha2_mem
  -- Unpack contiguousOnAH
  unfold contiguousOnAH at h_contig
  rw [List.all_eq_true] at h_contig
  have h1 := h_contig p1 hp1_mem
  rw [List.all_eq_true] at h1
  have h2 := h1 p2 hp2_mem
  -- p2.rank > p1.rank is true, so the if-branch fires
  simp only [hlt, ↓reduceIte] at h2
  -- Extract the specific rank r from the range
  rw [List.all_eq_true] at h2
  have h3 := h2 r (List.mem_range.mpr hhi)
  simp only [hlo, hhi, Bool.and_self] at h3
  exact h3

/-- **Primary Relativization Constraint (general proof).**

    If a list of AH positions is contiguous (HC₂) and contains `.subject`
    (i.e., the strategy is primary), then the list is upward-closed:
    for any covered position `p`, all positions above `p` on the AH
    are also covered.

    This proves that the PRC is a logical consequence of HC₂ + being primary,
    not an independent constraint — the paper's core derivation. -/
theorem prc_from_hc2 (positions : List AHPosition)
    (h_contig : contiguousOnAH positions = true)
    (h_su : positions.any (· == AHPosition.subject) = true)
    (p above : AHPosition)
    (hp : positions.any (· == p) = true)
    (habove : above.rank > p.rank) :
    positions.any (· == above) = true := by
  by_cases h_eq : above = AHPosition.subject
  · -- above = .subject → trivially from h_su
    subst h_eq; exact h_su
  · -- above ≠ .subject → above.rank < 6
    have h_above_lt : above.rank < 6 := by
      cases above <;> simp [AHPosition.rank] at h_eq ⊢
    -- p.rank < above.rank < 6 = subject.rank
    have h_su_rank : AHPosition.subject.rank = 6 := rfl
    have h_p_lt_su : p.rank < AHPosition.subject.rank := by
      rw [h_su_rank]; omega
    -- above.rank is intermediate between p.rank and subject.rank
    have h_inter := contiguous_intermediate positions h_contig p .subject hp h_su
      h_p_lt_su above.rank habove (by rw [h_su_rank]; omega)
    exact hasAHRank_implies_any positions above h_inter

/-- All 6 canonical primary strategy segments are upward-closed.
    These are the only possible contiguous segments containing `.subject`. -/
theorem prc_all_primary_segments :
    let segs := [
      [AHPosition.subject],
      [.subject, .directObject],
      [.subject, .directObject, .indirectObject],
      [.subject, .directObject, .indirectObject, .oblique],
      [.subject, .directObject, .indirectObject, .oblique, .genitive],
      [.subject, .directObject, .indirectObject, .oblique, .genitive, .objComparison] ]
    segs.all (λ seg =>
      contiguousOnAH seg &&
      seg.any (· == .subject) &&
      seg.all (λ p => AHPosition.all.all (λ above =>
        if above.rank > p.rank then seg.any (· == above) else true))) = true := by
  decide

end Core
