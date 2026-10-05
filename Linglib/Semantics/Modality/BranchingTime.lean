module

public import Linglib.Core.Order.LeftLinear
public import Linglib.Semantics.Tense.Defs
public import Mathlib.Order.Zorn

/-!
# Branching time

The branching-time model of Prior and Thomason depicts the open future as an order of moments
that is linear towards the past and branches towards the future: a left-linear partial order
(`Core.Order.IsLeftLinear`). A history is a complete possible course of the world, a maximal
chain of moments, mathlib's `Flag`; the histories through a moment are its possible futures
(`histories`). Propositions are sets, of moments or of moment–history pairs.

The two classic postsemantics evaluate the future operator differently. Peircean truth is at
a moment, and future truth requires settledness: a later witness on every history through the
moment (`Peircean.future`). Ockhamist truth is at a moment–history pair, future truth is a
later witness on the fixed history (`Ockhamist.future`), and settledness is a quantifier over
the histories through the moment (`Ockhamist.settled`). The history parameter is not fixed by
a context of utterance, since there is no actual future; only the moment is, which is why
settledness carries the felicity facts. The Peircean future is the settled Ockhamist future
(`Ockhamist.settled_future_atom`). On a finite frame every history is the down-set of a
maximal moment, so settledness is decidable.

## Main definitions

* `histories`: the histories through a moment.
* `Peircean.past`, `Peircean.future`: the Peircean operators on sets of moments.
* `Ockhamist.atom`, `Ockhamist.past`, `Ockhamist.future`, `Ockhamist.settled`: the Ockhamist
  operators on sets of moment–history pairs.

## Main results

* `histories_antitone`, `histories_eq_singleton`, `histories_inter_nonempty_iff`: later
  moments lie on fewer histories, a maximal moment lies on exactly one, and two moments
  share a history exactly when they are comparable.
* `Ockhamist.settled_atom`, `Ockhamist.settled_future_atom`: atomic propositions are settled,
  and the Peircean future is the settled Ockhamist future.
* `Ockhamist.past_atom_iff_holds`, `Ockhamist.future_atom_iff_holds`: on a linear frame the
  Ockhamist operators land in the library's tense comparison cells.
* `Peircean.mem_future_iff`: on a finite frame settled future truth is a bounded search over
  the maximal moments, hence decidable.

## Implementation notes

Historical connectedness, the condition that any two moments share a common past, figures in
no theorem here, so it is not bundled into a frame class; theorems assume the exact mixins
they use.

## References

* [prior-1967]
* [rumberg-lauer-2023]
-/

@[expose] public section

namespace BranchingTime

open Semantics

variable {M : Type*} [PartialOrder M]

/-! ### Histories -/

/-- The histories through a moment are the maximal chains containing it, written `Hist(m)` in
the branching-time literature. -/
def histories (m : M) : Set (Flag M) := {h | m ∈ h}

@[simp] theorem mem_histories {m : M} {h : Flag M} : h ∈ histories m ↔ m ∈ h := Iff.rfl

/-- Every moment lies on a history. -/
theorem histories_nonempty (m : M) : (histories m).Nonempty :=
  let ⟨s, hs⟩ := Flag.exists_mem m; ⟨s, hs⟩

section LeftLinear

variable [IsLeftLinear M]

/-- Later moments lie on fewer histories. -/
theorem histories_antitone : Antitone (histories (M := M)) :=
  fun _ _ hmn _ hh ↦ Flag.Iic_subset hh hmn

/-- A maximal moment lies on exactly one history, its past. -/
theorem histories_eq_singleton {x : M} (hx : IsMax x) : histories x = {Flag.ofIsMax hx} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨Set.mem_Iic.2 le_rfl, fun _ ↦ Flag.eq_ofIsMax_of_mem hx⟩

/-- Two moments share a history exactly when they are comparable. -/
theorem histories_inter_nonempty_iff {m n : M} :
    (histories m ∩ histories n).Nonempty ↔ m ≤ n ∨ n ≤ m :=
  ⟨fun ⟨h, hm, hn⟩ ↦ h.le_or_le hm hn, fun hmn ↦ hmn.elim
    (fun hmn ↦ let ⟨h, hh⟩ := histories_nonempty n; ⟨h, Flag.Iic_subset hh hmn, hh⟩)
    fun hnm ↦ let ⟨h, hh⟩ := histories_nonempty m; ⟨h, hh, Flag.Iic_subset hh hnm⟩⟩

end LeftLinear

/-! ### The Peircean postsemantics

Sentences are evaluated at a moment, and future truth is settled truth. -/

namespace Peircean

variable (φ : Set M)

/-- The Peircean past of a proposition holds where it held at an earlier moment. -/
def past : Set M := {m | ∃ m' < m, m' ∈ φ}

/-- The Peircean future of a proposition holds where every history through the moment has a
later witness. This is settled future truth, historical inevitability. -/
def future : Set M := {m | ∀ h ∈ histories m, ∃ m' ∈ h, m < m' ∧ m' ∈ φ}

variable {φ} {m : M}

@[simp] theorem mem_past : m ∈ past φ ↔ ∃ m' < m, m' ∈ φ := Iff.rfl

@[simp] theorem mem_future : m ∈ future φ ↔ ∀ h ∈ histories m, ∃ m' ∈ h, m < m' ∧ m' ∈ φ :=
  Iff.rfl

end Peircean

/-! ### The Ockhamist postsemantics

Sentences are evaluated at a moment–history pair, future truth is truth later on the given
history, and settledness quantifies over the histories through the moment. -/

namespace Ockhamist

variable (φ : Set (M × Flag M))

/-- A proposition of moments read at any history. -/
def atom (φ : Set M) : Set (M × Flag M) := Prod.fst ⁻¹' φ

/-- The Ockhamist past of a proposition holds where it held at an earlier moment, on the same
history. -/
def past : Set (M × Flag M) := {p | ∃ m' < p.1, (m', p.2) ∈ φ}

/-- The Ockhamist future of a proposition holds where a later moment of the fixed history is a
witness. -/
def future : Set (M × Flag M) := {p | ∃ m' ∈ p.2, p.1 < m' ∧ (m', p.2) ∈ φ}

/-- A proposition is settled where it holds at the moment on every history through it. The
history coordinate of the index is idle, since settledness quantifies it away. -/
def settled : Set (M × Flag M) := {p | ∀ h ∈ histories p.1, (p.1, h) ∈ φ}

variable {φ} {m : M} {h : Flag M}

@[simp] theorem mem_atom {φ : Set M} : (m, h) ∈ atom φ ↔ m ∈ φ := Iff.rfl

@[simp] theorem mem_past : (m, h) ∈ past φ ↔ ∃ m' < m, (m', h) ∈ φ := Iff.rfl

@[simp] theorem mem_future : (m, h) ∈ future φ ↔ ∃ m' ∈ h, m < m' ∧ (m', h) ∈ φ := Iff.rfl

@[simp] theorem mem_settled : (m, h) ∈ settled φ ↔ ∀ h' ∈ histories m, (m, h') ∈ φ := Iff.rfl

/-- Atomic propositions are settled, since the valuation depends only on the moment. -/
@[simp] theorem settled_atom (φ : Set M) : settled (atom φ) = atom φ :=
  Set.ext fun p ↦ ⟨fun H ↦ let ⟨h', hh'⟩ := histories_nonempty p.1; H h' hh', fun hφ _ _ ↦ hφ⟩

/-- The settled past of an atom is the Peircean past, since the past does not depend on the
history. -/
theorem settled_past_atom (φ : Set M) : settled (past (atom φ)) = atom (Peircean.past φ) :=
  Set.ext fun p ↦ ⟨fun H ↦ let ⟨h', hh'⟩ := histories_nonempty p.1; H h' hh', fun hφ _ _ ↦ hφ⟩

/-- The settled future of an atom is the Peircean future. -/
theorem settled_future_atom (φ : Set M) :
    settled (future (atom φ)) = atom (Peircean.future φ) := rfl

/-! #### Grounding in the library's tense cells

On a linear frame the Ockhamist past and future land in the same comparison cells as the rest
of the library's tense: the witness of `past` compares into `⟦Tense.past⟧` against the
evaluation moment, that of `future` into `⟦Tense.future⟧`. On a genuinely branching frame the
comparison lives on each history's own chain order, mathlib's `LinearOrder ↥h`
(`future_atom_iff_holds_on_hist`). -/

@[simp] theorem past_atom_iff_holds {M : Type*} [LinearOrder M]
    (φ : Set M) (m : M) (h : Flag M) :
    (m, h) ∈ past (atom φ) ↔ ∃ m', compare m' m ∈ ⟦Tense.past⟧ ∧ m' ∈ φ := by
  simp only [mem_past, mem_atom, Tense.compare_mem_past]

@[simp] theorem future_atom_iff_holds {M : Type*} [LinearOrder M]
    (φ : Set M) (m : M) (h : Flag M) :
    (m, h) ∈ future (atom φ) ↔ ∃ m' ∈ h, compare m' m ∈ ⟦Tense.future⟧ ∧ m' ∈ φ := by
  simp only [mem_future, mem_atom, Tense.compare_mem_future]

/-- The Ockhamist future along a history is the tense-cell future over the history's own
chain order. -/
theorem future_atom_iff_holds_on_hist {M : Type*} [PartialOrder M]
    [DecidableEq M] [DecidableLE M] [DecidableLT M]
    (φ : Set M) {m : M} {h : Flag M} (hm : m ∈ h) :
    (m, h) ∈ future (atom φ) ↔
      ∃ x : ↥h, compare x ⟨m, hm⟩ ∈ ⟦Tense.future⟧ ∧ (x : M) ∈ φ := by
  simp only [mem_future, mem_atom, Tense.compare_mem_future]
  exact ⟨fun ⟨m', hm', hlt, hφ⟩ ↦ ⟨⟨m', hm'⟩, hlt, hφ⟩, fun ⟨x, hlt, hφ⟩ ↦ ⟨x, x.2, hlt, hφ⟩⟩

end Ockhamist

/-! ### Finite frames

On a finite frame every history is the down-set of a maximal moment
(`Flag.exists_isMax_eq_ofIsMax`), so quantifying over the histories through a moment is
quantifying over the maximal moments above it, and settled future truth is decidable. -/

namespace Peircean

/-- Settled future truth on a finite frame is a search over the maximal moments. -/
theorem mem_future_iff [IsLeftLinear M] [Finite M] {φ : Set M} {m : M} :
    m ∈ future φ ↔ ∀ x, IsMax x → m ≤ x → ∃ m', m < m' ∧ m' ≤ x ∧ m' ∈ φ := by
  have : Nonempty M := ⟨m⟩
  refine Flag.forall_mem_iff.trans ?_
  exact forall_congr' fun x ↦ forall_congr' fun _ ↦ imp_congr_right fun _ ↦
    ⟨fun ⟨m', hm', hlt, hφ⟩ ↦ ⟨m', hlt, hm', hφ⟩, fun ⟨m', hlt, hm', hφ⟩ ↦ ⟨m', hm', hlt, hφ⟩⟩

variable [Fintype M] [DecidableEq M] [DecidableLE M] [DecidableLT M]
  (φ : Set M) [DecidablePred (· ∈ φ)] (m : M)

instance [IsLeftLinear M] : Decidable (m ∈ future φ) :=
  decidable_of_iff _ mem_future_iff.symm

instance : Decidable (m ∈ past φ) := inferInstanceAs (Decidable (∃ m' < m, m' ∈ φ))

end Peircean

end BranchingTime
