import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi

/-!
# The argmax set of a function on a finset

`Finset.argmax s f` is the finset of elements of `s` at which `f` attains its
maximum over `s`. Mathlib has only the tie-breaking `List.argmax : List α →
Option α`; the set-valued form is the natural companion of `Finset.max'` and
`Finset.exists_max_image`, and the carrier for argmax *correspondences*
(set-valued best responses) in game-theoretic consumers.

[UPSTREAM] candidate: `Mathlib.Data.Finset.Max`.

## Main definitions

* `Finset.argmax s f` — the score-maximal elements of `s`.
* `Finset.argmin s f` — the score-minimal elements of `s`.

## Main statements

* `mem_argmax` — membership characterization (simp normal form).
* `argmax_nonempty` — nonempty on nonempty input (via `exists_max_image`).
* `argmax_comp_strictMono` — invariance under strictly monotone rescaling.
-/

namespace Finset

variable {α β γ : Type*} [LinearOrder β] [LinearOrder γ] {s : Finset α}
  {f : α → β} {a : α}

/-- The elements of `s` at which `f` attains its maximum over `s`. -/
def argmax (s : Finset α) (f : α → β) : Finset α :=
  s.filter fun a => ∀ b ∈ s, f b ≤ f a

@[simp]
theorem mem_argmax : a ∈ s.argmax f ↔ a ∈ s ∧ ∀ b ∈ s, f b ≤ f a :=
  mem_filter

theorem argmax_subset : s.argmax f ⊆ s :=
  filter_subset _ _

theorem argmax_nonempty (hs : s.Nonempty) : (s.argmax f).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := s.exists_max_image f hs
  exact ⟨a, mem_argmax.mpr ⟨ha, hmax⟩⟩

/-- The elements of `s` at which `f` attains its minimum over `s`. -/
def argmin (s : Finset α) (f : α → β) : Finset α :=
  s.filter fun a => ∀ b ∈ s, f a ≤ f b

@[simp]
theorem mem_argmin : a ∈ s.argmin f ↔ a ∈ s ∧ ∀ b ∈ s, f a ≤ f b :=
  mem_filter

theorem argmin_subset : s.argmin f ⊆ s :=
  filter_subset _ _

theorem argmin_nonempty (hs : s.Nonempty) : (s.argmin f).Nonempty := by
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image f hs
  exact ⟨a, mem_argmin.mpr ⟨ha, hmin⟩⟩

theorem argmin_eq_argmax_toDual : s.argmin f = s.argmax (OrderDual.toDual ∘ f) :=
  rfl

/-- Scores that order `s` the same way have the same argmax. -/
theorem argmax_congr {f' : α → γ} (h : ∀ a ∈ s, ∀ b ∈ s, f a ≤ f b ↔ f' a ≤ f' b) :
    s.argmax f = s.argmax f' := by
  ext a; simp only [mem_argmax]
  exact and_congr_right λ ha => forall₂_congr λ b hb => h b hb a ha

/-- Scores that order `s` oppositely swap argmin and argmax. -/
theorem argmin_eq_argmax_of_le_iff {f' : α → γ}
    (h : ∀ a ∈ s, ∀ b ∈ s, f a ≤ f b ↔ f' b ≤ f' a) : s.argmin f = s.argmax f' := by
  ext a; simp only [mem_argmin, mem_argmax]
  exact and_congr_right λ ha => forall₂_congr λ b hb => h a ha b hb

/-- A score that is constant on `s` has all of `s` as argmax. -/
theorem argmax_eq_self_of_forall_le (h : ∀ a ∈ s, ∀ b ∈ s, f b ≤ f a) : s.argmax f = s :=
  filter_true_of_mem h

/-- The argmax of a score that is positive on a nonempty `t ⊆ s` and zero on
the rest of `s` is the argmax over `t`. -/
theorem argmax_eq_argmax_of_support [Zero β] {t : Finset α} (hts : t ⊆ s) (hne : t.Nonempty)
    (hpos : ∀ a ∈ t, 0 < f a) (hzero : ∀ a ∈ s, a ∉ t → f a = 0) : s.argmax f = t.argmax f := by
  obtain ⟨a₀, ha₀⟩ := hne
  ext a; simp only [mem_argmax]
  constructor
  · rintro ⟨ha, hmax⟩
    have hat : a ∈ t := by
      by_contra hat
      exact absurd (hmax a₀ (hts ha₀)) (not_le.mpr ((hzero a ha hat).symm ▸ hpos a₀ ha₀))
    exact ⟨hat, λ b hb => hmax b (hts hb)⟩
  · rintro ⟨hat, hmax⟩
    refine ⟨hts hat, λ b hb => ?_⟩
    by_cases hbt : b ∈ t
    · exact hmax b hbt
    · exact (hzero b hb hbt).symm ▸ (hpos a hat).le

/-- The argmax set is invariant under strictly monotone rescaling of the
score — inverse-temperature changes do not move the argmax. -/
theorem argmax_comp_strictMono {g : β → γ} (hg : StrictMono g) :
    s.argmax (g ∘ f) = s.argmax f := by
  ext a
  simp only [mem_argmax, Function.comp_apply, hg.le_iff_le]

@[simp]
theorem argmax_const (c : β) : s.argmax (fun _ => c) = s := by
  ext a
  simp

/-- Membership in an argmax over `univ`, through a surjection: `a` maximizes
`φ ∘ e` iff `e a` maximizes `φ`. Collapses argmax over a function space to
argmax over values when the objective factors through evaluation. -/
theorem mem_argmax_comp_surjective {α' : Type*} [Fintype α] [Fintype α']
    {e : α → α'} (he : Function.Surjective e) (φ : α' → β) {a : α} :
    a ∈ Finset.univ.argmax (φ ∘ e) ↔ e a ∈ Finset.univ.argmax φ := by
  simp only [mem_argmax, Finset.mem_univ, true_and, Function.comp_apply]
  exact ⟨fun h b => (he b).elim fun a' hb => hb ▸ h a',
    fun h a' => h (e a')⟩

/-- Membership in the argmax of a coordinatewise sum over a finite pi type:
`g` maximizes `∑ i, φ i (g i)` iff every coordinate maximizes its own
summand. The additive-separability workhorse for best responses in games. -/
theorem mem_argmax_pi_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : ι → Type*} [∀ i, Fintype (Y i)] {K : Type*} [AddCommMonoid K]
    [LinearOrder K] [IsOrderedCancelAddMonoid K]
    (φ : ∀ i, Y i → K) {g : ∀ i, Y i} :
    g ∈ Finset.univ.argmax (fun g' : (∀ i, Y i) => ∑ i, φ i (g' i)) ↔
      ∀ i, g i ∈ Finset.univ.argmax (φ i) := by
  simp only [mem_argmax, Finset.mem_univ, true_and, true_implies]
  refine ⟨fun h i b => ?_, fun h g' => Finset.sum_le_sum fun i _ => h i (g' i)⟩
  have key := h (Function.update g i b)
  simp only [Function.apply_update (fun k y => φ k y)] at key
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.erase_eq,
    ← Finset.add_sum_erase _ (fun k => φ k (g k)) (Finset.mem_univ i)] at key
  exact le_of_add_le_add_right key

/-- A `Finset.fold max` is attained either at the initial value or at some
element. [UPSTREAM] candidate alongside `argmax`. -/
theorem fold_max_attained (s : Finset α) (f : α → β) (b : β) :
    s.fold max b f = b ∨ ∃ x ∈ s, s.fold max b f = f x := by
  induction s using Finset.cons_induction with
  | empty => left; simp [Finset.fold_empty]
  | cons a s' hna ih =>
    rw [Finset.fold_cons]
    cases ih with
    | inl hb =>
      rw [hb]
      by_cases h : f a ≤ b
      · left; exact max_eq_right h
      · right
        push Not at h
        exact ⟨a, Finset.mem_cons_self a s', max_eq_left (le_of_lt h)⟩
    | inr hex =>
      obtain ⟨x, hx, hfx⟩ := hex
      rw [hfx]
      by_cases h : f a ≤ f x
      · right; exact ⟨x, Finset.mem_cons_of_mem hx, max_eq_right h⟩
      · right
        push Not at h
        exact ⟨a, Finset.mem_cons_self a s', max_eq_left (le_of_lt h)⟩

end Finset
