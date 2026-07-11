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

## Main statements

* `mem_argmax` — membership characterization (simp normal form).
* `argmax_nonempty` — nonempty on nonempty input (via `exists_max_image`).
* `argmax_comp_strictMono` — invariance under strictly monotone rescaling.
-/

set_option autoImplicit false

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
