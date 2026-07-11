import Mathlib.Data.Finset.Max

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
