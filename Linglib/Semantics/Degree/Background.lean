module

public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Degree.Measure.Basic

/-!
# Background orderings and threshold properties

In the states-based analysis of gradable predicates of [cariani-santorio-wellwood-2023], which
builds on the comparative of [wellwood-2015] and which [cariani-santorio-wellwood-2024] apply
to confidence reports, a gradable predicate contributes two things: a background ordering of
states, the states of having some heat for *hot*, and in each context a threshold property, the
states that count as hot. The positive form says that the subject holds a state with the
threshold property. The comparative bypasses the threshold: an admissible measure of one of
the subject's states exceeds the greatest degree of the standard's. No covert positive morpheme
is needed, and neither form entails the other.

The background is a preorder `S` and a threshold property is an upper set `T` of it, the
monotonicity postulate of the analysis. A map `ρ : S → X` sends each state to its holder, or to
its theme, so the positive form of `x` is `x ∈ ρ '' T`, and the comparative of `a` over `b` is
`Degree.maxComparative (ρ · = a) (ρ · = b) μ` for an admissible measure `μ`. This file adds no
definitions. It records how the two components interact: the one inference from a comparative
to a positive form, upward monotonicity, holds on a total background and on no other.

## Main results

* `mem_image_of_maxComparative`: if `b` has the property and `a` has more of it than `b`, then
  `a` has the property, given an admissible measure and a total background.
* `not_mem_image_Ici_of_not_le`: on a non-total background, any two states outside the ordering
  that the measure separates refute upward monotonicity.
* `maxComparative_and_not_mem_image`: the comparative does not entail the positive form.

The comparisons with delineation semantics and with the degree-threshold positive form are in
`Semantics/Degree/Hom.lean`.

## References

* [cariani-santorio-wellwood-2023]
* [cariani-santorio-wellwood-2024]
* [wellwood-2015]
-/

@[expose] public section

namespace Degree

open Set

variable {S X D : Type*} [Preorder S] [Preorder D] {ρ : S → X} {μ : S → D} {T : Set S}

/-! ### Upward monotonicity -/

/-- Upward monotonicity: if `b` has the property and `a` has more of it than `b`, then `a` has
the property. The comparative supplies a state of `a`'s measuring above a state of `b`'s with the
property, an admissible measure on a total background places it above that state, and the
threshold is upward closed. -/
theorem mem_image_of_maxComparative [@Std.Total S (· ≤ ·)] (hT : IsUpperSet T)
    (hμ : StrictMono μ) {a b : X} (hb : b ∈ ρ '' T)
    (h : maxComparative (ρ · = a) (ρ · = b) μ) : a ∈ ρ '' T :=
  let ⟨_, hs, hsb⟩ := hb
  let ⟨y, hya, hlt⟩ := h.exists_lt hsb
  ⟨y, hT (hμ.reflect_le hlt.le) hs, hya⟩

/-- Without admissibility upward monotonicity fails even on a total background: on `Bool` with
the measure reversed, `true` has the property `Ici true` and `false` measures above it. -/
example :
    (true : Bool) ∈ id '' Ici true ∧ maxComparative (· = false) (· = true) (fun b : Bool ↦ !b) ∧
      false ∉ id '' Ici true := by
  refine ⟨⟨true, mem_Ici.2 le_rfl, rfl⟩, (maxComparative_eq_iff _ _ _).2 (by decide), ?_⟩
  rintro ⟨u, hu, rfl⟩
  exact absurd (mem_Ici.1 hu) (by decide)

/-- Without totality upward monotonicity fails: when `s` and `t` are the only states of their
holders, `s` is not below `t` but measures below it, and the property is the one of lying above
`s`, the holder of `s` has the property and the holder of `t` has more of it without having it. -/
theorem not_mem_image_Ici_of_not_le {s t : S} (hst : ¬ s ≤ t) (hlt : μ s < μ t)
    (hs : ∀ u, ρ u = ρ s → u = s) (ht : ∀ u, ρ u = ρ t → u = t) :
    ρ s ∈ ρ '' Ici s ∧ maxComparative (ρ · = ρ t) (ρ · = ρ s) μ ∧ ρ t ∉ ρ '' Ici s :=
  ⟨⟨s, mem_Ici.2 le_rfl, rfl⟩,
    (maxComparative_unique (Pmatrix := (ρ · = ρ t)) (Pthan := (ρ · = ρ s)) rfl ht rfl hs).2 hlt,
    fun ⟨u, hu, hut⟩ ↦ hst (ht u hut ▸ hu)⟩

/-- The failure is realized by an admissible measure: on the componentwise order of `ℕ × ℕ`,
the sum of the coordinates is admissible and puts `(1, 0)` below the incomparable `(0, 2)`. -/
example :
    StrictMono (fun x : ℕ × ℕ ↦ x.1 + x.2) ∧ ¬ ((1, 0) : ℕ × ℕ) ≤ (0, 2) ∧
      (1, 0).1 + (1, 0).2 < (0, 2).1 + (0, 2).2 := by
  refine ⟨fun x y hxy ↦ ?_, by decide, by decide⟩
  rcases Prod.lt_iff.1 hxy with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> dsimp only <;> omega

/-! ### The comparative and the positive form -/

omit [Preorder S] in
/-- The comparative does not entail the positive form: when `s` and `t` are the only states of
their holders and `s` measures above `t` without the property, the holder of `s` has more of it
than the holder of `t` without having it. -/
theorem maxComparative_and_not_mem_image {s t : S} (hlt : μ t < μ s) (hsT : s ∉ T)
    (hs : ∀ u, ρ u = ρ s → u = s) (ht : ∀ u, ρ u = ρ t → u = t) :
    maxComparative (ρ · = ρ s) (ρ · = ρ t) μ ∧ ρ s ∉ ρ '' T :=
  ⟨(maxComparative_unique (Pmatrix := (ρ · = ρ s)) (Pthan := (ρ · = ρ t)) rfl hs rfl ht).2 hlt,
    fun ⟨u, hu, hus⟩ ↦ hsT (hs u hus ▸ hu)⟩

end Degree
