module

public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Quantification.Counting
public import Mathlib.Data.Fin.VecNotation

/-!
# Heim (2001): Degree Operators and Scope

This file formalizes [heim-2001], the question of how far a degree phrase moves at LF, put to
the max semantics of the comparative: *-er than t* says that the greatest degree of its
argument exceeds *t*, `Degree.maxIn (Ioi t)`, and a DegP scopes under a quantifier or over it,
`Degree.lowScope` and `Degree.highScope`. Over a monotone increasing quantifier on a finite
domain the two scopes coincide and under a monotone decreasing one the maximum is undefined,
so the *exactly*-differential and *less*, whose intervals are not upper sets, are the
diagnostic cases: under *every girl* their high scope is a weaker reading the sentence lacks,
which Kennedy's generalization, the Heim–Kennedy constraint `Minimalist.IsHeimKennedy`,
excludes, while over the intensional verbs both scopes are attested. For the neg-raising verbs
the maximum redefined as the greatest lower bound of the false degrees collapses the scopes
(`negRaising_collapse`), and *-est*, using its complement twice, is the absolute superlative
(`est_iff_absoluteSuperlative`).

## Implementation notes

* Quantifiers over individuals and over worlds are the same `Quantifier.NP`, so
  the intensional cases of Sections 2.1 and 2.3 are the theorems at a type of worlds.
* A high-scope truth condition carries the definedness presupposition of the maximum as an
  existence conjunct; the paper's undefined maxima are the negations of those conjuncts.
* The de re and de dicto than-clauses of Section 2.4 are [von-stechow-1984]'s diagnosis and
  are formalized in `Studies/VonStechow1984.lean`; the examples are typed in
  `Data/Examples/Heim2001.json`.

## References

* [heim-2001]
* [von-stechow-1984]
* [heim-1999]
-/

@[expose] public section

namespace Heim2001

open Degree Quantifier Quantifier.GQ Set

variable {Entity W D : Type*} [LinearOrder D]

/-! ### Monotone increasing quantifiers -/

/-- On a finite domain the two scopes of an upper-interval DegP under *every girl* coincide, the
comparative (10) at `Ioi t`, the equative (13a) at `Ici t`, and, at a type of worlds, the
necessity operator (16) (Section 2.1). -/
theorem forall_collapse [Finite Entity] {girl : Entity → Prop} (hg : ∃ x, girl x)
    (μ : Entity → D) {U : Set D} (hU : IsUpperSet U) :
    highScope (maxIn U) (every girl) μ ↔ lowScope (maxIn U) (every girl) μ :=
  highScope_maxIn_iff_lowScope (monotone_every girl) (λ h => let ⟨x, hx⟩ := hg; h x hx) hU

/-- Likewise under *some girl*, (12), (13b), and the possibility operator (15b). -/
theorem exists_collapse [Finite Entity] (girl : Entity → Prop) (μ : Entity → D) {U : Set D}
    (hU : IsUpperSet U) :
    highScope (maxIn U) (GQ.some girl) μ ↔ lowScope (maxIn U) (GQ.some girl) μ :=
  highScope_maxIn_iff_lowScope (monotone_some girl) (λ ⟨_, _, h⟩ => h) hU

/-! ### Monotone decreasing and non-monotone operators -/

/-- The degrees to which Mary is not tall have no maximum (17c). -/
theorem negation_high_undefined [NoMaxOrder D] (μ : Entity → D) (a : Entity) :
    ¬ ∃ m, IsGreatest (scopeDegrees (λ S => ¬ S a) μ) m :=
  not_isGreatest_scopeDegrees (Q := λ S => ¬ S a) (λ _ _ h hT hS => hT (h a hS)) μ

/-- The degrees to which at most two girls are tall have no maximum (18c). -/
theorem atMost_high_undefined [Fintype Entity] [NoMaxOrder D] (girl : Entity → Prop)
    (μ : Entity → D) : ¬ ∃ m, IsGreatest (scopeDegrees (atMost 2 girl) μ) m :=
  not_isGreatest_scopeDegrees (antitone_atMost (α := Entity) 2 girl) μ

/-- The maximal degree to which exactly two girls are tall, when defined, is the maximal degree
to which at least two are, so the high scope (20c) means *at least two girls are taller than 5
feet* (20). -/
theorem exactly_high_atLeast [Fintype Entity] {girl : Entity → Prop} {μ : Entity → D} {m : D}
    (h : IsGreatest (scopeDegrees (exactly 2 girl) μ) m) :
    IsGreatest (scopeDegrees (atLeast 2 girl) μ) m := by
  rw [exactly_eq_atLeast_inf_atMost] at h
  exact isGreatest_scopeDegrees_of_inf (antitone_atMost 2 girl) h

/-! ### Exactly-differentials and less -/

/-- Under *every girl* the low scope entails the high one at every interval, the shortest girl
attaining the maximum, so (22c) is weaker than (22b) at `{t}`, (24c) than (24b) at `Iio t`,
and at a type of worlds (28c) than (28b) and (30c) than (30b). -/
theorem forall_high_of_low [Finite Entity] {girl : Entity → Prop} (hg : ∃ x, girl x)
    (μ : Entity → D) (U : Set D) :
    lowScope (maxIn U) (every girl) μ → highScope (maxIn U) (every girl) μ :=
  have : Nonempty {x // girl x} := let ⟨x, hx⟩ := hg; ⟨⟨x, hx⟩⟩
  let ⟨⟨x₀, hx₀⟩, hmin⟩ := Finite.exists_min λ x : {x // girl x} => μ x.1
  highScope_every_of_lowScope ⟨x₀, hx₀, λ y hy => hmin ⟨y, hy⟩⟩

/-- Under *some girl* the high scope entails the low one at every interval, the tallest girl
being a witness, so (21c) is stronger than (21b), and at a type of worlds (29c) than (29b)
and (31c) than (31b). -/
theorem exists_low_of_high (girl : Entity → Prop) (μ : Entity → D) (U : Set D) :
    highScope (maxIn U) (GQ.some girl) μ → lowScope (maxIn U) (GQ.some girl) μ :=
  lowScope_some_of_highScope

/-- For two girls, one exactly the standard's height in inches and one taller, the degrees to
which every girl is tall are those up to the shorter. -/
private theorem scopeDegrees_heights :
    scopeDegrees (every λ _ : Fin 2 => True) ![49, 50] = Iic 49 := by
  ext d
  simp [scopeDegrees, every, Fin.forall_fin_two]
  omega

/-- The high scope is true and the low scope false when the shortest girl is exactly 4'1'' and
another is taller, so *every girl is exactly 1'' taller than that* is false there and (22c) is
no reading of it (22). -/
theorem exactly_high_not_low :
    highScope (maxIn {49}) (every λ _ : Fin 2 => True) ![49, 50] ∧
      ¬ lowScope (maxIn {49}) (every λ _ : Fin 2 => True) ![49, 50] :=
  ⟨⟨49, rfl, scopeDegrees_heights ▸ isGreatest_Iic⟩,
    λ h => by simpa using lowScope_maxIn.1 h 1 trivial⟩

/-- The high scope of *every girl is less tall than that* says only that the shortest girl is,
and is true where the sentence is false (24). -/
theorem less_high_not_low :
    highScope (maxIn (Iio 50)) (every λ _ : Fin 2 => True) ![49, 50] ∧
      ¬ lowScope (maxIn (Iio 50)) (every λ _ : Fin 2 => True) ![49, 50] :=
  ⟨⟨49, by decide, scopeDegrees_heights ▸ isGreatest_Iic⟩,
    λ h => by simpa using lowScope_maxIn.1 h 1 trivial⟩

/-! ### Intensional verbs -/

/-- *The paper is required to be less long than t* with the DegP over *required* says that the
paper is not required to be as long as *t* (30c). -/
theorem required_less [Finite W] {Acc : Set W} (hAcc : Acc.Nonempty) (ℓ : W → D) (t : D) :
    highScope (maxIn (Iio t)) (every (· ∈ Acc)) ℓ ↔ ¬ every (· ∈ Acc) λ w => t ≤ ℓ w := by
  have : Nonempty W := hAcc.to_type
  obtain ⟨w₀, hw₀⟩ := Finite.exists_min ℓ
  exact highScope_maxIn_Iio_iff (monotone_every _) (λ h => let ⟨w, hw⟩ := hAcc; h w hw)
    ⟨ℓ w₀, λ v _ => hw₀ v⟩

/-- *The paper is allowed to be less long than t* with the DegP over *allowed* says that the
paper is not allowed to be as long as *t* (31c). -/
theorem allowed_less [Finite W] {Acc : Set W} (hAcc : Acc.Nonempty) (ℓ : W → D) (t : D) :
    highScope (maxIn (Iio t)) (GQ.some (· ∈ Acc)) ℓ ↔ ¬ GQ.some (· ∈ Acc) λ w => t ≤ ℓ w :=
  highScope_maxIn_Iio_iff (monotone_some _) (λ ⟨_, _, h⟩ => h)
    (let ⟨w, hw⟩ := hAcc; ⟨ℓ w, w, hw, le_rfl⟩)

/-- With the maximum of (35), *I want the paper to be less long than t* with the DegP over
*want* says that the greatest lower bound of the lengths the paper is desired not to have,
those no desired world reaches, is below *t*, which is the low-scope reading (36a). -/
theorem negRaising_collapse [Finite W] [DenselyOrdered D] {Des : Set W} (hDes : Des.Nonempty)
    (ℓ : W → D) (t : D) :
    (∃ m ∈ Iio t, IsGLB (scopeDegrees (no (· ∈ Des)) ℓ) m) ↔
      lowScope (maxIn (Iio t)) (every (· ∈ Des)) ℓ := by
  have hex : ∃ m, IsGreatest (scopeDegrees (GQ.some (· ∈ Des)) ℓ) m :=
    let ⟨w, hw⟩ := exists_isGreatest_scopeDegrees (monotone_some _) (λ ⟨_, _, h⟩ => h)
      (let ⟨w, hw⟩ := hDes; ⟨ℓ w, w, hw, le_rfl⟩)
    ⟨_, hw⟩
  rw [scopeDegrees_no, lowScope_maxIn]
  refine (exists_congr λ m => and_congr_right λ _ =>
    isGLB_compl_scopeDegrees_iff (monotone_some _) hex).trans
    ((allowed_less hDes ℓ t).trans ?_)
  exact not_exists.trans (forall_congr' λ _ => not_and.trans (imp_congr_right λ _ => not_le))

/-! ### The superlative -/

/-- The entry for *-est* (59a), `λx. max{d : R(x, d)} > max{d : ∃y ≠ x. R(y, d)}`, over a
monotone adjective and a comparison class `C` is the max-quantified comparative of `x` against
the other members. -/
def est (μ : Entity → D) (C : Set Entity) (x : Entity) : Prop :=
  maxComparative (· = x) (λ y => y ∈ C ∧ y ≠ x) μ

/-- Over a comparison class with someone else in it, *-est* is the absolute superlative (59). -/
theorem est_iff_absoluteSuperlative [Finite Entity] {μ : Entity → D} {C : Set Entity}
    {x : Entity} (hx : x ∈ C) (hC : ∃ y ∈ C, y ≠ x) : est μ C x ↔ absoluteSuperlative μ C x := by
  have h := highScope_maxIn_Iio_iff (μ := μ) (t := μ x) (monotone_some λ y => y ∈ C ∧ y ≠ x)
    (λ ⟨_, _, h⟩ => h) (let ⟨y, hy, hyx⟩ := hC; ⟨μ y, y, ⟨hy, hyx⟩, le_rfl⟩)
  refine (⟨λ ⟨δ, hδ, _, rfl, hlt⟩ => ⟨δ, hlt, hδ⟩, λ ⟨δ, hlt, hδ⟩ => ⟨δ, hδ, x, rfl, hlt⟩⟩ :
    est μ C x ↔ highScope (maxIn (Iio (μ x))) (GQ.some λ y => y ∈ C ∧ y ≠ x) μ).trans
    (h.trans (Iff.trans ?_ (and_iff_right hx).symm))
  exact not_exists.trans (forall_congr' λ _ => not_and.trans (and_imp.trans
    (imp_congr_right λ _ => imp_congr_right λ _ => not_le)))

end Heim2001
