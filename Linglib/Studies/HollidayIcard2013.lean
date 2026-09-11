import Linglib.Logic.ComparativeProbability.Entailments
import Linglib.Core.Order.Probability.Completeness

/-!
# Holliday and Icard (2013): Measure semantics and qualitative semantics for epistemic modals

This file formalizes [holliday-icard-2013]'s comparison of semantics for the comparative
epistemic modal *at least as likely as* against the inference patterns of Figure 1, the
intuitively valid V1–V13 and invalid I1–I3 of [yalcin-2010]. [kratzer-1991]'s world-ordering
semantics lifts a preorder on worlds to propositions by [lewis-1973]'s l-lifting, which validates
the invalid patterns and misses V11 and V13 (`lLift_validities`, `disjunction_problem`): from
*φ ⩾ ψ* and *φ ⩾ χ* it licenses *φ ⩾ ψ ∨ χ*. The k-lifting of [kratzer-2012] does no better
when the compared propositions are disjoint (`kLift_rightUnion_of_disjoint`). Finitely additive
measures validate exactly the intended patterns, but so do the paper's two qualitative
alternatives: qualitatively additive measures, whose logic FA is complete by representation, and
the m-lifting, which asks for an injection from the ways one proposition can happen into the
ways the other can (`mLift_validities`) and which is sound for any measure that agrees with the
world ordering on singletons (`measure_le_of_matchingLift`).

What separates FA from finite additivity is [kraft-pratt-seidenberg-1959]'s ordering on five
worlds, which the paper phrases as the World Cup comparisons (3)–(6): no finitely additive
measure satisfies all four (`worldCup_not_finitelyAdditive`), while orders on fewer than five
worlds are always representable (`fa_representable_iff_card_lt_five`). The paper doubts that
speakers find (3)–(6) inconsistent, and concludes that finite additivity cannot be motivated
from intuitive entailments.

## Implementation notes

* The patterns, both liftings and the measure classes are substrate; the facts here bundle the
  substrate lemmas at the paper's granularity. V8–V10 are omitted, as in Figure 1.
* The completeness theorems are represented by the model-theoretic results they rest on:
  Theorem 2 by `dominationLift_repr_iff` ([halpern-2003]), Theorem 6 by
  `exists_qualAddMeasure_repr` ([van-der-hoek-1996]), Theorem 8 by the Kraft–Pratt–Seidenberg
  representation theorems. Theorems 3–5 and 7 and Fact 4 concern the logics themselves and are
  not formalized.
* Figure 7's chain of four worlds illustrates the two liftings: both make `{a, b}` more likely
  than `{b, c}`, only the l-lifting makes `{a}` more likely than `{b, c}`.

## TODO

* The FA-consistency of (3)–(6) is witnessed by the Kraft–Pratt–Seidenberg order of the
  substrate under a different labelling of the worlds; state it for the World Cup labelling.

## References

* [holliday-icard-2013]
* [yalcin-2010]
* [kratzer-1991]
* [kratzer-2012]
* [lewis-1973]
* [halpern-2003]
* [van-der-hoek-1996]
* [kraft-pratt-seidenberg-1959]
-/

namespace HollidayIcard2013

open ComparativeProbability
open scoped ComparativeProbability.QualitativeProbability

variable {W : Type*}

/-! ### Fact 1: Kratzer's world-ordering semantics -/

/-- **Fact 1**, validities: over a nonempty preorder on worlds the l-lifting validates V1–V7 and
V12. -/
theorem lLift_validities [Nonempty W] (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    patternV1 (dominationLift ge_w) ∧ patternV2 (dominationLift ge_w) ∧
      patternV3 (dominationLift ge_w) ∧ patternV4 (dominationLift ge_w) ∧
      patternV5 (dominationLift ge_w) ∧ patternV6 (dominationLift ge_w) ∧
      patternV7 (dominationLift ge_w) ∧ patternV12 (dominationLift ge_w) :=
  ⟨dominationLift_V1 ge_w, dominationLift_V2 ge_w, dominationLift_V3 ge_w,
    dominationLift_V4 ge_w, dominationLift_V5 ge_w hRefl, dominationLift_V6 ge_w,
    dominationLift_V7 ge_w, dominationLift_V12 ge_w hTrans⟩

/-- **Fact 1**, the disjunction problem: the l-lifting of any reflexive world order validates
the three measure-invalid patterns I1–I3. -/
theorem disjunction_problem (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w) :
    patternI1 (dominationLift ge_w) ∧ patternI2 (dominationLift ge_w) ∧
      patternI3 (dominationLift ge_w) :=
  ⟨dominationLift_I1 ge_w, dominationLift_I2 ge_w hRefl, dominationLift_I3 ge_w hRefl⟩

/-- **Fact 1**, the missing validities: the l-lifting refutes V11 and V13. -/
theorem lLift_refutes_V11_V13 :
    (∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternV11 (dominationLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternV13 (dominationLift ge_w)) :=
  ⟨dominationLift_not_V11, dominationLift_not_V13⟩

/-- [kratzer-2012]'s k-lifting: `A` is at least as likely as `B` unless some world in `B`
outside `A` strictly dominates every world in `A` outside `B`. -/
def kLift (ge_w : W → W → Prop) (A B : Set W) : Prop :=
  ¬ ∃ b ∈ B \ A, ∀ a ∈ A \ B, ge_w b a ∧ ¬ ge_w a b

/-- Lassiter's observation reported in the paper: when the `φ`-worlds are disjoint from the
`ψ`- and `χ`-worlds, the k-lifting still validates the J axiom behind the disjunction
problem. -/
theorem kLift_rightUnion_of_disjoint (ge_w : W → W → Prop) {A B C : Set W}
    (hB : Disjoint A B) (hC : Disjoint A C) (hAB : kLift ge_w A B) (hAC : kLift ge_w A C) :
    kLift ge_w A (B ∪ C) := by
  rintro ⟨b, ⟨hb | hb, hbA⟩, hall⟩
  · exact hAB ⟨b, ⟨hb, hbA⟩, λ a ha =>
      hall a ⟨ha.1, λ h => h.elim (Set.disjoint_left.mp hB ha.1) (Set.disjoint_left.mp hC ha.1)⟩⟩
  · exact hAC ⟨b, ⟨hb, hbA⟩, λ a ha =>
      hall a ⟨ha.1, λ h => h.elim (Set.disjoint_left.mp hB ha.1) (Set.disjoint_left.mp hC ha.1)⟩⟩

/-! ### Facts 2 and 3: finitely and qualitatively additive measures -/

section Measures

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Fact 2**, validities: every finitely additive measure validates V1–V13. -/
theorem measure_validities (m : FinAddMeasure K W) :
    patternV1 m.inducedGe ∧ patternV2 m.inducedGe ∧ patternV3 m.inducedGe ∧
      patternV4 m.inducedGe ∧ patternV5 m.inducedGe ∧ patternV6 m.inducedGe ∧
      patternV7 m.inducedGe ∧ patternV11 m.inducedGe ∧ patternV12 m.inducedGe ∧
      patternV13 m.inducedGe :=
  ⟨patternV1_holds, patternV2_of, patternV3_of, patternV4_of, patternV5_of, patternV6_of,
    patternV7_of, patternV11_of, patternV12_of, patternV13_of⟩

/-- **Fact 2**, invalidities: the uniform measure on three worlds refutes each of I1–I3. -/
theorem measures_refute_I_patterns :
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬patternI1 m.inducedGe) ∧
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬patternI2 m.inducedGe) ∧
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬patternI3 m.inducedGe) :=
  ⟨measure_not_I1, measure_not_I2, measure_not_I3⟩

/-- **Fact 3**, validities: qualitative additivity already yields V1–V13. -/
theorem qualAddMeasure_validities (m : QualAddMeasure K W) :
    patternV1 m.inducedGe ∧ patternV2 m.inducedGe ∧ patternV3 m.inducedGe ∧
      patternV4 m.inducedGe ∧ patternV5 m.inducedGe ∧ patternV6 m.inducedGe ∧
      patternV7 m.inducedGe ∧ patternV11 m.inducedGe ∧ patternV12 m.inducedGe ∧
      patternV13 m.inducedGe :=
  ⟨patternV1_holds, patternV2_of, patternV3_of, patternV4_of, patternV5_of, patternV6_of,
    patternV7_of, patternV11_of, patternV12_of, patternV13_of⟩

/-- **Fact 3**, invalidities: the uniform measure, read as a qualitatively additive measure,
refutes each of I1–I3. -/
theorem qualAddMeasures_refute_I_patterns :
    (∃ m : QualAddMeasure ℚ (Fin 3), ¬patternI1 m.inducedGe) ∧
    (∃ m : QualAddMeasure ℚ (Fin 3), ¬patternI2 m.inducedGe) ∧
    (∃ m : QualAddMeasure ℚ (Fin 3), ¬patternI3 m.inducedGe) :=
  ⟨let ⟨m, hm⟩ := measure_not_I1; ⟨m.toQualAdd, hm⟩,
    let ⟨m, hm⟩ := measure_not_I2; ⟨m.toQualAdd, hm⟩,
    let ⟨m, hm⟩ := measure_not_I3; ⟨m.toQualAdd, hm⟩⟩

/-- **Theorem 6** ([van-der-hoek-1996]): every FA order on a finite carrier is represented by a
qualitatively additive measure. -/
theorem fa_qualAdd_complete [Fintype W] (sys : QualitativeProbability (Set W)) :
    ∃ m : QualAddMeasure ℚ W, ∀ A B, A ≿[sys] B ↔ m.inducedGe A B :=
  let ⟨m, hm⟩ := exists_qualAddMeasure_repr sys
  ⟨m, λ A B => hm B A⟩

end Measures

/-! ### Fact 5: the m-lifting -/

/-- **Fact 5**, validities: on a finite nonempty preorder the m-lifting validates V1–V7 and
V11–V13. -/
theorem mLift_validities [Finite W] [Nonempty W] (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w) (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    patternV1 (matchingLift ge_w) ∧ patternV2 (matchingLift ge_w) ∧
      patternV3 (matchingLift ge_w) ∧ patternV4 (matchingLift ge_w) ∧
      patternV5 (matchingLift ge_w) ∧ patternV6 (matchingLift ge_w) ∧
      patternV7 (matchingLift ge_w) ∧ patternV11 (matchingLift ge_w) ∧
      patternV12 (matchingLift ge_w) ∧ patternV13 (matchingLift ge_w) :=
  ⟨matchingLift_V1 ge_w, matchingLift_V2 ge_w, matchingLift_V3 ge_w, matchingLift_V4 ge_w,
    matchingLift_V5 ge_w hRefl, matchingLift_V6 ge_w, matchingLift_V7 ge_w,
    matchingLift_V11 ge_w hRefl hTrans, matchingLift_V12 ge_w hRefl hTrans,
    matchingLift_V13 ge_w hRefl⟩

/-- **Fact 5**, invalidities: the m-lifting refutes I1–I3, dissolving the disjunction
problem. -/
theorem mLift_refutes_I_patterns :
    (∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI1 (matchingLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI2 (matchingLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI3 (matchingLift ge_w)) :=
  ⟨matchingLift_not_I1, matchingLift_not_I2, matchingLift_not_I3⟩

/-- Footnote 13: if the world ordering agrees with a finitely additive measure on singletons,
the m-lifting is sound for the measure order, since the injection carries the sum of the
singleton masses of `B` into a sum over a subset of `A`. -/
theorem measure_le_of_matchingLift {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Fintype W] (m : FinAddMeasure K W) (ge_w : W → W → Prop)
    (h : ∀ v u, ge_w v u ↔ m {u} ≤ m {v}) {A B : Set W} (hAB : matchingLift ge_w A B) :
    m B ≤ m A := by
  classical
  obtain ⟨f, hf, hinj⟩ := hAB
  calc m B = ∑ b ∈ B.toFinset, m {b} := by rw [m.sum_mu_singleton, Set.coe_toFinset]
    _ ≤ ∑ b ∈ B.toFinset, m {f b} :=
        Finset.sum_le_sum λ b hb => (h _ _).mp (hf b (Set.mem_toFinset.mp hb)).2
    _ = ∑ a ∈ B.toFinset.image f, m {a} := by
        rw [Finset.sum_image λ x hx y hy hxy =>
          hinj x y (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy) hxy]
    _ = m ↑(B.toFinset.image f) := m.sum_mu_singleton _
    _ ≤ m A := m.mu_mono λ a ha => by
        rw [Finset.coe_image, Set.coe_toFinset] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        exact (hf b hb).1

/-! ### Figure 7: the chain `a ≻ b ≻ c ≻ d`

Worlds are `Fin 4`, with `0` the best; `ge_w u v` is `u ≤ v`. -/

/-- Both liftings make `{a, b}` more likely than `{b, c}`. -/
theorem chain_pair_gt_pair :
    Strict (matchingLift (· ≤ · : Fin 4 → Fin 4 → Prop)) {0, 1} {1, 2} ∧
      Strict (dominationLift (· ≤ · : Fin 4 → Fin 4 → Prop)) {0, 1} {1, 2} := by
  have hm : matchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {0, 1} {1, 2} :=
    ⟨λ b => b - 1, λ b hb => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl <;> decide, λ b₁ b₂ hb₁ hb₂ hf => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb₁ hb₂
      rcases hb₁ with rfl | rfl <;> rcases hb₂ with rfl | rfl <;>
        first | rfl | exact absurd hf (by decide)⟩
  have hl : ¬ dominationLift (· ≤ · : Fin 4 → Fin 4 → Prop) {1, 2} {0, 1} := by
    intro hd
    obtain ⟨a, ha, hle⟩ := hd 0 (Set.mem_insert 0 {1})
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> exact absurd hle (by decide)
  exact ⟨⟨hm, λ h => hl (matchingLift_implies_dominationLift h)⟩,
    ⟨matchingLift_implies_dominationLift hm, hl⟩⟩

/-- Only the l-lifting makes `{a}` more likely than `{b, c}`: the m-lifting leaves the two
incomparable, since two worlds cannot be matched injectively into one. -/
theorem chain_singleton_vs_pair :
    Strict (dominationLift (· ≤ · : Fin 4 → Fin 4 → Prop)) {0} {1, 2} ∧
      ¬ matchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {0} {1, 2} ∧
      ¬ matchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {1, 2} {0} := by
  refine ⟨⟨λ b hb => ⟨0, rfl, Fin.zero_le b⟩, λ hd => ?_⟩, ?_, ?_⟩
  · obtain ⟨a, ha, hle⟩ := hd 0 rfl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> exact absurd hle (by decide)
  · rintro ⟨f, hf, hinj⟩
    have h1 := (hf 1 (Set.mem_insert 1 {2})).1
    have h2 := (hf 2 (Set.mem_insert_of_mem 1 rfl)).1
    rw [Set.mem_singleton_iff] at h1 h2
    exact absurd (hinj 1 2 (Set.mem_insert 1 {2}) (Set.mem_insert_of_mem 1 rfl) (h1.trans h2.symm))
      (by decide)
  · rintro ⟨f, hf, -⟩
    obtain ⟨hmem, hle⟩ := hf 0 rfl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h <;> rw [h] at hle <;> exact absurd hle (by decide)

/-! ### Theorem 8: what separates FA from finite additivity -/

/-- **Theorem 8** ([kraft-pratt-seidenberg-1959]): every FA order on `Fin n` is representable
by a finitely additive measure iff `n < 5`. -/
theorem fa_representable_iff_card_lt_five (n : ℕ) :
    (∀ sys : QualitativeProbability (Set (Fin n)), Representable sys) ↔ n < 5 :=
  ⟨λ h => by_contra λ hge =>
      let ⟨sys, hsys⟩ := exists_nonrepresentable_fin (n := n) (by omega); hsys (h sys),
    λ h sys => representable_of_card_lt_five sys (by simpa using h)⟩

/-- The World Cup comparisons (3)–(6), with Argentina, Brazil, China, Denmark and England as
the worlds `0`–`4`: no finitely additive measure makes Argentina-or-England more likely than
China-or-Denmark, Brazil-or-China more likely than Argentina-or-Denmark, Denmark more likely
than Argentina-or-China, and Argentina-or-China-or-Denmark more likely than Brazil-or-England,
because the four left-hand sides and the four right-hand sides have the same total mass. -/
theorem worldCup_not_finitelyAdditive (m : FinAddMeasure ℚ (Fin 5)) :
    ¬ (Strict m.inducedGe {0, 4} {2, 3} ∧ Strict m.inducedGe {1, 2} {0, 3} ∧
      Strict m.inducedGe {3} {0, 2} ∧ Strict m.inducedGe {0, 2, 3} {1, 4}) := by
  have pair : ∀ a b : Fin 5, a ≠ b → m {a, b} = m {a} + m {b} := λ a b hab => by
    rw [Set.insert_eq, m.additive (Set.disjoint_singleton.mpr hab)]
  have triple : m ({0, 2, 3} : Set (Fin 5)) = m {0} + m {2} + m {3} := by
    rw [Set.insert_eq, m.additive (Set.disjoint_singleton_left.mpr (by simp)), pair 2 3 (by decide),
      add_assoc]
  simp only [Strict, FinAddMeasure.inducedGe, ge_iff_le, not_le, triple,
    pair 0 4 (by decide), pair 2 3 (by decide), pair 1 2 (by decide), pair 0 3 (by decide),
    pair 0 2 (by decide), pair 1 4 (by decide)]
  intro ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩, ⟨_, h4⟩⟩
  linarith

end HollidayIcard2013
