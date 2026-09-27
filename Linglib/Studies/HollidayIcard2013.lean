module

public import Linglib.Logic.ComparativeProbability.WorldOrdering
public import Linglib.Logic.ComparativeProbability.Patterns
public import Linglib.Core.Order.Probability.Completeness
public import Linglib.Logic.ComparativeProbability.Defs

/-!
# Holliday and Icard (2013): Measure semantics and qualitative semantics for epistemic modals

This file formalizes [holliday-icard-2013]'s comparison of semantics for the comparative
epistemic modal *at least as likely as* against the inference patterns of Figure 1, the
intuitively valid V1–V13 and invalid I1–I3 of [yalcin-2010]. [kratzer-1991]'s world-ordering
semantics lifts a preorder on worlds to propositions by [lewis-1973]'s l-lifting, which validates
the invalid patterns and misses V11 and V13 (`lLift_validities`, `disjunction_problem`,
`lLift_refutes_V11_V13`): from *φ ⩾ ψ* and *φ ⩾ χ* it licenses *φ ⩾ ψ ∨ χ*. The k-lifting of
[kratzer-2012] does no better when the compared propositions are disjoint
(`kratzerLift_rightUnion_of_disjoint`). Finitely additive measures validate exactly the intended
patterns, but so do the paper's two qualitative alternatives: qualitatively additive measures,
whose logic FA is complete by representation, and the m-lifting, which asks for an injection from
the ways one proposition can happen into the ways the other can (`mLift_validities`,
`mLift_refutes_I_patterns`) and which is sound for any measure that agrees with the world
ordering on singletons (`measure_le_of_matchingLift`).

What separates FA from finite additivity is [kraft-pratt-seidenberg-1959]'s ordering on five
worlds, which the paper phrases as the World Cup comparisons (3)–(6): no finitely additive
measure satisfies all four (`worldCup_not_finitelyAdditive`), while orders on fewer than five
worlds are always representable (`fa_representable_iff_card_lt_five`). The paper doubts that
speakers find (3)–(6) inconsistent, and concludes that finite additivity cannot be motivated
from intuitive entailments.

## Implementation notes

* The axioms of comparative probability, the measure classes and the order theory of both
  liftings are substrate (`Core/Order/Probability`), and Figure 1's patterns V1–V12 and I1–I3
  are [yalcin-2010]'s (`Logic/ComparativeProbability/Patterns`); the figure's own addition V13
  lives here. Each pattern is derived once from the weakest axioms, and a model discharges it
  by instance resolution: the measures carry every axiom, and a world-ordering model carries
  a preorder on worlds, so both lifts are monotone and transitive and the m-lifting of a
  finite preorder reverses complements. V6, V12 for the l-lifting and V13 for the m-lifting
  use the lifts' own structure. V8–V10 are omitted, as in Figure 1, and V6 and V7 use the
  paper's order-internal `□a := ⊥ ≽ aᶜ` and `◇a := ¬ ⊥ ≽ a`.
* The refutations are countermodels: the uniform measure on three worlds for the measure
  classes, and the indiscriminate world order (every world at least as good as every other) on
  two or three worlds for the liftings.
* The completeness theorems are represented by the model-theoretic results they rest on:
  Theorem 2 by `lewisLift_repr_iff` ([halpern-2003]), Theorem 6 by
  `exists_qualAddMeasure_repr` ([van-der-hoek-1996]), Theorem 8 by the Kraft–Pratt–Seidenberg
  representation theorems. Theorems 3–5 and 7 and Fact 4 concern the logics themselves and are
  not formalized.
* Figure 7's chain of four worlds illustrates the two liftings: both make `{a, b}` more likely
  than `{b, c}`, only the l-lifting makes `{a}` more likely than `{b, c}`, and the m-lifting
  leaves `{a, d}` and `{b, c}` incomparable, which is the paper's remark that the m-lifting
  drops the totality axiom.

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

@[expose] public section

namespace HollidayIcard2013

open ComparativeProbability
open scoped ComparativeProbability.QualitativeProbability

variable {W : Type*}

/-- The indiscriminate world order: every world is at least as good as every other. -/
private instance {α : Type*} : IsPreorder α fun _ _ ↦ True where
  refl _ := trivial
  trans _ _ _ _ _ := trivial

/-! ### Figure 1's addition: V13

V1–V12 and I1–I3 are [yalcin-2010]'s, stated in `Logic/ComparativeProbability/Patterns`;
the figure adds V13. -/

/-- V13: `(a \ b) ≻ ⊥ → (a ⊔ b) ≻ b`, the pattern Lassiter suggested to the authors. -/
def StrictDisjunctionIntro {α : Type*} [BooleanAlgebra α] (r : α → α → Prop) : Prop :=
  ∀ a b : α, Strict r (a \ b) ⊥ → Strict r (a ⊔ b) b

/-- V13 from monotonicity and additivity. -/
theorem strictDisjunctionIntro_of {α : Type*} [BooleanAlgebra α] {r : α → α → Prop}
    [IsLikelihoodMono r] [IsQualitativeAdditive r] : StrictDisjunctionIntro r := by
  rintro a b ⟨_, hABnot⟩
  refine ⟨mono _ _ le_sup_right, ?_⟩
  intro hc
  apply hABnot
  have hb : b \ (a ⊔ b) = ⊥ := sdiff_eq_bot_iff.mpr le_sup_right
  have hab : (a ⊔ b) \ b = a \ b := sup_sdiff_right_self
  have hx := (qadd b (a ⊔ b)).mp hc
  rwa [hb, hab] at hx

/-! ### Fact 1: Kratzer's world-ordering semantics -/

section LLift

variable (ge_w : W → W → Prop) [IsPreorder W ge_w]

omit [IsPreorder W ge_w] in
/-- V6 for the l-lifting: only `W` itself is dominated by the empty set, and on a nonempty
domain `W` is strictly more likely than its complement. -/
theorem lLift_V6 [Nonempty W] :
    MustToProbably (LewisLift ge_w) (fun A ↦ LewisLift ge_w ⊥ Aᶜ) := by
  intro A hA
  obtain rfl : A = Set.univ := by simpa using lewisLift_empty_left_iff.1 hA
  rw [Probably, Strict, Set.compl_univ]
  exact ⟨lewisLift_empty _,
    fun h ↦ Set.univ_nonempty.ne_empty (lewisLift_empty_left_iff.1 h)⟩

/-- V12 for the l-lifting: a world of `Bᶜ` outside `A` is dominated through `A` and then
through `B`. -/
theorem lLift_V12 : ComplementTransfer (LewisLift ge_w) := by
  intro A B hBA hA y hy
  by_cases hyA : y ∈ A
  · exact hBA hyA
  · obtain ⟨a, ha, hay⟩ := hA hyA
    obtain ⟨b, hb, hba⟩ := hBA ha
    exact ⟨b, hb, _root_.trans hba hay⟩

/-- **Fact 1**, validities: over a nonempty preorder on worlds the l-lifting validates V1–V7 and
V12. -/
theorem lLift_validities [Nonempty W] :
    ProbablyToNotProbablyNot (LewisLift ge_w) ∧ ProbablyDistribInf (LewisLift ge_w) ∧
      ChancyDisjunctionIntro (LewisLift ge_w) ∧ Minimality (LewisLift ge_w) ∧
      Maximality (LewisLift ge_w) ∧
      MustToProbably (LewisLift ge_w) (fun A ↦ LewisLift ge_w ⊥ Aᶜ) ∧
      ProbablyToMight (LewisLift ge_w) (Possibly (LewisLift ge_w)) ∧
      ComplementTransfer (LewisLift ge_w) :=
  ⟨probablyToNotProbablyNot, probablyDistribInf_of, chancyDisjunctionIntro_of, minimality_of,
    maximality_of, lLift_V6 ge_w, probablyToMight_of, lLift_V12 ge_w⟩

/-- **Fact 1**, the disjunction problem: the l-lifting of any preorder on worlds validates the
three measure-invalid patterns I1–I3, since it is right-union closed. -/
theorem disjunction_problem :
    RightUnion (LewisLift ge_w) ∧ EquiprobabilityCollapse (LewisLift ge_w) ∧
      HamblinCollapse (LewisLift ge_w) :=
  have hI2 : EquiprobabilityCollapse (LewisLift ge_w) := fun A B hA ↦
    (rightUnion_lewisLift A A Aᶜ (refl_of _ A) hA).anti_right
      (by show B ⊆ A ∪ Aᶜ; rw [Set.union_compl_self]; exact Set.subset_univ B)
  ⟨rightUnion_lewisLift, hI2, fun A B hA ↦ hI2 A B hA.1⟩

end LLift

/-- **Fact 1**, the missing validities: the l-lifting refutes V11 and V13. On two indiscriminate
worlds, `W` is probable and `{0}` is at least as likely as `W`, yet `{0}` is not probable
(V11); `{0} \ {1}` is strictly more likely than `∅`, yet `{0} ∪ {1}` is not strictly more
likely than `{1}` (V13). -/
theorem lLift_refutes_V11_V13 :
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬PositiveFormTransfer (LewisLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬StrictDisjunctionIntro (LewisLift ge_w)) := by
  refine ⟨⟨Fin 2, fun _ _ ↦ True, inferInstance, fun h ↦ ?_⟩,
    ⟨Fin 2, fun _ _ ↦ True, inferInstance, fun h ↦ ?_⟩⟩
  · have hA : Probably (LewisLift fun _ _ : Fin 2 ↦ True) Set.univ := by
      rw [Probably, Strict, Set.compl_univ]
      exact ⟨lewisLift_empty _,
        fun h ↦ Set.univ_nonempty.ne_empty (lewisLift_empty_left_iff.1 h)⟩
    exact (h Set.univ {0} (fun _ _ ↦ ⟨0, rfl, trivial⟩) hA).2 fun _ _ ↦ ⟨1, by simp, trivial⟩
  · have hsd : ({0} : Set (Fin 2)) \ {1} = {0} := Set.sdiff_singleton_eq_self (by simp)
    refine (h {0} {1} ⟨lewisLift_empty _, fun h' ↦ ?_⟩).2 fun _ _ ↦ ⟨1, rfl, trivial⟩
    exact Set.singleton_ne_empty 0 (hsd ▸ lewisLift_empty_left_iff.1 h')

/-! ### Facts 2 and 3: finitely and qualitatively additive measures -/

section Measures

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Fact 2**, validities: every finitely additive measure validates V1–V13. -/
theorem measure_validities (m : FinAddMeasure K W) :
    ProbablyToNotProbablyNot m.inducedGe ∧ ProbablyDistribInf m.inducedGe ∧
      ChancyDisjunctionIntro m.inducedGe ∧ Minimality m.inducedGe ∧ Maximality m.inducedGe ∧
      MustToProbably m.inducedGe (fun A ↦ m.inducedGe ⊥ Aᶜ) ∧
      ProbablyToMight m.inducedGe (Possibly m.inducedGe) ∧ PositiveFormTransfer m.inducedGe ∧
      ComplementTransfer m.inducedGe ∧ StrictDisjunctionIntro m.inducedGe :=
  ⟨probablyToNotProbablyNot, probablyDistribInf_of, chancyDisjunctionIntro_of, minimality_of,
    maximality_of, mustToProbably_of, probablyToMight_of, positiveFormTransfer_of,
    complementTransfer_of, strictDisjunctionIntro_of⟩

/-- The uniform measure on three worlds. -/
local notation "uniform3" => FinAddMeasure.uniform (K := ℚ) (Fin 3)

private theorem uniform3_singleton (i : Fin 3) : uniform3 {i} = 1 / 3 := by simp

private theorem uniform3_pair (i j : Fin 3) (h : i ≠ j) : uniform3 {i, j} = 2 / 3 := by
  rw [FinAddMeasure.uniform_apply, Set.ncard_pair h]; norm_num

/-- I1 fails for the uniform measure: `{0}` is at least as likely as `{1}` and as `{2}` but not
as `{1, 2}`. -/
private theorem uniform3_not_I1 : ¬RightUnion (uniform3).inducedGe := fun h ↦ by
  have := h {0} {1} {2} (by simp [FinAddMeasure.inducedGe])
    (by simp [FinAddMeasure.inducedGe])
  simp only [FinAddMeasure.inducedGe, Set.sup_eq_union, Set.singleton_union, uniform3_singleton,
    uniform3_pair 1 2 (by decide)] at this
  norm_num at this

/-- `{0, 1}` beats its complement under the uniform measure … -/
private theorem uniform3_probably_pair : Probably (uniform3).inducedGe {0, 1} := by
  have := (uniform3).mu_compl {0, 1}
  rw [uniform3_pair 0 1 (by decide)] at this
  constructor <;> simp only [FinAddMeasure.inducedGe, uniform3_pair 0 1 (by decide)] <;> linarith

/-- … but is not at least as likely as `W`. -/
private theorem uniform3_not_pair_univ : ¬(uniform3).inducedGe {0, 1} Set.univ := by
  simp only [FinAddMeasure.inducedGe, uniform3_pair 0 1 (by decide), (uniform3).total]
  norm_num

/-- **Fact 2**, invalidities: the uniform measure on three worlds refutes each of I1–I3. -/
theorem measures_refute_I_patterns :
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬RightUnion m.inducedGe) ∧
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬EquiprobabilityCollapse m.inducedGe) ∧
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬HamblinCollapse m.inducedGe) :=
  ⟨⟨uniform3, uniform3_not_I1⟩,
    ⟨uniform3, fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair.1)⟩,
    ⟨uniform3, fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair)⟩⟩

/-- **Fact 3**, validities: qualitative additivity already yields V1–V13. -/
theorem qualAddMeasure_validities (m : QualAddMeasure K W) :
    ProbablyToNotProbablyNot m.inducedGe ∧ ProbablyDistribInf m.inducedGe ∧
      ChancyDisjunctionIntro m.inducedGe ∧ Minimality m.inducedGe ∧ Maximality m.inducedGe ∧
      MustToProbably m.inducedGe (fun A ↦ m.inducedGe ⊥ Aᶜ) ∧
      ProbablyToMight m.inducedGe (Possibly m.inducedGe) ∧ PositiveFormTransfer m.inducedGe ∧
      ComplementTransfer m.inducedGe ∧ StrictDisjunctionIntro m.inducedGe :=
  ⟨probablyToNotProbablyNot, probablyDistribInf_of, chancyDisjunctionIntro_of, minimality_of,
    maximality_of, mustToProbably_of, probablyToMight_of, positiveFormTransfer_of,
    complementTransfer_of, strictDisjunctionIntro_of⟩

/-- **Fact 3**, invalidities: the uniform measure, read as a qualitatively additive measure,
refutes each of I1–I3. -/
theorem qualAddMeasures_refute_I_patterns :
    (∃ m : QualAddMeasure ℚ (Fin 3), ¬RightUnion m.inducedGe) ∧
    (∃ m : QualAddMeasure ℚ (Fin 3), ¬EquiprobabilityCollapse m.inducedGe) ∧
    (∃ m : QualAddMeasure ℚ (Fin 3), ¬HamblinCollapse m.inducedGe) :=
  ⟨⟨(uniform3).toQualAdd, uniform3_not_I1⟩,
    ⟨(uniform3).toQualAdd, fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair.1)⟩,
    ⟨(uniform3).toQualAdd, fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair)⟩⟩

/-- **Theorem 6** ([van-der-hoek-1996]): every FA order on a finite carrier is represented by a
qualitatively additive measure. -/
theorem fa_qualAdd_complete [Fintype W] (sys : QualitativeProbability (Set W)) :
    ∃ m : QualAddMeasure ℚ W, ∀ A B, A ≿[sys] B ↔ m.inducedGe A B :=
  let ⟨m, hm⟩ := exists_qualAddMeasure_repr sys
  ⟨m, fun A B ↦ hm B A⟩

end Measures

/-! ### Fact 5: the m-lifting -/

section MLift

variable (ge_w : W → W → Prop) [IsPreorder W ge_w]

omit [IsPreorder W ge_w] in
/-- V6 for the m-lifting, as for the l-lifting. -/
theorem mLift_V6 [Nonempty W] :
    MustToProbably (MatchingLift ge_w) (fun A ↦ MatchingLift ge_w ⊥ Aᶜ) := by
  intro A hA
  obtain rfl : A = Set.univ := by simpa using matchingLift_empty_left_iff.1 hA
  rw [Probably, Strict, Set.compl_univ]
  exact ⟨matchingLift_empty _,
    fun h ↦ Set.univ_nonempty.ne_empty (matchingLift_empty_left_iff.1 h)⟩

/-- V13 for the m-lifting on a finite domain: `B ⊆ A ∪ B` gives the weak half, and a matching of
`A ∪ B` into `B` would contradict `|B| < |A ∪ B|`, which holds as `A \ B` is nonempty. -/
theorem mLift_V13 [Finite W] : StrictDisjunctionIntro (MatchingLift ge_w) := by
  rintro A B ⟨-, hne⟩
  have hsub : B ⊂ A ∪ B := Set.ssubset_iff_subset_ne.2 ⟨Set.subset_union_right, fun h ↦ hne ?_⟩
  · refine ⟨matchingLift_of_subset Set.subset_union_right, fun h ↦ ?_⟩
    have h₁ : (A ∪ B).ncard ≤ B.ncard := h.ncard_le
    have h₂ := Set.ncard_lt_ncard hsub
    omega
  · rw [Set.sdiff_eq_empty.2 (Set.union_eq_right.1 h.symm)]
    exact matchingLift_empty _

/-- **Fact 5**, validities: on a finite nonempty preorder the m-lifting validates V1–V7 and
V11–V13. -/
theorem mLift_validities [Finite W] [Nonempty W] :
    ProbablyToNotProbablyNot (MatchingLift ge_w) ∧ ProbablyDistribInf (MatchingLift ge_w) ∧
      ChancyDisjunctionIntro (MatchingLift ge_w) ∧ Minimality (MatchingLift ge_w) ∧
      Maximality (MatchingLift ge_w) ∧
      MustToProbably (MatchingLift ge_w) (fun A ↦ MatchingLift ge_w ⊥ Aᶜ) ∧
      ProbablyToMight (MatchingLift ge_w) (Possibly (MatchingLift ge_w)) ∧
      PositiveFormTransfer (MatchingLift ge_w) ∧
      ComplementTransfer (MatchingLift ge_w) ∧ StrictDisjunctionIntro (MatchingLift ge_w) :=
  ⟨probablyToNotProbablyNot, probablyDistribInf_of, chancyDisjunctionIntro_of, minimality_of,
    maximality_of, mLift_V6 ge_w, probablyToMight_of, positiveFormTransfer_of,
    complementTransfer_of, mLift_V13 ge_w⟩

end MLift

/-- **Fact 5**, invalidities: the m-lifting refutes I1–I3, dissolving the disjunction problem.
Between indiscriminate worlds only cardinality matters, so one world matches `{0}` and `{1}`
but not `{0, 1}` (I1), and on three worlds `{0, 1}` is strictly more likely than its
complement but cannot match all of `W` (I2, I3). -/
theorem mLift_refutes_I_patterns :
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬RightUnion (MatchingLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬EquiprobabilityCollapse (MatchingLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬HamblinCollapse (MatchingLift ge_w)) := by
  have hcard : ∀ {n : ℕ} {A B : Set (Fin n)}, A.ncard < B.ncard →
      ¬MatchingLift (fun _ _ : Fin n ↦ True) A B :=
    fun h hm ↦ (not_le.2 h) hm.ncard_le
  have hc : ({0, 1} : Set (Fin 3))ᶜ = {2} := by ext x; fin_cases x <;> simp
  have hAAc : MatchingLift (fun _ _ : Fin 3 ↦ True) {0, 1} ({0, 1} : Set (Fin 3))ᶜ := by
    rw [hc]; exact matchingLift_singleton_iff.2 ⟨0, by simp, trivial⟩
  have h23 : ({0, 1} : Set (Fin 3)).ncard < (Set.univ : Set (Fin 3)).ncard := by
    rw [Set.ncard_pair (by decide), Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  refine ⟨⟨Fin 2, fun _ _ ↦ True, inferInstance, fun h ↦ hcard ?_
      (h {0} {0} {1} (refl_of _ _) (matchingLift_singleton_iff.2 ⟨0, rfl, trivial⟩))⟩,
    ⟨Fin 3, fun _ _ ↦ True, inferInstance, fun h ↦ hcard h23 (h _ Set.univ hAAc)⟩,
    ⟨Fin 3, fun _ _ ↦ True, inferInstance, fun h ↦ hcard h23 (h _ Set.univ ⟨hAAc, hcard ?_⟩)⟩⟩
  · show ({0} : Set (Fin 2)).ncard < (({0} : Set (Fin 2)) ∪ {1}).ncard
    rw [Set.singleton_union, Set.ncard_singleton, Set.ncard_pair (by decide)]
    decide
  · rw [hc, Set.ncard_singleton, Set.ncard_pair (by decide)]
    decide

/-- Footnote 13: if the world ordering agrees with a finitely additive measure on singletons,
the m-lifting is sound for the measure order, since the injection carries the sum of the
singleton masses of `B` into a sum over a subset of `A`. -/
theorem measure_le_of_matchingLift {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Fintype W] (m : FinAddMeasure K W) (ge_w : W → W → Prop)
    (h : ∀ v u, ge_w v u ↔ m {u} ≤ m {v}) {A B : Set W} (hAB : MatchingLift ge_w A B) :
    m B ≤ m A := by
  classical
  obtain ⟨f, hf, hinj⟩ := hAB
  calc m B = ∑ b ∈ B.toFinset, m {b} := by rw [m.sum_mu_singleton, Set.coe_toFinset]
    _ ≤ ∑ b ∈ B.toFinset, m {f b} :=
        Finset.sum_le_sum fun b hb ↦ (h _ _).mp (hf b (Set.mem_toFinset.mp hb)).2
    _ = ∑ a ∈ B.toFinset.image f, m {a} := by
        rw [Finset.sum_image fun x hx y hy hxy ↦
          hinj (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy) hxy]
    _ = m ↑(B.toFinset.image f) := m.sum_mu_singleton _
    _ ≤ m A := m.mu_mono fun a ha ↦ by
        rw [Finset.coe_image, Set.coe_toFinset] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        exact (hf b hb).1

/-! ### Figure 7: the chain `a ≻ b ≻ c ≻ d`

Worlds are `Fin 4`, with `0` the best; `ge_w u v` is `u ≤ v`. -/

/-- Both liftings make `{a, b}` more likely than `{b, c}`. -/
theorem chain_pair_gt_pair :
    Strict (MatchingLift (· ≤ · : Fin 4 → Fin 4 → Prop)) {0, 1} {1, 2} ∧
      Strict (LewisLift (· ≤ · : Fin 4 → Fin 4 → Prop)) {0, 1} {1, 2} := by
  have hm : MatchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {0, 1} {1, 2} :=
    ⟨fun b ↦ b - 1, fun b hb ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl <;> decide, fun b₁ hb₁ b₂ hb₂ hf ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb₁ hb₂
      rcases hb₁ with rfl | rfl <;> rcases hb₂ with rfl | rfl <;>
        first | rfl | exact absurd hf (by decide)⟩
  have hl : ¬ LewisLift (· ≤ · : Fin 4 → Fin 4 → Prop) {1, 2} {0, 1} := by
    intro hd
    obtain ⟨a, ha, hle⟩ := hd (Set.mem_insert 0 {1})
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> exact absurd hle (by decide)
  exact ⟨⟨hm, fun h ↦ hl h.lewisLift⟩, ⟨hm.lewisLift, hl⟩⟩

/-- Only the l-lifting makes `{a}` more likely than `{b, c}`: the m-lifting leaves the two
incomparable, since two worlds cannot be matched injectively into one. -/
theorem chain_singleton_vs_pair :
    Strict (LewisLift (· ≤ · : Fin 4 → Fin 4 → Prop)) {0} {1, 2} ∧
      ¬ MatchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {0} {1, 2} ∧
      ¬ MatchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {1, 2} {0} := by
  refine ⟨⟨fun b _ ↦ ⟨0, rfl, Fin.zero_le b⟩, fun hd ↦ ?_⟩, fun h ↦ ?_, ?_⟩
  · obtain ⟨a, ha, hle⟩ := hd rfl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> exact absurd hle (by decide)
  · have := h.ncard_le
    rw [Set.ncard_singleton, Set.ncard_pair (by decide)] at this
    omega
  · rintro ⟨f, hf, -⟩
    obtain ⟨hmem, hle⟩ := hf 0 rfl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h <;> rw [h] at hle <;> exact absurd hle (by decide)

/-- The paper's remark before Fact 5: the m-lifting is not total, even over a linear order on
worlds. On the chain, `{a, d}` and `{b, c}` are incomparable: only `a` can match `c`, which
leaves nothing for `b`, and nothing in `{b, c}` matches `a`. -/
theorem mLift_not_total :
    ∃ (W : Type) (ge_w : W → W → Prop), IsLinearOrder W ge_w ∧
      ∃ A B : Set W, ¬MatchingLift ge_w A B ∧ ¬MatchingLift ge_w B A := by
  refine ⟨Fin 4, (· ≤ ·), inferInstance, {0, 3}, {1, 2}, fun ⟨f, hf, hinj⟩ ↦ ?_,
    fun ⟨f, hf, _⟩ ↦ ?_⟩
  · have h1 := hf 1 (by simp)
    have h2 := hf 2 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
    exact absurd (hinj (by simp) (by simp) (show f 1 = f 2 by omega)) (by decide)
  · obtain ⟨h, hle⟩ := hf 0 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    omega

/-! ### Theorem 8: what separates FA from finite additivity -/

/-- **Theorem 8** ([kraft-pratt-seidenberg-1959]): every FA order on `Fin n` is representable
by a finitely additive measure iff `n < 5`. -/
theorem fa_representable_iff_card_lt_five (n : ℕ) :
    (∀ sys : QualitativeProbability (Set (Fin n)), Representable sys) ↔ n < 5 :=
  ⟨fun h ↦ by_contra fun hge ↦
      let ⟨sys, hsys⟩ := exists_nonrepresentable_fin (n := n) (by omega); hsys (h sys),
    fun h sys ↦ representable_of_card_lt_five sys (by simpa using h)⟩

/-- The World Cup comparisons (3)–(6), with Argentina, Brazil, China, Denmark and England as
the worlds `0`–`4`: no finitely additive measure makes Argentina-or-England more likely than
China-or-Denmark, Brazil-or-China more likely than Argentina-or-Denmark, Denmark more likely
than Argentina-or-China, and Argentina-or-China-or-Denmark more likely than Brazil-or-England,
because the four left-hand sides and the four right-hand sides have the same total mass. -/
theorem worldCup_not_finitelyAdditive (m : FinAddMeasure ℚ (Fin 5)) :
    ¬ (Strict m.inducedGe {0, 4} {2, 3} ∧ Strict m.inducedGe {1, 2} {0, 3} ∧
      Strict m.inducedGe {3} {0, 2} ∧ Strict m.inducedGe {0, 2, 3} {1, 4}) := by
  have pair : ∀ a b : Fin 5, a ≠ b → m {a, b} = m {a} + m {b} := fun a b hab ↦ by
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
