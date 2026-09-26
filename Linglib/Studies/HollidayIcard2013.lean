module

public import Linglib.Logic.ComparativeProbability.WorldOrdering
public import Linglib.Core.Order.Probability.Completeness

/-!
# Holliday and Icard (2013): Measure semantics and qualitative semantics for epistemic modals

This file formalizes [holliday-icard-2013]'s comparison of semantics for the comparative
epistemic modal *at least as likely as* against the inference patterns of Figure 1, the
intuitively valid V1–V13 and invalid I1–I3 of [yalcin-2010]. [kratzer-1991]'s world-ordering
semantics lifts a preorder on worlds to propositions by [lewis-1973]'s l-lifting, which validates
the invalid patterns and misses V11 and V13 (`lLift_validities`, `disjunction_problem`,
`lLift_refutes_V11_V13`): from *φ ⩾ ψ* and *φ ⩾ χ* it licenses *φ ⩾ ψ ∨ χ*. The k-lifting of
[kratzer-2012] does no better when the compared propositions are disjoint
(`kLift_rightUnion_of_disjoint`). Finitely additive measures validate exactly the intended
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

* The order theory of both liftings and the measure classes are substrate; Figure 1's patterns
  and the paper's axiom schemas (`Mon`, `Tran`, `A`, `BT`, as unbundled mixin classes) are the
  paper's own apparatus and live here. Each pattern is derived once from the weakest axioms,
  and a model discharges it by instance resolution: the measures carry every axiom, and a
  world-ordering model carries a preorder on worlds, so both lifts are monotone and
  transitive and the m-lifting of a finite preorder reverses complements. V6, V12 for the
  l-lifting and V13 for the m-lifting use the lifts' own structure. V8–V10 are omitted, as in
  Figure 1.
* The refutations are countermodels: the uniform measure on three worlds for the measure
  classes, and the indiscriminate world order (every world at least as good as every other) on
  two or three worlds for the liftings.
* The completeness theorems are represented by the model-theoretic results they rest on:
  Theorem 2 by `dominationLift_repr_iff` ([halpern-2003]), Theorem 6 by
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

/-! ### Figure 1: the patterns

The intuitively valid (V1–V13) and invalid (I1–I3) patterns of [yalcin-2010] and Figure 1,
stated for a likelihood relation `r` on a Boolean algebra. -/

section Patterns

variable {α : Type*} [BooleanAlgebra α] (r : α → α → Prop)

/-- V1: `△a → ¬△aᶜ`. -/
def patternV1 : Prop := ∀ a : α, Probably r a → ¬ Probably r aᶜ
/-- V2: `△(a ⊓ b) → △a ∧ △b`. -/
def patternV2 : Prop := ∀ a b : α, Probably r (a ⊓ b) → Probably r a ∧ Probably r b
/-- V3: `△a → △(a ⊔ b)`. -/
def patternV3 : Prop := ∀ a b : α, Probably r a → Probably r (a ⊔ b)
/-- V4: `a ≽ ⊥`. -/
def patternV4 : Prop := ∀ a : α, r a ⊥
/-- V5: `⊤ ≽ a`. -/
def patternV5 : Prop := ∀ a : α, r ⊤ a
/-- V6: `□a → △a`, where `□a` is `⊥ ≽ aᶜ`. -/
def patternV6 : Prop := ∀ a : α, r ⊥ aᶜ → Probably r a
/-- V7: `△a → ◇a`. -/
def patternV7 : Prop := ∀ a : α, Probably r a → Possibly r a
/-- V11: `b ≽ a → △a → △b`. -/
def patternV11 : Prop := ∀ a b : α, r b a → Probably r a → Probably r b
/-- V12: `b ≽ a → a ≽ aᶜ → b ≽ bᶜ`. -/
def patternV12 : Prop := ∀ a b : α, r b a → r a aᶜ → r b bᶜ
/-- V13: `(a \ b) ≻ ⊥ → (a ⊔ b) ≻ b`. -/
def patternV13 : Prop := ∀ a b : α, Strict r (a \ b) ⊥ → Strict r (a ⊔ b) b
/-- I1: `a ≽ b → a ≽ c → a ≽ (b ⊔ c)`. -/
def patternI1 : Prop := ∀ a b c : α, r a b → r a c → r a (b ⊔ c)
/-- I2: `a ≽ aᶜ → a ≽ b`. -/
def patternI2 : Prop := ∀ a b : α, r a aᶜ → r a b
/-- I3: `△a → a ≽ b`. -/
def patternI3 : Prop := ∀ a b : α, Probably r a → r a b

end Patterns

/-! ### The axiom schemas as mixins

The paper's logics are axiom schemas over the comparative (Figures 4–6): monotonicity `Mon`,
transitivity `Tran` (mathlib's `IsTrans`), qualitative additivity `A` and non-triviality `BT`.
Complement reversal, `a ≽ b → bᶜ ≽ aᶜ`, is not an axiom of the paper's logics but the property
through which `A` yields V11 and V12, and the one the m-lifting shares with the measures. Each
is an unbundled `Prop`-class, so a pattern is proved once from the weakest axioms and every
model discharges it by instance resolution. -/

section Axioms

variable {α : Type*} [BooleanAlgebra α]

/-- `Mon` (monotonicity): larger events are at least as likely. -/
class IsLikelihoodMono (r : α → α → Prop) : Prop where
  mono : ∀ a b : α, a ≤ b → r b a

/-- Complement reversal: `a ≽ b → bᶜ ≽ aᶜ`. -/
class IsComplementReversing (r : α → α → Prop) : Prop where
  complRev : ∀ a b : α, r a b → r bᶜ aᶜ

/-- `A` (qualitative additivity): `a ≽ b ↔ (a \ b) ≽ (b \ a)`. -/
class IsQualitativeAdditive (r : α → α → Prop) : Prop where
  qadd : ∀ a b : α, r a b ↔ r (a \ b) (b \ a)

/-- `BT` (non-triviality): `⊥` is not at least as likely as `⊤`. -/
class IsNontrivial (r : α → α → Prop) : Prop where
  bot_not_ge_top : ¬ r ⊥ ⊤

export IsLikelihoodMono (mono)
export IsComplementReversing (complRev)
export IsQualitativeAdditive (qadd)

/-- Qualitative additivity implies complement reversal: `bᶜ \ aᶜ = a \ b` and
`aᶜ \ bᶜ = b \ a` turn the additivity equivalence for `bᶜ, aᶜ` into the one for `a, b`. -/
instance (priority := 100) instComplementReversingOfQualitativeAdditive
    {r : α → α → Prop} [h : IsQualitativeAdditive r] : IsComplementReversing r where
  complRev a b hab := by
    rw [h.qadd bᶜ aᶜ, compl_sdiff_compl, compl_sdiff_compl]
    exact (h.qadd a b).mp hab

variable {r : α → α → Prop}

/-- V1 holds for **any** relation: it is pure logic about `Strict` and double complement. -/
theorem patternV1_holds : patternV1 r := by
  rintro a ⟨_, hanot⟩ ⟨hac, _⟩
  rw [compl_compl] at hac; exact hanot hac

/-- V2 from monotonicity and transitivity. -/
theorem patternV2_of [IsLikelihoodMono r] [IsTrans α r] : patternV2 r := by
  rintro a b ⟨hab, habnot⟩
  have hsa : r a (a ⊓ b) := mono _ _ inf_le_left
  have hsb : r b (a ⊓ b) := mono _ _ inf_le_right
  have hca : r (a ⊓ b)ᶜ aᶜ := mono _ _ (compl_le_compl inf_le_left)
  have hcb : r (a ⊓ b)ᶜ bᶜ := mono _ _ (compl_le_compl inf_le_right)
  refine ⟨⟨Trans.trans (Trans.trans hsa hab) hca, ?_⟩,
          ⟨Trans.trans (Trans.trans hsb hab) hcb, ?_⟩⟩
  · exact fun hc ↦ habnot (Trans.trans (Trans.trans hca hc) hsa)
  · exact fun hc ↦ habnot (Trans.trans (Trans.trans hcb hc) hsb)

/-- V3 from monotonicity and transitivity. -/
theorem patternV3_of [IsLikelihoodMono r] [IsTrans α r] : patternV3 r := by
  rintro a b ⟨hA, hAnot⟩
  have h1 : r (a ⊔ b) a := mono _ _ le_sup_left
  have h2 : r aᶜ (aᶜ ⊓ bᶜ) := mono _ _ inf_le_left
  refine ⟨?_, ?_⟩
  · rw [compl_sup]; exact Trans.trans (Trans.trans h1 hA) h2
  · rw [compl_sup]; exact fun hc ↦ hAnot (Trans.trans (Trans.trans h2 hc) h1)

/-- V4 from monotonicity. -/
theorem patternV4_of [IsLikelihoodMono r] : patternV4 r := fun _ ↦ mono _ _ bot_le

/-- V5 from monotonicity. -/
theorem patternV5_of [IsLikelihoodMono r] : patternV5 r := fun _ ↦ mono _ _ le_top

/-- V6 from monotonicity, transitivity, additivity, and non-triviality. -/
theorem patternV6_of [IsLikelihoodMono r] [IsTrans α r] [hq : IsQualitativeAdditive r]
    [IsNontrivial r] : patternV6 r := by
  intro a h0ac
  have hA0 : r a ⊥ := mono _ _ bot_le
  refine ⟨Trans.trans hA0 h0ac, ?_⟩
  intro hAcA
  have h0A : r ⊥ a := Trans.trans h0ac hAcA
  have hAtop : r a ⊤ := by rw [hq.qadd a ⊤]; simpa using h0ac
  exact IsNontrivial.bot_not_ge_top (Trans.trans h0A hAtop)

/-- V7 from monotonicity and transitivity. -/
theorem patternV7_of [IsLikelihoodMono r] [IsTrans α r] : patternV7 r := by
  rintro a ⟨_, hAnot⟩ hempty
  exact hAnot (IsTrans.trans aᶜ ⊥ a (mono ⊥ aᶜ bot_le) hempty)

/-- V11 from transitivity and complement reversal. -/
theorem patternV11_of [IsTrans α r] [IsComplementReversing r] : patternV11 r := by
  rintro a b hba ⟨ha, hanot⟩
  have h2 : r aᶜ bᶜ := complRev _ _ hba
  refine ⟨Trans.trans (Trans.trans hba ha) h2, ?_⟩
  exact fun hc ↦ hanot (Trans.trans (Trans.trans h2 hc) hba)

/-- V12 from transitivity and complement reversal. -/
theorem patternV12_of [IsTrans α r] [IsComplementReversing r] : patternV12 r := by
  intro a b hba ha
  exact Trans.trans (Trans.trans hba ha) (complRev _ _ hba)

/-- V13 from monotonicity and additivity. -/
theorem patternV13_of [IsLikelihoodMono r] [IsQualitativeAdditive r] : patternV13 r := by
  rintro a b ⟨_, hABnot⟩
  refine ⟨mono _ _ le_sup_right, ?_⟩
  intro hc
  apply hABnot
  have hb : b \ (a ⊔ b) = ⊥ := sdiff_eq_bot_iff.mpr le_sup_right
  have hab : (a ⊔ b) \ b = a \ b := sup_sdiff_right_self
  have hx := (qadd b (a ⊔ b)).mp hc
  rwa [hb, hab] at hx

end Axioms

/-! ### The models

Every finitely and every qualitatively additive measure carries all four axioms. The lifts
inherit transitivity from the world relation (`Core.Order.Domination`), monotonicity needs
reflexivity, and complement reversal holds for the m-lifting of a finite preorder. -/

section Models

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

instance (m : FinAddMeasure K W) : IsLikelihoodMono m.inducedGe :=
  ⟨m.toQualitativeProbability.mono'⟩

instance (m : FinAddMeasure K W) : IsTrans (Set W) m.inducedGe :=
  ⟨fun _ _ _ hab hbc ↦ m.toQualitativeProbability.trans hbc hab⟩

instance (m : FinAddMeasure K W) : IsQualitativeAdditive m.inducedGe :=
  ⟨fun A B ↦ m.toQualitativeProbability.additive B A⟩

instance (m : FinAddMeasure K W) : IsNontrivial m.inducedGe :=
  ⟨m.toQualitativeProbability.nonTrivial⟩

instance (m : QualAddMeasure K W) : IsLikelihoodMono m.inducedGe :=
  ⟨m.toQualitativeProbability.mono'⟩

instance (m : QualAddMeasure K W) : IsTrans (Set W) m.inducedGe :=
  ⟨fun _ _ _ hab hbc ↦ m.toQualitativeProbability.trans hbc hab⟩

instance (m : QualAddMeasure K W) : IsQualitativeAdditive m.inducedGe :=
  ⟨fun A B ↦ m.toQualitativeProbability.additive B A⟩

instance (m : QualAddMeasure K W) : IsNontrivial m.inducedGe :=
  ⟨m.toQualitativeProbability.nonTrivial⟩

variable {ge_w : W → W → Prop}

instance [Std.Refl ge_w] : IsLikelihoodMono (DominationLift ge_w) :=
  ⟨fun _ _ h ↦ dominationLift_of_subset h⟩

instance [Std.Refl ge_w] : IsLikelihoodMono (MatchingLift ge_w) :=
  ⟨fun _ _ h ↦ matchingLift_of_subset h⟩

instance [Finite W] [IsPreorder W ge_w] : IsComplementReversing (MatchingLift ge_w) :=
  ⟨fun _ _ ↦ MatchingLift.compl⟩

end Models

/-! ### Fact 1: Kratzer's world-ordering semantics -/

section LLift

variable (ge_w : W → W → Prop) [IsPreorder W ge_w]

omit [IsPreorder W ge_w] in
/-- V6 for the l-lifting: only `W` itself is dominated by the empty set, and on a nonempty
domain `W` is strictly more likely than its complement. -/
theorem lLift_V6 [Nonempty W] : patternV6 (DominationLift ge_w) := by
  intro A hA
  obtain rfl : A = Set.univ := by simpa using dominationLift_empty_left_iff.1 hA
  rw [Probably, Strict, Set.compl_univ]
  exact ⟨dominationLift_empty _,
    fun h ↦ Set.univ_nonempty.ne_empty (dominationLift_empty_left_iff.1 h)⟩

/-- V12 for the l-lifting: a world of `Bᶜ` outside `A` is dominated through `A` and then
through `B`. -/
theorem lLift_V12 : patternV12 (DominationLift ge_w) := by
  intro A B hBA hA y hy
  by_cases hyA : y ∈ A
  · exact hBA y hyA
  · obtain ⟨a, ha, hay⟩ := hA y hyA
    obtain ⟨b, hb, hba⟩ := hBA a ha
    exact ⟨b, hb, _root_.trans hba hay⟩

/-- **Fact 1**, validities: over a nonempty preorder on worlds the l-lifting validates V1–V7 and
V12. -/
theorem lLift_validities [Nonempty W] :
    patternV1 (DominationLift ge_w) ∧ patternV2 (DominationLift ge_w) ∧
      patternV3 (DominationLift ge_w) ∧ patternV4 (DominationLift ge_w) ∧
      patternV5 (DominationLift ge_w) ∧ patternV6 (DominationLift ge_w) ∧
      patternV7 (DominationLift ge_w) ∧ patternV12 (DominationLift ge_w) :=
  ⟨patternV1_holds, patternV2_of, patternV3_of, patternV4_of, patternV5_of, lLift_V6 ge_w,
    patternV7_of, lLift_V12 ge_w⟩

/-- **Fact 1**, the disjunction problem: the l-lifting of any preorder on worlds validates the
three measure-invalid patterns I1–I3, since it is right-union closed. -/
theorem disjunction_problem :
    patternI1 (DominationLift ge_w) ∧ patternI2 (DominationLift ge_w) ∧
      patternI3 (DominationLift ge_w) :=
  have hI2 : patternI2 (DominationLift ge_w) := fun A B hA ↦
    (rightUnion_dominationLift A A Aᶜ (refl_of _ A) hA).anti_right
      (Set.union_compl_self A ▸ Set.subset_univ B)
  ⟨rightUnion_dominationLift, hI2, fun A B hA ↦ hI2 A B hA.1⟩

end LLift

/-- **Fact 1**, the missing validities: the l-lifting refutes V11 and V13. On two indiscriminate
worlds, `W` is probable and `{0}` is at least as likely as `W`, yet `{0}` is not probable
(V11); `{0} \ {1}` is strictly more likely than `∅`, yet `{0} ∪ {1}` is not strictly more
likely than `{1}` (V13). -/
theorem lLift_refutes_V11_V13 :
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬patternV11 (DominationLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬patternV13 (DominationLift ge_w)) := by
  refine ⟨⟨Fin 2, fun _ _ ↦ True, inferInstance, fun h ↦ ?_⟩,
    ⟨Fin 2, fun _ _ ↦ True, inferInstance, fun h ↦ ?_⟩⟩
  · have hA : Probably (DominationLift fun _ _ : Fin 2 ↦ True) Set.univ := by
      rw [Probably, Strict, Set.compl_univ]
      exact ⟨dominationLift_empty _,
        fun h ↦ Set.univ_nonempty.ne_empty (dominationLift_empty_left_iff.1 h)⟩
    exact (h Set.univ {0} (fun _ _ ↦ ⟨0, rfl, trivial⟩) hA).2 fun _ _ ↦ ⟨1, by simp, trivial⟩
  · have hsd : ({0} : Set (Fin 2)) \ {1} = {0} := Set.sdiff_singleton_eq_self (by simp)
    refine (h {0} {1} ⟨dominationLift_empty _, fun h' ↦ ?_⟩).2 fun _ _ ↦ ⟨1, rfl, trivial⟩
    exact Set.singleton_ne_empty 0 (hsd ▸ dominationLift_empty_left_iff.1 h')

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
  · exact hAB ⟨b, ⟨hb, hbA⟩, fun a ha ↦ hall a
      ⟨ha.1, fun h ↦ h.elim (Set.disjoint_left.mp hB ha.1) (Set.disjoint_left.mp hC ha.1)⟩⟩
  · exact hAC ⟨b, ⟨hb, hbA⟩, fun a ha ↦ hall a
      ⟨ha.1, fun h ↦ h.elim (Set.disjoint_left.mp hB ha.1) (Set.disjoint_left.mp hC ha.1)⟩⟩

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

/-- The uniform measure on three worlds. -/
private noncomputable def uniform3 : FinAddMeasure ℚ (Fin 3) :=
  .ofFintype (fun _ ↦ 1 / 3) (fun _ ↦ by norm_num)
    (by simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul])

private theorem uniform3_singleton (i : Fin 3) : uniform3 {i} = 1 / 3 := by simp [uniform3]

private theorem uniform3_pair (i j : Fin 3) (h : i ≠ j) : uniform3 {i, j} = 2 / 3 := by
  rw [Set.insert_eq, uniform3.additive (Set.disjoint_singleton.2 h), uniform3_singleton,
    uniform3_singleton]
  norm_num

/-- I1 fails for the uniform measure: `{0}` is at least as likely as `{1}` and as `{2}` but not
as `{1, 2}`. -/
private theorem uniform3_not_I1 : ¬patternI1 uniform3.inducedGe := fun h ↦ by
  have := h {0} {1} {2} (by simp [FinAddMeasure.inducedGe, uniform3_singleton])
    (by simp [FinAddMeasure.inducedGe, uniform3_singleton])
  simp only [FinAddMeasure.inducedGe, Set.sup_eq_union, Set.singleton_union, uniform3_singleton,
    uniform3_pair 1 2 (by decide)] at this
  norm_num at this

/-- `{0, 1}` beats its complement under the uniform measure … -/
private theorem uniform3_probably_pair : Probably uniform3.inducedGe {0, 1} := by
  have := uniform3.mu_compl {0, 1}
  rw [uniform3_pair 0 1 (by decide)] at this
  constructor <;> simp only [FinAddMeasure.inducedGe, uniform3_pair 0 1 (by decide)] <;> linarith

/-- … but is not at least as likely as `W`. -/
private theorem uniform3_not_pair_univ : ¬uniform3.inducedGe {0, 1} Set.univ := by
  simp only [FinAddMeasure.inducedGe, uniform3_pair 0 1 (by decide), uniform3.total]
  norm_num

/-- **Fact 2**, invalidities: the uniform measure on three worlds refutes each of I1–I3. -/
theorem measures_refute_I_patterns :
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬patternI1 m.inducedGe) ∧
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬patternI2 m.inducedGe) ∧
    (∃ m : FinAddMeasure ℚ (Fin 3), ¬patternI3 m.inducedGe) :=
  ⟨⟨uniform3, uniform3_not_I1⟩,
    ⟨uniform3, fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair.1)⟩,
    ⟨uniform3, fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair)⟩⟩

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
  ⟨⟨uniform3.toQualAdd, uniform3_not_I1⟩,
    ⟨uniform3.toQualAdd, fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair.1)⟩,
    ⟨uniform3.toQualAdd, fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair)⟩⟩

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
theorem mLift_V6 [Nonempty W] : patternV6 (MatchingLift ge_w) := by
  intro A hA
  obtain rfl : A = Set.univ := by simpa using matchingLift_empty_left_iff.1 hA
  rw [Probably, Strict, Set.compl_univ]
  exact ⟨matchingLift_empty _,
    fun h ↦ Set.univ_nonempty.ne_empty (matchingLift_empty_left_iff.1 h)⟩

/-- V13 for the m-lifting on a finite domain: `B ⊆ A ∪ B` gives the weak half, and a matching of
`A ∪ B` into `B` would contradict `|B| < |A ∪ B|`, which holds as `A \ B` is nonempty. -/
theorem mLift_V13 [Finite W] : patternV13 (MatchingLift ge_w) := by
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
    patternV1 (MatchingLift ge_w) ∧ patternV2 (MatchingLift ge_w) ∧
      patternV3 (MatchingLift ge_w) ∧ patternV4 (MatchingLift ge_w) ∧
      patternV5 (MatchingLift ge_w) ∧ patternV6 (MatchingLift ge_w) ∧
      patternV7 (MatchingLift ge_w) ∧ patternV11 (MatchingLift ge_w) ∧
      patternV12 (MatchingLift ge_w) ∧ patternV13 (MatchingLift ge_w) :=
  ⟨patternV1_holds, patternV2_of, patternV3_of, patternV4_of, patternV5_of, mLift_V6 ge_w,
    patternV7_of, patternV11_of, patternV12_of, mLift_V13 ge_w⟩

end MLift

/-- **Fact 5**, invalidities: the m-lifting refutes I1–I3, dissolving the disjunction problem.
Between indiscriminate worlds only cardinality matters, so one world matches `{0}` and `{1}`
but not `{0, 1}` (I1), and on three worlds `{0, 1}` is strictly more likely than its
complement but cannot match all of `W` (I2, I3). -/
theorem mLift_refutes_I_patterns :
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬patternI1 (MatchingLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬patternI2 (MatchingLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬patternI3 (MatchingLift ge_w)) := by
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
      Strict (DominationLift (· ≤ · : Fin 4 → Fin 4 → Prop)) {0, 1} {1, 2} := by
  have hm : MatchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {0, 1} {1, 2} :=
    ⟨fun b ↦ b - 1, fun b hb ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl <;> decide, fun b₁ hb₁ b₂ hb₂ hf ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb₁ hb₂
      rcases hb₁ with rfl | rfl <;> rcases hb₂ with rfl | rfl <;>
        first | rfl | exact absurd hf (by decide)⟩
  have hl : ¬ DominationLift (· ≤ · : Fin 4 → Fin 4 → Prop) {1, 2} {0, 1} := by
    intro hd
    obtain ⟨a, ha, hle⟩ := hd 0 (Set.mem_insert 0 {1})
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> exact absurd hle (by decide)
  exact ⟨⟨hm, fun h ↦ hl h.dominationLift⟩, ⟨hm.dominationLift, hl⟩⟩

/-- Only the l-lifting makes `{a}` more likely than `{b, c}`: the m-lifting leaves the two
incomparable, since two worlds cannot be matched injectively into one. -/
theorem chain_singleton_vs_pair :
    Strict (DominationLift (· ≤ · : Fin 4 → Fin 4 → Prop)) {0} {1, 2} ∧
      ¬ MatchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {0} {1, 2} ∧
      ¬ MatchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {1, 2} {0} := by
  refine ⟨⟨fun b _ ↦ ⟨0, rfl, Fin.zero_le b⟩, fun hd ↦ ?_⟩, fun h ↦ ?_, ?_⟩
  · obtain ⟨a, ha, hle⟩ := hd 0 rfl
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
