/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.ContextFreeGrammar.Probabilistic
import Linglib.Core.MeasureTheory.Measure.GiryMonad

/-!
# The tree measure of a probabilistic context-free grammar

A PCFG generates a derivation tree at a nonterminal by choosing a rule, generating a tree at each
nonterminal of its right-hand side, and forming the node: a system of recursive stochastic
equations, one per nonterminal. This file gives that system its least-fixed-point semantics on
the Giry monad, in the manner of [kozen-1981]: `PCFG.expand` is the one-step operator on
`G.NT → Measure (DerivationTree T G.NT)`, it is ω-Scott-continuous, and `PCFG.treeMeasure` is its
least fixed point, the supremum of the Kleene iterates from the zero measure.

The tree measure assigns to each finite tree rooted at `A` exactly the weight `PCFG.derivProb`
(`PCFG.treeMeasure_singleton`), so the product of rule weights is derived from the semantics
rather than stipulated. The total mass `treeMeasure A Set.univ` is the tightness of
[booth-thompson-1973] and [chi-1999], which is `1` exactly when the grammar's branching process
is subcritical or critical; that theorem is not proved here.

## Main definitions

* `PCFG.expand`: one expansion step from a family of tree measures.
* `PCFG.treeMeasure`: the least fixed point of `expand`.

## Main results

* `PCFG.ωScottContinuous_expand`, `PCFG.treeMeasure_eq_iSup_iterate`: continuity and the
  Kleene form of the fixed point.
* `PCFG.treeMeasure_singleton_node`, `PCFG.treeMeasure_singleton_of_ne`,
  `PCFG.treeMeasure_singleton`: the mass of a tree rooted at `A` is its `derivProb`, and trees
  rooted elsewhere have mass `0`.

## Implementation notes

Derivation trees, their lists, and rules carry the discrete σ-algebra `⊤`, so every function out
of them is measurable and every set is measurable, which discharges the side conditions of
`Measure.bind_apply` without a countability assumption on `T`. Rule choice at `A` is the finite sum
over the rules with left-hand side `A` of the rule weights times Dirac masses, so the evaluation
lemmas go through `lintegral_finsetSum_measure`. The singleton lemmas are stated for matching and
mismatching root symbols separately (`treeMeasure_singleton_node`, `treeMeasure_singleton_of_ne`);
the `if` form `treeMeasure_singleton` decides equality of trees classically, since
`DerivationTree` carries no `DecidableEq` instance.

## References

* [kozen-1981]
* [booth-thompson-1973]
* [chi-1999]
-/

open MeasureTheory OmegaCompletePartialOrder
open scoped ENNReal

instance {T N : Type*} : MeasurableSpace (DerivationTree T N) := ⊤
instance {T N : Type*} : MeasurableSpace (List (DerivationTree T N)) := ⊤
instance {T N : Type*} : MeasurableSpace (ContextFreeRule T N) := ⊤

namespace PCFG

open DerivationTree

variable {T : Type*} {G : ContextFreeGrammar T} [DecidableEq G.NT] (W : PCFG G)

noncomputable def ruleMeasure (A : G.NT) : Measure (ContextFreeRule T G.NT) :=
  ∑ r ∈ G.rules.filter (·.input = A), W.weight r • Measure.dirac r

noncomputable def childrenMeasure (κ : G.NT → Measure (DerivationTree T G.NT)) :
    List (Symbol T G.NT) → Measure (List (DerivationTree T G.NT))
  | [] => Measure.dirac []
  | .terminal t :: rest => (childrenMeasure κ rest).map (leaf t :: ·)
  | .nonterminal B :: rest => (κ B).bind fun c => (childrenMeasure κ rest).map (c :: ·)

noncomputable def expand (κ : G.NT → Measure (DerivationTree T G.NT)) (A : G.NT) :
    Measure (DerivationTree T G.NT) :=
  (W.ruleMeasure A).bind fun r => (childrenMeasure κ r.output).map (node A)

omit [DecidableEq G.NT] in
theorem ωScottContinuous_childrenMeasure (syms : List (Symbol T G.NT)) :
    ωScottContinuous fun κ : G.NT → Measure (DerivationTree T G.NT) => childrenMeasure κ syms := by
  induction syms with
  | nil => exact ωScottContinuous.const
  | cons s rest ih =>
    cases s with
    | terminal t => exact Measure.ωScottContinuous_map ih measurable_from_top
    | nonterminal B =>
      exact Measure.ωScottContinuous_bind (ωScottContinuous.apply B)
        (fun _ => Measure.ωScottContinuous_map ih measurable_from_top) fun _ => measurable_from_top

theorem ωScottContinuous_expand : ωScottContinuous W.expand :=
  ωScottContinuous.of_apply₂ fun _ => Measure.ωScottContinuous_bind_right
    (fun r => Measure.ωScottContinuous_map (ωScottContinuous_childrenMeasure r.output)
      measurable_from_top) fun _ => measurable_from_top

noncomputable def expandHom :
    (G.NT → Measure (DerivationTree T G.NT)) →o (G.NT → Measure (DerivationTree T G.NT)) :=
  ⟨W.expand, W.ωScottContinuous_expand.monotone⟩

noncomputable def treeMeasure : G.NT → Measure (DerivationTree T G.NT) :=
  OrderHom.lfp W.expandHom

theorem expand_treeMeasure : W.expand W.treeMeasure = W.treeMeasure :=
  W.expandHom.map_lfp

/-! ### Evaluation on singletons -/

section

variable {W} {κ : G.NT → Measure (DerivationTree T G.NT)}

theorem expand_apply (A : G.NT) (s : Set (DerivationTree T G.NT)) :
    W.expand κ A s =
      ∑ r ∈ G.rules.filter (·.input = A),
        W.weight r * childrenMeasure κ r.output (node A ⁻¹' s) := by
  simp only [expand, ruleMeasure]
  rw [Measure.bind_apply MeasurableSpace.measurableSet_top measurable_from_top.aemeasurable,
    lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ measurable_from_top, smul_eq_mul,
    Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]

omit [DecidableEq G.NT]

@[simp]
theorem childrenMeasure_nil_singleton_nil : childrenMeasure κ [] {[]} = 1 :=
  Measure.dirac_apply_of_mem rfl

@[simp]
theorem childrenMeasure_nil_singleton_cons (c : DerivationTree T G.NT)
    (cs : List (DerivationTree T G.NT)) : childrenMeasure κ [] {c :: cs} = 0 := by
  rw [childrenMeasure, Measure.dirac_apply' _ MeasurableSpace.measurableSet_top]
  simp

@[simp]
theorem childrenMeasure_cons_singleton_nil (s : Symbol T G.NT) (rest : List (Symbol T G.NT)) :
    childrenMeasure κ (s :: rest) {[]} = 0 := by
  cases s with
  | terminal t =>
    rw [childrenMeasure, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
    convert measure_empty (μ := childrenMeasure κ rest)
    ext; simp
  | nonterminal B =>
    rw [childrenMeasure, Measure.bind_apply MeasurableSpace.measurableSet_top
      measurable_from_top.aemeasurable]
    refine (lintegral_congr fun c => ?_).trans lintegral_zero
    rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
    convert measure_empty (μ := childrenMeasure κ rest)
    ext; simp

@[simp]
theorem childrenMeasure_terminal_singleton_leaf (t : T) (rest : List (Symbol T G.NT))
    (cs : List (DerivationTree T G.NT)) :
    childrenMeasure κ (.terminal t :: rest) {leaf t :: cs} = childrenMeasure κ rest {cs} := by
  rw [childrenMeasure, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
  congr 1; ext; simp

@[simp]
theorem childrenMeasure_terminal_singleton_cons_of_ne (t : T) (rest : List (Symbol T G.NT))
    {c : DerivationTree T G.NT} (hc : c ≠ leaf t) (cs : List (DerivationTree T G.NT)) :
    childrenMeasure κ (.terminal t :: rest) {c :: cs} = 0 := by
  rw [childrenMeasure, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
  convert measure_empty (μ := childrenMeasure κ rest)
  ext; simp [Ne.symm hc]

@[simp]
theorem childrenMeasure_nonterminal_singleton_cons (B : G.NT) (rest : List (Symbol T G.NT))
    (c : DerivationTree T G.NT) (cs : List (DerivationTree T G.NT)) :
    childrenMeasure κ (.nonterminal B :: rest) {c :: cs} =
      κ B {c} * childrenMeasure κ rest {cs} := by
  rw [childrenMeasure, Measure.bind_apply MeasurableSpace.measurableSet_top
    measurable_from_top.aemeasurable]
  have : (fun c' => ((childrenMeasure κ rest).map (c' :: ·)) {c :: cs}) =
      ({c} : Set (DerivationTree T G.NT)).indicator fun _ => childrenMeasure κ rest {cs} := by
    funext c'
    rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
    by_cases h : c' = c
    · subst h; simp; congr 1; ext; simp
    · rw [Set.indicator_of_notMem (by simpa using h)]
      convert measure_empty (μ := childrenMeasure κ rest)
      ext; simp [h]
  rw [this, lintegral_indicator_const MeasurableSpace.measurableSet_top, mul_comm]

/-- A child list whose root symbols do not match the right-hand side has mass `0`, for any
family of tree measures concentrated on trees with the right root. -/
theorem childrenMeasure_singleton_of_ne
    (hκ : ∀ B (c : DerivationTree T G.NT), c.rootSymbol ≠ .nonterminal B → κ B {c} = 0) :
    ∀ (syms : List (Symbol T G.NT)) (cs : List (DerivationTree T G.NT)),
      cs.map rootSymbol ≠ syms → childrenMeasure κ syms {cs} = 0
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => by simp
  | _ :: _, [], _ => by simp
  | .terminal t :: rest, c :: cs, h => by
    by_cases hc : c = leaf t
    · subst hc
      simp only [List.map_cons, rootSymbol_leaf, ne_eq, List.cons.injEq, true_and] at h
      simp [childrenMeasure_singleton_of_ne hκ rest cs h]
    · simp [hc]
  | .nonterminal B :: rest, c :: cs, h => by
    rw [childrenMeasure_nonterminal_singleton_cons]
    by_cases hc : c.rootSymbol = .nonterminal B
    · simp only [List.map_cons, hc, ne_eq, List.cons.injEq, true_and] at h
      simp [childrenMeasure_singleton_of_ne hκ rest cs h]
    · simp [hκ B c hc]

end

theorem treeMeasure_singleton_of_ne {t : DerivationTree T G.NT} {A : G.NT}
    (h : t.rootSymbol ≠ .nonterminal A) : W.treeMeasure A {t} = 0 := by
  rw [← W.expand_treeMeasure, expand_apply]
  have : node A ⁻¹' ({t} : Set (DerivationTree T G.NT)) = ∅ := by
    ext cs
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact h rfl
  simp [this]

mutual
/-- A tree rooted at `A` has mass `derivProb` under the tree measure at `A`. -/
theorem treeMeasure_singleton_node (A : G.NT) (cs : List (DerivationTree T G.NT)) :
    W.treeMeasure A {node A cs} = W.derivProb (node A cs) := by
  classical
  rw [← W.expand_treeMeasure, expand_apply, derivProb]
  have hpre : node A ⁻¹' ({node A cs} : Set (DerivationTree T G.NT)) = {cs} := by ext; simp
  rw [hpre, Finset.sum_congr rfl fun r hr =>
    show W.weight r * childrenMeasure W.treeMeasure r.output {cs} =
      if r = ⟨A, cs.map rootSymbol⟩ then W.weight r * W.derivProbList cs else 0 from ?_,
    Finset.sum_ite_eq']
  · split_ifs with h
    · rfl
    · rw [W.weight_eq_zero_of_not_mem _ fun h' => h (Finset.mem_filter.mpr ⟨h', rfl⟩), zero_mul]
  · obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hr
    by_cases hout : cs.map rootSymbol = r.output
    · rw [← hout, childrenMeasure_treeMeasure_singleton, if_pos]
      cases r; simp_all
    · rw [childrenMeasure_singleton_of_ne (fun _ _ => W.treeMeasure_singleton_of_ne) _ _ hout,
        mul_zero, if_neg fun h' => hout (congrArg ContextFreeRule.output h').symm]

/-- A child list has the mass its trees assign, at the right-hand side it spells out. -/
theorem childrenMeasure_treeMeasure_singleton (cs : List (DerivationTree T G.NT)) :
    childrenMeasure W.treeMeasure (cs.map rootSymbol) {cs} = W.derivProbList cs := by
  cases cs with
  | nil => simp [derivProbList]
  | cons c cs =>
    cases c with
    | leaf t => simp [derivProbList, derivProb, childrenMeasure_treeMeasure_singleton cs]
    | node B cs' =>
      simp [derivProbList, treeMeasure_singleton_node B cs',
        childrenMeasure_treeMeasure_singleton cs]
end

open scoped Classical in
/-- Under the tree measure at `A`, a tree has mass `derivProb` when rooted at `A` and `0`
otherwise. -/
theorem treeMeasure_singleton (t : DerivationTree T G.NT) (A : G.NT) :
    W.treeMeasure A {t} = if t.rootSymbol = .nonterminal A then W.derivProb t else 0 := by
  split_ifs with h
  · cases t with
    | leaf t => simp at h
    | node B cs =>
      obtain rfl : A = B := (by simpa using h.symm)
      exact W.treeMeasure_singleton_node A cs
  · exact W.treeMeasure_singleton_of_ne h

end PCFG
