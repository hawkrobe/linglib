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
* `PCFG.treeMeasure_singleton`: the mass of a tree rooted at `A` is its `derivProb`, and trees
  rooted elsewhere have mass `0`.

## Implementation notes

Derivation trees, their lists, and rules carry the discrete σ-algebra `⊤`, so every function out
of them is measurable and every set is measurable, which discharges the side conditions of
`Measure.bind_apply` without a countability assumption on `T`. Rule choice at `A` is the measure
`Measure.sum` over `G.RulesWithLHS A` of the rule weights times Dirac masses, so the evaluation
lemmas go through `lintegral_sum_measure` and `tsum_fintype`. The `if`s in the singleton lemmas
decide equality of trees classically, since `DerivationTree` carries no `DecidableEq` instance.

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

/-- The rule distribution at nonterminal `A`, as a measure on rules. -/
noncomputable def ruleMeasure (A : G.NT) : Measure (ContextFreeRule T G.NT) :=
  Measure.sum fun r : G.RulesWithLHS A => W.weight r.1 • Measure.dirac r.1

/-- Given a distribution `κ B` of trees rooted at each nonterminal `B`, the distribution of the
list of children expanding a right-hand side: terminals become leaves, nonterminals draw from
`κ`. -/
noncomputable def childrenMeasure (κ : G.NT → Measure (DerivationTree T G.NT)) :
    List (Symbol T G.NT) → Measure (List (DerivationTree T G.NT))
  | [] => Measure.dirac []
  | .terminal t :: rest => (childrenMeasure κ rest).map (leaf t :: ·)
  | .nonterminal B :: rest => (κ B).bind fun c => (childrenMeasure κ rest).map (c :: ·)

/-- One expansion step: choose a rule at `A`, expand its right-hand side from `κ`, and build the
node. -/
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

/-- The expansion operator as an order homomorphism. -/
noncomputable def expandHom :
    (G.NT → Measure (DerivationTree T G.NT)) →o (G.NT → Measure (DerivationTree T G.NT)) :=
  ⟨W.expand, W.ωScottContinuous_expand.monotone⟩

/-- The tree measure of a PCFG: at each nonterminal, the least fixed point of expansion. -/
noncomputable def treeMeasure : G.NT → Measure (DerivationTree T G.NT) :=
  OrderHom.lfp W.expandHom

theorem expand_treeMeasure : W.expand W.treeMeasure = W.treeMeasure :=
  W.expandHom.map_lfp

theorem treeMeasure_eq_iSup_iterate : W.treeMeasure = ⨆ n, W.expandHom^[n] ⊥ :=
  OrderHom.lfp_eq_iSup_iterate _ fun c => by
    show W.expand (⨆ n, c n) = ⨆ n, W.expand (c n)
    rw [← Pi.ωSup_eq_iSup (L := fun _ => Measure (DerivationTree T G.NT)) c,
      W.ωScottContinuous_expand.map_ωSup, Pi.ωSup_eq_iSup]
    rfl

/-! ### Evaluation on singletons -/

section

open scoped Classical

theorem expand_apply (κ : G.NT → Measure (DerivationTree T G.NT)) (A : G.NT)
    (s : Set (DerivationTree T G.NT)) :
    W.expand κ A s =
      ∑ r : G.RulesWithLHS A, W.weight r.1 * childrenMeasure κ r.1.output (node A ⁻¹' s) := by
  simp only [expand, ruleMeasure]
  rw [Measure.bind_apply MeasurableSpace.measurableSet_top measurable_from_top.aemeasurable,
    lintegral_sum_measure, tsum_fintype]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ measurable_from_top, smul_eq_mul,
    Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]

omit [DecidableEq G.NT] in
theorem childrenMeasure_nil_apply (κ : G.NT → Measure (DerivationTree T G.NT))
    (s : Set (List (DerivationTree T G.NT))) : childrenMeasure κ [] s = s.indicator 1 [] :=
  Measure.dirac_apply' _ MeasurableSpace.measurableSet_top

omit [DecidableEq G.NT] in
theorem childrenMeasure_terminal_apply (κ : G.NT → Measure (DerivationTree T G.NT)) (t : T)
    (rest : List (Symbol T G.NT)) (s : Set (List (DerivationTree T G.NT))) :
    childrenMeasure κ (.terminal t :: rest) s = childrenMeasure κ rest ((leaf t :: ·) ⁻¹' s) :=
  Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top

omit [DecidableEq G.NT] in
theorem childrenMeasure_nonterminal_apply (κ : G.NT → Measure (DerivationTree T G.NT)) (B : G.NT)
    (rest : List (Symbol T G.NT)) (s : Set (List (DerivationTree T G.NT))) :
    childrenMeasure κ (.nonterminal B :: rest) s =
      ∫⁻ c, childrenMeasure κ rest ((c :: ·) ⁻¹' s) ∂κ B := by
  simp only [childrenMeasure]
  rw [Measure.bind_apply MeasurableSpace.measurableSet_top measurable_from_top.aemeasurable]
  simp_rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]

omit [DecidableEq G.NT] in
theorem cons_preimage_singleton_nil {c' : DerivationTree T G.NT} :
    (c' :: ·) ⁻¹' ({[]} : Set (List (DerivationTree T G.NT))) = ∅ := by
  ext l; simp

omit [DecidableEq G.NT] in
theorem cons_preimage_singleton {c c' : DerivationTree T G.NT} {cs : List (DerivationTree T G.NT)} :
    (c' :: ·) ⁻¹' ({c :: cs} : Set (List (DerivationTree T G.NT))) =
      if c = c' then {cs} else ∅ := by
  ext l; by_cases h : c = c' <;> simp [h, eq_comm]

omit [DecidableEq G.NT] in
theorem node_preimage_singleton_leaf {A : G.NT} {t : T} :
    node A ⁻¹' ({leaf t} : Set (DerivationTree T G.NT)) = ∅ := by
  ext l; simp

theorem node_preimage_singleton {A B : G.NT} {cs : List (DerivationTree T G.NT)} :
    node A ⁻¹' ({node B cs} : Set (DerivationTree T G.NT)) = if A = B then {cs} else ∅ := by
  ext l; by_cases h : A = B <;> simp [h]

mutual
/-- Under the tree measure, a child list has the mass its trees assign, provided its root
symbols match the right-hand side. -/
theorem childrenMeasure_treeMeasure_singleton (syms : List (Symbol T G.NT))
    (cs : List (DerivationTree T G.NT)) :
    childrenMeasure W.treeMeasure syms {cs} =
      if cs.map rootSymbol = syms then W.derivProbList cs else 0 := by
  cases syms with
  | nil =>
    rw [childrenMeasure_nil_apply]
    cases cs <;> simp [derivProbList]
  | cons s rest =>
    cases s with
    | terminal t =>
      rw [childrenMeasure_terminal_apply]
      cases cs with
      | nil => simp [cons_preimage_singleton_nil]
      | cons c cs =>
        rw [cons_preimage_singleton]
        by_cases hc : c = leaf t
        · subst hc
          rw [if_pos rfl, childrenMeasure_treeMeasure_singleton rest cs]
          simp [derivProbList, derivProb]
        · rw [if_neg hc, measure_empty, eq_comm]
          cases c with
          | leaf t' => simp_all
          | node _ _ => simp
    | nonterminal B =>
      rw [childrenMeasure_nonterminal_apply]
      cases cs with
      | nil => simp [cons_preimage_singleton_nil]
      | cons c cs =>
        simp_rw [cons_preimage_singleton]
        have : (fun c' => childrenMeasure W.treeMeasure rest (if c = c' then {cs} else ∅)) =
            ({c} : Set (DerivationTree T G.NT)).indicator
              fun _ => childrenMeasure W.treeMeasure rest {cs} := by
          funext c'; by_cases h : c = c' <;> simp [h, Set.indicator, eq_comm]
        rw [this, lintegral_indicator_const MeasurableSpace.measurableSet_top,
          treeMeasure_singleton c B,
          childrenMeasure_treeMeasure_singleton rest cs]
        cases c with
        | leaf t => simp
        | node A cs' =>
          simp only [rootSymbol_node, List.map_cons, List.cons.injEq, Symbol.nonterminal.injEq,
            derivProbList]
          by_cases hA : A = B <;> by_cases hrest : cs.map rootSymbol = rest <;>
            simp [hA, hrest, mul_comm]

/-- Under the tree measure, a tree rooted at `A` has mass `derivProb`; trees rooted elsewhere
have mass `0`. -/
theorem treeMeasure_singleton (t : DerivationTree T G.NT) (A : G.NT) :
    W.treeMeasure A {t} = if t.rootSymbol = .nonterminal A then W.derivProb t else 0 := by
  rw [← W.expand_treeMeasure, expand_apply]
  cases t with
  | leaf t => simp [node_preimage_singleton_leaf]
  | node B cs =>
    simp_rw [node_preimage_singleton]
    by_cases hAB : A = B
    · subst hAB
      simp only [if_true, rootSymbol_node, derivProb]
      simp_rw [childrenMeasure_treeMeasure_singleton]
      rw [show (∑ r : G.RulesWithLHS A, W.weight r.1 *
            if cs.map rootSymbol = r.1.output then W.derivProbList cs else 0) =
          ∑ r ∈ G.rules.filter (·.input = A), W.weight r *
            if cs.map rootSymbol = r.output then W.derivProbList cs else 0 from
          Finset.sum_attach (G.rules.filter fun r : ContextFreeRule T G.NT => r.input = A)
            fun r => W.weight r * if cs.map rootSymbol = r.output then W.derivProbList cs else 0]
      by_cases hmem : (⟨A, cs.map rootSymbol⟩ : ContextFreeRule T G.NT) ∈ G.rules
      · rw [Finset.sum_eq_single ⟨A, cs.map rootSymbol⟩]
        · simp
        · rintro r hr hne
          have : cs.map rootSymbol ≠ r.output := fun h => hne (by
            obtain ⟨_, hrA⟩ := Finset.mem_filter.mp hr
            cases r; simp_all)
          simp [this]
        · exact fun h => (h (Finset.mem_filter.mpr ⟨hmem, rfl⟩)).elim
      · rw [W.weight_eq_zero_of_not_mem _ hmem, zero_mul]
        refine Finset.sum_eq_zero fun r hr => ?_
        have : cs.map rootSymbol ≠ r.output := fun h => hmem (by
          obtain ⟨hr', hrA⟩ := Finset.mem_filter.mp hr
          cases r; simp_all)
        simp [this]
    · simp [hAB, Ne.symm hAB]
end

end

end PCFG
