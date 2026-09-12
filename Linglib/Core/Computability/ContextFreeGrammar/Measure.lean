/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.ContextFreeGrammar.Probabilistic
import Linglib.Core.Probability.BranchingProcess.GaltonWatson

/-!
# The derivation measure of a probabilistic context-free grammar

A PCFG is a multitype Galton–Watson process: the types are the nonterminals, the marks are the
terminals, and an individual of type `A` has as offspring the right-hand side of a rule at `A`
chosen with its weight. The law of the family tree is the law of the derivation tree, and the
product of rule weights `PCFG.derivProb` is the Galton–Watson weight of the tree, so it is
derived from the generation process rather than stipulated. Total mass one is tightness in the
sense of [booth-thompson-1973] and [chi-1999], consistency in older terminology: the grammar
almost surely produces a finite derivation from every nonterminal.

## Main definitions

* `PCFG.galtonWatson`: the branching process of a PCFG.
* `PCFG.derivationMeasure`: the law of the derivation tree at each nonterminal.
* `PCFG.IsTight`: total mass one at every nonterminal.

## Main results

* `PCFG.galtonWatson_weight`: the Galton–Watson weight of a tree is `derivProb`.
* `PCFG.derivationMeasure_singleton`: a tree rooted at `A` has probability `derivProb` under the
  derivation measure at `A`, and trees rooted elsewhere have probability `0`.
* `PCFG.derivationMeasure_univ_le_one`: the derivation measure is a sub-probability measure.

## References

* [booth-thompson-1973]
* [chi-1999]
* [kozen-1981]
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

instance {T N : Type*} : MeasurableSpace (ContextFreeRule T N) := ⊤

namespace PCFG

open DerivationTree

variable {T : Type*} {G : ContextFreeGrammar T} [DecidableEq G.NT] (W : PCFG G)

/-- The rule distribution at nonterminal `A`, as a measure on rules. -/
noncomputable def ruleMeasure (A : G.NT) : Measure (ContextFreeRule T G.NT) :=
  ∑ r ∈ G.rules.filter (·.input = A), W.weight r • Measure.dirac r

theorem ruleMeasure_apply (A : G.NT) (s : Set (ContextFreeRule T G.NT)) :
    W.ruleMeasure A s = ∑ r ∈ G.rules.filter (·.input = A), W.weight r * s.indicator 1 r := by
  simp [ruleMeasure, Measure.finsetSum_apply,
    Measure.dirac_apply' _ MeasurableSpace.measurableSet_top]

/-- The branching process of a PCFG: an individual of type `A` has as offspring the right-hand
side of a rule at `A`, chosen with the rule's weight. -/
noncomputable def galtonWatson : GaltonWatson G.NT T where
  offspring A := (W.ruleMeasure A).map ContextFreeRule.output

theorem galtonWatson_offspring_singleton (A : G.NT) (syms : List (Symbol T G.NT)) :
    W.galtonWatson.offspring A {syms} = W.weight ⟨A, syms⟩ := by
  classical
  rw [galtonWatson, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top,
    ruleMeasure_apply,
    Finset.sum_congr rfl fun r hr =>
      show W.weight r * (ContextFreeRule.output ⁻¹' {syms}).indicator 1 r =
        if r = ⟨A, syms⟩ then W.weight r else 0 from ?_, Finset.sum_ite_eq']
  · split_ifs with h
    · rfl
    · rw [W.weight_eq_zero_of_not_mem _ fun h' => h (Finset.mem_filter.mpr ⟨h', rfl⟩)]
  · obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hr
    by_cases hs : r.output = syms
    · rw [Set.indicator_of_mem (by simpa using hs), if_pos (by cases r; simp_all)]
      simp
    · rw [Set.indicator_of_notMem (by simpa using hs),
        if_neg fun h => hs (congrArg ContextFreeRule.output h)]
      simp

theorem galtonWatson_offspring_univ_le_one (A : G.NT) :
    W.galtonWatson.offspring A Set.univ ≤ 1 := by
  rw [galtonWatson, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top,
    Set.preimage_univ, ruleMeasure_apply]
  simpa using W.sum_weight_le_one A

mutual
/-- The Galton–Watson weight of a derivation tree is the product of its rule weights. -/
theorem galtonWatson_weight :
    ∀ t : DerivationTree T G.NT, W.galtonWatson.weight t = W.derivProb t
  | .leaf t => by rw [GaltonWatson.weight, derivProb]
  | .node A cs => by
    rw [GaltonWatson.weight, derivProb, galtonWatson_offspring_singleton,
      galtonWatson_weightList cs]

theorem galtonWatson_weightList :
    ∀ cs : List (DerivationTree T G.NT), W.galtonWatson.weightList cs = W.derivProbList cs
  | [] => rfl
  | c :: cs => by
    rw [GaltonWatson.weightList, derivProbList, galtonWatson_weight c, galtonWatson_weightList cs]
end

/-- The law of the derivation tree at each nonterminal: the law of the family tree of the
grammar's branching process. -/
noncomputable def derivationMeasure : G.NT → Measure (DerivationTree T G.NT) :=
  W.galtonWatson.law

theorem derivationMeasure_singleton_node (A : G.NT) (cs : List (DerivationTree T G.NT)) :
    W.derivationMeasure A {node A cs} = W.derivProb (node A cs) :=
  (W.galtonWatson.law_singleton_node A cs).trans (W.galtonWatson_weight _)

theorem derivationMeasure_singleton_of_ne {t : DerivationTree T G.NT} {A : G.NT}
    (h : t.rootSymbol ≠ .nonterminal A) : W.derivationMeasure A {t} = 0 :=
  W.galtonWatson.law_singleton_of_ne h

open scoped Classical in
/-- Under the derivation measure at `A`, a tree has probability `derivProb` when rooted at `A`
and `0` otherwise. -/
theorem derivationMeasure_singleton (t : DerivationTree T G.NT) (A : G.NT) :
    W.derivationMeasure A {t} = if t.rootSymbol = .nonterminal A then W.derivProb t else 0 := by
  rw [derivationMeasure, GaltonWatson.law_singleton, galtonWatson_weight]
  split_ifs <;> rfl

/-- The derivation measure is a sub-probability measure at every nonterminal. -/
theorem derivationMeasure_univ_le_one (A : G.NT) : W.derivationMeasure A Set.univ ≤ 1 :=
  W.galtonWatson.law_univ_le_one W.galtonWatson_offspring_univ_le_one A

instance (A : G.NT) : IsFiniteMeasure (W.derivationMeasure A) :=
  ⟨(W.derivationMeasure_univ_le_one A).trans_lt ENNReal.one_lt_top⟩

/-- A PCFG is tight when the derivation measure has total mass one at every nonterminal: the
grammar almost surely produces a finite derivation from every nonterminal. Booth and Thompson
call this consistency. -/
def IsTight : Prop := ∀ A, W.galtonWatson.extinctionProb A = 1

theorem isTight_iff : W.IsTight ↔ ∀ A, IsProbabilityMeasure (W.derivationMeasure A) :=
  ⟨fun h A => ⟨h A⟩, fun h A => (h A).measure_univ⟩

end PCFG
