/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.ContextFreeGrammar.Tree
import Linglib.Core.MeasureTheory.Measure.GiryMonad
import Linglib.Core.Order.IterateFixedPoint

/-!
# Multitype Galton–Watson processes

A multitype Galton–Watson process with types `ι` and marks `T` is an offspring distribution for
each type over ordered lists of types and marks. An individual of type `i` draws its offspring,
each type among them founds an independent copy of the process, and each mark is a leaf. The
family tree of an individual is the plane tree of [neveu-1986]; its law on finite trees is the
least fixed point of the one-generation operator on the Giry monad, and the missing mass is the
probability of surviving forever.

A probabilistic context-free grammar is the instance whose types are the nonterminals, whose
marks are the terminals, and whose offspring at `A` is the right-hand side of a rule chosen with
its weight; see `PCFG.galtonWatson`.

## Main definitions

* `ProbabilityTheory.GaltonWatson`: the offspring kernel.
* `GaltonWatson.expand`: one generation, and `GaltonWatson.law`: its least fixed point, the law
  of the finite family tree.
* `GaltonWatson.weight`: the probability of a finite family tree, the product over its internal
  nodes of the offspring probability there.
* `GaltonWatson.extinctionProb`: the total mass of `law`, the probability that the family tree
  is finite.

## Main results

* `GaltonWatson.law_eq_iSup_iterate`: the law is the supremum of the Kleene iterates from the
  zero measure.
* `GaltonWatson.law_singleton`: a finite tree rooted at type `i` has probability `weight` under
  the law at `i`, and trees rooted elsewhere have probability `0`.
* `GaltonWatson.law_univ_le_one`: with sub-probability offspring the law is a sub-probability
  measure.

## Implementation notes

Family trees are `DerivationTree T ι`, with marks as leaves and types as internal labels, and
offspring lists are `List (Symbol T ι)`; both carry the discrete σ-algebra `⊤`, so every
function out of them is measurable without a countability assumption. The offspring measures
are not required to be probability measures: sub-probability offspring model killing, and the
grammar instance produces the zero measure at a nonterminal no rule expands. The extinction
probability is the least fixed point of the offspring generating function and equals one exactly
when the mean matrix is subcritical or critical ([athreya-ney-1972]); that theorem is not proved
here.

## References

* [neveu-1986]
* [athreya-ney-1972]
-/

open MeasureTheory OmegaCompletePartialOrder
open scoped ENNReal

instance {T N : Type*} : MeasurableSpace (DerivationTree T N) := ⊤
instance {T N : Type*} : MeasurableSpace (List (DerivationTree T N)) := ⊤
instance {T N : Type*} : MeasurableSpace (List (Symbol T N)) := ⊤

namespace ProbabilityTheory

/-- A multitype Galton–Watson process with types `ι` and marks `T`: an individual of type `i`
has offspring drawn from `offspring i`, an ordered list of types (individuals of the next
generation) and marks (leaves). -/
structure GaltonWatson (ι T : Type*) where
  /-- The offspring distribution of an individual of type `i`. -/
  offspring : ι → Measure (List (Symbol T ι))

namespace GaltonWatson

open DerivationTree

variable {ι T : Type*} (P : GaltonWatson ι T)

/-- Given laws `κ i` for the family trees of individuals of type `i`, the law of the list of
subtrees below a list of offspring: marks become leaves, types draw from `κ`. -/
noncomputable def childrenMeasure (κ : ι → Measure (DerivationTree T ι)) :
    List (Symbol T ι) → Measure (List (DerivationTree T ι))
  | [] => Measure.dirac []
  | .terminal t :: rest => (childrenMeasure κ rest).map (leaf t :: ·)
  | .nonterminal i :: rest => (κ i).bind fun c => (childrenMeasure κ rest).map (c :: ·)

/-- One generation: an individual of type `i` draws its offspring and each type among them grows
a family tree with law `κ`. -/
noncomputable def expand (κ : ι → Measure (DerivationTree T ι)) (i : ι) :
    Measure (DerivationTree T ι) :=
  (P.offspring i).bind fun syms => (childrenMeasure κ syms).map (node i)

theorem ωScottContinuous_childrenMeasure (syms : List (Symbol T ι)) :
    ωScottContinuous fun κ : ι → Measure (DerivationTree T ι) => childrenMeasure κ syms := by
  induction syms with
  | nil => exact ωScottContinuous.const
  | cons s rest ih =>
    cases s with
    | terminal t => exact Measure.ωScottContinuous_map ih measurable_from_top
    | nonterminal i =>
      exact Measure.ωScottContinuous_bind (ωScottContinuous.apply i)
        (fun _ => Measure.ωScottContinuous_map ih measurable_from_top) fun _ => measurable_from_top

theorem ωScottContinuous_expand : ωScottContinuous P.expand :=
  ωScottContinuous.of_apply₂ fun _ => Measure.ωScottContinuous_bind_right
    (fun syms => Measure.ωScottContinuous_map (ωScottContinuous_childrenMeasure syms)
      measurable_from_top) fun _ => measurable_from_top

/-- The generation operator as an order homomorphism. -/
noncomputable def expandHom :
    (ι → Measure (DerivationTree T ι)) →o (ι → Measure (DerivationTree T ι)) :=
  ⟨P.expand, P.ωScottContinuous_expand.monotone⟩

/-- The law of the family tree of an individual of type `i`, on finite trees: the least fixed
point of the generation operator. Its total mass is the extinction probability. -/
noncomputable def law : ι → Measure (DerivationTree T ι) :=
  OrderHom.lfp P.expandHom

theorem expand_law : P.expand P.law = P.law :=
  P.expandHom.map_lfp

theorem law_eq_iSup_iterate : P.law = ⨆ n, P.expandHom^[n] ⊥ :=
  OrderHom.lfp_eq_iSup_iterate _ fun c => by
    show P.expand (⨆ n, c n) = ⨆ n, P.expand (c n)
    rw [← Pi.ωSup_eq_iSup (L := fun _ => Measure (DerivationTree T ι)) c,
      P.ωScottContinuous_expand.map_ωSup, Pi.ωSup_eq_iSup]
    rfl

/-! ### The weight of a finite family tree -/

mutual
/-- The probability of a finite family tree: the product over its internal nodes of the
offspring probability of the list of symbols below that node. -/
noncomputable def weight : DerivationTree T ι → ℝ≥0∞
  | .leaf _ => 1
  | .node i cs => P.offspring i {cs.map rootSymbol} * weightList cs

/-- The product of the weights of a list of family trees. -/
noncomputable def weightList : List (DerivationTree T ι) → ℝ≥0∞
  | [] => 1
  | c :: cs => weight c * weightList cs
end

/-! ### Evaluation on singletons -/

section

variable {P} {κ : ι → Measure (DerivationTree T ι)}

theorem expand_apply (i : ι) (s : Set (DerivationTree T ι)) :
    P.expand κ i s = ∫⁻ syms, childrenMeasure κ syms (node i ⁻¹' s) ∂P.offspring i := by
  rw [expand, Measure.bind_apply MeasurableSpace.measurableSet_top measurable_from_top.aemeasurable]
  simp_rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]

@[simp]
theorem childrenMeasure_nil_singleton_nil : childrenMeasure κ [] {[]} = 1 :=
  Measure.dirac_apply_of_mem rfl

@[simp]
theorem childrenMeasure_nil_singleton_cons (c : DerivationTree T ι)
    (cs : List (DerivationTree T ι)) : childrenMeasure κ [] {c :: cs} = 0 := by
  rw [childrenMeasure, Measure.dirac_apply' _ MeasurableSpace.measurableSet_top]
  simp

@[simp]
theorem childrenMeasure_cons_singleton_nil (s : Symbol T ι) (rest : List (Symbol T ι)) :
    childrenMeasure κ (s :: rest) {[]} = 0 := by
  cases s with
  | terminal t =>
    rw [childrenMeasure, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
    convert measure_empty (μ := childrenMeasure κ rest)
    ext; simp
  | nonterminal i =>
    rw [childrenMeasure, Measure.bind_apply MeasurableSpace.measurableSet_top
      measurable_from_top.aemeasurable]
    refine (lintegral_congr fun c => ?_).trans lintegral_zero
    rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
    convert measure_empty (μ := childrenMeasure κ rest)
    ext; simp

@[simp]
theorem childrenMeasure_terminal_singleton_leaf (t : T) (rest : List (Symbol T ι))
    (cs : List (DerivationTree T ι)) :
    childrenMeasure κ (.terminal t :: rest) {leaf t :: cs} = childrenMeasure κ rest {cs} := by
  rw [childrenMeasure, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
  congr 1; ext; simp

@[simp]
theorem childrenMeasure_terminal_singleton_cons_of_ne (t : T) (rest : List (Symbol T ι))
    {c : DerivationTree T ι} (hc : c ≠ leaf t) (cs : List (DerivationTree T ι)) :
    childrenMeasure κ (.terminal t :: rest) {c :: cs} = 0 := by
  rw [childrenMeasure, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
  convert measure_empty (μ := childrenMeasure κ rest)
  ext; simp [Ne.symm hc]

@[simp]
theorem childrenMeasure_nonterminal_singleton_cons (i : ι) (rest : List (Symbol T ι))
    (c : DerivationTree T ι) (cs : List (DerivationTree T ι)) :
    childrenMeasure κ (.nonterminal i :: rest) {c :: cs} =
      κ i {c} * childrenMeasure κ rest {cs} := by
  rw [childrenMeasure, Measure.bind_apply MeasurableSpace.measurableSet_top
    measurable_from_top.aemeasurable]
  have : (fun c' => ((childrenMeasure κ rest).map (c' :: ·)) {c :: cs}) =
      ({c} : Set (DerivationTree T ι)).indicator fun _ => childrenMeasure κ rest {cs} := by
    funext c'
    rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
    by_cases h : c' = c
    · subst h; simp; congr 1; ext; simp
    · rw [Set.indicator_of_notMem (by simpa using h)]
      convert measure_empty (μ := childrenMeasure κ rest)
      ext; simp [h]
  rw [this, lintegral_indicator_const MeasurableSpace.measurableSet_top, mul_comm]

/-- A list of subtrees whose root symbols do not match the offspring has mass `0`, for any family
of laws concentrated on trees of the right type. -/
theorem childrenMeasure_singleton_of_ne
    (hκ : ∀ i (c : DerivationTree T ι), c.rootSymbol ≠ .nonterminal i → κ i {c} = 0) :
    ∀ (syms : List (Symbol T ι)) (cs : List (DerivationTree T ι)),
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
  | .nonterminal i :: rest, c :: cs, h => by
    rw [childrenMeasure_nonterminal_singleton_cons]
    by_cases hc : c.rootSymbol = .nonterminal i
    · simp only [List.map_cons, hc, ne_eq, List.cons.injEq, true_and] at h
      simp [childrenMeasure_singleton_of_ne hκ rest cs h]
    · simp [hκ i c hc]

end

theorem law_singleton_of_ne {t : DerivationTree T ι} {i : ι}
    (h : t.rootSymbol ≠ .nonterminal i) : P.law i {t} = 0 := by
  rw [← P.expand_law, expand_apply]
  have : node i ⁻¹' ({t} : Set (DerivationTree T ι)) = ∅ := by
    ext cs
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact h rfl
  simp [this]

mutual
/-- A family tree of an individual of type `i` has probability `weight` under the law at `i`. -/
theorem law_singleton_node (i : ι) (cs : List (DerivationTree T ι)) :
    P.law i {node i cs} = P.weight (node i cs) := by
  rw [← P.expand_law, expand_apply, weight]
  have hpre : node i ⁻¹' ({node i cs} : Set (DerivationTree T ι)) = {cs} := by ext; simp
  have hind : (fun syms => childrenMeasure P.law syms {cs}) =
      ({cs.map rootSymbol} : Set (List (Symbol T ι))).indicator fun _ => P.weightList cs := by
    funext syms
    by_cases hs : cs.map rootSymbol = syms
    · subst hs
      rw [childrenMeasure_law_singleton cs, Set.indicator_of_mem (Set.mem_singleton _)]
    · rw [childrenMeasure_singleton_of_ne (fun _ _ => P.law_singleton_of_ne) _ _ hs,
        Set.indicator_of_notMem (by simpa using Ne.symm hs)]
  rw [hpre, hind, lintegral_indicator_const MeasurableSpace.measurableSet_top, mul_comm]

/-- A list of family trees has probability `weightList` below the offspring it spells out. -/
theorem childrenMeasure_law_singleton (cs : List (DerivationTree T ι)) :
    childrenMeasure P.law (cs.map rootSymbol) {cs} = P.weightList cs := by
  cases cs with
  | nil => simp [weightList]
  | cons c cs =>
    cases c with
    | leaf t => simp [weightList, weight, childrenMeasure_law_singleton cs]
    | node i cs' =>
      simp [weightList, law_singleton_node i cs', childrenMeasure_law_singleton cs]
end

open scoped Classical in
/-- Under the law at `i`, a finite tree has probability `weight` when its root has type `i`
and `0` otherwise. -/
theorem law_singleton (t : DerivationTree T ι) (i : ι) :
    P.law i {t} = if t.rootSymbol = .nonterminal i then P.weight t else 0 := by
  split_ifs with h
  · cases t with
    | leaf t => simp at h
    | node j cs =>
      obtain rfl : i = j := (by simpa using h.symm)
      exact P.law_singleton_node i cs
  · exact P.law_singleton_of_ne h

/-! ### Extinction -/

section

variable {P}

theorem childrenMeasure_univ_le_one {κ : ι → Measure (DerivationTree T ι)}
    (hκ : ∀ i, κ i Set.univ ≤ 1) :
    ∀ syms : List (Symbol T ι), childrenMeasure κ syms Set.univ ≤ 1
  | [] => by simp [childrenMeasure]
  | .terminal t :: rest => by
    rw [childrenMeasure, Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top,
      Set.preimage_univ]
    exact childrenMeasure_univ_le_one hκ rest
  | .nonterminal i :: rest => by
    rw [childrenMeasure, Measure.bind_apply MeasurableSpace.measurableSet_top
      measurable_from_top.aemeasurable]
    calc ∫⁻ c, ((childrenMeasure κ rest).map (c :: ·)) Set.univ ∂κ i
        ≤ ∫⁻ _, 1 ∂κ i := lintegral_mono fun c => by
          rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top,
            Set.preimage_univ]
          exact childrenMeasure_univ_le_one hκ rest
      _ = κ i Set.univ := lintegral_one
      _ ≤ 1 := hκ i

theorem expand_univ_le_one (hP : ∀ i, P.offspring i Set.univ ≤ 1)
    {κ : ι → Measure (DerivationTree T ι)} (hκ : ∀ i, κ i Set.univ ≤ 1) (i : ι) :
    P.expand κ i Set.univ ≤ 1 := by
  rw [expand_apply]
  calc ∫⁻ syms, childrenMeasure κ syms (node i ⁻¹' Set.univ) ∂P.offspring i
      ≤ ∫⁻ _, 1 ∂P.offspring i := lintegral_mono fun syms => by
        rw [Set.preimage_univ]; exact childrenMeasure_univ_le_one hκ syms
    _ = P.offspring i Set.univ := lintegral_one
    _ ≤ 1 := hP i

end

variable (hP : ∀ i, P.offspring i Set.univ ≤ 1)
include hP

theorem iterate_expand_univ_le_one : ∀ (n : ℕ) (i : ι), (P.expandHom^[n] ⊥) i Set.univ ≤ 1
  | 0, _ => by
    rw [Function.iterate_zero_apply, Pi.bot_apply]
    exact (Measure.le_iff'.1 (bot_le (a := (0 : Measure (DerivationTree T ι)))) _).trans (by simp)
  | n + 1, i => by
    rw [Function.iterate_succ_apply']
    exact expand_univ_le_one hP (iterate_expand_univ_le_one n) i

/-- With sub-probability offspring, the law on finite family trees is a sub-probability measure;
the missing mass is the probability of survival forever. -/
theorem law_univ_le_one (i : ι) : P.law i Set.univ ≤ 1 := by
  rw [law_eq_iSup_iterate, iSup_apply,
    Measure.iSup_apply_of_monotone (fun m n h => P.expandHom.iterate_bot_mono h i)
      MeasurableSpace.measurableSet_top]
  exact iSup_le fun n => P.iterate_expand_univ_le_one hP n i

omit hP in
/-- The extinction probability of an individual of type `i`: the probability that its family
tree is finite. -/
noncomputable def extinctionProb (i : ι) : ℝ≥0∞ := P.law i Set.univ

end GaltonWatson

end ProbabilityTheory
