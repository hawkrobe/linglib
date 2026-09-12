/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.ContextFreeGrammar.Tree
import Linglib.Core.MeasureTheory.Measure.GiryMonad
import Linglib.Core.Order.IterateFixedPoint
import Linglib.Core.Probability.Kernel.Basic
import Linglib.Core.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Multitype Galton–Watson processes

A multitype Galton–Watson process with types `ι` and marks `T` is an offspring kernel
`ξ : Kernel ι (List (Symbol T ι))`. An individual of type `i` draws its offspring from `ξ i`, an
ordered list of types and marks; each type among them founds an independent copy of the process
and each mark is a leaf. The family tree of an individual is the plane tree of [neveu-1986]; its
law on finite trees is the least fixed point of the one-generation operator on the Giry monad,
and the missing mass is the probability of surviving forever.

A probabilistic context-free grammar is the instance whose types are the nonterminals, whose
marks are the terminals, and whose offspring at `A` is the right-hand side of a rule chosen with
its weight; see `PCFG.galtonWatson`.

## Main definitions

* `GaltonWatson.PartialTree`: family trees with holes, the states of the generation chain.
* `GaltonWatson.fill`: the kernel filling the holes of a partial tree with independent draws
  from a family of laws, and `GaltonWatson.generation`: the kernel expanding every hole by one
  generation.
* `GaltonWatson.expand`: one generation from a single hole followed by filling, and
  `GaltonWatson.law`: its least fixed point, the law of the finite family tree at each type.
* `GaltonWatson.weight`: the probability of a finite family tree, the product over its internal
  nodes of the offspring probability there.
* `GaltonWatson.extinctionProb`: the total mass of `law`, the probability that the family tree
  is finite.
* `GaltonWatson.chainKernel`, `GaltonWatson.trajectory`: with Markov offspring, the generation
  chain in Ionescu–Tulcea form and, through `ProbabilityTheory.Kernel.traj`, the law of its
  whole trajectory.

## Main results

* `GaltonWatson.law_eq_iSup_iterate`: the law is the supremum of the Kleene iterates of
  `expand` from the zero kernel.
* `GaltonWatson.law_singleton`: a finite tree rooted at type `i` has probability `weight` under
  the law at `i`, and trees rooted elsewhere have probability `0`.
* `GaltonWatson.law_univ_le_one`: with sub-probability offspring the law is a sub-probability
  kernel.
* `GaltonWatson.fill_expand`: filling with one more generation is one generation followed by
  filling, so `GaltonWatson.fill_iterate` identifies the Kleene iterates with the completed part
  of the generation chain and `GaltonWatson.law_eq_iSup_generation` expresses the law as their
  supremum.
* `GaltonWatson.trajectory_map_eval`: at time `n` the trajectory is distributed as `n`
  generations, so the Kleene iterates are the marginals of the trajectory measure.

## Implementation notes

Family trees are `DerivationTree T ι`, with marks as leaves and types as internal labels, and
partial trees are `DerivationTree (Symbol T ι) ι`, whose leaves are marks or holes. Both, and
lists of them, carry the discrete σ-algebra `⊤`, so every function out of them is measurable and,
with `ι` and `T` countable, every measure on them is s-finite and every kernel between them is an
s-finite kernel; Fubini then needs no finiteness hypotheses. The offspring kernel is not
required to be Markov: sub-probability offspring model killing, and the grammar instance
produces the zero measure at a nonterminal no rule expands. The extinction probability is the
least fixed point of the offspring generating function and equals one exactly when the mean
matrix is subcritical or critical ([athreya-ney-1972]); that theorem is not proved here.

## References

* [neveu-1986]
* [athreya-ney-1972]
-/

open MeasureTheory OmegaCompletePartialOrder ProbabilityTheory Kernel Finset Preorder
open scoped ENNReal

instance {T N : Type*} : MeasurableSpace (DerivationTree T N) := ⊤
instance {T N : Type*} : MeasurableSpace (List (DerivationTree T N)) := ⊤
instance {T N : Type*} : MeasurableSpace (List (Symbol T N)) := ⊤

namespace ProbabilityTheory.GaltonWatson

open DerivationTree

variable {ι T : Type*} [MeasurableSpace ι]

/-- Partial family trees: a leaf is a mark `Symbol.terminal t` or a hole `Symbol.nonterminal i`
of type `i`, yet to be expanded. -/
abbrev PartialTree (ι T : Type*) := DerivationTree (Symbol T ι) ι

/-! ### Filling the holes -/

section Fill

variable (κ : Kernel ι (DerivationTree T ι))

mutual
private noncomputable def fillFun : PartialTree ι T → Measure (DerivationTree T ι)
  | .leaf (.terminal t) => Measure.dirac (leaf t)
  | .leaf (.nonterminal i) => κ i
  | .node i cs => (fillListFun cs).map (node i)
private noncomputable def fillListFun : List (PartialTree ι T) → Measure (List (DerivationTree T ι))
  | [] => Measure.dirac []
  | s :: ss => ((fillFun s).prod (fillListFun ss)).map (Function.uncurry List.cons)
end

/-- Fill the holes of a partial tree with independent draws from the laws `κ`. -/
noncomputable def fill : Kernel (PartialTree ι T) (DerivationTree T ι) := ⟨fillFun κ, .of_discrete⟩

/-- Fill the holes of a list of partial trees independently. -/
noncomputable def fillList : Kernel (List (PartialTree ι T)) (List (DerivationTree T ι)) :=
  ⟨fillListFun κ, .of_discrete⟩

@[simp] theorem fill_leaf_terminal (t : T) : fill κ (leaf (.terminal t)) = Measure.dirac (leaf t) :=
  rfl

@[simp] theorem fill_leaf_nonterminal (i : ι) : fill κ (leaf (.nonterminal i)) = κ i := rfl

theorem fill_node (i : ι) (cs : List (PartialTree ι T)) :
    fill κ (node i cs) = (fillList κ cs).map (node i) := rfl

@[simp] theorem fillList_nil : fillList κ [] = Measure.dirac [] := rfl

theorem fillList_cons (s : PartialTree ι T) (ss : List (PartialTree ι T)) :
    fillList κ (s :: ss) = ((fill κ s).prod (fillList κ ss)).map (Function.uncurry List.cons) :=
  rfl

variable {κ}

@[simp]
theorem fillList_nil_singleton_cons (c : DerivationTree T ι) (cs : List (DerivationTree T ι)) :
    fillList κ [] {c :: cs} = 0 := by
  rw [fillList_nil, Measure.dirac_apply' _ .of_discrete]
  simp

mutual
theorem fill_univ_le_one [Countable ι] [Countable T] (hκ : ∀ i, κ i Set.univ ≤ 1) :
    ∀ s : PartialTree ι T, fill κ s Set.univ ≤ 1
  | .leaf (.terminal _) => by simp
  | .leaf (.nonterminal i) => hκ i
  | .node _ cs => by
    rw [fill_node, Measure.map_apply .of_discrete .univ, Set.preimage_univ]
    exact fillList_univ_le_one hκ cs
theorem fillList_univ_le_one [Countable ι] [Countable T] (hκ : ∀ i, κ i Set.univ ≤ 1) :
    ∀ ss : List (PartialTree ι T), fillList κ ss Set.univ ≤ 1
  | [] => by simp
  | s :: ss => by
    rw [fillList_cons, Measure.map_apply .of_discrete .univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod]
    exact mul_le_one' (fill_univ_le_one hκ s) (fillList_univ_le_one hκ ss)
end

mutual
theorem isProbabilityMeasure_fill [Countable ι] [Countable T] [IsMarkovKernel κ] :
    ∀ s : PartialTree ι T, IsProbabilityMeasure (fill κ s)
  | .leaf (.terminal _) => by rw [fill_leaf_terminal]; infer_instance
  | .leaf (.nonterminal i) => by rw [fill_leaf_nonterminal]; infer_instance
  | .node _ cs => by
    have := isProbabilityMeasure_fillList cs
    rw [fill_node]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
theorem isProbabilityMeasure_fillList [Countable ι] [Countable T] [IsMarkovKernel κ] :
    ∀ ss : List (PartialTree ι T), IsProbabilityMeasure (fillList κ ss)
  | [] => by rw [fillList_nil]; infer_instance
  | s :: ss => by
    have := isProbabilityMeasure_fill s
    have := isProbabilityMeasure_fillList ss
    rw [fillList_cons]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
end

variable [Countable ι] [Countable T]

instance [IsMarkovKernel κ] : IsMarkovKernel (fill κ) := ⟨isProbabilityMeasure_fill⟩

instance [IsMarkovKernel κ] : IsMarkovKernel (fillList κ) := ⟨isProbabilityMeasure_fillList⟩

@[simp]
theorem fillList_cons_singleton_cons (s : PartialTree ι T) (ss : List (PartialTree ι T))
    (c : DerivationTree T ι) (cs : List (DerivationTree T ι)) :
    fillList κ (s :: ss) {c :: cs} = fill κ s {c} * fillList κ ss {cs} := by
  rw [fillList_cons, Measure.map_apply .of_discrete .of_discrete, ← Measure.prod_prod]
  congr 1
  ext ⟨_, _⟩
  simp

@[simp]
theorem fillList_cons_singleton_nil (s : PartialTree ι T) (ss : List (PartialTree ι T)) :
    fillList κ (s :: ss) {[]} = 0 := by
  rw [fillList_cons, Measure.map_apply .of_discrete .of_discrete]
  convert measure_empty (μ := (fill κ s).prod (fillList κ ss))
  ext ⟨_, _⟩
  simp

/-- A list of subtrees whose root symbols do not spell out the holes has mass `0`, for any family
of laws concentrated on trees of the right type. -/
theorem fillList_map_leaf_singleton_of_ne
    (hκ : ∀ i (c : DerivationTree T ι), c.rootSymbol ≠ .nonterminal i → κ i {c} = 0) :
    ∀ (syms : List (Symbol T ι)) (cs : List (DerivationTree T ι)),
      cs.map rootSymbol ≠ syms → fillList κ (syms.map leaf) {cs} = 0
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => fillList_nil_singleton_cons _ _
  | _ :: _, [], _ => fillList_cons_singleton_nil _ _
  | .terminal t :: rest, c :: cs, h => by
    rw [List.map_cons, fillList_cons_singleton_cons, fill_leaf_terminal, Measure.dirac_apply]
    by_cases hc : c = leaf t
    · subst hc
      simp only [List.map_cons, rootSymbol_leaf, ne_eq, List.cons.injEq, true_and] at h
      rw [fillList_map_leaf_singleton_of_ne hκ rest cs h, mul_zero]
    · simp [Ne.symm hc]
  | .nonterminal i :: rest, c :: cs, h => by
    rw [List.map_cons, fillList_cons_singleton_cons, fill_leaf_nonterminal]
    by_cases hc : c.rootSymbol = .nonterminal i
    · simp only [List.map_cons, hc, ne_eq, List.cons.injEq, true_and] at h
      rw [fillList_map_leaf_singleton_of_ne hκ rest cs h, mul_zero]
    · rw [hκ i c hc, zero_mul]

end Fill

/-! ### One generation -/

section Generation

variable (ξ : Kernel ι (List (Symbol T ι)))

mutual
private noncomputable def generationFun : PartialTree ι T → Measure (PartialTree ι T)
  | .leaf (.terminal t) => Measure.dirac (leaf (.terminal t))
  | .leaf (.nonterminal i) => (ξ i).map fun syms => node i (syms.map leaf)
  | .node i cs => (generationListFun cs).map (node i)
private noncomputable def generationListFun :
    List (PartialTree ι T) → Measure (List (PartialTree ι T))
  | [] => Measure.dirac []
  | s :: ss => ((generationFun s).prod (generationListFun ss)).map (Function.uncurry List.cons)
end

/-- One synchronous generation: every hole draws its offspring and becomes a node whose children
are fresh holes and marks. -/
noncomputable def generation : Kernel (PartialTree ι T) (PartialTree ι T) :=
  ⟨generationFun ξ, .of_discrete⟩

/-- One synchronous generation on a list of partial trees. -/
noncomputable def generationList : Kernel (List (PartialTree ι T)) (List (PartialTree ι T)) :=
  ⟨generationListFun ξ, .of_discrete⟩

@[simp] theorem generation_leaf_terminal (t : T) :
    generation ξ (leaf (.terminal t)) = Measure.dirac (leaf (.terminal t)) := rfl

@[simp] theorem generation_leaf_nonterminal (i : ι) :
    generation ξ (leaf (.nonterminal i)) = (ξ i).map fun syms => node i (syms.map leaf) := rfl

theorem generation_node (i : ι) (cs : List (PartialTree ι T)) :
    generation ξ (node i cs) = (generationList ξ cs).map (node i) := rfl

@[simp] theorem generationList_nil : generationList ξ [] = Measure.dirac [] := rfl

theorem generationList_cons (s : PartialTree ι T) (ss : List (PartialTree ι T)) :
    generationList ξ (s :: ss) =
      ((generation ξ s).prod (generationList ξ ss)).map (Function.uncurry List.cons) := rfl

mutual
theorem isProbabilityMeasure_generation [Countable ι] [Countable T] [IsMarkovKernel ξ] :
    ∀ s : PartialTree ι T, IsProbabilityMeasure (generation ξ s)
  | .leaf (.terminal _) => by rw [generation_leaf_terminal]; infer_instance
  | .leaf (.nonterminal i) => by
    rw [generation_leaf_nonterminal]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  | .node _ cs => by
    have := isProbabilityMeasure_generationList cs
    rw [generation_node]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
theorem isProbabilityMeasure_generationList [Countable ι] [Countable T] [IsMarkovKernel ξ] :
    ∀ ss : List (PartialTree ι T), IsProbabilityMeasure (generationList ξ ss)
  | [] => by rw [generationList_nil]; infer_instance
  | s :: ss => by
    have := isProbabilityMeasure_generation s
    have := isProbabilityMeasure_generationList ss
    rw [generationList_cons]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
end

instance [Countable ι] [Countable T] [IsMarkovKernel ξ] : IsMarkovKernel (generation ξ) :=
  ⟨isProbabilityMeasure_generation ξ⟩

instance [Countable ι] [Countable T] [IsMarkovKernel ξ] : IsMarkovKernel (generationList ξ) :=
  ⟨isProbabilityMeasure_generationList ξ⟩

variable [Countable ι] [MeasurableSingletonClass ι]

/-- One generation from a type `i`: a single hole of type `i` draws its offspring, and each type
among them grows a family tree with law `κ`. -/
noncomputable def expand (κ : Kernel ι (DerivationTree T ι)) : Kernel ι (DerivationTree T ι) :=
  (fill κ ∘ₖ generation ξ).comap (fun i => leaf (.nonterminal i)) .of_discrete

variable {ξ} {κ : Kernel ι (DerivationTree T ι)}

@[simp]
theorem expand_apply (i : ι) : expand ξ κ i = fill κ ∘ₘ generation ξ (leaf (.nonterminal i)) := by
  rw [expand, comap_apply, comp_apply]

theorem expand_apply' (i : ι) (s : Set (DerivationTree T ι)) :
    expand ξ κ i s = ∫⁻ syms, fillList κ (syms.map leaf) (node i ⁻¹' s) ∂ξ i := by
  rw [expand_apply, Measure.bind_apply .of_discrete (Kernel.aemeasurable _),
    generation_leaf_nonterminal, lintegral_map (Kernel.measurable_coe _ .of_discrete) .of_discrete]
  simp_rw [fill_node, Measure.map_apply .of_discrete .of_discrete]

mutual
/-- Filling with one more generation is one generation followed by filling. -/
theorem fill_expand_apply [Countable T] :
    ∀ s : PartialTree ι T, fill (expand ξ κ) s = fill κ ∘ₘ generation ξ s
  | .leaf (.terminal t) => by
    rw [fill_leaf_terminal, generation_leaf_terminal, Measure.dirac_bind (Kernel.measurable _),
      fill_leaf_terminal]
  | .leaf (.nonterminal i) => by rw [fill_leaf_nonterminal, expand_apply]
  | .node i cs => by
    rw [fill_node, generation_node, fillList_expand_apply cs,
      Measure.map_bind (Kernel.measurable _) .of_discrete,
      Measure.bind_map .of_discrete (Kernel.measurable _)]
    rfl
theorem fillList_expand_apply [Countable T] :
    ∀ ss : List (PartialTree ι T), fillList (expand ξ κ) ss = fillList κ ∘ₘ generationList ξ ss
  | [] => by
    rw [fillList_nil, generationList_nil, Measure.dirac_bind (Kernel.measurable _), fillList_nil]
  | s :: ss => by
    rw [fillList_cons, generationList_cons, fill_expand_apply s, fillList_expand_apply ss,
      ← Measure.parallelComp_comp_prod, Measure.map_comp _ _ .of_discrete,
      Measure.bind_map .of_discrete (Kernel.measurable _)]
    congr 1
    funext ⟨s', ss'⟩
    rw [Function.comp_apply, Function.uncurry_apply_pair, fillList_cons,
      Kernel.map_apply _ .of_discrete, parallelComp_apply]
end

variable [Countable T]

instance [IsMarkovKernel ξ] [IsMarkovKernel κ] : IsMarkovKernel (expand ξ κ) := by
  rw [expand]; infer_instance

/-- Filling with one more generation is one generation followed by filling. -/
theorem fill_expand : fill (expand ξ κ) = fill κ ∘ₖ generation ξ :=
  Kernel.ext fill_expand_apply

end Generation

/-! ### The weight of a finite family tree -/

section Weight

variable (ξ : Kernel ι (List (Symbol T ι)))

mutual
/-- The probability of a finite family tree: the product over its internal nodes of the
offspring probability of the list of symbols below that node. -/
noncomputable def weight : DerivationTree T ι → ℝ≥0∞
  | .leaf _ => 1
  | .node i cs => ξ i {cs.map rootSymbol} * weightList cs
/-- The product of the weights of a list of family trees. -/
noncomputable def weightList : List (DerivationTree T ι) → ℝ≥0∞
  | [] => 1
  | c :: cs => weight c * weightList cs
end

end Weight

/-! ### The law of the family tree -/

section Law

variable (ξ : Kernel ι (List (Symbol T ι))) [Countable ι] [MeasurableSingletonClass ι]

mutual
theorem ωScottContinuous_fill [Countable T] (s : PartialTree ι T) :
    ωScottContinuous fun κ : ι → Measure (DerivationTree T ι) => fill (ofFunOfCountable κ) s := by
  cases s with
  | leaf s =>
    cases s with
    | terminal t => exact ωScottContinuous.const
    | nonterminal i => exact ωScottContinuous.apply i
  | node i cs => exact Measure.ωScottContinuous_map (ωScottContinuous_fillList cs) .of_discrete
theorem ωScottContinuous_fillList [Countable T] (ss : List (PartialTree ι T)) :
    ωScottContinuous fun κ : ι → Measure (DerivationTree T ι) =>
      fillList (ofFunOfCountable κ) ss := by
  cases ss with
  | nil => exact ωScottContinuous.const
  | cons s ss =>
    exact Measure.ωScottContinuous_map
      (Measure.ωScottContinuous_prod (ωScottContinuous_fill s) (ωScottContinuous_fillList ss))
      .of_discrete
end

variable [Countable T]

theorem ωScottContinuous_expand :
    ωScottContinuous fun κ : ι → Measure (DerivationTree T ι) => ⇑(expand ξ (ofFunOfCountable κ)) :=
  ωScottContinuous.of_apply₂ fun i => by
    simp only [expand_apply]
    exact Measure.ωScottContinuous_bind_right (fun s => ωScottContinuous_fill s) fun _ =>
      Kernel.measurable _

/-- The generation operator on families of laws indexed by type, as an order homomorphism. -/
noncomputable def expandHom :
    (ι → Measure (DerivationTree T ι)) →o (ι → Measure (DerivationTree T ι)) :=
  ⟨fun κ => ⇑(expand ξ (ofFunOfCountable κ)), (ωScottContinuous_expand ξ).monotone⟩

/-- The law of the family tree of an individual of each type, on finite trees: the least fixed
point of the generation operator. Its total mass is the extinction probability. -/
noncomputable def law : Kernel ι (DerivationTree T ι) := ofFunOfCountable (expandHom ξ).lfp

theorem expand_law : expand ξ (law ξ) = law ξ :=
  Kernel.ext fun i => congrFun (expandHom ξ).map_lfp i

theorem coe_iterate_expand : ∀ n : ℕ, ⇑((expand ξ)^[n] 0) = (expandHom ξ)^[n] ⊥
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← coe_iterate_expand n]
    rfl

/-- The law is the supremum of the Kleene iterates of `expand` from the zero kernel. -/
theorem law_eq_iSup_iterate : ⇑(law ξ) = ⨆ n, ⇑((expand ξ)^[n] 0) := by
  simp_rw [coe_iterate_expand]
  exact OrderHom.lfp_eq_iSup_iterate _ fun c => by
    show ⇑(expand ξ (ofFunOfCountable (⨆ n, c n))) = ⨆ n, ⇑(expand ξ (ofFunOfCountable (c n)))
    rw [← Pi.ωSup_eq_iSup (L := fun _ => Measure (DerivationTree T ι)) c,
      (ωScottContinuous_expand ξ).map_ωSup, Pi.ωSup_eq_iSup]
    rfl

theorem monotone_iterate_expand : Monotone fun n => ⇑((expand ξ)^[n] 0) := by
  simp_rw [coe_iterate_expand]
  exact (expandHom ξ).iterate_bot_mono

theorem law_singleton_of_ne {t : DerivationTree T ι} {i : ι} (h : t.rootSymbol ≠ .nonterminal i) :
    law ξ i {t} = 0 := by
  rw [← expand_law, expand_apply']
  have : node i ⁻¹' ({t} : Set (DerivationTree T ι)) = ∅ := by
    ext cs
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact h rfl
  simp [this]

mutual
/-- A family tree of an individual of type `i` has probability `weight` under the law at `i`. -/
theorem law_singleton_node (i : ι) (cs : List (DerivationTree T ι)) :
    law ξ i {node i cs} = weight ξ (node i cs) := by
  rw [← expand_law, expand_apply', weight]
  have hpre : node i ⁻¹' ({node i cs} : Set (DerivationTree T ι)) = {cs} := by ext; simp
  have hind : (fun syms => fillList (law ξ) (syms.map leaf) {cs}) =
      ({cs.map rootSymbol} : Set (List (Symbol T ι))).indicator fun _ => weightList ξ cs := by
    funext syms
    by_cases hs : cs.map rootSymbol = syms
    · subst hs
      rw [fillList_law_singleton cs, Set.indicator_of_mem (Set.mem_singleton _)]
    · rw [fillList_map_leaf_singleton_of_ne (fun _ _ => law_singleton_of_ne ξ) _ _ hs,
        Set.indicator_of_notMem (by simpa using Ne.symm hs)]
  rw [hpre, hind, lintegral_indicator_const .of_discrete, mul_comm]
/-- A list of family trees has probability `weightList` below the holes it spells out. -/
theorem fillList_law_singleton (cs : List (DerivationTree T ι)) :
    fillList (law ξ) ((cs.map rootSymbol).map leaf) {cs} = weightList ξ cs := by
  cases cs with
  | nil => simp [weightList]
  | cons c cs =>
    cases c with
    | leaf t =>
      rw [List.map_cons, List.map_cons, fillList_cons_singleton_cons, fillList_law_singleton cs,
        weightList, rootSymbol_leaf, fill_leaf_terminal, weight]
      simp
    | node i cs' =>
      rw [List.map_cons, List.map_cons, fillList_cons_singleton_cons, fillList_law_singleton cs,
        weightList, rootSymbol, fill_leaf_nonterminal, law_singleton_node i cs']
end

open scoped Classical in
/-- Under the law at `i`, a finite tree has probability `weight` when its root has type `i`
and `0` otherwise. -/
theorem law_singleton (t : DerivationTree T ι) (i : ι) :
    law ξ i {t} = if t.rootSymbol = .nonterminal i then weight ξ t else 0 := by
  split_ifs with h
  · cases t with
    | leaf t => simp at h
    | node j cs =>
      obtain rfl : i = j := (by simpa using h.symm)
      exact law_singleton_node ξ i cs
  · exact law_singleton_of_ne ξ h

/-! ### Extinction -/

variable {ξ}

theorem expand_univ_le_one (hξ : ∀ i, ξ i Set.univ ≤ 1) {κ : Kernel ι (DerivationTree T ι)}
    (hκ : ∀ i, κ i Set.univ ≤ 1) (i : ι) : expand ξ κ i Set.univ ≤ 1 := by
  rw [expand_apply, Measure.bind_apply .univ (Kernel.aemeasurable _)]
  calc ∫⁻ s, fill κ s Set.univ ∂generation ξ (leaf (.nonterminal i))
      ≤ ∫⁻ _, 1 ∂generation ξ (leaf (.nonterminal i)) :=
        lintegral_mono fun s => fill_univ_le_one hκ s
    _ = ξ i Set.univ := by
      rw [lintegral_one, generation_leaf_nonterminal, Measure.map_apply .of_discrete .univ,
        Set.preimage_univ]
    _ ≤ 1 := hξ i

theorem iterate_expand_univ_le_one (hξ : ∀ i, ξ i Set.univ ≤ 1) :
    ∀ (n : ℕ) (i : ι), ((expand ξ)^[n] 0) i Set.univ ≤ 1
  | 0, _ => by simp
  | n + 1, i => by
    rw [Function.iterate_succ_apply']
    exact expand_univ_le_one hξ (iterate_expand_univ_le_one hξ n) i

/-- With sub-probability offspring, the law on finite family trees is a sub-probability kernel;
the missing mass is the probability of survival forever. -/
theorem law_univ_le_one (hξ : ∀ i, ξ i Set.univ ≤ 1) (i : ι) : law ξ i Set.univ ≤ 1 := by
  rw [law_eq_iSup_iterate, iSup_apply,
    Measure.iSup_apply_of_monotone (fun m n h => monotone_iterate_expand ξ h i) .univ]
  exact iSup_le fun n => iterate_expand_univ_le_one hξ n i

variable (ξ)

/-- The extinction probability of an individual of type `i`: the total mass of the law on finite
family trees, which for Markov offspring is the probability that the family tree is finite. -/
noncomputable def extinctionProb (i : ι) : ℝ≥0∞ := law ξ i Set.univ

/-! ### Generations -/

/-- The `n`-th Kleene iterate fills a partial tree exactly as `n` synchronous generations do,
followed by the completion of what remains. -/
theorem fill_iterate : ∀ n : ℕ, fill ((expand ξ)^[n] 0) = fill 0 ∘ₖ (generation ξ ^ n)
  | 0 => (comp_id _).symm
  | n + 1 => by
    rw [Function.iterate_succ_apply', fill_expand, fill_iterate n, comp_assoc, pow_succ]
    rfl

/-- The law of the family tree at type `i` is the supremum over `n` of the completed part of
`n` synchronous generations from a single hole of type `i`. -/
theorem law_eq_iSup_generation (i : ι) :
    law ξ i = ⨆ n, fill 0 ∘ₘ (generation ξ ^ n) (leaf (.nonterminal i)) := by
  rw [law_eq_iSup_iterate, iSup_apply]
  exact iSup_congr fun n => by rw [← fill_leaf_nonterminal, fill_iterate, comp_apply]

end Law

/-! ### The generation chain as a Markov chain -/

section Chain

variable (ξ : Kernel ι (List (Symbol T ι)))

/-- The generation chain in Ionescu–Tulcea form: the state at time `n + 1` depends on the
trajectory up to time `n` only through its last coordinate. -/
noncomputable def chainKernel (n : ℕ) :
    Kernel (Π i : Iic n, (fun _ : ℕ => PartialTree ι T) i)
      ((fun _ : ℕ => PartialTree ι T) (n + 1)) :=
  (generation ξ).comap (fun x => x ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

variable [Countable ι] [Countable T] [IsMarkovKernel ξ]

instance (n : ℕ) : IsMarkovKernel (chainKernel ξ n) := IsMarkovKernel.comap _ _

/-- The Ionescu–Tulcea trajectory kernel of the generation chain. -/
noncomputable def chainTraj (n : ℕ) :
    Kernel (Π i : Iic n, (fun _ : ℕ => PartialTree ι T) i) (ℕ → PartialTree ι T) :=
  traj (X := fun _ : ℕ => PartialTree ι T) (chainKernel ξ) n

/-- The law of the whole trajectory of generations started at a partial tree. -/
noncomputable def trajectory (s : PartialTree ι T) : Measure (ℕ → PartialTree ι T) :=
  chainTraj ξ 0 fun _ => s

instance (s : PartialTree ι T) : IsProbabilityMeasure (trajectory ξ s) :=
  inferInstanceAs (IsProbabilityMeasure
    (traj (X := fun _ : ℕ => PartialTree ι T) (chainKernel ξ) 0 _))

/-- At time `n` the generation chain is distributed as `n` synchronous generations. -/
theorem trajectory_map_eval (s : PartialTree ι T) :
    ∀ n : ℕ, (trajectory ξ s).map (fun ω => ω n) = (generation ξ ^ n) s
  | 0 => by
    have h := traj_map_frestrictLe_apply (X := fun _ : ℕ => PartialTree ι T) (κ := chainKernel ξ)
      0 0 (fun _ => s)
    rw [partialTraj_self, Kernel.id_apply] at h
    show (trajectory ξ s).map (fun ω => ω 0) = Measure.dirac s
    have hm : (trajectory ξ s).map (fun ω => ω 0) = ((trajectory ξ s).map (frestrictLe 0)).map
        (fun x : Π i : Iic 0, (fun _ : ℕ => PartialTree ι T) i => x ⟨0, mem_Iic.2 le_rfl⟩) :=
      (Measure.map_map (μ := trajectory ξ s) (measurable_pi_apply (⟨0, mem_Iic.2 le_rfl⟩ : Iic 0))
        (measurable_frestrictLe 0)).symm
    rw [hm, show (trajectory ξ s).map (frestrictLe 0) = Measure.dirac (fun _ => s) from h]
    exact Measure.map_dirac _
  | n + 1 => by
    have hpt : ∀ x : Π i : Iic n, (fun _ : ℕ => PartialTree ι T) i,
        (traj (X := fun _ : ℕ => PartialTree ι T) (chainKernel ξ) n x).map (fun ω => ω (n + 1)) =
          generation ξ (x ⟨n, mem_Iic.2 le_rfl⟩) := fun x => by
      rw [← Kernel.map_apply (traj (X := fun _ : ℕ => PartialTree ι T) (chainKernel ξ) n)
          (measurable_pi_apply (n + 1)) x,
        map_traj_succ_self (X := fun _ : ℕ => PartialTree ι T) (κ := chainKernel ξ), chainKernel,
        comap_apply]
    have hmarg : (trajectory ξ s).map (fun ω => ω n) =
        (partialTraj (X := fun _ : ℕ => PartialTree ι T) (chainKernel ξ) 0 n (fun _ => s)).map
          (fun x : Π i : Iic n, (fun _ : ℕ => PartialTree ι T) i => x ⟨n, mem_Iic.2 le_rfl⟩) := by
      rw [← traj_map_frestrictLe_apply (X := fun _ : ℕ => PartialTree ι T) (κ := chainKernel ξ) 0 n
        (fun _ => s)]
      exact (Measure.map_map (μ := trajectory ξ s)
        (measurable_pi_apply (⟨n, mem_Iic.2 le_rfl⟩ : Iic n)) (measurable_frestrictLe n)).symm
    have hcomp := traj_comp_partialTraj (X := fun _ : ℕ => PartialTree ι T) (κ := chainKernel ξ)
      (Nat.zero_le n)
    calc (trajectory ξ s).map (fun ω => ω (n + 1))
        = ((partialTraj (X := fun _ : ℕ => PartialTree ι T) (chainKernel ξ) 0 n (fun _ => s)).bind
            (traj (X := fun _ : ℕ => PartialTree ι T) (chainKernel ξ) n)).map
              (fun ω => ω (n + 1)) := by
          rw [trajectory, chainTraj, ← hcomp, comp_apply]
      _ = (partialTraj (X := fun _ : ℕ => PartialTree ι T) (chainKernel ξ) 0 n (fun _ => s)).bind
            fun x => generation ξ (x ⟨n, mem_Iic.2 le_rfl⟩) := by
          rw [Measure.map_bind (Kernel.measurable _) (measurable_pi_apply _)]
          simp_rw [hpt]
      _ = ((partialTraj (X := fun _ : ℕ => PartialTree ι T) (chainKernel ξ) 0 n (fun _ => s)).map
            (fun x : Π i : Iic n, (fun _ : ℕ => PartialTree ι T) i => x ⟨n, mem_Iic.2 le_rfl⟩)).bind
              (generation ξ) :=
          (Measure.bind_map (measurable_pi_apply _) (Kernel.measurable _)).symm
      _ = generation ξ ∘ₘ (generation ξ ^ n) s := by rw [← hmarg, trajectory_map_eval s n]
      _ = (generation ξ ^ (n + 1)) s := by rw [pow_succ']; rfl

end Chain

end ProbabilityTheory.GaltonWatson
