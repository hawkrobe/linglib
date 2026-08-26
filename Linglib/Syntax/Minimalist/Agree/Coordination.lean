import Linglib.Syntax.Minimalist.Features
import Mathlib.Data.List.Basic

/-!
# Coordination resolution over a dual-feature system

This file defines resolution of gender features on a coordinate structure in a dual-feature
system: a nominal's features are interpretable, sent to LF, or uninterpretable, sent to PF, and
resolution is the composition of *percolation*, which collects one feature set from each conjunct
at the coordination, with *conversion*, which intersects the interpretable sets so that the group
bears exactly the features every member has. Uninterpretable sets are not intersected; they are
realized set by set, and realization converges only when every set receives the same exponent. A
feature geometry records, for each node, the nodes it entails, and a geometry satisfies mismatch
resolution when every pair of its nodes resolves to something without default insertion.

## Main definitions

* `Minimalist.Coordination.Annotated`, `Minimalist.Coordination.Bundle`: features annotated for
  interpretability and the feature sets of a nominal.
* `Minimalist.Coordination.percolate`, `Minimalist.Coordination.percolateU`: the interpretable and
  uninterpretable sets a conjunct contributes.
* `Minimalist.Coordination.conversion`, `Minimalist.Coordination.resolve`,
  `Minimalist.Coordination.resolveN`: intersection of percolated interpretable sets.
* `Minimalist.Coordination.redundancy`: the copying of interpretable values into empty
  uninterpretable slots at Transfer.
* `Minimalist.Coordination.realizeAll`: realization of a family of feature sets, converging only
  on a single exponent.
* `Minimalist.Coordination.MismatchResolutionOn`, `Minimalist.Coordination.Geometry`,
  `Geometry.Entails`, `Geometry.MismatchResolution`.

## Main statements

* `Minimalist.Coordination.resolveN_binary`: n-ary resolution restricts to binary resolution.
* `Minimalist.Coordination.resolve_self`: uniform conjuncts resolve to their shared features.

## References

* [adamson-anagnostopoulou-2025]
* [smith-2015]
-/

namespace Minimalist.Coordination

variable {F E : Type*}

/-- A feature value annotated for interpretability. -/
structure Annotated (F : Type*) where
  value : F
  interp : Interpretability
  deriving DecidableEq, Repr

/-- The gender features of a nominal, interpretable and uninterpretable. -/
abbrev Bundle (F : Type*) := List (Annotated F)

/-- The interpretable values of a bundle: what percolates to LF-bound resolution. -/
def percolate (fs : Bundle F) : List F :=
  (fs.filter (·.interp = .interpretable)).map (·.value)

/-- The uninterpretable values of a bundle. -/
def percolateU (fs : Bundle F) : List F :=
  (fs.filter (·.interp = .uninterpretable)).map (·.value)

/-- Interpretable annotation of every value in a list. -/
def interpretable (vs : List F) : Bundle F := vs.map fun v => ⟨v, .interpretable⟩

/-- Uninterpretable annotation of every value in a list. -/
def uninterpretable (vs : List F) : Bundle F := vs.map fun v => ⟨v, .uninterpretable⟩

@[simp] theorem percolate_interpretable (vs : List F) : percolate (interpretable vs) = vs := by
  simp [percolate, interpretable, List.filter_map, Function.comp_def]

@[simp] theorem percolateU_uninterpretable (vs : List F) :
    percolateU (uninterpretable vs) = vs := by
  simp [percolateU, uninterpretable, List.filter_map, Function.comp_def]

@[simp] theorem percolate_append (fs gs : Bundle F) :
    percolate (fs ++ gs) = percolate fs ++ percolate gs := by
  simp [percolate]

@[simp] theorem percolateU_append (fs gs : Bundle F) :
    percolateU (fs ++ gs) = percolateU fs ++ percolateU gs := by
  simp [percolateU]

@[simp] theorem percolate_uninterpretable (vs : List F) : percolate (uninterpretable vs) = [] := by
  simp [percolate, uninterpretable, List.filter_map, Function.comp_def]

@[simp] theorem percolateU_interpretable (vs : List F) : percolateU (interpretable vs) = [] := by
  simp [percolateU, interpretable, List.filter_map, Function.comp_def]

/-- The redundancy rule at Transfer: interpretable values fill an empty uninterpretable slot. -/
def redundancy (iFs uFs : List F) : List F := if uFs.isEmpty then iFs else uFs

@[simp] theorem redundancy_nil (iFs : List F) : redundancy iFs [] = iFs := rfl

theorem redundancy_of_ne_nil (iFs : List F) {uFs : List F} (h : uFs ≠ []) :
    redundancy iFs uFs = uFs := by
  simp [redundancy, h]

/-- Realization of a family of feature sets: the exponent they all receive, if they agree. -/
def realizeAll [DecidableEq E] (realize : List F → Option E) : List (List F) → Option E
  | [] => none
  | s :: ss => if ∀ t ∈ ss, realize t = realize s then realize s else none

@[simp] theorem realizeAll_singleton [DecidableEq E] (realize : List F → Option E) (s : List F) :
    realizeAll realize [s] = realize s := by
  simp [realizeAll]

theorem realizeAll_pair [DecidableEq E] (realize : List F → Option E) (s t : List F) :
    realizeAll realize [s, t] = if realize t = realize s then realize s else none := by
  simp [realizeAll]

variable [DecidableEq F]

/-- Conversion: the values shared by two percolated sets, in the order of the first. -/
def conversion (xs ys : List F) : List F := xs.filter (· ∈ ys)

theorem mem_conversion {xs ys : List F} {v : F} : v ∈ conversion xs ys ↔ v ∈ xs ∧ v ∈ ys := by
  simp [conversion]

@[simp] theorem conversion_self (xs : List F) : conversion xs xs = xs :=
  List.filter_eq_self.2 fun _ h => decide_eq_true h

/-- Resolution of two conjuncts: the shared interpretable values, none if there are none. -/
def resolve (fs gs : Bundle F) : Option (List F) :=
  match conversion (percolate fs) (percolate gs) with
  | [] => none
  | vs => some vs

/-- Resolution of a family of conjuncts by iterated conversion. -/
def resolveN (bundles : List (Bundle F)) : Option (List F) :=
  match bundles.map percolate with
  | [] => none
  | first :: rest =>
    match rest.foldl conversion first with
    | [] => none
    | vs => some vs

theorem resolveN_binary (fs gs : Bundle F) : resolveN [fs, gs] = resolve fs gs := rfl

/-- Uniform conjuncts resolve to their shared features. -/
theorem resolve_self (fs : Bundle F) (h : percolate fs ≠ []) :
    resolve fs fs = some (percolate fs) := by
  unfold resolve
  rw [conversion_self]
  split
  · exact absurd (by assumption) h
  · rfl

/-- Every pair of bundles resolves without default insertion. -/
def MismatchResolutionOn (bundles : List (Bundle F)) : Prop :=
  ∀ a ∈ bundles, ∀ b ∈ bundles, (resolve a b).isSome

instance (bundles : List (Bundle F)) : Decidable (MismatchResolutionOn bundles) :=
  inferInstanceAs (Decidable (∀ a ∈ bundles, ∀ b ∈ bundles, _ = true))

/-- A feature geometry: for each node, the nodes it entails, itself included. -/
structure Geometry (F : Type*) where
  /-- The nodes. -/
  nodes : List F
  /-- The closure of a node under entailment. -/
  above : F → List F

namespace Geometry

variable (G : Geometry F)

/-- `a` entails `b` when `b`'s closure lies within `a`'s. -/
def Entails (a b : F) : Prop := List.Subset (G.above b) (G.above a)

instance (a b : F) : Decidable (G.Entails a b) :=
  inferInstanceAs (Decidable (∀ x, x ∈ G.above b → x ∈ G.above a))

/-- Every pair of nodes resolves without default insertion. -/
def MismatchResolution : Prop :=
  MismatchResolutionOn (G.nodes.map fun a => interpretable (G.above a))

instance : Decidable G.MismatchResolution := inferInstanceAs (Decidable (MismatchResolutionOn _))

end Geometry

end Minimalist.Coordination
