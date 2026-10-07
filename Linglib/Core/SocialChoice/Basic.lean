module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.Unbundled
public import Linglib.Core.Order.Antisymmetrization

/-!
# Social welfare functionals

In Sen's framework for social choice with interpersonal comparisons, each individual assigns each
alternative a value, and a rule sends every profile of values to an overall relation on the
alternatives, read `x ⪰ y`. Here a profile assigns each alternative its vector of values, one per
individual; the individuals may equally be voters, criteria or dimensions.

The informational requirements on a rule are invariance under a class of transformation vectors:
strictly increasing maps, common-unit positive affine maps, similarities, and the comparability
classes that apply one map to every individual. Arrow's conditions and the strong Pareto,
Pareto-indifference and anonymity conditions are predicates on rules.

## Main definitions

* `SocialChoice.Profile`, `SocialChoice.Rule`: profiles of values and rules on them.
* `SocialChoice.Invariant`: invariance under a class of transformation vectors, with the classes
  `ordinal`, `ordinalLevel`, `cardinalUnit`, `ratio`, `cardinalFull` and `ratioFull`.
* `SocialChoice.WeakPareto`, `SocialChoice.Independent`, `SocialChoice.WeakOrderValued`,
  `SocialChoice.IsDictator`: Arrow's conditions.

## Implementation notes

* A rule is total on profiles, so Arrow's unrestricted-domain condition is built in; a domain
  restriction is a hypothesis of the statement that needs it.
* Outputs are bare relations, since majority rule is not transitive. `AsymmRel` is the strict
  part of an output and `AntisymmRel` its indifference part.

## References

* [arrow-1950]
* [sen-1970]
-/

@[expose] public section

namespace SocialChoice

variable {ι α K : Type*}

/-- A profile assigns each alternative its vector of values, one per individual. -/
abbrev Profile (ι α K : Type*) := α → ι → K

/-- An aggregation rule assigns to each profile a relation on the alternatives, read `x ⪰ y`. -/
abbrev Rule (ι α K : Type*) := Profile ι α K → α → α → Prop

/-- A vector of transformations, one per individual, applied to a profile. -/
def Profile.transform (f : ι → K → K) (v : Profile ι α K) : Profile ι α K :=
  fun x i ↦ f i (v x i)

/-! ### Informational invariance -/

/-- Invariance of a function of profiles, such as a rule or a statement about values, under a class
of transformation vectors. -/
def Invariant {β : Type*} (T : Set (ι → K → K)) (a : Profile ι α K → β) : Prop :=
  ∀ f ∈ T, ∀ v, a (v.transform f) = a v

theorem Invariant.mono {β : Type*} {S T : Set (ι → K → K)} (h : S ⊆ T) {a : Profile ι α K → β}
    (ha : Invariant T a) : Invariant S a :=
  fun f hf ↦ ha f (h hf)

/-- Vectors of strictly increasing transformations; invariance under them is ordinal
non-comparability. -/
def ordinal [Preorder K] : Set (ι → K → K) := {f | ∀ i, StrictMono (f i)}

/-- Vectors applying one strictly increasing transformation to every individual; invariance under
them is ordinal level comparability. -/
def ordinalLevel [Preorder K] : Set (ι → K → K) := {f | ∃ u : K → K, StrictMono u ∧ ∀ i, f i = u}

theorem ordinalLevel_subset_ordinal [Preorder K] : ordinalLevel ⊆ (ordinal : Set (ι → K → K)) :=
  fun _ ⟨_, hu, hf⟩ i ↦ hf i ▸ hu

section Cardinal

variable [Semiring K] [PartialOrder K]

/-- Common-unit positive affine transformation vectors; invariance under them is cardinal unit
comparability. -/
def cardinalUnit : Set (ι → K → K) :=
  {f | ∃ a : K, 0 < a ∧ ∃ b : ι → K, ∀ i t, f i t = a * t + b i}

/-- Similarity transformation vectors; invariance under them is ratio-scale
non-comparability. -/
def ratio : Set (ι → K → K) := {f | ∃ a : ι → K, (∀ i, 0 < a i) ∧ ∀ i t, f i t = a i * t}

/-- Vectors applying one positive affine transformation to every individual; invariance under them
is cardinal full comparability. -/
def cardinalFull : Set (ι → K → K) := {f | ∃ a : K, 0 < a ∧ ∃ b : K, ∀ i t, f i t = a * t + b}

/-- Vectors applying one similarity transformation to every individual; invariance under them is
ratio-scale full comparability. -/
def ratioFull : Set (ι → K → K) := {f | ∃ a : K, 0 < a ∧ ∀ i t, f i t = a * t}

theorem cardinalFull_subset_cardinalUnit : cardinalFull ⊆ (cardinalUnit : Set (ι → K → K)) :=
  fun _ ⟨a, ha, b, hf⟩ ↦ ⟨a, ha, fun _ ↦ b, hf⟩

theorem ratioFull_subset_cardinalFull : ratioFull ⊆ (cardinalFull : Set (ι → K → K)) :=
  fun _ ⟨a, ha, hf⟩ ↦ ⟨a, ha, 0, fun i t ↦ by rw [hf, add_zero]⟩

theorem ratioFull_subset_ratio : ratioFull ⊆ (ratio : Set (ι → K → K)) :=
  fun _ ⟨a, ha, hf⟩ ↦ ⟨fun _ ↦ a, fun _ ↦ ha, hf⟩

variable [IsStrictOrderedRing K]

theorem cardinalFull_subset_ordinalLevel : cardinalFull ⊆ (ordinalLevel : Set (ι → K → K)) :=
  fun _ ⟨a, ha, b, hf⟩ ↦ ⟨(a * · + b), fun _ _ hst ↦ add_lt_add_left
    (mul_lt_mul_of_pos_left hst ha) _, fun i ↦ funext (hf i)⟩

theorem cardinalUnit_subset_ordinal : cardinalUnit ⊆ (ordinal : Set (ι → K → K)) := by
  rintro f ⟨a, ha, b, hf⟩ i s t hst
  simp only [hf]
  exact add_lt_add_left (mul_lt_mul_of_pos_left hst ha) _

theorem ratio_subset_ordinal : ratio ⊆ (ordinal : Set (ι → K → K)) := by
  rintro f ⟨a, ha, hf⟩ i s t hst
  simp only [hf]
  exact mul_lt_mul_of_pos_left hst (ha i)

end Cardinal

/-! ### Conditions on rules -/

section Conditions

variable (a : Rule ι α K)

/-- Pareto indifference says that alternatives with the same vector of values are indifferent. -/
def ParetoIndifferent : Prop := ∀ v x y, v x = v y → AntisymmRel (a v) x y

/-- Independence of irrelevant alternatives says that the verdict on a pair depends only on the
vectors of that pair. -/
def Independent : Prop := ∀ v w x y, v x = w x → v y = w y → (a v x y ↔ a w x y)

/-- Every output is transitive. -/
def Transitive : Prop := ∀ v, IsTrans α (a v)

/-- Every output is complete. -/
def Complete : Prop := ∀ v, Std.Total (a v)

/-- Every output is a weak ordering, a complete preorder. -/
def WeakOrderValued : Prop := Transitive a ∧ Complete a

/-- Every output is a quasi-ordering, a preorder. -/
def QuasiOrderValued : Prop := ∀ v, IsPreorder α (a v)

/-- Anonymity says that permuting the individuals leaves the output unchanged. -/
def Anonymous : Prop := ∀ (σ : Equiv.Perm ι) v, a (fun x ↦ v x ∘ σ) = a v

variable {a}

theorem WeakOrderValued.quasiOrderValued (h : WeakOrderValued a) : QuasiOrderValued a :=
  fun v ↦
    haveI := h.1 v
    haveI := h.2 v
    IsPreorder.mk

variable (a) [Preorder K]

/-- Weak Pareto says that an alternative every individual ranks strictly above another is strictly
preferred. -/
def WeakPareto : Prop := ∀ v x y, (∀ i, v y i < v x i) → AsymmRel (a v) x y

/-- Strong Pareto says that an alternative every individual ranks weakly above another is weakly
preferred, and strictly so if some individual ranks it strictly above. -/
def StrongPareto : Prop :=
  ∀ v x y, v y ≤ v x → a v x y ∧ ((∃ i, v y i < v x i) → AsymmRel (a v) x y)

/-- Individual `i` is a dictator when its strict rankings are the strict overall rankings. -/
def IsDictator (i : ι) : Prop := ∀ v x y, v y i < v x i → AsymmRel (a v) x y

/-- No individual is a dictator. -/
def NonDictatorial : Prop := ∀ i, ¬ IsDictator a i

end Conditions

end SocialChoice
