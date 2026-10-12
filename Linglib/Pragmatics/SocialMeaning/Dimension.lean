module

public import Linglib.Core.Combinatorics.SimpleGraph.MaximalIndepSet
public import Mathlib.Basic.Sign.Defs

/-!
# Dimensions of social evaluation

This file defines the incompatibility of properties that are values of dimensions, and the
dimensions on which hearers evaluate a speaker. Two properties are incompatible when they are
distinct values of one dimension, so a persona, Burnett's maximal set of compatible properties,
takes one value of each dimension. The dimensions of social evaluation are competence and
warmth, the two universal dimensions of social cognition of the Stereotype Content Model, and
anti-solidarity, the factor of Beltrama, Solt and Burnett's ratings that loads apart from
warmth, and their values are their two poles.

## Main definitions

* `SocialMeaning.incompatible`: the graph joining distinct values of one dimension.
* `Dimension`: competence, warmth and anti-solidarity.
* `Pole`: the six ends of the dimensions, with `Pole.dimension` and `Pole.polarity`.
* `Pole.opposite`: the other end of a pole's dimension.

## Main results

* `SocialMeaning.mem_maximalIndepSets_incompatible_iff`: the personae are the sets with exactly
  one value of each dimension.
* `Pole.eq_iff`: a pole is determined by its dimension and polarity.
* `Pole.incompatible_adj_iff`: two poles are incompatible when one is opposite the other.

## References

* [fiske-cuddy-glick-xu-2002]
* [fiske-cuddy-glick-2007]
* [beltrama-solt-burnett-2023]
* [burnett-2019]
-/

@[expose] public section

namespace SocialMeaning

section Incompatible

variable {P D : Type*} {dim : P → D}

/-- The incompatibility graph of a family of dimensions joins two properties when they are
distinct values of one dimension. -/
def incompatible (dim : P → D) : SimpleGraph P where
  Adj p q := p ≠ q ∧ dim p = dim q
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

@[simp] theorem incompatible_adj {p q : P} :
    (incompatible dim).Adj p q ↔ p ≠ q ∧ dim p = dim q := Iff.rfl

instance [DecidableEq P] [DecidableEq D] : DecidableRel (incompatible dim).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A set of properties is consistent when it takes at most one value of each dimension. -/
theorem isIndepSet_incompatible_iff {s : Set P} :
    (incompatible dim).IsIndepSet s ↔ s.InjOn dim := by
  simp only [SimpleGraph.IsIndepSet, Set.Pairwise, incompatible_adj, Set.InjOn]
  grind

/-- The personae of a family of dimensions are the sets with exactly one value of each dimension
that has values. -/
theorem mem_maximalIndepSets_incompatible_iff [Fintype P] [DecidableEq P] [DecidableEq D]
    {s : Finset P} :
    s ∈ (incompatible dim).maximalIndepSets ↔ ∀ p, (s.filter (dim · = dim p)).card = 1 := by
  simp only [SimpleGraph.mem_maximalIndepSets,
    SimpleGraph.maximal_isIndepSet_iff_forall_exists_adj, isIndepSet_incompatible_iff,
    incompatible_adj, Set.InjOn, Finset.mem_coe, ← Nat.le_antisymm_iff.symm, Finset.card_le_one,
    Finset.one_le_card, Finset.Nonempty, Finset.mem_filter, forall_and]
  refine and_congr ⟨fun h _ _ ha _ hb ↦ h ha.1 hb.1 (ha.2.trans hb.2.symm),
    fun h a ha b hb hab ↦ h a a ⟨ha, rfl⟩ b ⟨hb, hab.symm⟩⟩ ⟨fun h p ↦ ?_, fun h v hv ↦ ?_⟩
  · by_cases hp : p ∈ s
    · exact ⟨p, hp, rfl⟩
    · obtain ⟨w, hw, -, h⟩ := h p hp
      exact ⟨w, hw, h.symm⟩
  · obtain ⟨w, hw, h⟩ := h v
    exact ⟨w, hw, fun e ↦ hv (e ▸ hw), h.symm⟩

end Incompatible

/-- The dimensions of social evaluation are competence and warmth, and anti-solidarity, the
factor on which pedantic and uptight load apart from the warmth scales. -/
inductive Dimension where
  | competence
  | warmth
  | antiSolidarity
  deriving DecidableEq

instance : Fintype Dimension :=
  ⟨{.competence, .warmth, .antiSolidarity}, fun d ↦ by cases d <;> simp⟩

/-- A pole is one end of a dimension of social evaluation. -/
inductive Pole where
  | competent
  | incompetent
  | warm
  | cold
  | solidary
  | antiSolidary
  deriving DecidableEq

instance : Fintype Pole :=
  ⟨{.competent, .incompetent, .warm, .cold, .solidary, .antiSolidary}, fun p ↦ by cases p <;> simp⟩

/-- The dimension a pole is an end of. -/
def Pole.dimension : Pole → Dimension
  | .competent | .incompetent => .competence
  | .warm | .cold => .warmth
  | .solidary | .antiSolidary => .antiSolidarity

/-- The polarity of a pole is positive at the end its dimension is named for, competent, warm
and antisolidary, and negative at the other. -/
def Pole.polarity : Pole → SignType
  | .competent | .warm | .antiSolidary => 1
  | .incompetent | .cold | .solidary => -1

/-- A pole is determined by its dimension and polarity. -/
theorem Pole.eq_iff {p q : Pole} :
    p = q ↔ p.dimension = q.dimension ∧ p.polarity = q.polarity := by
  revert p q; decide

/-- The other end of a pole's dimension. -/
def Pole.opposite : Pole → Pole
  | .competent => .incompetent
  | .incompetent => .competent
  | .warm => .cold
  | .cold => .warm
  | .solidary => .antiSolidary
  | .antiSolidary => .solidary

@[simp] theorem Pole.opposite_opposite (p : Pole) : p.opposite.opposite = p := by cases p <;> rfl

@[simp] theorem Pole.dimension_opposite (p : Pole) : p.opposite.dimension = p.dimension := by
  cases p <;> rfl

@[simp] theorem Pole.polarity_opposite (p : Pole) : p.opposite.polarity = -p.polarity := by
  cases p <;> rfl

/-- `Pole.opposite` as an involutive permutation. -/
def Pole.oppositeEquiv : Equiv.Perm Pole := Function.Involutive.toPerm _ Pole.opposite_opposite

@[simp] theorem Pole.oppositeEquiv_apply (p : Pole) : Pole.oppositeEquiv p = p.opposite := rfl

@[simp] theorem Pole.oppositeEquiv_symm : Pole.oppositeEquiv.symm = Pole.oppositeEquiv := rfl

theorem Pole.dimension_surjective : Function.Surjective Pole.dimension
  | .competence => ⟨.competent, rfl⟩
  | .warmth => ⟨.warm, rfl⟩
  | .antiSolidarity => ⟨.solidary, rfl⟩

/-- Two poles are incompatible when one is opposite the other. -/
theorem Pole.incompatible_adj_iff {p q : Pole} :
    (incompatible Pole.dimension).Adj p q ↔ q = p.opposite := by
  revert p q; decide

/-- The personae are the sets with exactly one pole of each dimension. -/
theorem Pole.mem_maximalIndepSets_iff (s : Finset Pole) :
    s ∈ (incompatible Pole.dimension).maximalIndepSets ↔
      ∀ d, (s.filter (·.dimension = d)).card = 1 :=
  mem_maximalIndepSets_incompatible_iff.trans
    (Pole.dimension_surjective.forall (p := fun d ↦ (s.filter (·.dimension = d)).card = 1)).symm

end SocialMeaning
