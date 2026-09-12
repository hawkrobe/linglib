import Linglib.Semantics.Degree.Delineation
import Linglib.Studies.Kamp1975

/-!
# Klein (1980): A Semantics for Positive and Comparative Adjectives

This file formalizes [klein-1980]'s degree-free semantics of gradable adjectives: an adjective
is a predicate whose extension is fixed relative to a comparison class, the comparative is
derived from the positive by quantifying over comparison classes, and degrees, where they are
wanted, are recovered as equivalence classes rather than posited. The substrate's delineation
vocabulary (`Degree.Delineation`) supplies comparison classes, the induced ordering,
monotonicity and the modifiers *very* and *fairly*; this file adds the paper's claims about
that apparatus. A delineation that switches criterion with the comparison class, the paper's
nonlinear adjective *clever*, orders two entities each above the other, which monotonicity
forbids (`clever_nonlinear`, `monotone_not_nonlinear`). *Very* narrows the comparison class to
the positive extension, entailing the base adjective for measure-induced delineations while the
converse fails (`measureDelineation_very_entails_base`, `very_strictly_stronger`). Degrees are
the classes of nondistinct entities and agree with measure equality (`kleinDegree`,
`kleinDegree_measureDelineation`), a non-trivial delineation discriminates in every comparison
class with two members (`IsNontrivialDelineation`), and under monotonicity the ordering is a
strict weak order, asymmetric and negatively transitive, from which transitivity and almost
connectedness follow (`klein_strict_weak_order`, `klein_transitivity_derived`,
`klein_almost_connected`). Klein's *as … as* is [kamp-1975]'s *at least as* over all
completions (`kleinPreorder_eq_kampPreorder`).

## Implementation notes

* The measure-induced delineation, its monotonicity and its ordering-to-degree equivalence are
  substrate (`measureDelineation`, `ordering_iff_degree`); the study states what the paper
  adds on top of them.

## References

* [klein-1980]
* [kamp-1975]
-/

namespace Klein1980

open Degree.Delineation

/-! ### Linear and nonlinear adjectives (§2.2, §3.3)

*Tall* is linear, a single criterion and a monotone delineation, while *clever* can produce
cycles: which of two entities counts as clever depends on which criterion the comparison class
makes salient. -/

/-- Two entities, Jude and Mona. -/
inductive Clever2
  | j
  | m

/-- A non-monotone delineation for *clever* with two conflicting criteria: Jude is clever when
Mona is absent from the comparison class, Mona when Jude is, and neither when both are present.
-/
def cleverDel : ComparisonClass Clever2 → Clever2 → Prop
  | C, .j => Clever2.m ∉ C
  | C, .m => Clever2.j ∉ C

/-- The clever delineation is nonlinear: in the class of both, each is ordered above the other.
-/
theorem clever_nonlinear : IsNonlinearDelineation cleverDel :=
  ⟨{Clever2.j, Clever2.m}, Clever2.j, Clever2.m,
    ⟨{Clever2.j}, by simp, by simp [cleverDel], by simp [cleverDel]⟩,
    ⟨{Clever2.m}, by simp, by simp [cleverDel], by simp [cleverDel]⟩⟩

/-- Monotone delineations cannot be nonlinear: monotonicity is what forces a total ordering. -/
theorem monotone_not_nonlinear {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hmono : IsMonotoneDelineation delineation Set.univ)
    (hnn : IsNonlinearDelineation delineation) : False := by
  obtain ⟨_, u, u', ⟨X₁, _, hu₁, hnu'₁⟩, ⟨X₂, _, hu'₂, hnu₂⟩⟩ := hnn
  exact hnu₂ (hmono X₁ X₂ (Set.mem_univ _) (Set.mem_univ _) u u' hu₁ hnu'₁ hu'₂)

/-! ### *Very* narrows the comparison class (eq. 42)

*Very* narrows the comparison class to the positive extension. The substrate's
`very_entails_base` needs Klein's domain restriction, that a delineation classifies only members
of its class; measure-induced delineations lack it, yet `very A → A` holds for them by
transitivity of the measure order, while being tall does not make one very tall. -/

/-- `very A → A` for measure-induced delineations: the witness chain `z ∈ C`, `μ z < μ y`,
`μ y < μ x` gives `μ z < μ x`. -/
theorem measureDelineation_very_entails_base {E D : Type*} [LinearOrder D]
    (μ : E → D) (C : ComparisonClass E) (x : E)
    (hv : veryDelineation (measureDelineation μ) C x) :
    measureDelineation μ C x := by
  obtain ⟨y, hy, hlt⟩ := hv
  obtain ⟨z, hz, hlt'⟩ := hy
  exact ⟨z, hz, lt_trans hlt' hlt⟩

/-- The converse fails: an entity tall relative to everyone need not be tall relative to the
tall, the zone of *fairly tall*. -/
theorem very_strictly_stronger :
    ∃ (E : Type) (del : ComparisonClass E → E → Prop) (C : ComparisonClass E) (x : E),
      del C x ∧ ¬ veryDelineation del C x := by
  refine ⟨Fin 3, λ C x => ∃ y ∈ C, (y : Fin 3) < x, Set.univ, (1 : Fin 3),
    ⟨0, Set.mem_univ _, by omega⟩, ?_⟩
  intro ⟨y, hy, hlt⟩
  simp only [Set.mem_ofPred_eq] at hy
  obtain ⟨z, _, hlt_z⟩ := hy
  omega

/-! ### Degrees recovered (§4.2, eq. 62)

Degrees are dispensable but recoverable: the degree of `u` in a comparison class is the class
of entities nondistinct from `u`, so degrees emerge from comparison classes rather than being
primitive. -/

/-- Klein's degree of `u` at a comparison class: the entities nondistinct from `u`. -/
def kleinDegree {E : Type*} (delineation : ComparisonClass E → E → Prop)
    (cc : ComparisonClass E) (u : E) : Set E :=
  {u' | nondistinct delineation cc u u'}

/-- For measure-induced delineations, two entities share a Klein degree iff they share a
measure value. -/
theorem kleinDegree_measureDelineation {E D : Type*} [LinearOrder D]
    (μ : E → D) (cc : ComparisonClass E) (a b : E) (ha : a ∈ cc) (hb : b ∈ cc) :
    b ∈ kleinDegree (measureDelineation μ) cc a ↔ μ a = μ b := by
  simp only [kleinDegree, Set.mem_ofPred_eq, nondistinct, measureDelineation]
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := (h {a, b} (by intro x hx; rcases hx with rfl | rfl <;> assumption)
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)).mpr ⟨a, Set.mem_insert _ _, hlt⟩
      obtain ⟨y, hy, hlt_y⟩ := this
      rcases hy with rfl | rfl
      · exact absurd hlt_y (lt_irrefl _)
      · exact absurd hlt_y (not_lt.mpr (le_of_lt hlt))
    · have := (h {a, b} (by intro x hx; rcases hx with rfl | rfl <;> assumption)
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)).mp
          ⟨b, Set.mem_insert_of_mem _ rfl, hgt⟩
      obtain ⟨y, hy, hlt_y⟩ := this
      rcases hy with rfl | rfl
      · exact absurd hlt_y (not_lt.mpr (le_of_lt hgt))
      · exact absurd hlt_y (lt_irrefl _)
  · intro heq X _ _ _
    simp [heq]

/-! ### Non-triviality (§5) -/

/-- A delineation is non-trivial when it discriminates in every comparison class with at least
two members: some member is positive and some is not. -/
def IsNontrivialDelineation {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop) : Prop :=
  ∀ C : ComparisonClass Entity, (∃ a b : Entity, a ∈ C ∧ b ∈ C ∧ a ≠ b) →
    ∃ u v : Entity, u ∈ C ∧ v ∈ C ∧ delineation C u ∧ ¬ delineation C v

/-! ### The ordering is a strict weak order (§6)

Under monotonicity the context-relative ordering is asymmetric and negatively transitive, the
same ordering structure a degree scale would give without degrees in the ontology; transitivity
and almost connectedness follow. -/

/-- Klein's main theorem: under monotonicity the ordering is a strict weak order. -/
theorem klein_strict_weak_order {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hmono : IsMonotoneDelineation delineation Set.univ) (cc : ComparisonClass Entity) :
    (∀ u v, ordering delineation cc u v → ¬ ordering delineation cc v u) ∧
      (∀ u v w, ordering delineation cc u w →
        ordering delineation cc u v ∨ ordering delineation cc v w) :=
  ⟨λ _ _ => ordering_asymm delineation hmono, λ _ _ _ => ordering_neg_trans delineation⟩

/-- Transitivity from asymmetry and negative transitivity. -/
theorem klein_transitivity_derived {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hmono : IsMonotoneDelineation delineation Set.univ) (cc : ComparisonClass Entity)
    (u v w : Entity) (huv : ordering delineation cc u v) (hvw : ordering delineation cc v w) :
    ordering delineation cc u w := by
  rcases ordering_neg_trans (v := u) delineation hvw with h | h
  · exact absurd h (ordering_asymm delineation hmono huv)
  · exact h

/-- Almost connected: two entities are ordered one way or the other or nondistinct. -/
theorem klein_almost_connected {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop) (cc : ComparisonClass Entity)
    (u v : Entity) :
    ordering delineation cc u v ∨ ordering delineation cc v u ∨
      nondistinct delineation cc u v := by
  by_cases h1 : ordering delineation cc u v
  · exact Or.inl h1
  · by_cases h2 : ordering delineation cc v u
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (nondistinct_of_incomparable h1 h2))

/-! ### *As … as* and Kamp's *at least as* (§5.3)

Both quantify universally over ways of making the predicate precise, completions for Kamp and
comparison classes for Klein, so over all completions the two preorders coincide. -/

/-- Klein's preorder is Kamp's over all completions of the same extension function. -/
theorem kleinPreorder_eq_kampPreorder {E : Type*}
    (delineation : ComparisonClass E → E → Prop) (u u' : E) :
    (kleinPreorder delineation).le u u' ↔ (Kamp1975.kampPreorder delineation Set.univ).le u u' :=
  ⟨λ h c _ => h c, λ h c => h c (Set.mem_univ _)⟩

end Klein1980
