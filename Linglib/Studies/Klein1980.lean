module

public import Linglib.Semantics.Degree.Delineation
public import Linglib.Studies.Kamp1975

/-!
# Klein (1980): A Semantics for Positive and Comparative Adjectives

Klein gives gradable adjectives a semantics without degrees. An adjective is a predicate whose
extension is fixed relative to a comparison class, the comparative is derived from the positive
by quantifying over comparison classes, and degrees, where they are wanted, are recovered as
classes of entities no comparison class tells apart. The delineation vocabulary of
`Degree.Delineation` supplies comparison classes, the induced ordering, monotonicity and the
modifiers *very* and *fairly*; this file states the paper's claims about them. A nonlinear
adjective such as *clever* switches criterion with the comparison class, so its ordering ranks
two entities each above the other, which monotonicity forbids. Klein's *as … as* is Kamp's
*at least as* over all completions.

## Main statements

* `clever_not_monotone`: the delineation for *clever* is not monotone, so no measure induces it.
* `klein_strict_weak_order`: under monotonicity the ordering is a strict weak order.
* `kleinDegree_measureDelineation`: Klein's degrees agree with equality of measure.
* `kleinPreorder_eq_kampPreorder`: the equative is Kamp's *at least as* over all completions.

## Implementation notes

* The measure-induced delineation, its monotonicity and its ordering-to-degree equivalence are
  substrate (`measureDelineation`, `ordering_iff_degree`); the study states what the paper
  adds on top of them.

## References

* [klein-1980]
* [kamp-1975]
-/

@[expose] public section

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

/-- This delineation for *clever* applies two conflicting criteria. Jude is clever when Mona is
absent from the comparison class, Mona when Jude is, and neither when both are present. -/
def cleverDel : ComparisonClass Clever2 → Clever2 → Prop
  | C, .j => Clever2.m ∉ C
  | C, .m => Clever2.j ∉ C

/-- The clever delineation is nonlinear, since in the class of both each is ordered above the
other. -/
theorem clever_nonlinear : IsNonlinearDelineation cleverDel :=
  ⟨{Clever2.j, Clever2.m}, Clever2.j, Clever2.m,
    ⟨{Clever2.j}, by simp, by simp [cleverDel], by simp [cleverDel]⟩,
    ⟨{Clever2.m}, by simp, by simp [cleverDel], by simp [cleverDel]⟩⟩

/-- The clever delineation is not monotone, so no measure function induces it. -/
theorem clever_not_monotone : ¬ IsMonotoneDelineation cleverDel Set.univ :=
  fun h ↦ h.not_isNonlinearDelineation clever_nonlinear

/-! ### *Very* narrows the comparison class (eq. 42)

*Very* narrows the comparison class to the positive extension. The substrate's
`very_entails_base` needs Klein's domain restriction, that a delineation classifies only members
of its class; measure-induced delineations lack it, yet `very A → A` holds for them by
transitivity of the measure order, while being tall does not make one very tall. -/

/-- Under a measure-induced delineation *very A* entails *A*. -/
theorem measureDelineation_very_entails_base {E D : Type*} [LinearOrder D]
    (μ : E → D) (C : ComparisonClass E) (x : E)
    (hv : veryDelineation (measureDelineation μ) C x) :
    measureDelineation μ C x := by
  obtain ⟨y, hy, hlt⟩ := hv
  obtain ⟨z, hz, hlt'⟩ := hy
  exact ⟨z, hz, lt_trans hlt' hlt⟩

/-- An entity tall relative to everyone need not be tall relative to the tall; such an entity is
*fairly tall*. -/
theorem very_strictly_stronger :
    ∃ (E : Type) (del : ComparisonClass E → E → Prop) (C : ComparisonClass E) (x : E),
      del C x ∧ ¬ veryDelineation del C x := by
  refine ⟨Fin 3, fun C x ↦ ∃ y ∈ C, (y : Fin 3) < x, Set.univ, (1 : Fin 3),
    ⟨0, Set.mem_univ _, by omega⟩, ?_⟩
  intro ⟨y, hy, hlt⟩
  simp only [Set.mem_ofPred_eq] at hy
  obtain ⟨z, _, hlt_z⟩ := hy
  omega

/-! ### Degrees recovered (§4.2, eq. 62)

Degrees are dispensable but recoverable: the degree of `u` in a comparison class is the class
of entities nondistinct from `u`, so degrees emerge from comparison classes rather than being
primitive. -/

/-- Klein's degree of `u` at a comparison class is the set of entities nondistinct from `u`. -/
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

/-- A delineation is non-trivial when every comparison class with at least two members contains
a member in the extension and a member outside it. -/
def IsNontrivialDelineation {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop) : Prop :=
  ∀ C : ComparisonClass Entity, (∃ a b : Entity, a ∈ C ∧ b ∈ C ∧ a ≠ b) →
    ∃ u v : Entity, u ∈ C ∧ v ∈ C ∧ delineation C u ∧ ¬ delineation C v

/-! ### The ordering is a strict weak order (§6)

Under monotonicity the context-relative ordering is asymmetric and negatively transitive, the
same ordering structure a degree scale would give without degrees in the ontology; transitivity
and almost connectedness follow. -/

/-- Under monotonicity the ordering is a strict weak order. -/
theorem klein_strict_weak_order {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hmono : IsMonotoneDelineation delineation Set.univ) (cc : ComparisonClass Entity) :
    (∀ u v, ordering delineation cc u v → ¬ ordering delineation cc v u) ∧
      (∀ u v w, ordering delineation cc u w →
        ordering delineation cc u v ∨ ordering delineation cc v w) :=
  ⟨fun _ _ ↦ ordering_asymm delineation hmono, fun _ _ _ ↦ ordering_neg_trans delineation⟩

/-- Transitivity from asymmetry and negative transitivity. -/
theorem klein_transitivity_derived {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hmono : IsMonotoneDelineation delineation Set.univ) (cc : ComparisonClass Entity)
    (u v w : Entity) (huv : ordering delineation cc u v) (hvw : ordering delineation cc v w) :
    ordering delineation cc u w := by
  rcases ordering_neg_trans (v := u) delineation hvw with h | h
  · exact absurd h (ordering_asymm delineation hmono huv)
  · exact h

/-- Any two entities are ordered one way or the other or are nondistinct. -/
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
  ⟨fun h c _ ↦ h c, fun h c ↦ h c (Set.mem_univ _)⟩

end Klein1980
