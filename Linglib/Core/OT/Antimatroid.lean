import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Antimatroids — Accessible Set Systems Closed Under Union

Antimatroids are combinatorial structures that generalize the notion of
a partial order. They were first described by @cite{dilworth-1940} in
the context of lattice theory and have been rediscovered many times
under different names (see @cite{korte-lovasz-schrader-1991} for
a comprehensive survey).

For Optimality Theory, antimatroids are significant because
@cite{merchant-riggle-2016} prove that consistent ERC sets are
isomorphic to antimatroids. This means any result about antimatroids
transfers immediately to OT grammars.

## Definitions

Following @cite{merchant-riggle-2016} Definitions 2–5:

- `SetSystem` — a ground set `G` with a collection `F` of feasible subsets
- `AccessibleSetSystem` — augmentation + removal properties
- `Antimatroid` — accessible set system closed under union

The design follows mathlib's `Matroid` pattern: bundled structure with
`Set α` ground set and `Prop` axioms.

## References

@cite{dilworth-1940} — Lattices with unique irreducible decompositions
@cite{korte-lovasz-schrader-1991} — Greedoids
@cite{merchant-riggle-2016} — OT grammars, beyond partial orders
-/

namespace Core.OT

-- ============================================================================
-- § 1: Set System (Definition 2)
-- ============================================================================

/-- A **set system** `(G, F)` is a finite ground set `G` with a
    collection `F` of subsets of `G`, called **feasible sets**.

    Any subset of a power set is a set system. The feasible sets are
    the subsets of `G` that the system "recognizes." -/
structure SetSystem (α : Type*) where
  /-- The ground set. -/
  E : Set α
  /-- The feasible set predicate: `IsFeasible S` means `S` is a
      recognized subset of the ground set. -/
  IsFeasible : Set α → Prop
  /-- The empty set is always feasible. -/
  empty_feasible : IsFeasible ∅
  /-- Feasible sets are subsets of the ground set. -/
  feasible_sub : ∀ S, IsFeasible S → S ⊆ E

-- ============================================================================
-- § 2: Accessible Set System (Definition 3)
-- ============================================================================

/-- An **accessible set system** is a set system with augmentation and
    removal properties. Informally:

    - **Augmentation**: any feasible set that isn't the full ground set
      can be extended by adding one element to produce another feasible set.
    - **Removal**: any non-empty feasible set can be shrunk by removing
      one element to produce another feasible set.

    The term "accessible" refers to the fact that both the empty set and
    the ground set are reachable from any feasible set via single-element
    additions or removals.

    @cite{merchant-riggle-2016} Definition 3. -/
structure AccessibleSetSystem (α : Type*) extends SetSystem α where
  /-- The ground set is feasible. -/
  ground_feasible : IsFeasible E
  /-- **Augmentation**: every feasible set that is not the ground set
      can be extended by adding one element from `E` to produce another
      feasible set. -/
  augmentation : ∀ S, IsFeasible S → S ≠ E →
    ∃ x ∈ E, x ∉ S ∧ IsFeasible (insert x S)
  /-- **Removal**: every non-empty feasible set can be shrunk by
      removing one element to produce another feasible set. -/
  removal : ∀ S, IsFeasible S → S.Nonempty →
    ∃ x ∈ S, IsFeasible (S \ {x})

-- ============================================================================
-- § 3: Antimatroid (Definition 5)
-- ============================================================================

/-- An **antimatroid** is an accessible set system that is closed under
    union: the union of any two feasible sets is also feasible.

    This is the structure that @cite{merchant-riggle-2016} prove is
    isomorphic to consistent ERC sets. The three defining properties —
    accessibility (augmentation + removal) and union closure — correspond
    exactly to the combinatorial structure of OT ranking spaces.

    The design follows mathlib's `Matroid`: bundled structure (not a
    typeclass), `Set α` ground set, `Prop` axioms.

    @cite{merchant-riggle-2016} Definition 5. -/
structure Antimatroid (α : Type*) extends AccessibleSetSystem α where
  /-- **Union closure**: the union of any two feasible sets is feasible.

      This property distinguishes antimatroids from arbitrary accessible
      set systems. It corresponds to the fact that consistent ERC sets
      have "disjunctive" ranking requirements — if two partial rankings
      are consistent, their union (combining their requirements) is also
      consistent. -/
  union_closed : ∀ S T, IsFeasible S → IsFeasible T → IsFeasible (S ∪ T)

-- ============================================================================
-- § 4: Finiteness
-- ============================================================================

/-- An antimatroid with a finite ground set. Following mathlib's
    `Matroid.Finite`, this is a typeclass so it can be inferred. -/
class Antimatroid.Finite {α : Type*} (A : Antimatroid α) : Prop where
  ground_finite : A.E.Finite

theorem Antimatroid.ground_finite {α : Type*} (A : Antimatroid α)
    [A.Finite] : A.E.Finite :=
  Antimatroid.Finite.ground_finite

-- ============================================================================
-- § 5: Basic Properties
-- ============================================================================

variable {α : Type*}

/-- The ground set of an antimatroid is feasible. -/
theorem Antimatroid.ground_isFeasible (A : Antimatroid α) :
    A.IsFeasible A.E :=
  A.ground_feasible

/-- The empty set is feasible in any antimatroid. -/
theorem Antimatroid.empty_isFeasible (A : Antimatroid α) :
    A.IsFeasible ∅ :=
  A.empty_feasible

/-- Singletons in the ground set are feasible in any antimatroid.

    Proof: the empty set is feasible and not equal to `E` (since `E`
    contains `x`), so by augmentation there exists some `y ∈ E` with
    `{y}` feasible. By induction (via removal from larger sets), every
    singleton is feasible.

    For now, we prove only the weaker statement that some singleton
    exists. -/
theorem Antimatroid.exists_singleton_feasible (A : Antimatroid α)
    (hne : A.E.Nonempty) : ∃ x ∈ A.E, A.IsFeasible {x} := by
  have hne_ground : (∅ : Set α) ≠ A.E := by
    intro h; obtain ⟨x, hx⟩ := hne; simp [← h] at hx
  obtain ⟨x, hx_mem, _, hx_feas⟩ := A.augmentation ∅ A.empty_feasible hne_ground
  have : insert x (∅ : Set α) = {x} := by ext; simp
  rw [this] at hx_feas
  exact ⟨x, hx_mem, hx_feas⟩

-- ============================================================================
-- § 6: The Free Antimatroid
-- ============================================================================

/-- The **free antimatroid** on a set `E`: every subset is feasible.

    This corresponds to the OT system with no ranking requirements
    (the empty ERC set) — all `n!` rankings are consistent.
    @cite{merchant-riggle-2016} Definition 8. -/
def Antimatroid.free (E : Set α) : Antimatroid α where
  E := E
  IsFeasible := fun S => S ⊆ E
  empty_feasible := Set.empty_subset E
  feasible_sub := fun _ h => h
  ground_feasible := Set.Subset.refl E
  augmentation := fun S hS hne => by
    obtain ⟨x, hxE, hxS⟩ : ∃ x, x ∈ E ∧ x ∉ S := by
      by_contra h
      apply hne
      ext x
      constructor
      · intro hx; exact hS hx
      · intro hx
        by_contra hxS
        exact h ⟨x, hx, hxS⟩
    exact ⟨x, hxE, hxS, Set.insert_subset hxE hS⟩
  removal := fun S hS hne => by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, Set.diff_subset.trans hS⟩
  union_closed := fun _ _ hS hT => Set.union_subset hS hT

/-- The free antimatroid on `E` has `IsFeasible S ↔ S ⊆ E`. -/
theorem Antimatroid.free_isFeasible (E : Set α) (S : Set α) :
    (Antimatroid.free E).IsFeasible S ↔ S ⊆ E :=
  Iff.rfl

-- ============================================================================
-- § 7: Traces (Definition 7)
-- ============================================================================

/-- The **trace** of antimatroid `A` on subset `S ⊆ E` is the
    antimatroid `(S, {f ∩ S | f ∈ F})` — restricting the feasible
    sets to their intersections with `S`.

    Traces capture the ordering relations that the original antimatroid
    places on the constraints in `S`.

    @cite{merchant-riggle-2016} Definition 7. -/
def Antimatroid.trace (A : Antimatroid α) (S : Set α) (_hS : S ⊆ A.E) :
    SetSystem α where
  E := S
  IsFeasible := fun T => ∃ F, A.IsFeasible F ∧ T = F ∩ S
  empty_feasible := ⟨∅, A.empty_feasible, by simp⟩
  feasible_sub := fun T ⟨F, _, hT⟩ => hT ▸ Set.inter_subset_right

-- ============================================================================
-- § 8: Rooted Circuits (Definition 9)
-- ============================================================================

/-- A **rooted circuit** of antimatroid `A` on `S ⊆ E` is a trace
    `A : S` such that every proper subset of `S` gives a free trace
    (no ordering constraints), but `A : S` itself is not free.

    Rooted circuits are the minimal subsets of `E` that encode actual
    ranking requirements. Each rooted circuit corresponds to exactly
    one ERC under the `RCErc` map.

    The **root** of the circuit is the unique element `r ∈ S` such that
    `{r}` is not feasible in `A : S`.

    @cite{merchant-riggle-2016} Definition 9. -/
structure Antimatroid.RootedCircuit (A : Antimatroid α) where
  /-- The set defining the circuit. -/
  carrier : Set α
  /-- The carrier is a subset of the ground set. -/
  carrier_sub : carrier ⊆ A.E
  /-- The root element. -/
  root : α
  /-- The root is in the carrier. -/
  root_mem : root ∈ carrier
  /-- The trace on the carrier is not free: `{root}` is not feasible
      in the trace. -/
  not_free : ¬ (A.trace carrier carrier_sub).IsFeasible {root}
  /-- Every proper subset of the carrier gives a free trace:
      for every `T ⊂ carrier` and `x ∈ T`, the singleton `{x}` is
      feasible in the trace `A : T`. -/
  proper_free : ∀ T : Set α, ∀ hT : T ⊂ carrier,
    ∀ x ∈ T,
      (A.trace T (hT.subset.trans carrier_sub)).IsFeasible {x}

end Core.OT
