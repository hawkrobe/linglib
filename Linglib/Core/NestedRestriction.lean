import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Nested Restriction

A `NestedRestriction S D` is a monotone family of predicates on `D` indexed by an
ordered scale `S`, where going up the scale gives a superset. The top of the scale
contains everything.

This structure unifies three independently-developed formalizations:

1. **Domain restriction** (@cite{ritchie-schiller-2024}): spatial regions induce nested
   candidate domain restrictors for quantifiers. `S = SpatialScale`, `D = Entity`.

2. **Comparison class inference** (@cite{tessler-goodman-2022}): comparison classes
   (subordinate vs. superordinate) induce nested reference populations for adjective
   thresholds. `S = ComparisonClass`, `D = Person`.

3. **ASL height** (@cite{davidson-gagne-2022}): vertical height in signing space
   overtly marks quantifier domain size. `S = VerticalHeight`, `D = Entity`.
   Higher signing maps to mereologically larger domains via pronominal elements.

The downstream *applications* differ — quantifier domain filtering vs. threshold
derivation vs. overt signing-space marking — but the nesting structure is identical:
a monotone map from an ordered scale to predicates on a domain.
-/

set_option autoImplicit false

namespace Core

/-- A monotone family of predicates indexed by an ordered scale.

    Each scale level `s : S` induces a predicate `region s : Set D`. The family
    is monotone: if `s₁ ≤ s₂`, then `region s₁` is contained in `region s₂`. The
    top element `⊤` contains everything.

    Field names match `DDRP` exactly so that `abbrev DDRP := NestedRestriction`
    is a drop-in replacement with zero downstream breakage. -/
structure NestedRestriction (S D : Type*) [Preorder S] [OrderTop S] where
  /-- Each scale level induces a predicate on the domain. -/
  region : S → Set D
  /-- Nesting: smaller scale ⊆ larger scale. -/
  monotone : ∀ {s₁ s₂ : S}, s₁ ≤ s₂ → ∀ d, d ∈ region s₁ → d ∈ region s₂
  /-- The top scale contains everything. -/
  top_total : ∀ d, d ∈ region ⊤

section Theorems

variable {S D : Type*} [Preorder S] [OrderTop S]

/-- Unwraps `monotone`: if `s₁ ≤ s₂` then the `s₁`-region is a subset of the
    `s₂`-region. Trivial but documents the pattern for downstream use. -/
theorem NestedRestriction.subset_of_le (nr : NestedRestriction S D)
    {s₁ s₂ : S} (h : s₁ ≤ s₂) (d : D) :
    d ∈ nr.region s₁ → d ∈ nr.region s₂ :=
  nr.monotone h d

/-- If a property holds for all elements of a larger region, it holds for all
    elements of any smaller region.

    This is the abstract pattern behind `DDRP.every_nesting`: ⟦every⟧ under a
    larger scale entails ⟦every⟧ under any smaller scale (restrictor ↓MON). -/
theorem NestedRestriction.forall_nesting (nr : NestedRestriction S D)
    {s₁ s₂ : S} (h : s₁ ≤ s₂)
    {P : D → Prop} (hP : ∀ d, d ∈ nr.region s₂ → P d) :
    ∀ d, d ∈ nr.region s₁ → P d :=
  λ d hr => hP d (nr.monotone h d hr)

/-- If some element of a smaller region satisfies a property, some element of any
    larger region does too.

    This is the abstract pattern behind `DDRP.some_nesting`: ⟦some⟧ under a
    smaller scale entails ⟦some⟧ under any larger scale (restrictor ↑MON). -/
theorem NestedRestriction.exists_nesting (nr : NestedRestriction S D)
    {s₁ s₂ : S} (h : s₁ ≤ s₂)
    {P : D → Prop} (hP : ∃ d, d ∈ nr.region s₁ ∧ P d) :
    ∃ d, d ∈ nr.region s₂ ∧ P d := by
  obtain ⟨d, hr, hp⟩ := hP
  exact ⟨d, nr.monotone h d hr, hp⟩

end Theorems

-- ============================================================================
-- Generic Comparison Class Constructor
-- ============================================================================

/-- A two-level scale for comparison class restrictions: `restricted` ≤ `full`.

    Used by `comparisonClassRestriction` to build a generic nested restriction
    from any relevance predicate. -/
inductive TwoLevel where
  | restricted
  | full
  deriving DecidableEq, Repr

instance : Fintype TwoLevel where
  elems := {.restricted, .full}
  complete := λ x => by cases x <;> simp

private def TwoLevel.toFin : TwoLevel → Fin 2
  | .restricted => 0
  | .full => 1

private theorem TwoLevel.toFin_injective : Function.Injective TwoLevel.toFin := by
  intro a b h; cases a <;> cases b <;> simp_all [toFin]

instance : LinearOrder TwoLevel :=
  LinearOrder.lift' TwoLevel.toFin TwoLevel.toFin_injective

instance : OrderTop TwoLevel where
  top := .full
  le_top a := by cases a <;> decide

/-- Generic constructor: given any relevance predicate `isRelevant : Set D`,
    build a 2-level `NestedRestriction` where the bottom level filters by
    `isRelevant` and the top level is universal.

    This captures the comparison class pattern: the subordinate class restricts
    to a subpopulation (e.g., basketball players), while the superordinate class
    includes everyone. -/
def comparisonClassRestriction {D : Type*} (isRelevant : Set D) :
    NestedRestriction TwoLevel D where
  region
    | .restricted => isRelevant
    | .full => Set.univ
  monotone {s₁ s₂} h d hr := by
    cases s₁ <;> cases s₂ <;> simp_all [Set.mem_univ]
    · exact absurd h (by decide)
  top_total _ := Set.mem_univ _

end Core
