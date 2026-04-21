import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.Heyting.Hom
import Linglib.Theories.Semantics.Entailment.AntiAdditivity
import Linglib.Core.Lexical.PolarityItem

/-!
# Hoeksema (1983): Negative Polarity and the Comparative
@cite{hoeksema-1983}

@cite{hoeksema-1983} (NLLT 1: 403–434) argues that the *than*-argument of
the comparative is the licensing context for NPIs in
"Mary is taller than anyone in the class" / "Mary is taller than anyone is".
Two distinctly typed comparatives:

- **NP-comparative** `[Adj-er than NP]` operates on a set of individuals
  (or a generalized quantifier). Hoeksema's Eq (22) frames the GQ version
  as a *Boolean homomorphism* `Set (Set U) → Set U` — preserves `∩`, `∪`,
  and complement. We realize this with mathlib's
  `BoundedLatticeHom (Set (Set Entity)) (Set Entity)`: since `Set _` is a
  `BooleanAlgebra`, mathlib's `BoundedLatticeHomClass.toBiheytingHomClass`
  derives `map_compl` automatically, so all three Boolean preservation
  properties (and monotonicity, Hoeksema Fact 3) come from the standard
  `map_inf` / `map_sup` / `map_compl` / `OrderHomClass.mono` API.
- **S-comparative** `[Adj-er than S]` operates on a set of degrees
  (the than-clause's existential closure over a degree variable).
  Anti-additive, but not a Boolean homomorphism.

Hoeksema's **Fact 5** distinguishes them: the NP-comparative is strictly
stronger than the S-comparative on the Boolean-closure hierarchy, but
both are anti-additive (`.antiAdd` in `EntailmentSig`), so both license
strong NPIs by Zwarts-style reasoning. Both anti-additivity proofs delegate
to the general `isAntiAdditive_forall_mem` lemma in
`Theories/Semantics/Entailment/AntiAdditivity.lean`.

The licensing-context registry slots `.comparativeNP` and `.comparativeS`
are imported from `Core/Lexical/PolarityItem.lean`.
-/

namespace Hoeksema1983

open Semantics.Entailment.AntiAdditivity
open Core.Lexical.PolarityItem (LicensingContext contextProperties)

/-! ## NP-comparative as set-of-individuals -/

variable {Entity : Type*} {D : Type*} [LinearOrder D]

/-- NP-comparative on a set of individuals: `y ∈ npComparative μ X` iff
    `μ y` strictly exceeds `μ x` for every `x ∈ X`.

    "Mary is taller than every X" — universal quantification over X. -/
def npComparative (μ : Entity → D) (X : Set Entity) : Set Entity :=
  fun y => ∀ x ∈ X, μ x < μ y

/-- The NP-comparative is anti-additive in its set-of-individuals
    argument: `npComparative μ (A ∪ B) = npComparative μ A ∩ npComparative μ B`.

    "Mary is taller than every (A ∪ B)" iff "Mary is taller than every A
    and every B". This is the source of NPI licensing in the than-NP. -/
theorem npComparative_isAntiAdditive (μ : Entity → D) :
    IsAntiAdditive (npComparative μ) :=
  isAntiAdditive_forall_mem (fun x y => μ x < μ y)

/-! ## S-comparative as set-of-degrees -/

/-- S-comparative on a set of degrees: `y ∈ sComparative μ Δ` iff
    `μ y` strictly exceeds every degree in `Δ`.

    "Mary is taller than [d-many tall]" with the than-clause supplying
    a set of degrees `Δ` (typically existentially closed). -/
def sComparative (μ : Entity → D) (Δ : Set D) : Set Entity :=
  fun y => ∀ d ∈ Δ, d < μ y

/-- The S-comparative is anti-additive in its set-of-degrees argument.
    Same NPI-licensing potential as `npComparative`, but on the degree
    domain rather than the individual domain — this is what makes its
    type `Set D → Set Entity` (cross-sortal), unlike the NP-comparative
    which is `Set Entity → Set Entity`. -/
theorem sComparative_isAntiAdditive (μ : Entity → D) :
    IsAntiAdditive (sComparative μ) :=
  isAntiAdditive_forall_mem (fun d y => d < μ y)

/-! ## NP-comparative as Boolean homomorphism (Eq 22) -/

/-- @cite{hoeksema-1983} Eq (22) formulation: the NP-comparative as a
    function on generalized quantifiers, packaged as a mathlib
    `BoundedLatticeHom`.

    `npComparativeGQ μ Q y` holds iff the property `λx. μ x < μ y` (the
    things `y` is taller than) is one of the properties picked out by the
    GQ `Q`. This is the genuine Boolean-homomorphism case: `Q` is just
    being evaluated at a fixed property, so preservation of `∩` / `∪` /
    `⊤` / `⊥` is definitional. Complement preservation follows for free
    via mathlib's `BoundedLatticeHomClass.toBiheytingHomClass` instance
    for `BooleanAlgebra → BooleanAlgebra`, and monotonicity (Hoeksema
    Fact 3) from `OrderHomClass.mono`. -/
def npComparativeGQ (μ : Entity → D) :
    BoundedLatticeHom (Set (Set Entity)) (Set Entity) where
  toFun Q := fun y => {x : Entity | μ x < μ y} ∈ Q
  map_inf' _ _ := by ext y; rfl
  map_sup' _ _ := by ext y; rfl
  map_top' := by ext y; exact Iff.rfl
  map_bot' := by ext y; exact Iff.rfl

/-- @cite{hoeksema-1983} Fact 3: the GQ NP-comparative is monotone in its
    GQ argument. Derived from the `BoundedLatticeHom`'s underlying
    `OrderHomClass`. -/
theorem npComparativeGQ_monotone (μ : Entity → D) :
    Monotone (npComparativeGQ μ) :=
  OrderHomClass.mono _

/-- @cite{hoeksema-1983} Eq (22), complement clause: complement preservation
    on the NP-comparative GQ, via mathlib's automatic `BiheytingHomClass`
    instance for `BooleanAlgebra → BooleanAlgebra` `BoundedLatticeHom`s. -/
theorem npComparativeGQ_map_compl (μ : Entity → D) (Q : Set (Set Entity)) :
    npComparativeGQ μ Qᶜ = (npComparativeGQ μ Q)ᶜ :=
  map_compl (npComparativeGQ μ) Q

/-- The NP-comparative GQ underlies a Boolean homomorphism in the sense
    of @cite{hoeksema-1983}; the bundled `BoundedLatticeHom` IS the
    witness. -/
theorem npComparativeGQ_isBooleanHomomorphism (μ : Entity → D) :
    IsBooleanHomomorphism (fun Q => (npComparativeGQ μ : _ → _) Q) :=
  ⟨npComparativeGQ μ, rfl⟩

/-! ## Connection to the licensing-context registry -/

/-- The `.comparativeNP` registry slot is anti-additive, matching
    `npComparative_isAntiAdditive`. -/
theorem comparativeNP_signature_anti_additive :
    (contextProperties .comparativeNP).signature = .antiAdd := rfl

/-- The `.comparativeS` registry slot is anti-additive, matching
    `sComparative_isAntiAdditive`. -/
theorem comparativeS_signature_anti_additive :
    (contextProperties .comparativeS).signature = .antiAdd := rfl

/-- Both registry slots cite Hoeksema 1983, anchoring the registry's
    classification to this study file. -/
theorem both_comparatives_cite_hoeksema :
    "hoeksema-1983" ∈ (contextProperties .comparativeNP).citations ∧
    "hoeksema-1983" ∈ (contextProperties .comparativeS).citations := by
  refine ⟨?_, ?_⟩ <;> decide

end Hoeksema1983
