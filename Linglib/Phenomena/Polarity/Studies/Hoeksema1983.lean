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
  and complement.
- **S-comparative** `[Adj-er than S]` operates on a set of degrees
  (the than-clause's existential closure over a degree variable).
  Anti-additive, but not a Boolean homomorphism.

Hoeksema's **Fact 5** distinguishes them: the NP-comparative is strictly
stronger than the S-comparative on the Boolean-closure hierarchy, but
both are anti-additive (`.antiAdd` in `EntailmentSig`), so both license
strong NPIs by Zwarts-style reasoning.

The structural primitives — `IsAntiAdditive`, `IsBooleanHomomorphism` —
are imported from `Theories/Semantics/Entailment/AntiAdditivity.lean`
(see PR 1). The licensing-context registry slots `.comparativeNP` and
`.comparativeS` are imported from `Core/Lexical/PolarityItem.lean`
(see PR 3).
-/

namespace Hoeksema1983

open Semantics.Entailment.AntiAdditivity
open Core.Lexical.PolarityItem (LicensingContext contextProperties)

-- ════════════════════════════════════════════════════
-- § 1. NP-Comparative as Set-of-Individuals
-- ════════════════════════════════════════════════════

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
    IsAntiAdditive (npComparative μ) := by
  intro A B y
  refine ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩, ?_⟩
  rintro ⟨hA, hB⟩ x (hx | hx)
  · exact hA x hx
  · exact hB x hx

-- ════════════════════════════════════════════════════
-- § 2. S-Comparative as Set-of-Degrees
-- ════════════════════════════════════════════════════

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
    IsAntiAdditive (sComparative μ) := by
  intro A B y
  refine ⟨fun h => ⟨fun d hd => h d (Or.inl hd), fun d hd => h d (Or.inr hd)⟩, ?_⟩
  rintro ⟨hA, hB⟩ d (hd | hd)
  · exact hA d hd
  · exact hB d hd

-- ════════════════════════════════════════════════════
-- § 3. NP-Comparative as Boolean Homomorphism (Eq 22)
-- ════════════════════════════════════════════════════

/-- @cite{hoeksema-1983} Eq (22) formulation: the NP-comparative as a
    function on generalized quantifiers (sets of properties).

    `npComparativeGQ μ Q y` holds iff the property `λx. μ x < μ y`
    (the things `y` is taller than) is one of the properties picked
    out by the GQ `Q`. This is the genuine Boolean-homomorphism case:
    `Q` is being applied pointwise, so `f` distributes over all three
    Boolean operations on `Set (Set Entity)`. -/
def npComparativeGQ (μ : Entity → D) : Set (Set Entity) → Set Entity :=
  fun Q y => {x : Entity | μ x < μ y} ∈ Q

/-- @cite{hoeksema-1983} Fact in §4: the GQ NP-comparative is a Boolean
    homomorphism. Preservation of `∩`, `∪`, and complement holds by
    construction — `Q` is just being evaluated at a fixed property. -/
theorem npComparativeGQ_isBooleanHomomorphism (μ : Entity → D) :
    IsBooleanHomomorphism (npComparativeGQ μ) where
  preserves_inter A B := by ext y; rfl
  preserves_union A B := by ext y; rfl
  preserves_compl A := by ext y; rfl

/-- @cite{hoeksema-1983} Fact 3 instantiated: the GQ NP-comparative is
    monotone in its GQ argument, derived from the Boolean-homomorphism
    structure rather than stipulated. -/
theorem npComparativeGQ_monotone (μ : Entity → D) :
    Monotone (npComparativeGQ μ) :=
  (npComparativeGQ_isBooleanHomomorphism μ).monotone

-- ════════════════════════════════════════════════════
-- § 4. Connection to the Licensing-Context Registry
-- ════════════════════════════════════════════════════

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
