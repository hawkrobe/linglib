import Linglib.Core.Number
import Linglib.Core.Prominence
import Linglib.Theories.Syntax.Minimalism.Agreement.GenderResolution

/-!
# Coordinate Agreement Resolution

@cite{corbett-2000} @cite{adamson-anagnostopoulou-2025} @cite{carstens-2026}

When DPs are conjoined, &P must bear phi-features for agreement.
Each phi-dimension resolves conjuncts' features using a distinct operation:

- **Number** (@cite{corbett-2000} §6.3): summation — sg + sg → pl
- **Gender** (@cite{adamson-anagnostopoulou-2025}, @cite{carstens-2026}):
  intersection — shared i-features survive (via `GenderResolution.resolve`)
- **Person** (@cite{noyer-1997}): hierarchy — most marked person wins

Despite different operations, all three share a common architecture:

1. **Percolation**: only i(nterpretable) features enter resolution
2. **Resolution**: apply the dimension-specific operation
3. **Default**: if resolution yields nothing, apply a language-specific default

A key structural asymmetry: number and person resolution always succeed
(conjoined DPs always have some number and person), while gender
resolution can fail (empty intersection → language-specific default).

## Relation to existing modules

- `GenderResolution.lean`: the single compositional endpoint for gender
  resolution, handling multi-feature bundles (nP stacking) via the A&A
  percolation-and-intersection mechanism. `resolveCoordinate` here calls
  it directly for the gender dimension.
- `Corbett2000.lean`: defines `semanticResolve` for number. `numberResolve`
  here is the `Option`-wrapped equivalent.
- `Carstens2026.lean`: instantiates the Bantu gender system and connects
  all three resolution levels.
-/

namespace Theories.Syntax.Minimalism.Agreement.CoordinateResolution

open Core.Number (Category)
open Core.Prominence (PersonLevel)
open GenderResolution (AnnotatedFeature FeatureBundle)

-- ============================================================================
-- § 1: Resolution Operations
-- ============================================================================

/-- A resolution operation for a single phi-feature dimension.

    Person and number each have their own algebraic structure for
    combining feature values from conjoined DPs. Gender uses
    `GenderResolution.resolve` directly (multi-feature intersection).

    `resolve f₁ f₂` combines two percolated (interpretable) feature
    values and returns the resolved value, or `none` if resolution fails.

    Concrete instances:
    - **Number** (summation): `resolve .singular .singular = some .plural`
    - **Person** (hierarchy): `resolve p₁ p₂ = some (max p₁ p₂)` -/
structure ResolutionOp (F : Type) where
  resolve : F → F → Option F

-- ============================================================================
-- § 2: Number Resolution (Summation)
-- ============================================================================

/-- Number resolution: referent summation (@cite{corbett-2000} §6.3).

    The referent of a conjoined DP is the mereological sum of the
    conjuncts' referents. sg + sg → pl (1 + 1 > 1). In languages
    with richer number systems, sg + du → tri. Resolution always
    succeeds — conjoined DPs always have some number value. -/
def numberResolve : Category → Category → Option Category
  | .singular, .singular => some .plural
  | .singular, .dual     => some .trial
  | .dual,     .singular => some .trial
  | _,         _         => some .plural

/-- Number resolution operation. -/
def numberOp : ResolutionOp Category := ⟨numberResolve⟩

-- ============================================================================
-- § 3: Person Resolution (Hierarchy)
-- ============================================================================

/-- Person resolution: most marked wins (@cite{noyer-1997}).

    1st > 2nd > 3rd. The person with the higher prominence rank
    determines the resolved person on &P. This follows from person
    features being privative: [+participant] subsumes [−participant],
    and [+author] subsumes [−author]. Resolution always succeeds. -/
def personResolve : PersonLevel → PersonLevel → Option PersonLevel
  | .first,  _       => some .first
  | _,       .first  => some .first
  | .second, _       => some .second
  | _,       .second => some .second
  | .third,  .third  => some .third

/-- Person resolution operation. -/
def personOp : ResolutionOp PersonLevel := ⟨personResolve⟩

-- ============================================================================
-- § 4: Percolation and Annotated Resolution
-- ============================================================================

/-- Percolation: extract the feature value iff interpretable.

    u-features are excluded from the resolution calculus
    (@cite{adamson-anagnostopoulou-2025}, @cite{carstens-2026}).

    Reuses `GenderResolution.AnnotatedFeature` — the i/u annotation
    is the same across all phi-dimensions, not specific to gender. -/
def percolate {F : Type} (a : AnnotatedFeature F) : Option F :=
  if a.interp then some a.value else none

/-- Resolve two annotated features: percolate, then apply the operation.

    Both features must be interpretable for resolution to proceed.
    If either is uninterpretable, resolution yields `none` (default). -/
def resolveAnnotated {F : Type} (op : ResolutionOp F)
    (a b : AnnotatedFeature F) : Option F :=
  match percolate a, percolate b with
  | some x, some y => op.resolve x y
  | _, _ => none

-- ============================================================================
-- § 5: Properties — Totality
-- ============================================================================

/-- Number resolution always succeeds: conjoined DPs always have a number. -/
theorem number_total (a b : Category) :
    (numberResolve a b).isSome = true := by
  cases a <;> cases b <;> rfl

/-- Person resolution always succeeds: conjoined DPs always have a person. -/
theorem person_total (p₁ p₂ : PersonLevel) :
    (personResolve p₁ p₂).isSome = true := by
  cases p₁ <;> cases p₂ <;> rfl

/-- Gender resolution with singleton interpretable bundles succeeds iff
    features match — the only dimension that can fail, triggering
    default agreement. -/
theorem gender_singleton_iff_match {G : Type} [BEq G] [LawfulBEq G] (g₁ g₂ : G) :
    (GenderResolution.resolve [⟨g₁, true⟩] [⟨g₂, true⟩]).isSome = (g₁ == g₂) := by
  have hp₁ : GenderResolution.percolateI (F := G) [⟨g₁, true⟩] = [g₁] := rfl
  have hp₂ : GenderResolution.percolateI (F := G) [⟨g₂, true⟩] = [g₂] := rfl
  by_cases h : g₁ = g₂
  · subst h
    have hi : GenderResolution.intersectFeatures [g₁] [g₁] = [g₁] := by
      unfold GenderResolution.intersectFeatures
      simp only [List.filter_cons, List.filter_nil, List.contains_cons,
                 List.contains_nil, beq_self_eq_true, Bool.or_false, ite_true]
    simp [GenderResolution.resolve, hp₁, hi]
  · have hbeq : (g₁ == g₂) = false := by simp [h]
    have hi : GenderResolution.intersectFeatures [g₁] [g₂] = [] := by
      unfold GenderResolution.intersectFeatures; simp [h]
    simp [GenderResolution.resolve, hp₁, hp₂, hi, hbeq]

-- ============================================================================
-- § 6: Properties — Commutativity
-- ============================================================================

/-- Number resolution is commutative. -/
theorem number_comm (a b : Category) :
    numberResolve a b = numberResolve b a := by
  cases a <;> cases b <;> rfl

/-- Person resolution is commutative (both directions yield max). -/
theorem person_comm (p₁ p₂ : PersonLevel) :
    personResolve p₁ p₂ = personResolve p₂ p₁ := by
  cases p₁ <;> cases p₂ <;> rfl

-- ============================================================================
-- § 7: Structural Asymmetry
-- ============================================================================

/-- The structural asymmetry: number and person always resolve
    successfully, but gender can fail. This explains why default
    agreement is a gender phenomenon, not a number or person one.

    The existential witness uses `Bool` (the simplest BEq type with
    distinct values) but the point generalizes to any gender system
    with multiple values. -/
theorem gender_only_fallible :
    (∀ a b : Category, (numberResolve a b).isSome = true) ∧
    (∀ p₁ p₂ : PersonLevel, (personResolve p₁ p₂).isSome = true) ∧
    (∃ g₁ g₂ : FeatureBundle Bool,
      (GenderResolution.resolve g₁ g₂).isSome = false) :=
  ⟨number_total, person_total, ⟨[⟨true, true⟩], [⟨false, true⟩], rfl⟩⟩

-- ============================================================================
-- § 8: Composed Phi-Resolution
-- ============================================================================

/-- A phi-feature bundle for a single conjunct DP.

    Person and number carry single `AnnotatedFeature`s. Gender carries
    a `FeatureBundle` — a list of annotated features from outermost to
    innermost nP layer — so that nP stacking is handled natively via
    `GenderResolution.resolve`. -/
structure PhiBundle (G : Type) where
  person : AnnotatedFeature PersonLevel
  number : AnnotatedFeature Category
  gender : FeatureBundle G

/-- Resolved phi-features for a conjoined DP (&P).

    Each dimension is resolved independently. `none` in a dimension
    means resolution failed and the language-specific default applies.
    Gender resolution returns a list of shared i-features (or `none`). -/
structure PhiResolved (G : Type) where
  person : Option PersonLevel
  number : Option Category
  gender : Option (List G)

/-- Resolve all phi-features for two conjoined DPs.

    Each dimension is resolved independently using its own operation:
    - Number: summation (`numberOp`)
    - Person: hierarchy (`personOp`)
    - Gender: `GenderResolution.resolve` (percolation + intersection)

    This is the unified API that subsumes `semanticResolve` (Corbett
    number) and person hierarchy. Gender goes directly through the
    A&A endpoint rather than a single-feature equality check. -/
def resolveCoordinate {G : Type} [BEq G]
    (dp1 dp2 : PhiBundle G) : PhiResolved G :=
  { person := resolveAnnotated personOp dp1.person dp2.person
    number := resolveAnnotated numberOp dp1.number dp2.number
    gender := GenderResolution.resolve dp1.gender dp2.gender }

-- ============================================================================
-- § 9: Examples
-- ============================================================================

private inductive ExGender where | m | f | n deriving DecidableEq, BEq

/-- Person: 1st + 3rd → 1st (hierarchy). Number: sg + sg → pl (summation).
    Gender: [m] + [m] → some [m] (intersection). All three succeed. -/
example : resolveCoordinate
    (⟨⟨.first, true⟩, ⟨.singular, true⟩, [⟨ExGender.m, true⟩]⟩ : PhiBundle ExGender)
    ⟨⟨.third, true⟩, ⟨.singular, true⟩, [⟨ExGender.m, true⟩]⟩
    = ⟨some .first, some .plural, some [.m]⟩ := rfl

/-- Gender mismatch: [m] + [f] → none (default). Number and person still resolve. -/
example : resolveCoordinate
    (⟨⟨.third, true⟩, ⟨.singular, true⟩, [⟨ExGender.m, true⟩]⟩ : PhiBundle ExGender)
    ⟨⟨.third, true⟩, ⟨.singular, true⟩, [⟨ExGender.f, true⟩]⟩
    = ⟨some .third, some .plural, none⟩ := rfl

/-- Uninterpretable gender: u + u → none (default), regardless of values. -/
example : resolveCoordinate
    (⟨⟨.third, true⟩, ⟨.singular, true⟩, [⟨ExGender.m, false⟩]⟩ : PhiBundle ExGender)
    ⟨⟨.third, true⟩, ⟨.singular, true⟩, [⟨ExGender.m, false⟩]⟩
    = ⟨some .third, some .plural, none⟩ := rfl

/-- Person: 2nd + 3rd → 2nd. -/
example : resolveCoordinate
    (⟨⟨.second, true⟩, ⟨.singular, true⟩, [⟨ExGender.f, true⟩]⟩ : PhiBundle ExGender)
    ⟨⟨.third, true⟩, ⟨.singular, true⟩, [⟨ExGender.f, true⟩]⟩
    = ⟨some .second, some .plural, some [.f]⟩ := rfl

-- ============================================================================
-- § 10: Number — Concrete Predictions
-- ============================================================================

/-- sg + sg → pl: the canonical case (@cite{corbett-2000} §6.3). -/
theorem sg_sg_pl : numberResolve .singular .singular = some .plural := rfl

/-- sg + du → tri: in languages with trial (@cite{corbett-2000} §6.3). -/
theorem sg_du_tri : numberResolve .singular .dual = some .trial := rfl

-- ============================================================================
-- § 11: Person — Concrete Predictions
-- ============================================================================

/-- 1st + 3rd → 1st: first person is highest on the hierarchy. -/
theorem first_wins_third : personResolve .first .third = some .first := rfl

/-- 2nd + 3rd → 2nd. -/
theorem second_wins_third : personResolve .second .third = some .second := rfl

/-- 1st + 2nd → 1st: first person outranks second. -/
theorem first_wins_second : personResolve .first .second = some .first := rfl

/-- 3rd + 3rd → 3rd: full DPs are always third person. -/
theorem third_third : personResolve .third .third = some .third := rfl

end Theories.Syntax.Minimalism.Agreement.CoordinateResolution
