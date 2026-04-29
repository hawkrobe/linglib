import Linglib.Theories.Semantics.Quantification.DomainRestriction

/-!
# Domain Vagueness

@cite{kadmon-landman-1993}

Kadmon & Landman (1993) "Any". *Linguistics and Philosophy* 16: 353–422.

## Core Distinction

K&L distinguish two kinds of quantificational expressions:

- **Domain precise**: the contextual restriction determines a unique precise
  domain of quantification (e.g., *every owl*, *no owl*).
- **Domain vague**: the contextual restriction is inherently vague — different
  precisifications yield different domains (e.g., *an owl* in generic use).

This distinction explains why generics allow exceptions while universal
quantifiers do not: the vague restricting set leaves room for objects that
might or might not fall under the generalization.

## Formal Apparatus

A **vague restriction** ⟨v₀, V⟩ consists of:
- `v₀`: the *precise part* — properties known to hold of the relevant entities
- `V`: the *precisifications* — consistent ways to complete the restriction

Each precisification `v ∈ V` extends `v₀` (i.e., `v₀ ⊆ v`) and determines
a domain of entities: those satisfying all properties in `v`.

## Widening and Dimensional Universality

K&L's analysis of FC *any* relies on widening along a contextual dimension
{P, ¬P}. When widening removes both P and ¬P from all precisifications,
the quantifier becomes **universal with respect to** that dimension: objects
are not excluded merely for having or lacking property P.

*Any CN* is **dimensionally universal** — universal wrt its dimension of
widening in every context. This is why *almost* can modify *any owl*
(dimensionally universal) but not *an owl* (not dimensionally universal).
-/

set_option autoImplicit false

namespace Semantics.Quantification.DomainVagueness

-- ============================================================================
-- §1. Vague Sets and Precisifications
-- ============================================================================

/-- A vague restriction on a type of properties.

    `precise` is the set of properties known to hold (v₀ in K&L's notation).
    `precisifications` are the consistent complete extensions of `precise`.
    Every precisification must extend the precise part, and the precise
    part itself is always a valid (minimal) precisification. -/
structure VagueRestriction (Property : Type*) where
  /-- The precise part: properties definitely in the restriction -/
  precise : Set Property
  /-- The set of precisifications: consistent ways to complete the restriction -/
  precisifications : Set (Set Property)
  /-- Every precisification extends the precise part -/
  extends_precise : ∀ v ∈ precisifications, precise ⊆ v
  /-- The precise part is itself a (minimal) precisification.
      K&L: v₀ trivially extends itself, so it is always among V. -/
  precise_mem : precise ∈ precisifications

/-- The domain of entities induced by a set of properties and an application
    function. An entity is in the domain iff it satisfies every property. -/
def domainOf {Property Entity : Type*}
    (props : Set Property) (apply : Property → Set Entity) : Set Entity :=
  {e | ∀ P ∈ props, e ∈ apply P}

-- ============================================================================
-- §2. Domain Precise vs Domain Vague
-- ============================================================================

/-- A vague restriction is **domain precise** on a base set iff every
    precisification determines the same domain of entities.

    *Every owl* and *no owl* are domain precise: the contextual restriction
    on "owl" determines a unique set of owls to quantify over.

    K&L (164): ⟨v₀, V⟩ is domain precise on B iff for every v ∈ V,
    D_{v,B} = D_{v₀,B}. -/
def isDomainPrecise {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity) : Prop :=
  ∀ v ∈ X.precisifications, domainOf v apply = domainOf X.precise apply

/-- A vague restriction is **domain vague** iff it is not domain precise:
    some precisifications yield different domains.

    Generic NPs like *an owl* are domain vague: different precisifications
    of "normalcy for owls" yield different sets of relevant owls.
    This is why generics tolerate exceptions — it is always possible that
    an apparent counterexample falls outside the domain under the "right"
    precisification. -/
def isDomainVague {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity) : Prop :=
  ¬isDomainPrecise X apply

/-- A trivially precise restriction: when every precisification equals the
    precise part, the restriction is domain precise. This is the case for
    standard universal quantifiers like *every* and *no*. -/
theorem trivially_precise {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (h : ∀ v ∈ X.precisifications, v = X.precise) :
    isDomainPrecise X apply := by
  intro v hv
  rw [h v hv]

-- ============================================================================
-- §3. Widening
-- ============================================================================

/-- Remove a property and its negation from a vague restriction.

    K&L (174): ⟦X_A ∼ {P, ¬P}⟧_c is the result of removing every
    property S except for P and ¬P from ⟦X_A⟧_c and from all its
    precisifications.

    Here we model "removing a dimension" by filtering out a specific
    property from the precise part and all precisifications. In the
    full K&L treatment, both P and ¬P are removed; we parameterize
    by a predicate `onDimension` that identifies properties on the
    dimension to be removed. -/
def widenAlong {Property : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    [DecidablePred onDimension] : VagueRestriction Property where
  precise := {P ∈ X.precise | ¬onDimension P}
  precisifications := (λ v => {P ∈ v | ¬onDimension P}) '' X.precisifications
  extends_precise := by
    intro v' hv'
    obtain ⟨v, hv, rfl⟩ := hv'
    intro P ⟨hPprec, hPnot⟩
    exact ⟨X.extends_precise v hv hPprec, hPnot⟩
  precise_mem := ⟨X.precise, X.precise_mem, rfl⟩

/-- Widening weakens the restriction: the precise part of the widened
    restriction is a subset of the original precise part. -/
theorem widenAlong_weakens_precise {Property : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    [DecidablePred onDimension] :
    (widenAlong X onDimension).precise ⊆ X.precise :=
  λ _ ⟨h, _⟩ => h

/-- Widening expands the domain: if we remove properties from the restriction,
    fewer constraints means more entities qualify. -/
theorem widenAlong_expands_domain {Property Entity : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    [DecidablePred onDimension] (apply : Property → Set Entity) :
    domainOf X.precise apply ⊆
    domainOf (widenAlong X onDimension).precise apply := by
  intro e he P ⟨hPprec, _⟩
  exact he P hPprec

-- ============================================================================
-- §4. Universality with respect to a Dimension
-- ============================================================================

/-- A quantificational expression Q ↾ X_A(A) is **universal with respect to**
    a pair of properties {P, ¬P} in context c iff removing P and ¬P from
    the restriction leaves the quantifier ranging over all objects in ⟦A⟧_c.

    K&L (175): Q ↾ X_A(A) is universal wrt {P, ¬P} in c iff
    ⟦Q ↾ X_A ∼ {P, ¬P}(A)⟧_c = ⟦∀(A)⟧_c or ⟦¬∃(A)⟧_c.

    We formalize the positive case: after removing properties on the
    dimension, every entity in the base denotation is in the domain. -/
def universalWrtDimension {Property Entity : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    [DecidablePred onDimension]
    (apply : Property → Set Entity) (baseDenotation : Set Entity) : Prop :=
  baseDenotation ⊆ domainOf (widenAlong X onDimension).precise apply

/-- A pair of properties {P, ¬P} is **non-trivial** on a base set iff
    some entity in the base satisfies P and some entity satisfies ¬P.

    K&L (176): {P, ¬P} is non-trivial on A iff both P and ¬P contain
    some object in A. This rules out vacuous dimensions where universality
    is trivially achieved. -/
def nonTrivialDimension {Property Entity : Type*}
    (onDimension : Property → Prop) (apply : Property → Set Entity)
    (baseDenotation : Set Entity) : Prop :=
  (∃ P, onDimension P ∧ ∃ e ∈ baseDenotation, e ∈ apply P) ∧
  (∃ P, onDimension P ∧ ∃ e ∈ baseDenotation, e ∉ apply P)

/-- An NP is **dimensionally universal** if there exists some non-trivial
    dimension wrt which it is universal.

    K&L (177): Q ↾ X_A(A) is dimensionally universal iff for every
    context c, there is a pair {P, ¬P} which is non-trivial on ⟦A⟧_c
    such that Q ↾ X_A(A) is universal wrt {P, ¬P} in c.

    *any CN* is dimensionally universal (universal wrt its dimension
    of widening), while generic *a CN* is not. This explains why *almost*
    can modify *any owl* but not *an owl*: *almost* requires a quantifier
    that is (dimensionally) universal. -/
def dimensionallyUniversal {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (baseDenotation : Set Entity) : Prop :=
  ∃ (onDimension : Property → Prop) (_ : DecidablePred onDimension),
    nonTrivialDimension onDimension apply baseDenotation ∧
    universalWrtDimension X onDimension apply baseDenotation

-- ============================================================================
-- §5. Widening Creates Dimensional Universality
-- ============================================================================

/-- **Theorem (K&L §4.3): Widening creates universality wrt its dimension.**

    After widening a vague restriction along a dimension, the widened
    restriction is universal wrt that dimension. This is because widening
    removes all properties on the dimension from both the precise part and
    all precisifications — so no entity is excluded on the basis of that
    dimension.

    This is the core of K&L's explanation for why *any CN* is dimensionally
    universal: *any* widens along a contextual dimension, and widening
    along a dimension automatically creates universality wrt that dimension. -/
theorem widening_creates_universality {Property Entity : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    [DecidablePred onDimension] (apply : Property → Set Entity)
    (baseDenotation : Set Entity)
    -- The base denotation only depends on non-dimensional properties:
    -- entities in the base satisfy all non-dimensional precise properties
    (hBase : baseDenotation ⊆ domainOf {P ∈ X.precise | ¬onDimension P} apply) :
    universalWrtDimension X onDimension apply baseDenotation :=
  hBase

/-- **Corollary: *any CN* is dimensionally universal** (given a non-trivial
    dimension of widening).

    If a vague restriction X has a non-trivial dimension along which
    widening is applied, and the base denotation satisfies the
    non-dimensional properties, then the widened restriction is
    dimensionally universal. -/
theorem any_cn_dimensionally_universal {Property Entity : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    [DecidablePred onDimension] (apply : Property → Set Entity)
    (baseDenotation : Set Entity)
    (hNT : nonTrivialDimension onDimension apply baseDenotation)
    (hBase : baseDenotation ⊆ domainOf {P ∈ X.precise | ¬onDimension P} apply) :
    dimensionallyUniversal (widenAlong X onDimension) apply baseDenotation := by
  refine ⟨onDimension, inferInstance, hNT, ?_⟩
  intro e he P ⟨⟨hPprec, hPnot⟩, hPnot'⟩
  exact hBase he P ⟨hPprec, hPnot⟩

-- ============================================================================
-- §6. DE on a Constant Parameter
-- ============================================================================

/-- **DE on a constant parameter**: a multi-place function is DE in one
    argument when another argument is held constant.

    K&L use this pattern twice:
    - Adversative predicates are "DE on a constant perspective" (§3.3):
      sorry(x, p, A) is DE in A when perspective p is held constant
    - Conditionals are "DE on a constant restriction" (§3.5):
      if_R(A, C) is DE in A when the implicit restriction R is held constant

    This is the same structure as Kratzer's modal base: necessity(f, g, p)
    is DE in p when the modal base f and ordering source g are held constant. -/
def IsDE_OnConstant {Param Prop' : Type*} [Preorder Prop']
    (f : Param → Prop' → Prop') (param : Param) : Prop :=
  Antitone (f param)

-- ============================================================================
-- §6b. Bridge: DomainRestrictor → VagueRestriction
-- ============================================================================

/-!
## Connecting Domain Restriction to Domain Vagueness

`DomainRestriction.lean` formalizes **domain-precise** quantifiers: each
`DomainRestrictor E` is a single predicate `Set E` that determines a
unique domain. K&L's `VagueRestriction` generalizes this: domain-precise
quantifiers are the degenerate case where all precisifications agree.

The bridge theorem below shows that any `DomainRestrictor`-based quantifier
is trivially domain precise in K&L's sense: the restriction has only one
precisification (the restrictor itself), so all precisifications yield the
same domain. This connects @cite{ritchie-schiller-2024}'s DDRP apparatus
to K&L's domain vagueness distinction.
-/

open Semantics.Quantification.DomainRestriction (DomainRestrictor)

/-- Lift a single `DomainRestrictor` into a trivially precise
    `VagueRestriction`. The precise part is the singleton set containing
    the restrictor, and the only precisification equals the precise part.

    This embedding shows that standard domain-restricted quantifiers
    (*every*, *no*) are the degenerate case of K&L's vague restriction
    framework — they have exactly one precisification. -/
def VagueRestriction.ofRestrictor {Entity : Type*}
    (C : DomainRestrictor Entity) : VagueRestriction (Set Entity) where
  precise := {C}
  precisifications := {{C}}
  extends_precise := by
    intro v hv
    simp only [Set.mem_singleton_iff] at hv
    rw [hv]
  precise_mem := Set.mem_singleton_iff.mpr rfl

/-- A `DomainRestrictor`-based vague restriction is domain precise.

    This is the formal bridge: standard quantifiers (which use a single
    `DomainRestrictor`) are always domain precise in K&L's sense, because
    their restriction has only one precisification. This is why *every owl*
    and *no owl* do not tolerate exceptions — there is a unique domain to
    quantify over, and counterexamples cannot be excluded by shifting to a
    different precisification. -/
theorem restrictor_is_domain_precise {Entity : Type*}
    (C : DomainRestrictor Entity) (apply : Set Entity → Set Entity) :
    isDomainPrecise (VagueRestriction.ofRestrictor C) apply := by
  intro v hv
  simp only [VagueRestriction.ofRestrictor, Set.mem_singleton_iff] at hv
  subst hv
  rfl

-- ============================================================================
-- §7. Generic Quantification as Vague Universality
-- ============================================================================

/-!
## Generic Quantification (K&L §4.1.1)

K&L propose that generic statements involve a universal quantifier (∀)
restricted by a **vague** set of properties. For example, "An owl hunts mice"
means roughly:

    ∀ ↾ X_owl(Owl)(Hunts mice)

where `X_owl` is a vague restriction defining "normality" for owls. The
quantifier ranges over all entities satisfying a precisification of `X_owl`
that is compatible with the CN denotation.

This explains two key properties of generics:

1. **Exception tolerance**: Because the restriction is vague, apparent
   counterexamples can always be excluded under *some* precisification.
   This is why "A poodle gives live birth" is true despite male poodles.

2. **Incompatibility with *almost***: Generic NPs (*an owl*) are domain vague,
   so there is no unique precise domain to be "almost all of." *Almost*
   requires a domain-precise or dimensionally-universal NP.
-/

/-- The **generic operator** as a vague universal: a generic sentence
    `GEN(CN)(VP)` is true under precisification `v` iff every entity
    in the v-induced domain satisfies the VP scope.

    K&L (p. 407, eq. (159)): ∀ ↾ X_owl(Owl)(Hunts mice) -/
def genericTrue {Property Entity : Type*}
    (_X : VagueRestriction Property) (apply : Property → Set Entity)
    (scope : Entity → Prop) (v : Set Property) : Prop :=
  ∀ e ∈ domainOf v apply, scope e

/-- A generic is true on its **standard** (supervaluationist) semantics
    iff it is true under EVERY precisification.

    K&L (p. 411): The generic quantifier ∀ ↾ X_A(A) is domain precise iff
    for every context, the restriction determines a unique domain.
    For domain-vague generics, truth requires all precisifications to agree. -/
def genericSuperTrue {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (scope : Entity → Prop) : Prop :=
  ∀ v ∈ X.precisifications, genericTrue X apply scope v

/-- A generic is true on its **subvaluationist** semantics iff it is
    true under SOME precisification.

    This captures the exception-tolerant reading: the generic holds
    as long as there exists a "way of being normal" under which all
    entities in the domain satisfy the scope. -/
def genericSubTrue {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (scope : Entity → Prop) : Prop :=
  ∃ v ∈ X.precisifications, genericTrue X apply scope v

/-- **Exception tolerance from domain vagueness.**

    If a restriction is domain vague, then for any entity e, there exists
    a precisification under which e is outside the domain. This means
    apparent counterexamples to the generic are always "excusable" — they
    can be excluded by choosing the right precisification.

    K&L (p. 409): "When we encounter objects that do not fall under the
    generalization, there is always the possibility that they are not among
    the objects that the generalization is supposed to apply to."

    Formalized: if the restriction is domain vague, there exist two
    precisifications with different domains, so some entity is in one
    domain but not the other. -/
theorem domain_vague_allows_exceptions {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (hVague : isDomainVague X apply) :
    ∃ v₁ ∈ X.precisifications, ∃ v₂ ∈ X.precisifications,
      domainOf v₁ apply ≠ domainOf v₂ apply := by
  unfold isDomainVague isDomainPrecise at hVague
  push Not at hVague
  obtain ⟨v, hv, hne⟩ := hVague
  exact ⟨v, hv, X.precise, X.precise_mem, hne⟩

/-- **Domain-precise quantifiers have unique domains per precisification.**

    When a restriction is domain precise, all precisifications yield the
    same domain as the precise part. This means the generic degenerates
    into a standard universal: there is one domain, and truth is
    checked against it. No exceptions are tolerated.

    K&L (p. 412): "Every owl and no owl are domain precise universal
    quantifiers. Every owl hunts mice and no owl hunts mice express in
    every context a generalization about all objects in D_{X_owl,c}." -/
theorem domain_precise_unique_domain {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (hPrecise : isDomainPrecise X apply) :
    ∀ v ∈ X.precisifications,
      domainOf v apply = domainOf X.precise apply :=
  hPrecise

-- ============================================================================
-- §8. Total Widening Creates True Universality
-- ============================================================================

/-- **Total widening creates true universality** (K&L p. 419).

    If widening is total — it eliminates ALL properties from the restriction
    (both precise part and precisifications) — then the widened restriction
    imposes no constraints at all. The quantifier becomes a standard
    universal over the entire base denotation.

    K&L: "if in a context widening is total and eliminates all properties
    from the restriction, then *any CN* becomes not only universal wrt
    some pair {P, ¬P}, but also truly universal." -/
theorem total_widening_creates_universality {Property : Type*}
    (X : VagueRestriction Property)
    (onDimension : Property → Prop) [DecidablePred onDimension]
    (hAllOnDim : ∀ P ∈ X.precise, onDimension P) :
    (widenAlong X onDimension).precise = ∅ := by
  ext P
  simp only [widenAlong, Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false]
  intro ⟨hP, hNot⟩
  exact hNot (hAllOnDim P hP)

end Semantics.Quantification.DomainVagueness
