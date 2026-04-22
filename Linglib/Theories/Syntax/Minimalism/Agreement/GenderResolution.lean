import Linglib.Theories.Syntax.Minimalism.Features

/-!
# Gender Resolution in Coordination

@cite{adamson-anagnostopoulou-2025} @cite{carstens-2026}

When singular DPs are conjoined, the resulting &P must bear phi-features
for agreement. For number, sg + sg → pl by summation (@cite{corbett-2000}
§6.3). For gender, the mechanism is more complex: percolation of
interpretable features to &P, followed by intersection and selection.

This file formalizes the percolation-and-intersection mechanism proposed by
@cite{adamson-anagnostopoulou-2025} and adopted by @cite{carstens-2026},
parameterized over the feature type so it applies across language families.

## The mechanism

1. **Percolation**: each conjunct's i(nterpretable) gender features
   percolate to &P; u(ninterpretable) features are excluded.

2. **Intersection**: percolated features common to all conjuncts form
   a single set on &P.

3. **Result**: non-empty intersection → `some features` (gender-matching
   agreement); empty → `none` (language-specific default).

## Cross-linguistic instantiation

- **Bantu** (@cite{carstens-2026}): features are i[entity] flavors
  ([human], [animal], [inanimate]). u-genders (Xhosa 3/4, 5/6) have no
  i-features → empty intersection → default cl 2 or cl 8.
- **Greek** (@cite{adamson-anagnostopoulou-2025}): features are organized
  in a hierarchy (CLASS > MASC > FEM). FEM entails MASC, so mismatched
  humans yield {CLASS,MASC} → masculine (via Subset Principle). Inanimates
  bear only iCLASS, so mismatch yields {CLASS} → neuter (least specified
  exponent). No default insertion — all outcomes from intersection.
- **Icelandic**: MASC and FEM are independent under CLASS. Mismatched
  human intersection yields {CLASS} → neuter. Same vocabulary as Greek;
  different geometry → different result.
- **BCS**: MASC is under INDIV (not CLASS). All coordinatable nominals
  have INDIV → intersection always includes {INDIV} → masculine.

## Selection grammars

When the intersection contains multiple i-features (from stacked nPs),
the language must select which one determines the agreement class.
@cite{carstens-2026} §5.1 identifies two grammars available to Xhosa
speakers: **Highest Wins** (outermost nP layer wins) and **Best Semantic
Match** (most specific semantic core wins).
-/

namespace Minimalism.Agreement.GenderResolution

open _root_.Minimalism (Interpretability)

-- ============================================================================
-- § 1: Annotated Features
-- ============================================================================

/-- A gender feature annotated with interpretability.
    @cite{kramer-2015}: gender features on categorizing heads n are either
    interpretable (i) — natural gender — or uninterpretable (u) — arbitrary.
    Only i-features enter the resolution calculus.

    Uses the unified `Interpretability` type from `Features.lean`. -/
structure AnnotatedFeature (F : Type) where
  value : F
  interp : Interpretability
  deriving DecidableEq, Repr

/-- A feature bundle on a conjunct DP. Features are ordered from outermost
    (highest nP layer) to innermost (lowest/core). Single-layer DPs have
    singletons or empty bundles; stacked nPs have multiple entries. -/
abbrev FeatureBundle (F : Type) := List (AnnotatedFeature F)

-- ============================================================================
-- § 2: Percolation
-- ============================================================================

/-- Percolation: extract only interpretable feature values.
    u-features are excluded from the resolution calculus
    (@cite{adamson-anagnostopoulou-2025}). -/
def percolateI {F : Type} (fs : FeatureBundle F) : List F :=
  (fs.filter (·.interp == .interpretable)).map (·.value)

-- ============================================================================
-- § 3: Intersection and Resolution
-- ============================================================================

/-- Intersection of percolated feature lists from two conjuncts.
    Features present in both lists survive; others are eliminated.
    Result retains the ordering from the first list. -/
def intersectFeatures {F : Type} [BEq F] (xs ys : List F) : List F :=
  xs.filter (ys.contains ·)

/-- Resolve gender agreement for two conjoined DPs via the
    percolation-and-intersection mechanism.

    1. Percolate: extract i-features from each conjunct
    2. Intersect: find shared i-features
    3. Return: `some features` if non-empty, `none` if empty

    This is the single compositional endpoint for gender resolution.
    All language-specific resolution functions are projections of this. -/
def resolve {F : Type} [BEq F]
    (fs1 fs2 : FeatureBundle F) : Option (List F) :=
  match intersectFeatures (percolateI fs1) (percolateI fs2) with
  | [] => none
  | xs => some xs

-- ============================================================================
-- § 4: Properties — Self-matching
-- ============================================================================

/-- A singleton interpretable feature bundle always self-matches under
    resolution: resolving ⟨f, i⟩ & ⟨f, i⟩ yields `some [f]`.

    This is the foundation of the A&A mechanism: each geometry node,
    coordinated with itself, yields matching agreement. The proof
    requires `LawfulBEq` to ensure `f == f = true`. -/
theorem singleton_self_matching {F : Type} [BEq F] [LawfulBEq F]
    (f : F) :
    resolve [⟨f, .interpretable⟩] [⟨f, .interpretable⟩] = some [f] := by
  have hp : percolateI (F := F) [⟨f, .interpretable⟩] = [f] := rfl
  suffices h : intersectFeatures [f] [f] = [f] by
    simp only [resolve, hp, h]
  unfold intersectFeatures
  simp only [List.filter_cons, List.filter_nil, List.contains_cons,
             List.contains_nil, beq_self_eq_true, Bool.or_false, ite_true]

/-- Uninterpretable features are excluded from resolution:
    a singleton u-feature bundle always yields `none`. -/
theorem singleton_u_default {F : Type} [BEq F]
    (f : F) :
    resolve [⟨f, .uninterpretable⟩] [⟨f, .uninterpretable⟩] = none := by
  unfold resolve percolateI intersectFeatures
  rfl

-- ============================================================================
-- § 5: Selection Grammars
-- ============================================================================

/-- When multiple i-features survive intersection (from stacked nPs),
    the language selects which one determines the agreement class.
    @cite{carstens-2026} §5.1 proposes two grammars available to speakers. -/
inductive SelectionGrammar where
  /-- The feature from the outermost (highest) nP layer wins.
      Since features retain their percolation ordering, this is the
      first element of the intersection. -/
  | highestWins
  /-- The most specific semantic match wins. A core gender
      (i[human], i[inanimate], i[animal]) beats a plain i[entity]
      from an arbitrary gender member. -/
  | bestSemanticMatch
  deriving DecidableEq, Repr

/-- Select the determining feature from a non-empty intersection.
    `specificity` maps features to a ranking (higher = more specific). -/
def selectFeature {F : Type}
    (grammar : SelectionGrammar) (specificity : F → Nat)
    (features : List F) : Option F :=
  match grammar with
  | .highestWins => features.head?
  | .bestSemanticMatch =>
    features.foldl (init := none) fun acc f =>
      match acc with
      | none => some f
      | some best =>
        match Nat.blt (specificity best) (specificity f) with
        | true => some f
        | false => some best

-- ============================================================================
-- § 6: Idempotency
-- ============================================================================

/-- Intersecting a feature list with itself is the identity.
    Every element is trivially contained in itself (via `LawfulBEq`).
    TODO: induction on xs; each element satisfies `xs.contains x`
    by `LawfulBEq` reflexivity. -/
theorem intersectFeatures_self {F : Type} [BEq F] [LawfulBEq F] (xs : List F) :
    intersectFeatures xs xs = xs := by
  simp only [intersectFeatures]
  rw [List.filter_eq_self]
  intro x hx
  exact List.elem_eq_true_of_mem hx

/-- **General idempotency**: resolving a bundle with itself always yields its
    percolated i-features (when non-empty). This generalizes
    `singleton_self_matching` to bundles of any size.

    Linguistically: uniform conjuncts (same gender) always produce
    gender-matching agreement, regardless of bundle complexity. -/
theorem resolve_idempotent {F : Type} [BEq F] [LawfulBEq F] (fs : FeatureBundle F)
    (h : percolateI fs ≠ []) :
    resolve fs fs = some (percolateI fs) := by
  unfold resolve
  rw [intersectFeatures_self]
  cases hpi : percolateI fs with
  | nil => exact absurd hpi h
  | cons _ _ => rfl

-- ============================================================================
-- § 7: N-ary Resolution
-- ============================================================================

/-- Resolve gender agreement across n conjuncts by iterated intersection.

    1. Percolate i-features from each conjunct
    2. Intersect all percolated lists pairwise (left fold)
    3. Return `some features` if non-empty, `none` if empty

    Binary `resolve` is the special case `resolveN [fs1, fs2]`. -/
def resolveN {F : Type} [BEq F] (bundles : List (FeatureBundle F)) : Option (List F) :=
  match bundles.map percolateI with
  | [] => none
  | first :: rest =>
    match rest.foldl intersectFeatures first with
    | [] => none
    | xs => some xs

/-- N-ary resolution subsumes binary: `resolveN [fs1, fs2] = resolve fs1 fs2`. -/
theorem resolveN_binary {F : Type} [BEq F] (fs1 fs2 : FeatureBundle F) :
    resolveN [fs1, fs2] = resolve fs1 fs2 := by
  simp only [resolveN, resolve, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]

-- ============================================================================
-- § 8: Mismatch Resolution Hypothesis
-- ============================================================================

/-- A set of feature bundles **satisfies MRH** (Mismatch Resolution Hypothesis)
    if resolution succeeds for every pair of bundles — i.e., no pair produces
    an empty intersection, and no default insertion is ever needed.

    @cite{adamson-anagnostopoulou-2025}: Greek satisfies MRH because all
    resolution outcomes emerge from intersection alone. Bantu does NOT
    satisfy MRH because uninterpretable genders produce empty intersections. -/
def satisfiesMRH {F : Type} [BEq F] (bundles : List (FeatureBundle F)) : Bool :=
  bundles.all fun fs1 =>
    bundles.all fun fs2 =>
      (resolve fs1 fs2).isSome

-- ============================================================================
-- § 9: Feature Order
-- ============================================================================

/-- A feature geometry that defines entailment between feature nodes.
    @cite{adamson-anagnostopoulou-2025}: cross-linguistic variation in
    resolution follows from differences in feature geometry — the same
    labels with different entailment relations yield different outcomes.

    - `nodes`: the feature nodes in this geometry
    - `bundle`: maps each node to its full feature bundle (itself +
      everything it entails, as interpretable features) -/
structure FeatureOrder (F : Type) [BEq F] where
  nodes : List F
  bundle : F → FeatureBundle F

/-- Feature entailment: `f₁` entails `f₂` iff every i-feature in `f₂`'s
    bundle is also present in `f₁`'s bundle. In Greek: FEM entails MASC
    (because FEM's bundle {CLASS,MASC,FEM} ⊇ MASC's bundle {CLASS,MASC}). -/
def FeatureOrder.entails {F : Type} [BEq F]
    (order : FeatureOrder F) (f₁ f₂ : F) : Bool :=
  (percolateI (order.bundle f₂)).all ((percolateI (order.bundle f₁)).contains ·)

/-- A feature order satisfies MRH if all bundles from its geometry
    produce non-empty intersections under resolution. -/
def FeatureOrder.satisfiesMRH' {F : Type} [BEq F] (order : FeatureOrder F) : Bool :=
  satisfiesMRH (order.nodes.map order.bundle)

end Minimalism.Agreement.GenderResolution
