import Linglib.Core.Case.Basic
import Linglib.Core.Prominence

/-!
# Feature Infrastructure for Minimalist Agree
@cite{adger-2003} @cite{chomsky-2000} @cite{chomsky-2001} @cite{alok-2020} @cite{alok-bhalla-2026} @cite{lobeck-1995} @cite{panagiotidis-2015} @cite{pollock-1989}

Phi-features, case values, and feature bundles — the shared infrastructure
underlying all Agree-based operations. Extracted from `Agree.lean` to
separate the feature *types* (what can be checked) from the Agree
*operation* (how checking works) and the *failure model* (what happens
when checking fails; see `ObligatoryOperations.lean`).

## Design Decision: `PersonLevel` replaces `Nat`

`PhiFeature.person` uses `Core.Prominence.PersonLevel` (`.first |.second
|.third`) rather than a raw `Nat`. This eliminates the possibility of
meaningless person values (e.g., `person 47`) and grounds the feature
inventory in the same canonical type used across the library:

- `Core.Prominence.PersonLevel` — framework-agnostic person hierarchy
- `PersonGeometry.DecomposedPerson` — @cite{preminger-2014}'s [±participant,
  ±author] decomposition, now mapping from `PersonLevel`
- `DifferentialIndexing.IndexingPersonLevel` — @cite{just-2024}'s SAP/3rd
  binary split, bridged to `PersonLevel`

For unvalued (probe) features, the `PersonLevel` value is irrelevant —
`FeatureVal.sameType` matches any `.person _` against any `.person _`,
ignoring the specific value. Use `.person.third` as the conventional
placeholder for probes.

-/

namespace Minimalism

open Core.Prominence

-- ============================================================================
-- § 1: Phi-Features
-- ============================================================================

/-- Phi-features (agreement features). -/
inductive PhiFeature where
  | person : PersonLevel → PhiFeature
  | number : Bool → PhiFeature       -- true = plural, false = singular
  | gender : Nat → PhiFeature        -- language-specific encoding
  deriving Repr, DecidableEq

-- ============================================================================
-- § 2: Case Values
-- ============================================================================

/-- Case values used in the Agree system.

    This is the Minimalism-internal case type, covering the 8 values needed
    for Agree-based case assignment. For the full cross-linguistic inventory,
    see `Core.Case`. -/
inductive CaseVal where
  | nom    -- nominative (subject)
  | acc    -- accusative (object)
  | dat    -- dative
  | gen    -- genitive
  | obl    -- oblique (default)
  | abl    -- ablative (source: Japanese *kara*, Latin *ab*)
  | erg    -- ergative (transitive subject: Basque, Hindi)
  | abs    -- absolutive (intransitive subject / transitive object)
  deriving Repr, DecidableEq

/-- Convert a Minimalist `CaseVal` to the theory-neutral `Core.Case`.

    `obl` (oblique) is a Minimalism-internal category, not a specific case in
    @cite{blake-1994}'s typology. We map it to `dat` as the highest-ranked
    peripheral case — this is an approximation, since "oblique" in Minimalism
    is a cover term for non-core cases, most commonly dative-like. -/
def CaseVal.toCase : CaseVal → Core.Case
  | .nom => .nom
  | .acc => .acc
  | .dat => .dat
  | .gen => .gen
  | .obl => .dat  -- oblique: Minimalism-internal, approx. as highest peripheral
  | .abl => .abl
  | .erg => .erg
  | .abs => .abs

-- ============================================================================
-- § 3: Honorific Features
-- ============================================================================

/-- Honorific level: social ordering between speaker and referent.
    Relational, not absolute.
    ⟦iHON⟧ = λx. S_i ≺ x, where ≺ encodes social hierarchy. -/
inductive HonLevel where
  | nh    -- nonhonorific: S ≥ referent
  | h     -- honorific: S < referent
  | hh    -- high honorific: S << referent
  deriving Repr, DecidableEq

-- ============================================================================
-- § 4: Feature Values
-- ============================================================================

/-- Feature values that can be checked via Agree -/
inductive FeatureVal where
  | phi : PhiFeature → FeatureVal
  | case : CaseVal → FeatureVal
  | wh : Bool → FeatureVal           -- [±wh]
  | q : Bool → FeatureVal            -- [±Q] (question)
  | epp : Bool → FeatureVal          -- EPP (needs specifier)
  | tense : Bool → FeatureVal        -- [±tense]
  | hon : HonLevel → FeatureVal      -- [iHON] (@cite{alok-bhalla-2026})
  | finite : Bool → FeatureVal       -- [±finite] (Fin head, @cite{rizzi-1997})
  | factive : Bool → FeatureVal      -- [±factive] (clause-typing)
  | neg : Bool → FeatureVal          -- [±neg] (NegP, @cite{pollock-1989})
  | rel : Bool → FeatureVal          -- [±rel] (relative clause typing, @cite{rizzi-1997})
  | oblique : Bool → FeatureVal     -- [±oblique] (extraction tracking, @cite{elkins-torrence-brown-2026})
  | ellipsis : Bool → FeatureVal   -- [E] feature licensing NP-ellipsis (@cite{lobeck-1995}, @cite{saab-2026})
  | catN : Bool → FeatureVal       -- [N] referentiality (@cite{panagiotidis-2015})
  | catV : Bool → FeatureVal       -- [V] temporal predication (@cite{panagiotidis-2015})
  deriving Repr, DecidableEq

/-- Do two feature values have the same type, ignoring specific values?

    This is the correct matching predicate for Agree: a probe with
    [uPerson] should match any goal with [Person:x], regardless of
    the specific person value x. In contrast, `DecidableEq` (`==`)
    compares both type and value, which is wrong for Agree matching
    where the probe carries a placeholder value. -/
def FeatureVal.sameType : FeatureVal → FeatureVal → Bool
  | .phi p1, .phi p2 => match p1, p2 with
    | .person _, .person _ => true
    | .number _, .number _ => true
    | .gender _, .gender _ => true
    | _, _ => false
  | .case _, .case _ => true
  | .wh _, .wh _ => true
  | .q _, .q _ => true
  | .epp _, .epp _ => true
  | .tense _, .tense _ => true
  | .hon _, .hon _ => true
  | .finite _, .finite _ => true
  | .factive _, .factive _ => true
  | .neg _, .neg _ => true
  | .rel _, .rel _ => true
  | .oblique _, .oblique _ => true
  | .ellipsis _, .ellipsis _ => true
  | .catN _, .catN _ => true
  | .catV _, .catV _ => true
  | _, _ => false

-- ============================================================================
-- § 5: Grammatical Features (Valued / Unvalued)
-- ============================================================================

/-- A grammatical feature: either valued or unvalued

    - Valued (interpretable): contributes to meaning, can be a goal
    - Unvalued (uninterpretable): must be checked, acts as probe -/
inductive GramFeature where
  | valued : FeatureVal → GramFeature
  | unvalued : FeatureVal → GramFeature  -- The FeatureVal indicates feature TYPE
  deriving Repr, DecidableEq

/-- Is this feature valued? -/
def GramFeature.isValued : GramFeature → Bool
  | .valued _ => true
  | .unvalued _ => false

/-- Is this feature unvalued (a potential probe)? -/
def GramFeature.isUnvalued : GramFeature → Bool
  | .valued _ => false
  | .unvalued _ => true

/-- Get the feature type (ignoring valued/unvalued distinction) -/
def GramFeature.featureType : GramFeature → FeatureVal
  | .valued v => v
  | .unvalued v => v

/-- Do two features match in type? (for Agree)
    Delegates to `FeatureVal.sameType`, ignoring specific values. -/
def featuresMatch (f1 f2 : GramFeature) : Bool :=
  f1.featureType.sameType f2.featureType

-- ============================================================================
-- § 6: Feature Bundles
-- ============================================================================

/-- A feature bundle: list of grammatical features -/
abbrev FeatureBundle := List GramFeature

/-- Does the bundle have an unvalued feature of a given type?
    Uses `sameType` so that e.g. [uPerson:_] matches ftype [Person:_]. -/
def hasUnvaluedFeature (fb : FeatureBundle) (ftype : FeatureVal) : Bool :=
  fb.any λ f => f.isUnvalued && f.featureType.sameType ftype

/-- Does the bundle have a valued feature of a given type?
    Uses `sameType` so that e.g. [Person:3] matches ftype [Person:_]. -/
def hasValuedFeature (fb : FeatureBundle) (ftype : FeatureVal) : Bool :=
  fb.any λ f => f.isValued && f.featureType.sameType ftype

/-- Get the valued feature of a given type (if present).
    Uses `sameType` for type-level matching. -/
def getValuedFeature (fb : FeatureBundle) (ftype : FeatureVal) : Option GramFeature :=
  fb.find? λ f => f.isValued && f.featureType.sameType ftype

end Minimalism
