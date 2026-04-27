import Linglib.Core.Case.Basic
import Linglib.Core.Lexical.Word
import Linglib.Features.Prominence

/-!
# Feature Infrastructure for Minimalist Agree
@cite{adger-2003} @cite{chomsky-1995} @cite{chomsky-2000} @cite{chomsky-2001} @cite{alok-2020} @cite{alok-bhalla-2026} @cite{lobeck-1995} @cite{panagiotidis-2015} @cite{pollock-1989}

Phi-features, case values, and feature bundles — the shared infrastructure
underlying all Agree-based operations. Extracted from `Agree.lean` to
separate the feature *types* (what can be checked) from the Agree
*operation* (how checking works) and the *failure model* (what happens
when checking fails; see `ObligatoryOperations.lean`).

## ±Interpretable Features (@cite{chomsky-1995} Ch 4 §4.5)

The ±Interpretable distinction is orthogonal to valued/unvalued:

- **+Interpretable**: contributes to meaning, survives to LF.
  Categorial features ([N], [V], [D], [C]) and φ-features of nouns.
- **–Interpretable**: must be checked and deleted before LF.
  Case features, φ-features of T/v, strong [nominal-] features.

Interpretability is determined by the combination of feature type and
host category: person on N is +Interpretable, person on T is
–Interpretable. `isInterpretableOn` encodes this mapping.

## Design Decision: `PersonLevel` replaces `Nat`

`PhiFeature.person` uses `Features.Prominence.PersonLevel` (`.first |.second
|.third`) rather than a raw `Nat`. This eliminates the possibility of
meaningless person values (e.g., `person 47`) and grounds the feature
inventory in the same canonical type used across the library:

- `Features.Prominence.PersonLevel` — framework-agnostic person hierarchy
- `PersonGeometry.DecomposedPerson` — @cite{preminger-2014}'s [±participant,
  ±author] decomposition, now mapping from `PersonLevel`
- `DifferentialIndexing.IndexingPersonLevel` — @cite{just-2024}'s SAP/3rd
  binary split, bridged to `PersonLevel`

For unvalued (probe) features, the value is irrelevant —
`FeatureVal.sameType` matches any `.person _` against any `.person _`
and any `.number _` against any `.number _`, ignoring specific values.
Use `.person .third` and `.number .sg` as conventional placeholders
for probes.

-/

namespace Minimalist

open Features.Prominence

-- ============================================================================
-- § 1: Phi-Features
-- ============================================================================

/-- Phi-features (agreement features). -/
inductive PhiFeature where
  | person : PersonLevel → PhiFeature
  | number : Number → PhiFeature      -- grammatical number (UD.Number)
  | gender : Nat → PhiFeature        -- language-specific encoding
  deriving Repr, DecidableEq

-- ============================================================================
-- § 2: Honorific Features
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
-- § 3: Feature Values
-- ============================================================================

/-- Feature values that can be checked via Agree -/
inductive FeatureVal where
  | phi : PhiFeature → FeatureVal
  | case : Core.Case → FeatureVal
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
  | foc : Bool → FeatureVal       -- [±FOC] information structure (@cite{westergaard-2009})
  | pol : Bool → FeatureVal       -- [±Pol] polarity (@cite{laka-1990}; @cite{holmberg-2016})
  | pov : Bool → FeatureVal      -- [±d] point-of-view (@cite{chou-2012}; @cite{chan-shen-2026})
  -- Harbour decompositional features for person/number; distinct from the
  -- `phi` constructors above so postsyntactic rules can target them
  -- individually without colliding with existing person/number/gender
  -- pattern-matching elsewhere in the library.
  | atomic : Bool → FeatureVal     -- [±atomic] number lattice (@cite{harbour-2014})
  | minimal : Bool → FeatureVal    -- [±minimal] number lattice (@cite{harbour-2014})
  | participant : Bool → FeatureVal -- [±participant] person lattice (@cite{harbour-2016})
  | author : Bool → FeatureVal     -- [±author] person lattice (@cite{harbour-2016})
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
  | .foc _, .foc _ => true
  | .pol _, .pol _ => true
  | .pov _, .pov _ => true
  | .atomic _, .atomic _ => true
  | .minimal _, .minimal _ => true
  | .participant _, .participant _ => true
  | .author _, .author _ => true
  | _, _ => false

-- ============================================================================
-- § 4: Grammatical Features (Valued / Unvalued)
-- ============================================================================

/-- A grammatical feature: either valued or unvalued.

    **Valued vs unvalued** is about whether the feature carries a specific
    value (person:3) or just a type placeholder (person:_). This is
    orthogonal to ±Interpretable (see `Interpretability` below):

    |                 | +Interpretable          | –Interpretable               |
    |-----------------|------------------------|-------------------------------|
    | **Valued**      | φ of N (person:3)      | —                             |
    | **Unvalued**    | —                      | φ of T/v, Case of N           |

    Unvalued features act as probes; valued features can be goals.
    But interpretability determines whether a feature *must be checked
    and deleted* before LF — a separate question from whether it
    currently carries a value. -/
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
-- § 5: Feature Bundles
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

-- ============================================================================
-- § 6: ±Interpretable Features
-- ============================================================================

/-- Whether a feature is interpretable (contributes to LF) or
    uninterpretable (must be checked and deleted before LF).

    This is the central distinction of @cite{chomsky-1995} Ch 4 §4.5.
    It is orthogonal to valued/unvalued: a feature can be interpretable
    but unvalued (rare), or uninterpretable but valued (never, in the
    standard theory). The typical pairings are:

    - +Interpretable, valued: φ-features on nouns, categorial features
    - –Interpretable, unvalued: φ-features on T/v, Case on nouns

    `AgreeSOT.lean` uses `Interpretability` directly for tense features.
    `GenderResolution.lean`'s `AnnotatedFeature.interp` uses `Interpretability`
    directly; `CoordinateResolution.lean`, `AdamsonAnagnostopoulou2025.lean`,
    and `Carstens2026.lean` all use it via `open _root_.Minimalist`. -/
inductive Interpretability where
  | interpretable    -- +Interp: contributes to LF, survives
  | uninterpretable  -- –Interp: must be checked and deleted
  deriving Repr, DecidableEq

/-- Whether a feature is inherently interpretable regardless of host.

    Some features are always interpretable (categorial, honorific,
    factive) or always uninterpretable (Case, EPP, ellipsis).
    For features whose interpretability depends on host category
    (phi, wh, tense), see `isInterpretableOn` in `Checking.lean`. -/
def FeatureVal.inherentInterpretability : FeatureVal → Option Interpretability
  | .catN _ | .catV _ => some .interpretable
  | .case _ => some .uninterpretable
  | .epp _ => some .uninterpretable
  | .ellipsis _ => some .uninterpretable
  | .oblique _ => some .uninterpretable
  | .hon _ => some .interpretable
  | .neg _ => some .interpretable
  | .factive _ | .pol _ | .pov _ => some .interpretable
  | _ => none  -- host-dependent: phi, wh, q, tense, finite, foc, rel

/-- Case is always uninterpretable. -/
theorem case_always_uninterpretable (c : Core.Case) :
    FeatureVal.inherentInterpretability (.case c) = some .uninterpretable := rfl

/-- Categorial [N] is always interpretable. -/
theorem catN_always_interpretable (b : Bool) :
    FeatureVal.inherentInterpretability (.catN b) = some .interpretable := rfl

end Minimalist
