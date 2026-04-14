import Linglib.Core.Lexical.PolarityItem

/-!
# Core Negation Types

Framework-agnostic types for negation phenomena shared across
fragments and phenomena layers.

## Expletive Negation Classification

Two orthogonal classifications of expletive negation (EN):

- `ENType` (high/low) — @cite{rett-2026}'s position-based classification
- `ENStrength` (weak/strong) — @cite{greco-2020}'s polarity-based classification
- `PolarityClass` / `PolarityLicensing` — polarity-sensitive element classes
  and their licensing profiles

These types are framework-agnostic: they classify EN constructions by
their empirical properties without committing to a syntactic analysis.
The syntactic derivation (from merge position in the extended projection)
lives in `Theories.Syntax.Minimalism.Core.NegScope`.
-/

namespace Core

open Core.Lexical.PolarityItem (PolarityType)

/-- Cross-linguistic reasons why a trigger class may not license
    expletive negation in a particular language (@cite{jin-koenig-2021} §7). -/
inductive ENBlockingReason where
  /-- Language disprefers modal operators in complement clauses -/
  | modalRestriction
  /-- Comparative complements only allow NPs, not clauses -/
  | npOnlyComplement
  /-- Concept expressed analytically with necessary (non-expletive) negation -/
  | analyticNegation
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. EN type classification
-- ════════════════════════════════════════════════════

/-- Two syntactic types of expletive negation (@cite{rett-2026}).

    **High EN** appears above TP, targets non-truth-conditional content
    (exclamatives, surprise negation). It is obligatory where licensed.

    **Low EN** appears below TP (VP-level), targets truth-conditional
    content in ambidirectional environments. It is optional and triggers
    a manner implicature (evaluativity). -/
inductive ENType where
  | high   -- Non-truth-conditional; obligatory (exclamatives, surprise)
  | low    -- Truth-conditional; optional (before, than, fear)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. EN strength classification
-- ════════════════════════════════════════════════════

/-- @cite{greco-2020} §2.1: EN constructions divide into two classes
    based on co-occurrence with polarity-sensitive elements.

    **Weak EN** retains some polarity properties of standard negation:
    licenses weak NPIs and N-words (e.g. *finché*-clauses, *unless*-clauses).

    **Strong EN** loses all polarity properties: rejects weak NPIs,
    strong NPIs, not-also conjunctions, and N-words (e.g. negative
    exclamatives, rhetorical questions, surprise negation). -/
inductive ENStrength where
  | weak    -- Retains some SN properties (weak NPIs, N-words)
  | strong  -- Loses all SN polarity properties
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 4. Polarity classes and licensing profiles
-- ════════════════════════════════════════════════════

/-- The four classes of polarity-sensitive elements tested by
    @cite{greco-2020} Table 1. Each EN environment either licenses
    or rejects each class, giving a four-bit fingerprint. -/
inductive PolarityClass where
  | weakNPI      -- weak NPIs: *alcuno*, *qualche*, *any*
  | strongNPI    -- strong NPIs: minimizers like *muovere un dito*
  | notAlsoConj  -- *e neanche* / *not ... also* conjunctions
  | nWord        -- N-words: *nessuno*, *niente*, *mai*
  deriving DecidableEq, Repr

/-- Polarity licensing profile for an EN environment (@cite{greco-2020} Table 1).
    Each field records whether that class of polarity-sensitive element
    is grammatical in the construction. -/
structure PolarityLicensing where
  weakNPIs : Bool
  strongNPIs : Bool
  notAlsoConj : Bool
  nWords : Bool
  deriving DecidableEq, Repr

/-- Accessor: look up a polarity class in the licensing profile. -/
def PolarityLicensing.licenses (p : PolarityLicensing) : PolarityClass → Bool
  | .weakNPI     => p.weakNPIs
  | .strongNPI   => p.strongNPIs
  | .notAlsoConj => p.notAlsoConj
  | .nWord       => p.nWords

/-- Weak EN environments license weak NPIs and N-words but NOT
    strong NPIs or not-also conjunctions. -/
def weakENProfile : PolarityLicensing :=
  { weakNPIs := true, strongNPIs := false, notAlsoConj := false, nWords := true }

/-- Strong EN environments license NONE of the four polarity classes. -/
def strongENProfile : PolarityLicensing :=
  { weakNPIs := false, strongNPIs := false, notAlsoConj := false, nWords := false }

/-- Strong EN rejects ALL polarity classes (universally quantified). -/
theorem strongEN_rejects_all (c : PolarityClass) :
    strongENProfile.licenses c = false := by cases c <;> rfl

/-- Weak EN licenses exactly the weak NPIs and N-words. -/
theorem weakEN_licenses_weakNPI : weakENProfile.licenses .weakNPI = true := rfl
theorem weakEN_licenses_nWord : weakENProfile.licenses .nWord = true := rfl
theorem weakEN_rejects_strongNPI : weakENProfile.licenses .strongNPI = false := rfl
theorem weakEN_rejects_notAlso : weakENProfile.licenses .notAlsoConj = false := rfl

-- ════════════════════════════════════════════════════
-- § 5. Bridge: PolarityClass ↔ PolarityType
-- ════════════════════════════════════════════════════

/-- Partial map from PolarityClass to PolarityType.
    Two of the four Greco classes correspond directly to PolarityType
    constructors. N-words and not-also conjunctions are Italian-specific
    categories without a PolarityType counterpart. -/
def PolarityClass.toPolarityType? : PolarityClass → Option PolarityType
  | .weakNPI   => some .npiWeak
  | .strongNPI => some .npiStrong
  | _          => none

/-- Inverse: map PolarityType to PolarityClass (partial — only NPIs). -/
def PolarityClass.fromPolarityType? : PolarityType → Option PolarityClass
  | .npiWeak  => some .weakNPI
  | .npiStrong => some .strongNPI
  | _          => none

/-- Round-trip: PolarityType → PolarityClass → PolarityType is identity
    (for the NPI types that have counterparts). -/
theorem PolarityClass.roundtrip_npiWeak :
    (PolarityClass.fromPolarityType? .npiWeak).bind PolarityClass.toPolarityType?
    = some .npiWeak := rfl

theorem PolarityClass.roundtrip_npiStrong :
    (PolarityClass.fromPolarityType? .npiStrong).bind PolarityClass.toPolarityType?
    = some .npiStrong := rfl

/-- Compose the bridges: look up a PolarityType in a licensing profile
    by routing through PolarityClass. Returns `none` for types without
    a PolarityClass counterpart (FCIs, PPIs, NPI-FCIs). -/
def PolarityLicensing.licensesType (p : PolarityLicensing) (t : PolarityType) :
    Option Bool :=
  (PolarityClass.fromPolarityType? t).map p.licenses

end Core
