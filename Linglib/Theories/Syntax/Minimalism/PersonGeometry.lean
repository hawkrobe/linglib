import Linglib.Features.Person

/-!
# Person Feature Geometry @cite{preminger-2014}
@cite{bejar-rezac-2009} @cite{pancheva-zubizarreta-2018}

@cite{preminger-2014} decomposes phi-features into a
hierarchical geometry where person sub-features are organized in a
containment hierarchy:

    [φ] → [PERSON] → [participant] → [author]
    [φ] → [NUMBER] → [plural]

This decomposition drives **relativized probing**: a probe seeking
[participant] skips DPs that lack it (3rd person), targeting only
1st/2nd person DPs. A separate probe seeking [plural] skips DPs
that lack it (singulars), targeting only plurals.

The two-probe system derives the **omnivorous agreement hierarchy**
in Kaqchikel Agent Focus:

    [+participant] (π⁰) > [+plural] (#⁰) > default (3SG)

π⁰ outranks #⁰ because person probing takes priority over number
probing. If π⁰ succeeds, its target determines the marker; if it
fails, #⁰ provides the result; if both fail, the default surfaces.

## Extended Geometry: [±proximate]

@cite{pancheva-zubizarreta-2018} extend the hierarchy with a
`[±proximate]` feature for the Person Case Constraint:

    [+author] ⊂ [+participant] ⊂ [+proximate]

1P and 2P are inherently [+proximate]. 3P arguments are
[-proximate] by default but can be contextually marked [+proximate]
(when co-occurring with another 3P). The [±proximate] distinction
also captures the 3P proximate/obviative split in direct/inverse
alignment systems (@cite{pancheva-zubizarreta-2018}, §2.1 (11)).

## Relationship to Core PersonFeatures

`DecomposedPerson` extends `Features.Person.Features`
(the framework-neutral [±participant, ±author] decomposition) with
the Minimalism-specific [±proximate] feature. The two-feature core
is shared across all theoretical frameworks; `[±proximate]` is
specific to @cite{pancheva-zubizarreta-2018}'s P-Constraint.

## Person Type

`decomposePerson` takes `Features.Prominence.PersonLevel` (`.first |
.second |.third`) — the canonical person type shared across the
library — rather than a raw `Nat`. This eliminates meaningless
person values and grounds the decomposition in the same type used
by `DifferentialIndexing`, `Prominence.PersonLevel.isSAP`, etc.

-/

namespace Minimalism

open Features.Prominence

-- ============================================================================
-- § 1: Decomposed Person Features
-- ============================================================================

/-- Person features decomposed according to @cite{preminger-2014}'s
    geometry, extended with `[±proximate]` from
    @cite{pancheva-zubizarreta-2018}.

    Extends `Features.Person.Features` (the framework-neutral
    [±participant, ±author] core) with the Minimalism-specific
    [±proximate] feature:

    - [proximate] marks potential point-of-view centers. 1P/2P are
      inherently [+proximate]; 3P can be contextually [+proximate].
    - [participant] distinguishes 1st/2nd from 3rd person.
    - [author] distinguishes 1st from 2nd person.

    The geometry imposes a containment hierarchy:
      [+author] → [+participant] → [+proximate]

    Note: The paper treats these as **privative** features:
    3rd person simply LACKS [participant], rather than bearing
    [−participant]. We encode this as `Bool` for computational
    convenience; the well-formedness constraint `wellFormed`
    ensures the privative entailments are maintained. -/
structure DecomposedPerson extends Features.Person.Features where
  /-- Bears [proximate]? SAPs inherently; 3P contextually. -/
  hasProximate : Bool
  deriving DecidableEq, Repr

/-- Geometry well-formedness: [author] → [participant] → [proximate].
    Each feature entails the next in the containment hierarchy. -/
def DecomposedPerson.wellFormed (dp : DecomposedPerson) : Bool :=
  (!dp.hasAuthor || dp.hasParticipant) &&
  (!dp.hasParticipant || dp.hasProximate)

-- ============================================================================
-- § 2: Person Decomposition
-- ============================================================================

/-- Decompose a person value into sub-features.

    - 1st person: [+proximate, +participant, +author]
    - 2nd person: [+proximate, +participant, −author]
    - 3rd person: [−proximate, −participant, −author]

    3rd person is [-proximate] by default; contextual [+proximate]
    marking is handled by the P-Constraint evaluation. -/
def decomposePerson : PersonLevel → DecomposedPerson
  | .first  => { hasParticipant := true,  hasAuthor := true,  hasProximate := true }
  | .second => { hasParticipant := true,  hasAuthor := false, hasProximate := true }
  | .third  => { hasParticipant := false, hasAuthor := false, hasProximate := false }

-- ============================================================================
-- § 3: Probe Targets
-- ============================================================================

/-- What a phi-probe seeks.

    In the AF construction, two probes operate:
    - **π⁰** seeks [participant]: targets 1st/2nd person DPs
    - **#⁰** seeks [plural]: targets plural DPs

    π⁰ structurally outranks #⁰ (person probing > number probing). -/
inductive ProbeTarget where
  /-- π⁰: person probe, seeks [participant]. -/
  | participant
  /-- #⁰: number probe, seeks [plural]. -/
  | plural
  deriving DecidableEq, Repr

/-- Is a DP visible to this probe? Relativized probing: probes skip
    DPs that lack the feature they seek.

    A DP with person value `person` and number `isPlural` is visible
    to the probe iff it bears the probe's target feature. -/
def probeVisible (target : ProbeTarget) (person : PersonLevel) (isPlural : Bool) : Bool :=
  match target with
  | .participant => (decomposePerson person).hasParticipant
  | .plural => isPlural

-- ============================================================================
-- § 4: Probe Resolution Rank
-- ============================================================================

/-- Omnivorous probe resolution rank for a DP.

    Determines which DP an omnivorous probe targets when multiple DPs
    are in its domain. Higher rank = more likely to be targeted.

    - Rank 2: visible to π⁰ ([+participant]) — highest priority
    - Rank 1: visible to #⁰ but not π⁰ ([+plural, −participant])
    - Rank 0: invisible to both probes (3SG default)

    This rank is derived from the probing mechanism, not stipulated:
    π⁰ outranks #⁰, and each probe targets any DP bearing the sought
    feature. The rank captures the combined effect. -/
def probeResolutionRank (person : PersonLevel) (isPlural : Bool) : Nat :=
  if (decomposePerson person).hasParticipant then 2
  else if isPlural then 1
  else 0

-- ============================================================================
-- § 5: Verification — Cross-module Agreement and Hierarchy
-- ============================================================================

/-- All person values yield well-formed decompositions. -/
theorem all_decompositions_wellFormed (p : PersonLevel) :
    (decomposePerson p).wellFormed = true := by
  cases p <;> rfl

/-- `decomposePerson` is consistent with the framework-neutral
    `PersonLevel.toFeatures`: the [±participant, ±author] core of
    the Minimalist decomposition agrees with Core Person.Features. -/
theorem decomposePerson_toFeatures_eq (p : PersonLevel) :
    (decomposePerson p).toFeatures = p.toFeatures := by
  cases p <;> rfl

/-- Rank is monotone in the probe hierarchy: any DP visible to π⁰
    (rank 2) outranks any DP visible only to #⁰ (rank 1), which
    outranks any DP invisible to both (rank 0). -/
theorem rank_hierarchy :
    probeResolutionRank .first false > probeResolutionRank .third true ∧
    probeResolutionRank .third true > probeResolutionRank .third false := by decide

/-- Smoke check on per-cell decomposition / probe / rank values.
    Per-cell theorems would be rfl-trivial on a 3-element type;
    this single `decide` keeps a kept-tested-shape signal without
    inflating the API surface. -/
example :
    (decomposePerson .first).hasParticipant = true ∧
    (decomposePerson .first).hasAuthor = true ∧
    (decomposePerson .second).hasAuthor = false ∧
    (decomposePerson .third).hasParticipant = false ∧
    probeVisible .participant .first false = true ∧
    probeVisible .participant .third false = false ∧
    probeVisible .plural .third true = true ∧
    probeVisible .plural .third false = false ∧
    probeResolutionRank .first false = 2 ∧
    probeResolutionRank .second false = 2 ∧
    probeResolutionRank .third true = 1 ∧
    probeResolutionRank .third false = 0 := by decide

-- ============================================================================
-- § 6: Identity Subfeature (@cite{olivier-2026})
-- ============================================================================

/-! ### Referential identity as a person sub-feature

**Status: experimental.** `IdFeature` is a single-paper extension
of the Harley–Ritter geometry, motivated by @cite{olivier-2025b}
and applied in @cite{olivier-2026}. The only consumer is
`Phenomena/AuxiliaryVerbs/Studies/Olivier2026.lean`. The framework
is not yet replicated in independent literature; @cite{amato-2025}
NLLT derives the same Italian auxiliary-selection predictions purely
from feature ordering + Nested Agree, *without* an IdFeature
primitive — see `Theories/Syntax/Minimalism/NestedAgree.lean`. Treat
this as scoped to the Olivier line of work; do not propagate to
other PersonGeometry consumers without further literature support.

@cite{olivier-2026}, extending @cite{harley-ritter-2002}, argues
that two pronouns can share the same `[3, masc, sg]` φ-features yet
differ in *referential identity*: `[the men]ᵢ` and `[the men]ₖ`
have identical φ-values but distinct indices. ID-features are
valued indices; reflexive clitics carry an unvalued ID-feature
that gets valued through binding (mediated by Voice*).

Auxiliary selection in Romance restructuring is then sensitive to
ID-identity between T and vAux, not just person-value match: the
matrix auxiliary surfaces as BE iff the two ID-features match,
and as HAVE otherwise. This refines the φ-only matching of
classical accounts and is what allows reflexive-clitic climbing
(which equates ID across the matrix and embedded domains) to
trigger Auxiliary Switch. -/

/-- Identity subfeature on Person, representing referential identity
    (distinct from grammatical person value).

    @cite{olivier-2026} (extending @cite{harley-ritter-2002}) argues
    that two pronouns can share `[3, masc, sg]` φ-features yet differ
    in referential identity: `[the men]ᵢ` vs `[the men]ₖ`. ID-features
    are valued indices; reflexive clitics carry an unvalued ID-feature
    that gets valued through binding (mediated by Voice*).

    Auxiliary selection in Romance restructuring is sensitive to
    ID-identity between T and vAux, not just person-value match
    (@cite{olivier-2026}). -/
inductive IdFeature where
  /-- Unvalued: reflexive clitic awaiting binding by an antecedent. -/
  | unvalued
  /-- Valued with a referential index. -/
  | valued (idx : Nat)
  deriving DecidableEq, Repr

/-- ID-features match iff both are valued with the same index.
    Two unvalued features do NOT match — valuation must occur first.
    This drives @cite{olivier-2026}'s aux-selection rule. -/
def IdFeature.matches : IdFeature → IdFeature → Bool
  | .valued i, .valued j => i = j
  | _, _ => false

/-- Valuation by binding: an unvalued ID receives the binder's index.
    A valued ID is not overwritten (idempotent on already-valued IDs). -/
def IdFeature.valueBy : IdFeature → Nat → IdFeature
  | .unvalued, k => .valued k
  | .valued i, _ => .valued i

/-- A valued ID-feature matches itself. -/
theorem valued_matches_self (i : Nat) :
    IdFeature.matches (.valued i) (.valued i) = true := by
  simp only [IdFeature.matches, decide_true]

/-- An unvalued ID-feature matches nothing — neither another
    unvalued nor any valued feature. -/
theorem unvalued_matches_nothing (f : IdFeature) :
    IdFeature.matches .unvalued f = false := by
  cases f <;> rfl

/-- Valuation of an unvalued ID yields a valued ID at the binder's index. -/
theorem valueBy_unvalued_yields_valued (k : Nat) :
    IdFeature.valueBy .unvalued k = .valued k := rfl

/-- Valuation is idempotent on already-valued IDs: a second
    valuation attempt does not overwrite the existing index. -/
theorem valueBy_idempotent (i k : Nat) :
    IdFeature.valueBy (.valued i) k = .valued i := rfl

/-- After binding by an antecedent with index `k`, a previously
    unvalued reflexive ID matches an antecedent ID also valued at `k`. -/
theorem reflexive_after_binding_matches_antecedent (k : Nat) :
    IdFeature.matches (IdFeature.valueBy .unvalued k) (.valued k) = true := by
  simp only [IdFeature.valueBy, IdFeature.matches, decide_true]

end Minimalism
