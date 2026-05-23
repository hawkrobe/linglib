import Linglib.Features.Person

/-!
# Person Feature Geometry @cite{harley-ritter-2002} @cite{bejar-rezac-2003}
@cite{bejar-rezac-2009} @cite{preminger-2014} @cite{pancheva-zubizarreta-2018}

The privative-feature geometry @cite{harley-ritter-2002} decomposes
person into a containment hierarchy where each sub-feature
implies the next:

    [φ] → [PERSON] → [participant] → [author]
    [φ] → [NUMBER] → [plural]

This decomposition drives **relativized probing**
(@cite{bejar-rezac-2003}): a probe seeking [participant] skips DPs
that lack it (3rd person), targeting only 1st/2nd person DPs. A
separate probe seeking [plural] skips DPs that lack it (singulars),
targeting only plurals.

@cite{bejar-rezac-2003} apply this two-probe mechanism to derive
the Person Case Constraint; @cite{bejar-rezac-2009} formalize it as
Cyclic Agree. @cite{preminger-2014} §4.4 applies the same B&R 2003
mechanism to Kichean Agent Focus — explicitly reframing earlier
"omnivorous hierarchy" accounts in terms of two independently
relativized probes π⁰ ([participant]) and #⁰ ([plural]). @cite{preminger-2014} Ch. 7 then argues against
direct hierarchy/scale primitives like
`[+participant] > [+plural] > default`, on four grounds:
restrictedness of "salience" effects to AF, K'ichee' formal
addressee *la* (a 2nd-person form patterning as 3rd-person under
AF), the AF person restriction (1+2 blocked but 3pl+3pl licit),
and the morphophonological 1st/2nd vs 3rd asymmetry (clitic
doubling vs direct exponence, @cite{preminger-2014} §3.4 and
§4.4). The relativized-probing mechanism derives the same surface
patterns without committing to a salience scale.

## Extended Geometry: [±proximate]

@cite{pancheva-zubizarreta-2018} extend the hierarchy with a
`[±proximate]` feature for the Person Case Constraint:

    [+author] ⊂ [+participant] ⊂ [+proximate]

1P and 2P are inherently [+proximate]. 3P arguments are
[-proximate] by default but can be contextually marked [+proximate]
(when co-occurring with another 3P). The [±proximate] distinction
also captures the 3P proximate/obviative split in direct/inverse
alignment systems (@cite{pancheva-zubizarreta-2018} §2.1 (11)).

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

## Note on `probeResolutionRank`

The `probeResolutionRank` function below assigns rank 2 to
[+participant] DPs, rank 1 to [+plural, −participant] DPs, and
rank 0 elsewhere. This is a CONVENIENCE encoding of the
*surface effect* of the two-probe (π⁰ ≫ #⁰) system on a single DP
— useful for downstream computations that need a totally ordered
target — but it should not be read as endorsing the salience-scale
analysis @cite{preminger-2014} Ch. 7 argues against. The actual
derivation goes via two independently relativized probes; the rank
is a derived quantity, not a primitive.

-/

namespace Minimalist

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

/-- Probe resolution rank for a DP under the two-probe (π⁰ ≫ #⁰) system.

    A surface-effect summary of which probe targets a given DP:

    - Rank 2: visible to π⁰ ([+participant])
    - Rank 1: visible to #⁰ but not π⁰ ([+plural, −participant])
    - Rank 0: invisible to both probes (3SG default)

    Derived from the probing mechanism (@cite{bejar-rezac-2003}),
    not stipulated as a salience scale: π⁰ takes priority over #⁰
    by virtue of being structurally higher and earlier in the
    derivation, and each probe targets any DP bearing the sought
    feature. The rank captures the combined effect on a single DP.
    See module docstring for why this is a convenience encoding,
    not an endorsement of the salience-scale analyses
    @cite{preminger-2014} Ch. 7 argues against. -/
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

end Minimalist
