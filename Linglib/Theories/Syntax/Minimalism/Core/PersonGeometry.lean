import Linglib.Core.Prominence

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

## Person Type

`decomposePerson` takes `Core.Prominence.PersonLevel` (`.first |
.second |.third`) — the canonical person type shared across the
library — rather than a raw `Nat`. This eliminates meaningless
person values and grounds the decomposition in the same type used
by `DifferentialIndexing`, `Prominence.PersonLevel.isSAP`, etc.

-/

namespace Minimalism

open Core.Prominence

-- ============================================================================
-- § 1: Decomposed Person Features
-- ============================================================================

/-- Person features decomposed according to @cite{preminger-2014}'s
    geometry, extended with `[±proximate]` from
    @cite{pancheva-zubizarreta-2018}.

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
structure DecomposedPerson where
  /-- Bears [proximate]? SAPs inherently; 3P contextually. -/
  hasProximate : Bool
  /-- Bears [participant]? 1st and 2nd person = true; 3rd = false. -/
  hasParticipant : Bool
  /-- Bears [author]? 1st person = true; 2nd and 3rd = false. -/
  hasAuthor : Bool
  deriving DecidableEq, BEq, Repr

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
  | .first  => ⟨true, true, true⟩
  | .second => ⟨true, true, false⟩
  | .third  => ⟨false, false, false⟩

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
  deriving DecidableEq, BEq, Repr

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
-- § 5: Verification — Decomposition Properties
-- ============================================================================

/-- 1st person is [+proximate, +participant, +author]. -/
theorem first_person_decomposition :
    (decomposePerson .first).hasProximate = true ∧
    (decomposePerson .first).hasParticipant = true ∧
    (decomposePerson .first).hasAuthor = true := ⟨rfl, rfl, rfl⟩

/-- 2nd person is [+proximate, +participant, −author]. -/
theorem second_person_decomposition :
    (decomposePerson .second).hasProximate = true ∧
    (decomposePerson .second).hasParticipant = true ∧
    (decomposePerson .second).hasAuthor = false := ⟨rfl, rfl, rfl⟩

/-- 3rd person is [−proximate, −participant, −author]. -/
theorem third_person_decomposition :
    (decomposePerson .third).hasProximate = false ∧
    (decomposePerson .third).hasParticipant = false ∧
    (decomposePerson .third).hasAuthor = false := ⟨rfl, rfl, rfl⟩

/-- All person values yield well-formed decompositions. -/
theorem all_decompositions_wellFormed (p : PersonLevel) :
    (decomposePerson p).wellFormed = true := by
  cases p <;> rfl

-- ============================================================================
-- § 6: Verification — Probe Visibility
-- ============================================================================

/-- 1st person is visible to the person probe (π⁰). -/
theorem first_visible_to_pi : probeVisible .participant .first false = true := rfl

/-- 3rd person is invisible to the person probe. -/
theorem third_invisible_to_pi : probeVisible .participant .third false = false := rfl

/-- 3rd plural is visible to the number probe (#⁰). -/
theorem third_plural_visible_to_hash : probeVisible .plural .third true = true := rfl

/-- 3rd singular is invisible to both probes. -/
theorem third_sg_invisible_to_both :
    probeVisible .participant .third false = false ∧
    probeVisible .plural .third false = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Verification — Resolution Rank
-- ============================================================================

/-- 1st/2nd person get rank 2 (visible to π⁰). -/
theorem participant_rank :
    probeResolutionRank .first false = 2 ∧
    probeResolutionRank .second false = 2 ∧
    probeResolutionRank .first true = 2 ∧
    probeResolutionRank .second true = 2 := ⟨rfl, rfl, rfl, rfl⟩

/-- 3rd plural gets rank 1 (visible to #⁰ only). -/
theorem plural_rank : probeResolutionRank .third true = 1 := rfl

/-- 3rd singular gets rank 0 (invisible to both probes = default). -/
theorem default_rank : probeResolutionRank .third false = 0 := rfl

/-- Rank is monotone in the probe hierarchy: any DP visible to π⁰
    (rank 2) outranks any DP visible only to #⁰ (rank 1), which
    outranks any DP invisible to both (rank 0). -/
theorem rank_hierarchy :
    probeResolutionRank .first false > probeResolutionRank .third true ∧
    probeResolutionRank .third true > probeResolutionRank .third false := by decide

end Minimalism
