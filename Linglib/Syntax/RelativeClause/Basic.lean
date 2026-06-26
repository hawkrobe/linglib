import Mathlib.Tactic.DeriveFintype
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Linglib.Features.Definiteness
import Linglib.Syntax.Extraction

/-!
# Relative clauses: structural core

Theory-neutral types for cross-linguistic relative-clause data: the
[keenan-comrie-1977] Accessibility Hierarchy, the relative-clause
position relative to the head noun, what occupies the relativized position
(NP_rel), and the `Marker` schema fragments instantiate. Fragments use these
to encode relative-clause markers and their distributional properties;
phenomenon studies use them to verify typological generalizations like the
Accessibility Hierarchy. Mirrors `Case` for case inventories.

## Main declarations

* `RelativeClause.AHPosition` — grammatical positions on the
  [keenan-comrie-1977] Accessibility Hierarchy, with `rank` and the
  `contiguousOnAH` segment predicate (HC₂).
* `RelativeClause.RCPosition` — position of the relative clause with respect
  to the head noun (post-nominal, pre-nominal, internally-headed, correlative).
* `RelativeClause.NPRelType` — what occupies the relativized position
  (gap, resumptive, relative pronoun, …).
* `RelativeClause.Realization` — what one derivation realizes (AH position +
  NP_rel type); the framework-neutral hook a syntactic account projects to.
* `RelativeClause.Marker` — a relative-clause marker or construction, with
  the `Covers` / `IsContinuous` / `IsPrimary` predicates fragments and studies
  consume.

## Implementation notes

The contiguity machinery (`contiguousOnAH`, `AHPosition.rank`) mirrors
`Core.validInventory` for the case hierarchy ([blake-1994]); the
`contiguousOnAH : Bool` kernel with a `ContiguousOnAH : Prop` wrapper is the
load-bearing form for the decide-checked case analyses in
`Studies/KeenanComrie1977.lean`. Coverage predicates (`Covers`, `IsContinuous`,
`IsPrimary`) are stated as `Prop` with `Decidable` instances — no parallel
`Bool` projections.
-/

set_option autoImplicit false

namespace RelativeClause

open Extraction (ExtractionTarget)

/-! ### Grammatical positions on the Accessibility Hierarchy -/

/-- Grammatical positions on the [keenan-comrie-1977] Accessibility
    Hierarchy (AH).

    The hierarchy ranks grammatical relations by their accessibility to
    relativization. Higher positions are more accessible: more languages
    can relativize them, and simpler strategies (gap) suffice.

    Subject > DirectObject > IndirectObject > Oblique > Genitive > ObjComparison -/
inductive AHPosition where
  /-- Subject: the most accessible position. Virtually all languages
      with relative clauses can relativize subjects. -/
  | subject
  /-- Direct object: the second most accessible position. -/
  | directObject
  /-- Indirect object: third position. -/
  | indirectObject
  /-- Oblique: fourth position (instrumentals, locatives, etc.). -/
  | oblique
  /-- Genitive: fifth position (possessors). -/
  | genitive
  /-- Object of comparison: the least accessible position
      ("the person [that I am taller than _]"). -/
  | objComparison
  deriving DecidableEq, Repr, Fintype

/-- Numeric rank of a position on the Accessibility Hierarchy.
    Higher rank = more accessible = more languages can relativize it. -/
def AHPosition.rank : AHPosition → Nat
  | .subject        => 6
  | .directObject   => 5
  | .indirectObject => 4
  | .oblique        => 3
  | .genitive       => 2
  | .objComparison  => 1

/-- The accessibility order on `AHPosition` (the scale mixin): `p₁ ≤ p₂` iff
    `p₁` is no more accessible than `p₂`. Lets HC₂ continuity and the PRC be
    stated through mathlib's `Set.OrdConnected` / `IsUpperSet` rather than
    bespoke rank arithmetic. -/
instance : LinearOrder AHPosition :=
  LinearOrder.lift' AHPosition.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [AHPosition.rank])

/-- Position p1 is at least as accessible as p2 on the hierarchy. -/
def AHPosition.atLeastAsAccessible (p1 p2 : AHPosition) : Prop :=
  p1.rank ≥ p2.rank

instance (p1 p2 : AHPosition) : Decidable (p1.atLeastAsAccessible p2) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- Position p1 is strictly more accessible than p2. -/
def AHPosition.moreAccessible (p1 p2 : AHPosition) : Prop :=
  p1.rank > p2.rank

instance (p1 p2 : AHPosition) : Decidable (p1.moreAccessible p2) :=
  inferInstanceAs (Decidable (_ > _))

/-- All AH positions in descending order of accessibility. -/
def AHPosition.all : List AHPosition :=
  [.subject, .directObject, .indirectObject, .oblique, .genitive, .objComparison]

/-! ### Relative-clause position -/

/-- Position of the relative clause with respect to the head noun.

    Post-nominal is the dominant type cross-linguistically; pre-nominal
    correlates with OV word order; internally-headed and correlative
    (double-headed) types are rare but typologically significant. -/
inductive RCPosition where
  /-- Post-nominal: RC follows the head noun. E.g., English "the man
      [who left]", Arabic "ar-rajul [alladhi ghadara]". -/
  | postNominal
  /-- Pre-nominal: RC precedes the head noun. E.g., Japanese
      "[ _ kaetta] hito", Korean "[ _ tteonagan] saram". -/
  | preNominal
  /-- Internally-headed: the head noun appears inside the RC. E.g.,
      Bambara. -/
  | internallyHeaded
  /-- Correlative (double-headed): the head noun appears both inside
      and outside the RC. E.g., Hindi-Urdu "jo aadmii aayaa, vo
      aadmii meraa bhaaii hai". -/
  | correlative
  deriving DecidableEq, Repr

/-! ### NP_rel type (what occupies the relativized position) -/

/-- What occupies the relativized position (NP_rel) inside the RC.

    This is the core of [keenan-comrie-1977]'s ±case distinction:
    -case strategies delete NP_rel (gap), while +case strategies retain
    a pronominal element that bears case marking. -/
inductive NPRelType where
  /-- Gap: NP_rel is deleted; no overt element at the extraction site.
      The "lightest" strategy. E.g., English "the man [that _ left]". -/
  | gap
  /-- Resumptive pronoun: NP_rel is a personal pronoun (usually
      bearing case). E.g., Arabic "al-madina [illi saafartu ila-ha]"
      'the-city [that I-traveled to-it]'. -/
  | resumptive
  /-- Movement resumptive: a lower copy of an Ā-movement chain that
      is partially pronounced rather than fully deleted. Featurally
      reduced relative to a bound resumptive (e.g., personless in
      Swahili). Diagnosed by parasitic gap constructions.
      [scott-2021] -/
  | resumptiveMovement
  /-- Bound resumptive: a base-generated pronoun syntactically bound
      by the head of the relative clause. Not a movement copy — immune
      to chain reduction. Retains full person features. Diagnosed by
      obligatory presence inside adjunct islands.
      [scott-2021] -/
  | resumptiveBound
  /-- Relative pronoun: NP_rel is a dedicated relative pronoun that
      typically fronts to clause-initial position and bears case.
      E.g., English "the man [who left]", German "der Mann [der ging]". -/
  | relPronoun
  /-- Non-reduction: NP_rel is a full NP — the head noun is repeated
      inside the RC. E.g., Bambara. -/
  | nonReduction
  deriving DecidableEq, Repr

/-- The movement/base-generation status of a resumptive pronoun, for
    languages where the two coexist morphologically ([scott-2021] for
    Swahili, [sichel-2014] for Hebrew). -/
inductive ResumptiveKind where
  /-- A partially-pronounced lower copy of an Ā-movement chain. -/
  | movementCopy
  /-- A base-generated pronoun bound by the relative-clause head. -/
  | bound
  /-- A resumptive whose movement-vs-base-generation status is unspecified
      (pre-[scott-2021] typology). -/
  | unspecified
  deriving DecidableEq, Repr

/-- The resumptive kind of an `NPRelType`, or `none` for non-resumptive
    types. Refines the movement-vs-bound contrast; unlike a tri-state
    `Option Bool`, it keeps "unspecified resumptive" and "not a resumptive"
    as genuinely distinct outcomes. -/
def NPRelType.resumptiveKind : NPRelType → Option ResumptiveKind
  | .resumptiveMovement => some .movementCopy
  | .resumptiveBound    => some .bound
  | .resumptive         => some .unspecified
  | _                   => none

/-! ### Realization -/

/-- What a single relative-clause derivation *realizes*, stated
    framework-neutrally: the relativized [keenan-comrie-1977] AH position
    and the NP_rel type occupying it.

    This is the hook by which a syntactic framework's derivation connects to the
    shared relativization substrate: HPSG's GAP/MOD derivation, Minimalism's
    trace + predicate-abstraction, etc. each *project* to a `Realization`, even
    though their derivation mechanisms are framework-specific and not unified.
    Distinct from the per-language WALS `Profile` (a typological survey of a
    language's strategies); a `Realization` describes one derivation. -/
structure Realization where
  /-- The relativized position on the Accessibility Hierarchy. -/
  position : AHPosition
  /-- What occupies the relativized position (gap, resumptive, …). -/
  npRel : NPRelType
  deriving DecidableEq, Repr

/-! ### Relative-clause marker -/

/-- A relative clause marker or construction in a language.

    Each marker introduces one type of relative clause with specific
    distributional properties. Fragments encode the actual linguistic
    objects — particles, pronouns, verbal suffixes — rather than
    typological strategy labels. The strategy classification is derived
    from marker properties in study files.

    Examples:
    - Welsh particle *a* (gap, -case, covers SU/DO)
    - Finnish relative pronoun *joka* (+case, covers SU–GEN)
    - Korean adnominal suffix *-(n)ɨn* (gap, -case, covers SU–OBL) -/
structure Marker where
  /-- Surface form of the marker (e.g., "a", "joka", "that/∅", "-(n)ɨn"). -/
  form : String
  /-- What occupies the relativized position in this construction. -/
  npRel : NPRelType
  /-- Whether the relative element bears case marking (±case). -/
  bearsCaseMarking : Bool
  /-- Position of the RC with respect to the head noun. -/
  rcPosition : RCPosition
  /-- Which grammatical positions can be relativized using this marker. -/
  positions : List AHPosition
  /-- Which head-NP definiteness context attests the marker (purely
      descriptive). Reuses `Features.Definiteness.Definiteness` rather
      than introducing a parallel enum. `none` if the language doesn't
      make a comparable definiteness contrast on relative-clause markers
      (the typical case) or if the data hasn't been encoded. Languages
      whose RC marker is attested in BOTH definite- and indefinite-headed
      contexts split into separate marker entries (one per context),
      so the field stays single-valued.

      The descriptive distinction is the one Arabic grammars draw
      (Wright 1896; Cantarino 1974; [ryding-2005]): MSA *alladhī*
      with definite antecedents vs Ø-relative-pronoun with indefinite
      antecedents. Substrate makes no claim about syntactic mechanism. -/
  headDefiniteness : Option Features.Definiteness.Definiteness := none
  /-- Additional notes. -/
  notes : String := ""
  deriving BEq, Repr

/-- Does this marker cover a given AH position? -/
def Marker.Covers (m : Marker) (p : AHPosition) : Prop :=
  p ∈ m.positions

instance (m : Marker) (p : AHPosition) : Decidable (m.Covers p) :=
  inferInstanceAs (Decidable (p ∈ m.positions))

/-! ### Accessibility-Hierarchy contiguity (HC₂) -/

/-- Whether a list of AH positions contains at least one position at rank r. -/
def hasAHRank (positions : List AHPosition) (r : Nat) : Bool :=
  positions.any fun p => p.rank == r

/-- A set of AH positions forms a contiguous segment on the hierarchy:
    for every pair of positions in the set, every intermediate rank
    is also represented.

    Mirrors `Core.validInventory` for the case hierarchy ([blake-1994]).

    This formalizes HC₂ of [keenan-comrie-1977]: "Any RC-forming
    strategy must apply to a continuous segment of the AH." -/
def contiguousOnAH (positions : List AHPosition) : Bool :=
  positions.all fun p1 =>
    positions.all fun p2 =>
      if p2.rank > p1.rank then
        let lo := p1.rank
        let hi := p2.rank
        List.range hi |>.all fun r =>
          if r > lo && r < hi then hasAHRank positions r
          else true
      else true

/-- Prop wrapper around `contiguousOnAH`. The `Bool`-shaped definition
    is structural and load-bearing for the PRC general-proof case-analysis
    in `Studies/KeenanComrie1977.lean`; this Prop version is the canonical
    user-facing predicate. -/
def ContiguousOnAH (positions : List AHPosition) : Prop :=
  contiguousOnAH positions = true

instance (positions : List AHPosition) : Decidable (ContiguousOnAH positions) :=
  inferInstanceAs (Decidable (_ = _))

/-- A marker's positions form a contiguous segment of the AH. -/
def Marker.IsContinuous (m : Marker) : Prop :=
  ContiguousOnAH m.positions

instance (m : Marker) : Decidable m.IsContinuous :=
  inferInstanceAs (Decidable (ContiguousOnAH _))

/-- A marker is **primary** in [keenan-comrie-1977]'s sense if it can be
    used to relativize subjects. HC₁ requires every language to have at
    least one primary marker. -/
def Marker.IsPrimary (m : Marker) : Prop :=
  m.Covers .subject

instance (m : Marker) : Decidable m.IsPrimary :=
  inferInstanceAs (Decidable (m.Covers .subject))

/-! ### Ordering theorems -/

/-- The hierarchy rank is injective — no two positions share a rank.
    Combined with the natural order on ℕ, this makes the AH a total order. -/
theorem ah_rank_injective (a b : AHPosition) (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> simp_all [AHPosition.rank]

/-- All ranks are between 1 and 6. -/
theorem ah_rank_bounded (p : AHPosition) : 1 ≤ p.rank ∧ p.rank ≤ 6 := by
  cases p <;> simp [AHPosition.rank]

/-- Accessibility is reflexive (follows from `≥` on ℕ). -/
theorem ah_reflexive (p : AHPosition) : p.atLeastAsAccessible p := by
  simp [AHPosition.atLeastAsAccessible]

/-- Accessibility is transitive (follows from `≥` on ℕ). -/
theorem ah_transitive (a b c : AHPosition)
    (h1 : a.atLeastAsAccessible b) (h2 : b.atLeastAsAccessible c) :
    a.atLeastAsAccessible c := by
  simp [AHPosition.atLeastAsAccessible] at *; omega

/-! ### Extraction bridge

Maps between `Extraction.ExtractionTarget` (5 structural positions from
extraction morphology, in `Typology/Extraction.lean`) and `AHPosition` (6
positions on the [keenan-comrie-1977] Accessibility Hierarchy). Both
encode overlapping Ā-movement phenomena: extraction focuses on *where*
extraction occurs (Mayan, Austronesian, Celtic Fragments); the AH focuses on
*what can be relativized*. The bridge is partial: `AHPosition.objComparison`
has no standard `ExtractionTarget` equivalent; `ExtractionTarget.possessor`
maps to `AHPosition.genitive`. -/

/-- Map an extraction target to its AH position. Possessor extraction
    corresponds to the genitive position on the AH. -/
def extractionTargetToAH : ExtractionTarget → AHPosition
  | .subject        => .subject
  | .directObject   => .directObject
  | .indirectObject => .indirectObject
  | .oblique        => .oblique
  | .possessor      => .genitive

/-- Map an AH position to an extraction target (partial:
    `objComparison` has no standard `ExtractionTarget` equivalent). -/
def ahToExtractionTarget : AHPosition → Option ExtractionTarget
  | .subject        => some .subject
  | .directObject   => some .directObject
  | .indirectObject => some .indirectObject
  | .oblique        => some .oblique
  | .genitive       => some .possessor
  | .objComparison  => none

/-- ExtractionTarget → AH → ExtractionTarget is the identity. -/
theorem extraction_ah_roundtrip (t : ExtractionTarget) :
    ahToExtractionTarget (extractionTargetToAH t) = some t := by
  cases t <;> rfl

/-- AH → ExtractionTarget → AH is the identity for every position
    except `objComparison` (which has no `ExtractionTarget`). -/
theorem ah_extraction_roundtrip (p : AHPosition) (h : p ≠ .objComparison) :
    ∃ t, ahToExtractionTarget p = some t ∧ extractionTargetToAH t = p := by
  cases p with
  | objComparison => exact absurd rfl h
  | subject => exact ⟨.subject, rfl, rfl⟩
  | directObject => exact ⟨.directObject, rfl, rfl⟩
  | indirectObject => exact ⟨.indirectObject, rfl, rfl⟩
  | oblique => exact ⟨.oblique, rfl, rfl⟩
  | genitive => exact ⟨.possessor, rfl, rfl⟩

/-- `objComparison` is the only AH position without an `ExtractionTarget`. -/
theorem objComparison_no_extraction_target :
    ahToExtractionTarget .objComparison = none := rfl

/-- Every non-`objComparison` AH position has an `ExtractionTarget` equivalent. -/
theorem non_ocomp_have_extraction_target (p : AHPosition) (h : p ≠ .objComparison) :
    (ahToExtractionTarget p).isSome := by
  cases p <;> first | rfl | exact absurd rfl h

end RelativeClause
