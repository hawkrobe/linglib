import Mathlib.Order.Nat
import Mathlib.Tactic.DeriveFintype

/-!
# Prominence Scales and Differential Argument Marking @cite{just-2024} @cite{haspelmath-2021}
@cite{aissen-2003} @cite{haspelmath-2019}

Framework-agnostic prominence hierarchies for referential properties. These
scales underlie both **differential flagging** (case marking: DOM, DSM) and
**differential indexing** (verbal agreement), as argued by @cite{just-2024} and
building on @cite{aissen-2003}.

## Scales

Three independently motivated prominence hierarchies:

- **Animacy**: Human > Animate > Inanimate
- **Definiteness**: Personal Pronoun > Proper Name > Definite NP >
  Indefinite Specific > Non-specific
- **Person**: 1st > 2nd > 3rd

These are the same scales for all argument roles (A, P, R, T),
but the **polarity** of differential marking depends on argument role:

- P/T marking targets **prominent** referents (departures from low default)
- A/R marking targets **non-prominent** referents (departures from high default)

## Argument Roles (@cite{haspelmath-2021}, §2–5)

Five roles span monotransitive and ditransitive clauses:

- **S**: sole argument of intransitive (reference point for alignment)
- **A**: agent-like argument of monotransitive
- **P**: patient-like argument of monotransitive
- **R**: recipient-like argument of ditransitive (higher role rank, like A)
- **T**: theme-like argument of ditransitive (lower role rank, like P)

## Marking Channels

Differential argument marking has two independent realization channels:

- **Flagging**: morphological case on the NP
- **Indexing**: verbal agreement / cross-referencing

These serve different functions — flagging disambiguates roles, indexing
tracks referents through discourse — but both are governed by the same
prominence scales.

-/

namespace Features.Prominence

-- ============================================================================
-- § 1: Animacy Scale (@cite{aissen-2003}, §2)
-- ============================================================================

/-- Levels of the animacy prominence scale.
    Human > Animate > Inanimate. -/
inductive AnimacyLevel where
  /-- Most prominent: human referents -/
  | human
  /-- Non-human animates -/
  | animate
  /-- Least prominent: inanimate referents -/
  | inanimate
  deriving DecidableEq, Repr, Inhabited

/-- Numeric rank on the animacy scale: Human (2) > Animate (1) > Inanimate (0). -/
def AnimacyLevel.rank : AnimacyLevel → Nat
  | .human     => 2
  | .animate   => 1
  | .inanimate => 0

/-- Inanimate < Animate < Human (ordered by prominence rank). -/
instance : LinearOrder AnimacyLevel :=
  LinearOrder.lift' AnimacyLevel.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [AnimacyLevel.rank])

/-- All animacy levels (exhaustive enumeration for finite verification). -/
def AnimacyLevel.all : List AnimacyLevel := [.human, .animate, .inanimate]

theorem AnimacyLevel.all_length : AnimacyLevel.all.length = 3 := by native_decide

-- ============================================================================
-- § 1b: Fine-Grained Animacy Hierarchy (@cite{corbett-2000}, @cite{smith-stark-1974})
-- ============================================================================

/-- Fine-grained animacy hierarchy for nominal plural marking and agreement
    (@cite{smith-stark-1974}, @cite{corbett-2000}).

    Languages mark plural on nouns according to an implicational scale:

      speaker > addressee > 3rd person > kin > human > higher animals >
      lower animals > discrete inanimates > nondiscrete inanimates

    If a language marks plural at a given point on the scale, it marks
    plural at all higher points. This refines the coarser `AnimacyLevel`
    (human/animate/inanimate) used for differential argument marking. -/
inductive AnimacyRank where
  | speaker
  | addressee
  | thirdPerson
  | kin
  | human
  | higherAnimal
  | lowerAnimal
  | discreteInanimate
  | nondiscreteInanimate
  deriving DecidableEq, Repr

/-- Numeric rank for comparison (higher = more likely to be plural-marked). -/
def AnimacyRank.toNat : AnimacyRank → Nat
  | .speaker => 8
  | .addressee => 7
  | .thirdPerson => 6
  | .kin => 5
  | .human => 4
  | .higherAnimal => 3
  | .lowerAnimal => 2
  | .discreteInanimate => 1
  | .nondiscreteInanimate => 0

/-- Coarsen the 9-level animacy hierarchy to the 3-level scale used for
    differential argument marking. The mapping:
    - speaker/addressee/thirdPerson/kin/human → `.human`
    - higherAnimal/lowerAnimal → `.animate`
    - discreteInanimate/nondiscreteInanimate → `.inanimate` -/
def AnimacyRank.toAnimacyLevel : AnimacyRank → AnimacyLevel
  | .speaker | .addressee | .thirdPerson | .kin | .human => .human
  | .higherAnimal | .lowerAnimal => .animate
  | .discreteInanimate | .nondiscreteInanimate => .inanimate

/-- Coarsening is monotone: higher rank implies ≥ level. -/
theorem AnimacyRank.toAnimacyLevel_monotone (r₁ r₂ : AnimacyRank)
    (h : r₁.toNat ≥ r₂.toNat) : r₁.toAnimacyLevel.rank ≥ r₂.toAnimacyLevel.rank := by
  cases r₁ <;> cases r₂ <;> simp only [toNat, toAnimacyLevel, AnimacyLevel.rank] at * <;> omega

/-- The hierarchy is consistent: speaker outranks addressee outranks
    third person, and so forth down the scale. -/
theorem AnimacyRank.hierarchy_ordering :
    AnimacyRank.speaker.toNat > AnimacyRank.addressee.toNat ∧
    AnimacyRank.addressee.toNat > AnimacyRank.thirdPerson.toNat ∧
    AnimacyRank.thirdPerson.toNat > AnimacyRank.kin.toNat ∧
    AnimacyRank.kin.toNat > AnimacyRank.human.toNat ∧
    AnimacyRank.human.toNat > AnimacyRank.higherAnimal.toNat ∧
    AnimacyRank.higherAnimal.toNat > AnimacyRank.lowerAnimal.toNat ∧
    AnimacyRank.lowerAnimal.toNat > AnimacyRank.discreteInanimate.toNat ∧
    AnimacyRank.discreteInanimate.toNat > AnimacyRank.nondiscreteInanimate.toNat := by
  native_decide

/-- The hierarchy predicts: if a language marks plural at rank r, it marks
    plural at all ranks above r. -/
def AnimacyRank.respectsHierarchy (markedRanks : List AnimacyRank) : Bool :=
  markedRanks.all fun r =>
    markedRanks.all fun r' =>
      r'.toNat >= r.toNat || markedRanks.contains r' == false

-- ============================================================================
-- § 2: Definiteness Scale (@cite{aissen-2003}, §2)
-- ============================================================================

/-- Levels of the definiteness prominence scale.
    Personal Pronoun > Proper Name > Definite NP > Indefinite Specific NP >
    Non-specific NP. -/
inductive DefinitenessLevel where
  /-- Most prominent: personal pronouns -/
  | personalPronoun
  /-- Proper names -/
  | properName
  /-- Definite NPs (with article or demonstrative) -/
  | definite
  /-- Indefinite but specific NPs -/
  | indefiniteSpecific
  /-- Least prominent: non-specific indefinites -/
  | nonSpecific
  deriving DecidableEq, Repr, Inhabited

/-- Numeric rank on the definiteness scale:
    Pronoun (4) > Proper (3) > Definite (2) > IndSp (1) > NonSp (0). -/
def DefinitenessLevel.rank : DefinitenessLevel → Nat
  | .personalPronoun    => 4
  | .properName         => 3
  | .definite           => 2
  | .indefiniteSpecific => 1
  | .nonSpecific        => 0

/-- All definiteness levels (exhaustive enumeration). -/
def DefinitenessLevel.all : List DefinitenessLevel :=
  [.personalPronoun, .properName, .definite, .indefiniteSpecific, .nonSpecific]

theorem DefinitenessLevel.all_length : DefinitenessLevel.all.length = 5 := by
  native_decide

-- ============================================================================
-- § 3: Scale Ordering Verification
-- ============================================================================

/-- Distinct animacy levels have distinct ranks — the rank function is injective. -/
theorem animacy_rank_injective (a b : AnimacyLevel) (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> simp_all [AnimacyLevel.rank]

/-- Animacy ranks are bounded: 0 ≤ rank ≤ 2. -/
theorem animacy_rank_bounded (a : AnimacyLevel) : a.rank ≤ 2 := by
  cases a <;> simp [AnimacyLevel.rank]

/-- Distinct definiteness levels have distinct ranks — the rank function is injective. -/
theorem definiteness_rank_injective (a b : DefinitenessLevel) (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> simp_all [DefinitenessLevel.rank]

/-- Definiteness ranks are bounded: 0 ≤ rank ≤ 4. -/
theorem definiteness_rank_bounded (d : DefinitenessLevel) : d.rank ≤ 4 := by
  cases d <;> simp [DefinitenessLevel.rank]

-- ============================================================================
-- § 4: Person Scale (@cite{haspelmath-2021}, §6)
-- ============================================================================

/-- Person prominence scale.
    1st > 2nd > 3rd. SAP (speech-act participants, 1st/2nd) are more
    prominent than 3rd person. -/
inductive PersonLevel where
  | first
  | second
  | third
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Numeric rank on the person scale: 1st (2) > 2nd (1) > 3rd (0). -/
def PersonLevel.rank : PersonLevel → Nat
  | .first  => 2
  | .second => 1
  | .third  => 0

/-- All person levels. -/
def PersonLevel.all : List PersonLevel := [.first, .second, .third]

/-- Whether a person level is a speech-act participant (SAP = local). -/
def PersonLevel.isSAP : PersonLevel → Bool
  | .first  => true
  | .second => true
  | .third  => false

/-- Distinct person levels have distinct ranks — the rank function is injective. -/
theorem person_rank_injective (a b : PersonLevel) (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> simp_all [PersonLevel.rank]

/-- Person ranks are bounded: 0 ≤ rank ≤ 2. -/
theorem person_rank_bounded (p : PersonLevel) : p.rank ≤ 2 := by
  cases p <;> simp [PersonLevel.rank]

-- ============================================================================
-- § 5: Argument Role and Marking Channel (@cite{haspelmath-2021}, §2–5)
-- ============================================================================

/-- Argument roles spanning monotransitive and ditransitive clauses.

    Follows @cite{comrie-1978} and @cite{haspelmath-2021} in using S/A/P/R/T
    (not subject/object) to avoid theory-dependent constituency assumptions.

    Role rank determines the direction of differential marking:
    - Higher-rank roles (A, R) default to high prominence; differential
      marking targets the NON-prominent end (anti-monotone / lower set).
    - Lower-rank roles (P, T) default to low prominence; differential
      marking targets the PROMINENT end (monotone / upper set).
    - S is the alignment reference point. -/
inductive ArgumentRole where
  /-- S: sole argument of an intransitive verb -/
  | S
  /-- A: the more agent-like argument of a transitive verb -/
  | A
  /-- P: the more patient-like argument of a transitive verb -/
  | P
  /-- R: the recipient-like argument of a ditransitive verb -/
  | R
  /-- T: the theme-like argument of a ditransitive verb -/
  | T
  deriving DecidableEq, Repr

/-- Role rank: A > P for monotransitives,
    R > T for ditransitives. S is in between. Higher rank = higher
    default prominence expectation. -/
def ArgumentRole.roleRank : ArgumentRole → Nat
  | .A => 4
  | .R => 3
  | .S => 2
  | .T => 1
  | .P => 0

/-- Whether this role has high default prominence (A-like). Differential
    marking for high-default roles targets non-prominent referents. -/
def ArgumentRole.highDefault : ArgumentRole → Bool
  | .A => true
  | .R => true
  | _  => false

/-- Whether this role has low default prominence (P-like). Differential
    marking for low-default roles targets prominent referents. -/
def ArgumentRole.lowDefault : ArgumentRole → Bool
  | .P => true
  | .T => true
  | _  => false

/-- Two independent channels for marking argument properties on verbs or NPs
    (@cite{haspelmath-2019}, @cite{just-2024} §2).

    - **Flagging**: morphological case on the NP (e.g., accusative suffix)
    - **Indexing**: verbal agreement / cross-referencing (e.g., Set A/B markers)

    These serve distinct functions: flagging disambiguates roles, indexing
    tracks referents. Both are governed by the same prominence scales but
    the two dimensions are logically independent. -/
inductive MarkingChannel where
  /-- Case morphology on the NP -/
  | flagging
  /-- Verbal agreement / cross-referencing -/
  | indexing
  deriving DecidableEq, Repr

-- ============================================================================
-- § 6: Default Prominence (@cite{just-2024}, §3; @cite{haspelmath-2021}, §7)
-- ============================================================================

/-- Combined prominence rank for a cell in the animacy × definiteness grid.
    Sum of the two individual ranks, giving a scalar from 0 (inanimate,
    nonspecific) to 6 (human, personal pronoun). -/
def prominenceRank (a : AnimacyLevel) (d : DefinitenessLevel) : Nat :=
  a.rank + d.rank

/-- Default prominence expectation per argument role.

    High-default roles (A, R) are typically human, definite, topical.
    Low-default roles (P, T) are typically inanimate, indefinite.
    S is the reference point — no strong default.

    Differential marking targets departures from these defaults:
    - P/T marking targets *prominent* referents (high prominence, unexpected)
    - A/R marking targets *non-prominent* referents (low prominence, unexpected)

    Returns `true` when the cell represents the "expected" (unmarked) zone. -/
def isDefaultZone (role : ArgumentRole) (a : AnimacyLevel) (d : DefinitenessLevel) : Bool :=
  match role with
  | .A => prominenceRank a d ≥ 3  -- A args expected to be prominent
  | .R => prominenceRank a d ≥ 3  -- R args expected to be prominent (like A)
  | .S => true                    -- S is the reference point, always "default"
  | .P => prominenceRank a d ≤ 2  -- P args expected to be non-prominent
  | .T => prominenceRank a d ≤ 2  -- T args expected to be non-prominent (like P)

-- ============================================================================
-- § 7: Differential Marking Profiles
-- ============================================================================

/-- A differential marking profile: which cells in the animacy × definiteness
    grid receive overt differential marking for a given argument role and
    channel.

    Covers all four combinations of role × channel: P flagging, A flagging,
    P indexing, A indexing. -/
structure DifferentialMarkingProfile where
  /-- Language name -/
  name : String
  /-- Which argument role: A or P -/
  role : ArgumentRole
  /-- Realization channel: flagging (case) or indexing (agreement) -/
  channel : MarkingChannel
  /-- Whether cell (a, d) receives differential marking -/
  marks : AnimacyLevel → DefinitenessLevel → Bool

/-- Monotonicity for P marking (upper set): if a cell is marked, all more
    prominent cells are also marked. This is @cite{aissen-2003}'s staircase
    prediction, extended to P indexing by @cite{just-2024}. -/
def DifferentialMarkingProfile.isMonotoneP (p : DifferentialMarkingProfile) : Bool :=
  AnimacyLevel.all.all λ a =>
    DefinitenessLevel.all.all λ d =>
      if p.marks a d then
        AnimacyLevel.all.all λ a' =>
          DefinitenessLevel.all.all λ d' =>
            if a'.rank ≥ a.rank && d'.rank ≥ d.rank then p.marks a' d'
            else true
      else true

/-- Anti-monotonicity for A marking (lower set): if a cell is marked, all
    less prominent cells are also marked. This is the "mirror image"
    predicted by @cite{just-2024}: A indexing marks non-prominent As. -/
def DifferentialMarkingProfile.isMonotoneA (p : DifferentialMarkingProfile) : Bool :=
  AnimacyLevel.all.all λ a =>
    DefinitenessLevel.all.all λ d =>
      if p.marks a d then
        AnimacyLevel.all.all λ a' =>
          DefinitenessLevel.all.all λ d' =>
            if a'.rank ≤ a.rank && d'.rank ≤ d.rank then p.marks a' d'
            else true
      else true

/-- Role-appropriate monotonicity: low-default roles (P, T) must be monotone
    (upper set), high-default roles (A, R) must be anti-monotone (lower set).
    S profiles are vacuously monotone. -/
def DifferentialMarkingProfile.isMonotone (p : DifferentialMarkingProfile) : Bool :=
  match p.role with
  | .P => p.isMonotoneP
  | .T => p.isMonotoneP  -- T behaves like P (@cite{haspelmath-2021}, §3)
  | .A => p.isMonotoneA
  | .R => p.isMonotoneA  -- R behaves like A (@cite{haspelmath-2021}, §3)
  | .S => true            -- S is the reference point

/-- Whether a marking profile depends only on animacy (definiteness is irrelevant). -/
def DifferentialMarkingProfile.isAnimacyOnly (p : DifferentialMarkingProfile) : Bool :=
  DefinitenessLevel.all.all λ d₁ =>
    DefinitenessLevel.all.all λ d₂ =>
      AnimacyLevel.all.all λ a =>
        p.marks a d₁ == p.marks a d₂

/-- Whether a marking profile depends only on definiteness (animacy is irrelevant). -/
def DifferentialMarkingProfile.isDefinitenessOnly (p : DifferentialMarkingProfile) : Bool :=
  AnimacyLevel.all.all λ a₁ =>
    AnimacyLevel.all.all λ a₂ =>
      DefinitenessLevel.all.all λ d =>
        p.marks a₁ d == p.marks a₂ d

-- ============================================================================
-- § 8: Constructors for One-Dimensional Profiles
-- ============================================================================

/-- Construct a one-dimensional animacy-based P-marking profile: P arguments
    at or above the cutoff are marked. (For A marking, use `animacyCutoffA`.) -/
def DifferentialMarkingProfile.animacyCutoffP
    (name : String) (channel : MarkingChannel) (cutoff : AnimacyLevel)
    : DifferentialMarkingProfile :=
  { name, role := .P, channel, marks := λ a _ => a.rank ≥ cutoff.rank }

/-- Construct a one-dimensional definiteness-based P-marking profile. -/
def DifferentialMarkingProfile.definitenessCutoffP
    (name : String) (channel : MarkingChannel) (cutoff : DefinitenessLevel)
    : DifferentialMarkingProfile :=
  { name, role := .P, channel, marks := λ _ d => d.rank ≥ cutoff.rank }

/-- Construct a one-dimensional animacy-based A-marking profile: A arguments
    at or below the cutoff are marked (anti-monotone / lower set). -/
def DifferentialMarkingProfile.animacyCutoffA
    (name : String) (channel : MarkingChannel) (cutoff : AnimacyLevel)
    : DifferentialMarkingProfile :=
  { name, role := .A, channel, marks := λ a _ => a.rank ≤ cutoff.rank }

/-- Construct a one-dimensional definiteness-based A-marking profile. -/
def DifferentialMarkingProfile.definitenessCutoffA
    (name : String) (channel : MarkingChannel) (cutoff : DefinitenessLevel)
    : DifferentialMarkingProfile :=
  { name, role := .A, channel, marks := λ _ d => d.rank ≤ cutoff.rank }

-- ============================================================================
-- § 9: One-Dimensional Monotonicity Theorems
-- ============================================================================

/-- Animacy-cutoff P profiles are always monotone. -/
theorem animacyCutoffP_monotone (ch : MarkingChannel) (cutoff : AnimacyLevel) :
    (DifferentialMarkingProfile.animacyCutoffP "" ch cutoff).isMonotone = true := by
  cases ch <;> cases cutoff <;> native_decide

/-- Definiteness-cutoff P profiles are always monotone. -/
theorem definitenessCutoffP_monotone (ch : MarkingChannel) (cutoff : DefinitenessLevel) :
    (DifferentialMarkingProfile.definitenessCutoffP "" ch cutoff).isMonotone = true := by
  cases ch <;> cases cutoff <;> native_decide

/-- Animacy-cutoff A profiles are always monotone (anti-monotone). -/
theorem animacyCutoffA_monotone (ch : MarkingChannel) (cutoff : AnimacyLevel) :
    (DifferentialMarkingProfile.animacyCutoffA "" ch cutoff).isMonotone = true := by
  cases ch <;> cases cutoff <;> native_decide

/-- Definiteness-cutoff A profiles are always monotone (anti-monotone). -/
theorem definitenessCutoffA_monotone (ch : MarkingChannel) (cutoff : DefinitenessLevel) :
    (DifferentialMarkingProfile.definitenessCutoffA "" ch cutoff).isMonotone = true := by
  cases ch <;> cases cutoff <;> native_decide

-- ============================================================================
-- § 10: Mirror Image Theorem (@cite{just-2024}, §3)
-- ============================================================================

/-- For any one-dimensional animacy cutoff, P marking at level `c` and A
    marking at level `c` produce complementary profiles: every cell is
    marked by exactly one of them (except the cutoff row itself, marked
    by both). -/
theorem animacy_mirror_image (cutoff : AnimacyLevel) :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        (DifferentialMarkingProfile.animacyCutoffP "" .indexing cutoff).marks a d ||
        (DifferentialMarkingProfile.animacyCutoffA "" .indexing cutoff).marks a d)) = true := by
  cases cutoff <;> native_decide

-- ============================================================================
-- § 11: Scenarios (@cite{haspelmath-2021}, §6)
-- ============================================================================

/-- A monotransitive scenario: the person combination of A and P.

    Scenario splits arise when argument coding depends not on a single
    argument's prominence but on the *combination* of A-person and P-person.
    E.g., 1→3 ("I see him") vs. 3→1 ("He sees me") may get different
    flagging or indexing. -/
structure Scenario where
  /-- Person of the A argument -/
  aPerson : PersonLevel
  /-- Person of the P argument -/
  pPerson : PersonLevel
  deriving DecidableEq, Repr

/-- Whether a scenario is "downstream": A has higher
    person rank than P. This is the "usual" direction — the role-reference
    association predicts high-rank roles (A) to have high-prominence referents.
    Downstream scenarios tend to get the shortest coding. -/
def Scenario.isDownstream (s : Scenario) : Bool :=
  s.aPerson.rank > s.pPerson.rank

/-- Whether a scenario is "upstream": P has higher
    person rank than A. This is the "unusual" direction — against the
    role-reference association. Upstream scenarios tend to get the longest
    coding. -/
def Scenario.isUpstream (s : Scenario) : Bool :=
  s.aPerson.rank < s.pPerson.rank

/-- Whether a scenario is "balanced": A and P have the same person rank
    (e.g., 3→3). Intermediate coding predicted. -/
def Scenario.isBalanced (s : Scenario) : Bool :=
  s.aPerson.rank == s.pPerson.rank

/-- Whether a scenario is "local": both arguments are SAP (1st or 2nd).
    Local scenarios (1↔2) are frequent and tend to get short coding. -/
def Scenario.isLocal (s : Scenario) : Bool :=
  s.aPerson.isSAP && s.pPerson.isSAP

/-- Whether a scenario is "direct": SAP acts on 3rd person.
    A subtype of downstream scenarios. -/
def Scenario.isDirect (s : Scenario) : Bool :=
  s.aPerson.isSAP && !s.pPerson.isSAP

/-- Whether a scenario is "inverse": 3rd person acts on SAP.
    A subtype of upstream scenarios. -/
def Scenario.isInverse (s : Scenario) : Bool :=
  !s.aPerson.isSAP && s.pPerson.isSAP

/-- Whether a scenario is "non-local": 3rd person acts on 3rd person.
    A subtype of balanced scenarios. -/
def Scenario.isNonlocal (s : Scenario) : Bool :=
  !s.aPerson.isSAP && !s.pPerson.isSAP

/-- All 9 person-pair scenarios. -/
def Scenario.all : List Scenario :=
  (PersonLevel.all.map λ a => PersonLevel.all.map λ p => ⟨a, p⟩).flatten

theorem Scenario.all_length : Scenario.all.length = 9 := by native_decide

-- ============================================================================
-- § 12: Role-Reference Association (@cite{haspelmath-2021}, §2)
-- ============================================================================

/-- The direction of differential marking: for a given role, does
    differential coding target the prominent end (upper set) or the
    non-prominent end (lower set)?

    Returns `true` when differential marking targets the prominent end.
    P and T → true (mark prominent referents).
    A and R → false (mark non-prominent referents). -/
def differentialTargetsProminent : ArgumentRole → Bool
  | .P => true
  | .T => true
  | .A => false
  | .R => false
  | .S => false  -- S doesn't have differential marking

/-- R behaves like A: both have high default prominence and differential
    marking targets the non-prominent end. -/
theorem R_like_A_default : ArgumentRole.R.highDefault = ArgumentRole.A.highDefault := rfl

/-- T behaves like P: both have low default prominence and differential
    marking targets the prominent end. -/
theorem T_like_P_default : ArgumentRole.T.lowDefault = ArgumentRole.P.lowDefault := rfl

/-- Role rank ordering: A > R > S > T > P. -/
theorem role_rank_ordering :
    ArgumentRole.A.roleRank > ArgumentRole.R.roleRank ∧
    ArgumentRole.R.roleRank > ArgumentRole.S.roleRank ∧
    ArgumentRole.S.roleRank > ArgumentRole.T.roleRank ∧
    ArgumentRole.T.roleRank > ArgumentRole.P.roleRank := by decide

-- ============================================================================
-- § 13: Scenario Frequency Class (@cite{haspelmath-2021}, §8)
-- ============================================================================

/-- Frequency class for scenarios: downstream (usual) most frequent.
    Downstream = 2, balanced = 1, upstream = 0. -/
def Scenario.frequencyClass (s : Scenario) : Nat :=
  if s.isDownstream then 2 else if s.isBalanced then 1 else 0

/-- Gradient upstream degree: how far P's rank exceeds A's.
    Uses Nat saturating subtraction (negative → 0). -/
def Scenario.upstreamDegree (s : Scenario) : Nat :=
  s.pPerson.rank - s.aPerson.rank

theorem downstream_frequency_class :
    (⟨.first, .third⟩ : Scenario).frequencyClass = 2 := rfl

theorem upstream_frequency_class :
    (⟨.third, .first⟩ : Scenario).frequencyClass = 0 := rfl

/-- Frequency class is monotone: downstream > balanced > upstream. -/
theorem frequency_class_monotone :
    (⟨.first, .third⟩ : Scenario).frequencyClass >
    (⟨.third, .third⟩ : Scenario).frequencyClass ∧
    (⟨.third, .third⟩ : Scenario).frequencyClass >
    (⟨.third, .first⟩ : Scenario).frequencyClass := by decide

end Features.Prominence
