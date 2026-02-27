/-!
# Prominence Scales and Differential Argument Marking @cite{just-2024} @cite{haspelmath-2021}

Framework-agnostic prominence hierarchies for referential properties. These
scales underlie both **differential flagging** (case marking: DOM, DSM) and
**differential indexing** (verbal agreement), as argued by Just (2024) and
building on Aissen (2003).

## Scales

Three independently motivated prominence hierarchies:

- **Animacy**: Human > Animate > Inanimate
- **Definiteness**: Personal Pronoun > Proper Name > Definite NP >
  Indefinite Specific > Non-specific
- **Person**: 1st > 2nd > 3rd (Haspelmath 2021, §6)

These are the same scales for all argument roles (A, P, R, T),
but the **polarity** of differential marking depends on argument role:

- P/T marking targets **prominent** referents (departures from low default)
- A/R marking targets **non-prominent** referents (departures from high default)

## Argument Roles (Haspelmath 2021, §2–5)

Five roles span monotransitive and ditransitive clauses:

- **S**: sole argument of intransitive (reference point for alignment)
- **A**: agent-like argument of monotransitive
- **P**: patient-like argument of monotransitive
- **R**: recipient-like argument of ditransitive (higher role rank, like A)
- **T**: theme-like argument of ditransitive (lower role rank, like P)

## Marking Channels (Just 2024, §2)

Differential argument marking has two independent realization channels:

- **Flagging**: morphological case on the NP (Aissen 2003)
- **Indexing**: verbal agreement / cross-referencing (Just 2024)

These serve different functions — flagging disambiguates roles, indexing
tracks referents through discourse — but both are governed by the same
prominence scales.

## References

- Haspelmath, M. (2021). Explaining argument-coding splits with
  role-reference associations. Linguistics 59(5): 1231–1270.
- Just, E. (2024). A structural and functional comparison of differential A
  and P indexing. Linguistics 62(2): 295–321.
- Aissen, J. (2003). Differential Object Marking: Iconicity vs. Economy.
  Natural Language & Linguistic Theory 21(3): 435–483.
- Haspelmath, M. (2019). Indexing and flagging, and the definition of
  "head". Open Linguistics 5: 539–557.
-/

namespace Core.Prominence

-- ============================================================================
-- § 1: Animacy Scale (Aissen 2003, §2)
-- ============================================================================

/-- Levels of the animacy prominence scale (Aissen 2003, §2).
    Human > Animate > Inanimate. -/
inductive AnimacyLevel where
  /-- Most prominent: human referents -/
  | human
  /-- Non-human animates -/
  | animate
  /-- Least prominent: inanimate referents -/
  | inanimate
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Numeric rank on the animacy scale: Human (2) > Animate (1) > Inanimate (0). -/
def AnimacyLevel.rank : AnimacyLevel → Nat
  | .human     => 2
  | .animate   => 1
  | .inanimate => 0

/-- All animacy levels (exhaustive enumeration for finite verification). -/
def AnimacyLevel.all : List AnimacyLevel := [.human, .animate, .inanimate]

theorem AnimacyLevel.all_length : AnimacyLevel.all.length = 3 := by native_decide

-- ============================================================================
-- § 2: Definiteness Scale (Aissen 2003, §2)
-- ============================================================================

/-- Levels of the definiteness prominence scale (Aissen 2003, §2).
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
  deriving DecidableEq, BEq, Repr, Inhabited

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

theorem animacy_human_gt_animate :
    AnimacyLevel.human.rank > AnimacyLevel.animate.rank := by decide

theorem animacy_animate_gt_inanimate :
    AnimacyLevel.animate.rank > AnimacyLevel.inanimate.rank := by decide

theorem definiteness_pronoun_gt_proper :
    DefinitenessLevel.personalPronoun.rank > DefinitenessLevel.properName.rank := by decide

theorem definiteness_proper_gt_definite :
    DefinitenessLevel.properName.rank > DefinitenessLevel.definite.rank := by decide

theorem definiteness_definite_gt_indSp :
    DefinitenessLevel.definite.rank > DefinitenessLevel.indefiniteSpecific.rank := by decide

theorem definiteness_indSp_gt_nonSp :
    DefinitenessLevel.indefiniteSpecific.rank > DefinitenessLevel.nonSpecific.rank := by decide

-- ============================================================================
-- § 4: Person Scale (Haspelmath 2021, §6)
-- ============================================================================

/-- Person prominence scale (Haspelmath 2021, §6; Silverstein 1976).
    1st > 2nd > 3rd. SAP (speech-act participants, 1st/2nd) are more
    prominent than 3rd person. -/
inductive PersonLevel where
  | first
  | second
  | third
  deriving DecidableEq, BEq, Repr, Inhabited

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

theorem person_first_gt_second :
    PersonLevel.first.rank > PersonLevel.second.rank := by decide

theorem person_second_gt_third :
    PersonLevel.second.rank > PersonLevel.third.rank := by decide

-- ============================================================================
-- § 5: Argument Role and Marking Channel (Haspelmath 2021, §2–5)
-- ============================================================================

/-- Argument roles spanning monotransitive and ditransitive clauses.

    Follows Comrie (1978) and Haspelmath (2021) in using S/A/P/R/T
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
  deriving DecidableEq, BEq, Repr

/-- Role rank (Haspelmath 2021, §7): A > P for monotransitives,
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
    (Haspelmath 2019, Just 2024 §2).

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
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 6: Default Prominence (Just 2024, §3; Haspelmath 2021, §7)
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
    prominent cells are also marked. This is Aissen's (2003) staircase
    prediction, extended to P indexing by Just (2024). -/
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
    predicted by Just (2024, §3): A indexing marks non-prominent As. -/
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
    S profiles are vacuously monotone (Haspelmath 2021, §7). -/
def DifferentialMarkingProfile.isMonotone (p : DifferentialMarkingProfile) : Bool :=
  match p.role with
  | .P => p.isMonotoneP
  | .T => p.isMonotoneP  -- T behaves like P (Haspelmath 2021, §3)
  | .A => p.isMonotoneA
  | .R => p.isMonotoneA  -- R behaves like A (Haspelmath 2021, §3)
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
-- § 10: Mirror Image Theorem (Just 2024, §3)
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
-- § 11: Scenarios (Haspelmath 2021, §6)
-- ============================================================================

/-- A monotransitive scenario: the person combination of A and P.

    Scenario splits arise when argument coding depends not on a single
    argument's prominence but on the *combination* of A-person and P-person.
    E.g., 1→3 ("I see him") vs. 3→1 ("He sees me") may get different
    flagging or indexing (Haspelmath 2021, §6). -/
structure Scenario where
  /-- Person of the A argument -/
  aPerson : PersonLevel
  /-- Person of the P argument -/
  pPerson : PersonLevel
  deriving DecidableEq, BEq, Repr

/-- Whether a scenario is "downstream" (Haspelmath 2021, §3): A has higher
    person rank than P. This is the "usual" direction — the role-reference
    association predicts high-rank roles (A) to have high-prominence referents.
    Downstream scenarios tend to get the shortest coding. -/
def Scenario.isDownstream (s : Scenario) : Bool :=
  s.aPerson.rank > s.pPerson.rank

/-- Whether a scenario is "upstream" (Haspelmath 2021, §3): P has higher
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
    Local scenarios (1↔2) are frequent and tend to get short coding
    (Haspelmath 2021, §6). -/
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
-- § 12: Role-Reference Association (Haspelmath 2021, §2)
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
-- § 13: Scenario Frequency Class (Haspelmath 2021, §8)
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

end Core.Prominence
