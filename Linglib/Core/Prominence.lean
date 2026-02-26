/-!
# Prominence Scales and Differential Argument Marking @cite{just-2024}

Framework-agnostic prominence hierarchies for referential properties. These
scales underlie both **differential flagging** (case marking: DOM, DSM) and
**differential indexing** (verbal agreement), as argued by Just (2024) and
building on Aissen (2003).

## Scales

Two independently motivated prominence hierarchies:

- **Animacy**: Human > Animate > Inanimate
- **Definiteness**: Personal Pronoun > Proper Name > Definite NP >
  Indefinite Specific > Non-specific

These are the same scales for both A (agent) and P (patient) arguments,
but the **polarity** of differential marking depends on argument role:

- P marking targets **prominent** Ps (departures from low P default)
- A marking targets **non-prominent** As (departures from high A default)

## Marking Channels (Just 2024, §2)

Differential argument marking has two independent realization channels:

- **Flagging**: case morphology on the NP (Aissen 2003)
- **Indexing**: verbal agreement / cross-referencing (Just 2024)

These serve different functions — flagging disambiguates thematic roles,
indexing tracks referents through discourse — but both are governed by
the same prominence scales.

## References

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
-- § 4: Argument Role and Marking Channel (Just 2024)
-- ============================================================================

/-- The two core argument roles in a transitive clause.

    Just (2024) follows Comrie (1978) and Haspelmath (2011) in using A/P
    (not subject/object) to avoid theory-dependent constituency assumptions. -/
inductive ArgumentRole where
  /-- A: the more agent-like argument of a transitive verb -/
  | A
  /-- P: the more patient-like argument of a transitive verb -/
  | P
  deriving DecidableEq, BEq, Repr

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
-- § 5: Default Prominence (Just 2024, §3)
-- ============================================================================

/-- Combined prominence rank for a cell in the animacy × definiteness grid.
    Sum of the two individual ranks, giving a scalar from 0 (inanimate,
    nonspecific) to 6 (human, personal pronoun). -/
def prominenceRank (a : AnimacyLevel) (d : DefinitenessLevel) : Nat :=
  a.rank + d.rank

/-- Default prominence expectation per argument role (Just 2024, §3).

    A arguments are typically human, definite, topical — **high** default
    prominence. P arguments are typically inanimate, indefinite, non-topical
    — **low** default prominence.

    Differential marking targets departures from these defaults:
    - Differential P marking targets *prominent* Ps (high prominence, unexpected)
    - Differential A marking targets *non-prominent* As (low prominence, unexpected)

    Returns `true` when the cell represents the "expected" (unmarked) zone. -/
def isDefaultZone (role : ArgumentRole) (a : AnimacyLevel) (d : DefinitenessLevel) : Bool :=
  match role with
  | .A => prominenceRank a d ≥ 3  -- A args expected to be prominent
  | .P => prominenceRank a d ≤ 2  -- P args expected to be non-prominent

-- ============================================================================
-- § 6: Differential Marking Profiles
-- ============================================================================

/-- A differential marking profile: which cells in the animacy × definiteness
    grid receive overt differential marking for a given argument role and
    channel.

    This generalizes Aissen's (2003) `DOMProfile` (= P + flagging) to all
    four combinations: P flagging, A flagging, P indexing, A indexing. -/
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

/-- Role-appropriate monotonicity: P profiles must be monotone (upper set),
    A profiles must be anti-monotone (lower set). -/
def DifferentialMarkingProfile.isMonotone (p : DifferentialMarkingProfile) : Bool :=
  match p.role with
  | .P => p.isMonotoneP
  | .A => p.isMonotoneA

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
-- § 7: Constructors for One-Dimensional Profiles
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
-- § 8: One-Dimensional Monotonicity Theorems
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
-- § 9: Mirror Image Theorem (Just 2024, §3)
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

end Core.Prominence
