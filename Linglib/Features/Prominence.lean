import Mathlib.Order.Nat
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Order.Markedness
import Linglib.Features.Person.Basic

/-!
# Prominence Scales and Differential Argument Marking [just-2024] [haspelmath-2021]
[aissen-2003] [haspelmath-2019]

Framework-agnostic prominence hierarchies for referential properties. These
scales underlie both **differential flagging** (case marking: DOM, DSM) and
**differential indexing** (verbal agreement), as argued by [just-2024] and
building on [aissen-2003].

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

## Argument Roles ([haspelmath-2021], §2–5)

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
-- § 1: Animacy Scale ([aissen-2003], §2)
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
  deriving DecidableEq, Repr, Inhabited, Fintype

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

theorem AnimacyLevel.all_length : AnimacyLevel.all.length = 3 := by decide

-- ============================================================================
-- § 1b: Fine-Grained Animacy Hierarchy ([corbett-2000], [smith-stark-1974])
-- ============================================================================

/-- Fine-grained animacy hierarchy for nominal plural marking and agreement
    ([smith-stark-1974], [corbett-2000]).

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
  decide

/-- The hierarchy predicts: if a language marks plural at rank r, it marks
    plural at all ranks above r. -/
def AnimacyRank.respectsHierarchy (markedRanks : List AnimacyRank) : Bool :=
  markedRanks.all fun r =>
    markedRanks.all fun r' =>
      r'.toNat >= r.toNat || markedRanks.contains r' == false

-- ============================================================================
-- § 2: Definiteness Scale ([aissen-2003], §2)
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
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Numeric rank on the definiteness scale:
    Pronoun (4) > Proper (3) > Definite (2) > IndSp (1) > NonSp (0). -/
def DefinitenessLevel.rank : DefinitenessLevel → Nat
  | .personalPronoun    => 4
  | .properName         => 3
  | .definite           => 2
  | .indefiniteSpecific => 1
  | .nonSpecific        => 0

/-- NonSpecific < IndefiniteSpecific < Definite < ProperName < PersonalPronoun
    (ordered by prominence rank). -/
instance : LinearOrder DefinitenessLevel :=
  LinearOrder.lift' DefinitenessLevel.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [DefinitenessLevel.rank])

/-- All definiteness levels (exhaustive enumeration). -/
def DefinitenessLevel.all : List DefinitenessLevel :=
  [.personalPronoun, .properName, .definite, .indefiniteSpecific, .nonSpecific]

theorem DefinitenessLevel.all_length : DefinitenessLevel.all.length = 5 := by
  decide

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
-- § 4: Person Scale ([haspelmath-2021], §6)
-- ============================================================================

/-- Numeric rank on the person prominence scale: 1st (2) > 2nd (1) >
    3rd (0) ([haspelmath-2021] §6). Stated over the canonical `Person`
    inventory (the dissolved `Person`'s role): clusivity-marked
    firsts rank with `first`; the impersonal `zero` is `[−participant]`
    and is placed with third person (a linglib convention — the scale's
    source does not discuss impersonals). -/
def _root_.Person.prominence : Person → Nat
  | .first | .firstInclusive | .firstExclusive => 2
  | .second => 1
  | .third | .zero => 0

/-- The three-way prominence scale carrier: the tripartition values. -/
abbrev personScaleLevels : List Person := Person.System.tripartition.values

/-- Prominence separates the tripartition: on `first`/`second`/`third`
    the rank function is injective. -/
theorem person_prominence_injective :
    ∀ a ∈ personScaleLevels, ∀ b ∈ personScaleLevels,
      a.prominence = b.prominence → a = b := by decide

/-- Person prominence ranks are bounded: 0 ≤ rank ≤ 2. -/
theorem person_prominence_bounded (p : Person) : p.prominence ≤ 2 := by
  cases p <;> simp [Person.prominence]

/-- Prominence tracks SAP-hood: rank ≥ 1 iff speech-act participant. -/
theorem prominence_pos_iff_sap (p : Person) :
    1 ≤ p.prominence ↔ p.IsSAP := by
  cases p <;> simp [Person.prominence, Person.IsSAP]

-- ============================================================================
-- § 5: Argument Role and Marking Channel ([haspelmath-2021], §2–5)
-- ============================================================================

/-- Argument roles spanning monotransitive and ditransitive clauses.

    Follows [comrie-1978] and [haspelmath-2021] in using S/A/P/R/T
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

/-- The monotransitive core roles: A, P, and S (omits the ditransitive
    scaffolding roles R/T). The domain over which alignment partitions
    and per-language case/agreement coverage theorems quantify. -/
def ArgumentRole.core : List ArgumentRole := [.A, .P, .S]

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
    ([haspelmath-2019], [just-2024] §2).

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
-- § 6: Default Prominence ([just-2024], §3; [haspelmath-2021], §7)
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
-- § 7: Differential marking patterns
-- ============================================================================

/-- A differential-marking pattern: which cells in the animacy × definiteness
    grid receive overt differential marking, for whatever argument role and
    channel a consumer pairs the pattern with ([aissen-2003] flagging,
    [just-2024] indexing). A `def`, not an `abbrev`, so the checkers below
    are dot-accessible. -/
def MarkingPattern := AnimacyLevel → DefinitenessLevel → Bool

namespace MarkingPattern

/-- Marking is closed under moving up both scales — the upper-set staircase
    of [aissen-2003]'s (33b), appropriate to P/T marking and extended to
    P indexing by [just-2024]. -/
def MonotoneP (p : MarkingPattern) : Prop :=
  ∀ a a' d d', a ≤ a' → d ≤ d' → p a d = true → p a' d' = true

/-- Marking closed downward — the mirror image appropriate to A/R marking
    ([just-2024]). -/
def MonotoneA (p : MarkingPattern) : Prop :=
  ∀ a a' d d', a' ≤ a → d' ≤ d → p a d = true → p a' d' = true

/-- The pattern depends only on animacy. -/
def AnimacyOnly (p : MarkingPattern) : Prop :=
  ∀ a d d', p a d = p a d'

/-- The pattern depends only on definiteness. -/
def DefinitenessOnly (p : MarkingPattern) : Prop :=
  ∀ a a' d, p a d = p a' d

instance : DecidablePred MonotoneP := λ p => by unfold MonotoneP; infer_instance
instance : DecidablePred MonotoneA := λ p => by unfold MonotoneA; infer_instance
instance : DecidablePred AnimacyOnly := λ p => by unfold AnimacyOnly; infer_instance
instance : DecidablePred DefinitenessOnly := λ p => by
  unfold DefinitenessOnly; infer_instance

/-- **The transfer equation**: `MonotoneP` is upper-set closure of the marked
    zone in the product prominence order — [aissen-2003]'s (33b), with the
    product order of the paper's fn. 23. -/
theorem monotoneP_iff_isUpperSet (p : MarkingPattern) :
    p.MonotoneP ↔
      IsUpperSet {c : AnimacyLevel × DefinitenessLevel | p c.1 c.2 = true} :=
  ⟨λ h _ _ hle hm => h _ _ _ _ hle.1 hle.2 hm,
    λ h _ _ _ _ ha hd hm => h (Prod.mk_le_mk.mpr ⟨ha, hd⟩) hm⟩

-- ============================================================================
-- § 8: One-dimensional cutoff patterns
-- ============================================================================

/-- Mark the cells at or above an animacy cutoff — P/T-type marking; the
    marked zone is `Core.Order.atOrAbove` on the animacy axis. -/
def animacyAtLeast (cutoff : AnimacyLevel) : MarkingPattern :=
  λ a _ => decide (cutoff ≤ a)

/-- Mark the cells at or above a definiteness cutoff (P/T-type marking). -/
def definitenessAtLeast (cutoff : DefinitenessLevel) : MarkingPattern :=
  λ _ d => decide (cutoff ≤ d)

/-- Mark the cells at or below an animacy cutoff — A/R-type marking; the
    marked zone is the complementary lower set. -/
def animacyAtMost (cutoff : AnimacyLevel) : MarkingPattern :=
  λ a _ => decide (a ≤ cutoff)

/-- Mark the cells at or below a definiteness cutoff (A/R-type marking). -/
def definitenessAtMost (cutoff : DefinitenessLevel) : MarkingPattern :=
  λ _ d => decide (d ≤ cutoff)

/-- [just-2024]'s mirror image: the P-type and A-type cutoffs at the same
    level jointly cover the grid — every cell is marked by at least one,
    both exactly at the cutoff row. -/
theorem animacy_mirror_image (cutoff a : AnimacyLevel) (d : DefinitenessLevel) :
    (animacyAtLeast cutoff a d || animacyAtMost cutoff a d) = true := by
  simpa [animacyAtLeast, animacyAtMost] using le_total cutoff a

end MarkingPattern

-- ============================================================================
-- § 11: Scenarios ([haspelmath-2021], §6)
-- ============================================================================

/-- A monotransitive scenario: the person combination of A and P.

    Scenario splits arise when argument coding depends not on a single
    argument's prominence but on the *combination* of A-person and P-person.
    E.g., 1→3 ("I see him") vs. 3→1 ("He sees me") may get different
    flagging or indexing. -/
structure Scenario where
  /-- Person of the A argument -/
  aPerson : Person
  /-- Person of the P argument -/
  pPerson : Person
  deriving DecidableEq, Repr

/-- Whether a scenario is "downstream": A has higher
    person rank than P. This is the "usual" direction — the role-reference
    association predicts high-rank roles (A) to have high-prominence referents.
    Downstream scenarios tend to get the shortest coding. -/
def Scenario.isDownstream (s : Scenario) : Bool :=
  s.aPerson.prominence > s.pPerson.prominence

/-- Whether a scenario is "upstream": P has higher
    person rank than A. This is the "unusual" direction — against the
    role-reference association. Upstream scenarios tend to get the longest
    coding. -/
def Scenario.isUpstream (s : Scenario) : Bool :=
  s.aPerson.prominence < s.pPerson.prominence

/-- Whether a scenario is "balanced": A and P have the same person rank
    (e.g., 3→3). Intermediate coding predicted. -/
def Scenario.isBalanced (s : Scenario) : Bool :=
  s.aPerson.prominence == s.pPerson.prominence

/-- Whether a scenario is "local": both arguments are SAP (1st or 2nd).
    Local scenarios (1↔2) are frequent and tend to get short coding. -/
def Scenario.isLocal (s : Scenario) : Bool :=
  decide s.aPerson.IsSAP && decide s.pPerson.IsSAP

/-- Whether a scenario is "direct": SAP acts on 3rd person.
    A subtype of downstream scenarios. -/
def Scenario.isDirect (s : Scenario) : Bool :=
  decide s.aPerson.IsSAP && !decide s.pPerson.IsSAP

/-- Whether a scenario is "inverse": 3rd person acts on SAP.
    A subtype of upstream scenarios. -/
def Scenario.isInverse (s : Scenario) : Bool :=
  !decide s.aPerson.IsSAP && decide s.pPerson.IsSAP

/-- Whether a scenario is "non-local": 3rd person acts on 3rd person.
    A subtype of balanced scenarios. -/
def Scenario.isNonlocal (s : Scenario) : Bool :=
  !decide s.aPerson.IsSAP && !decide s.pPerson.IsSAP

/-- All 9 person-pair scenarios. Explicit literal so `decide` reduces;
    the equivalent map over `personScaleLevels` pairs
    typechecks but defeats kernel-level `decide` over `Scenario.all.all (...)`. -/
def Scenario.all : List Scenario :=
  [⟨.first, .first⟩,  ⟨.first, .second⟩,  ⟨.first, .third⟩,
   ⟨.second, .first⟩, ⟨.second, .second⟩, ⟨.second, .third⟩,
   ⟨.third, .first⟩,  ⟨.third, .second⟩,  ⟨.third, .third⟩]

theorem Scenario.all_length : Scenario.all.length = 9 := rfl

-- ============================================================================
-- § 12: Role-Reference Association ([haspelmath-2021], §2)
-- ============================================================================

/-- The direction of differential marking: for a given role, does
    differential coding target the prominent end (upper set) or the
    non-prominent end (lower set)?

    Returns `true` when differential marking targets the prominent end.
    P and T → true (mark prominent referents); A and R → false (mark
    non-prominent referents); S → false.

    Definitionally `r.lowDefault` — the two functions agree pointwise
    over all five argument roles. The aliasing makes U3, U7, U8 in
    `Studies/Haspelmath2021.lean` `rfl` against the
    substrate, rather than re-proving the equality in the study file. -/
def differentialTargetsProminent (r : ArgumentRole) : Bool := r.lowDefault

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
-- § 13: Scenario Frequency Class ([haspelmath-2021], §8)
-- ============================================================================

/-- Frequency class for scenarios: downstream (usual) most frequent.
    Downstream = 2, balanced = 1, upstream = 0. -/
def Scenario.frequencyClass (s : Scenario) : Nat :=
  if s.isDownstream then 2 else if s.isBalanced then 1 else 0

/-- Gradient upstream degree: how far P's rank exceeds A's.
    Uses Nat saturating subtraction (negative → 0). -/
def Scenario.upstreamDegree (s : Scenario) : Nat :=
  s.pPerson.prominence - s.aPerson.prominence

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
