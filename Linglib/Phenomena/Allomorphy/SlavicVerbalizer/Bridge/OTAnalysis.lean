import Linglib.Theories.Phonology.Features
import Linglib.Theories.Phonology.OT.Core
import Linglib.Phenomena.Allomorphy.SlavicVerbalizer.Data

/-!
# Slavic Verbalizer — OT Analysis @cite{stojkovic-2026}

OT evaluation connecting constraint rankings to the empirical surface
forms of the Slavic verbalizer (VBLZ). Stojković (2026) argues the VBLZ
has a single abstract underlying representation (a defective diphthong)
across all Slavic; surface alternation is derived by OT constraint ranking.

## Candidates

The VBLZ in the pre-vocalic context (before the thematic /-a-/) can
surface as one of five candidates, differing in how the unspecified
slot of the diphthong is resolved:

| Candidate | Vowel     | Mechanism                           |
|-----------|-----------|-------------------------------------|
| [ov]      | [o] = [+back, −high] | epenthesise [+back] and [−high] |
| [ev]      | [e] = [−back, −high] | share [−back] from palatal, epenthesise [−high] |
| [uv]      | [u] = [+back, +high] | epenthesise [+back] and [+high] |
| [iv]      | [i] = [−back, +high] | share [−back] from palatal, epenthesise [+high] |
| [u.a]     | hiatus     | monophthongise, delete unspecified slot |

## Constraints

Six constraints, of which two (NOHIATUS, SPECIFY) are undominated and
four (*SHARE[−back], DEP[+back], DEP[−high], DEP[+high]) are variable:

- **NOHIATUS** (markedness): no adjacent vowels
- **SPECIFY** (markedness): every base node must be fully specified
- ***SHARE[−back]** (markedness): don't copy [−back] from adjacent segment
- **DEP[+back]** (faithfulness): don't epenthesise [+back]
- **DEP[−high]** (faithfulness): don't epenthesise [−high]
- **DEP[+high]** (faithfulness): don't epenthesise [+high]

Note: DEP[+high] is implicit in Stojković's analysis. Without it, [uv]
harmonically bounds [ov] (strictly fewer violations at every constraint),
making it impossible for any ranking to select [ov]. The paper derives
the same effect from the markedness of [+high] vs [−high]: [−high] is
the cross-linguistically unmarked epenthetic height (p. 14), while
[+high] epenthesis incurs an implicit faithfulness cost. Making this
explicit as DEP[+high] yields the correct factorial typology.

## Factorial Typology

The 4! = 24 permutations of the four variable constraints produce
exactly 4 distinct optima: {[ov]}, {[ev]}, {[uv]}, {[iv]}. Three
correspond to attested groups; {[iv]} is unattested.

## References

- Stojković, J. (2026). Same Form, Different Grammars: The Slavic
  [ov]∼[u] Alternation. In *Advances in Formal Slavic Linguistics 2023*.
-/

namespace Phenomena.Allomorphy.SlavicVerbalizer.Bridge.OTAnalysis

open Theories.Phonology.OT Core.ConstraintEvaluation
open Phenomena.Allomorphy.SlavicVerbalizer.Data

-- ============================================================================
-- § 1: Candidates
-- ============================================================================

/-- Candidate surface realisations of the VBLZ before the thematic /-a-/.
    Each represents a different resolution of the defective diphthong. -/
inductive VBLZCandidate where
  /-- [ov]: diphthong fissions, slot 1 → [o] via epenthetic [+back, −high]. -/
  | ov
  /-- [ev]: diphthong fissions, slot 1 → [e] via shared [−back], epenthetic [−high]. -/
  | ev
  /-- [uv]: diphthong fissions, slot 1 → [u] via epenthetic [+back, +high]. -/
  | uv
  /-- [iv]: diphthong fissions, slot 1 → [i] via shared [−back], epenthetic [+high]. -/
  | iv
  /-- [u.a]: monophthongisation, unspecified slot deleted, hiatus with /-a-/. -/
  | uHiatus
  deriving DecidableEq, BEq, Repr

/-- All candidates. -/
def allCandidates : List VBLZCandidate := [.ov, .ev, .uv, .iv, .uHiatus]

theorem allCandidates_nonempty : allCandidates ≠ [] := by decide

/-- The four fission candidates (excluding hiatus), for factorial typology. -/
def fissionCandidates : List VBLZCandidate := [.ov, .ev, .uv, .iv]

theorem fissionCandidates_nonempty : fissionCandidates ≠ [] := by decide

-- ============================================================================
-- § 2: Constraints
-- ============================================================================

/-- NOHIATUS: assign * for adjacent vowels. -/
def noHiatus : NamedConstraint VBLZCandidate :=
  { name := "NOHIATUS"
  , family := .markedness
  , eval := fun | .uHiatus => 1 | _ => 0 }

/-- SPECIFY(•→[F]): assign * for unspecified base node.
    Only violated by the fully faithful candidate (not in our candidate set),
    so this constraint is vacuously satisfied. Included for completeness. -/
def specify : NamedConstraint VBLZCandidate :=
  { name := "SPECIFY"
  , family := .markedness
  , eval := fun _ => 0 }

/-- *SHARE[−back]: don't copy [−back] from an adjacent palatal.
    Violated by [ev] (shares [−back] for [e]) and [iv] (shares [−back] for [i]). -/
def noShareBack : NamedConstraint VBLZCandidate :=
  { name := "*SHARE[−back]"
  , family := .markedness
  , eval := fun | .ev => 1 | .iv => 1 | _ => 0 }

/-- DEP[+back]: don't epenthesise [+back] on the unspecified slot.
    Violated by [ov] and [uv] (both epenthesise [+back] to get a back vowel). -/
def depBack : NamedConstraint VBLZCandidate :=
  { name := "DEP[+back]"
  , family := .faithfulness
  , eval := fun | .ov => 1 | .uv => 1 | _ => 0 }

/-- DEP[−high]: don't epenthesise [−high] on the unspecified slot.
    Violated by [ov] and [ev] (both epenthesise [−high] to get a mid vowel). -/
def depLowHigh : NamedConstraint VBLZCandidate :=
  { name := "DEP[−high]"
  , family := .faithfulness
  , eval := fun | .ov => 1 | .ev => 1 | _ => 0 }

/-- DEP[+high]: don't epenthesise [+high] on the unspecified slot.
    Violated by [uv] and [iv] (both epenthesise [+high] to get a high vowel).

    Implicit in Stojković's analysis. Without this constraint, [uv]
    harmonically bounds [ov], making it impossible for any ranking to
    select [ov] as optimal. Stojković derives the equivalent effect
    from the markedness of [+high] vs [−high] (p. 14): "The feature
    [−high] is cross-linguistically more likely to be unmarked compared
    to [+high]." -/
def depHigh : NamedConstraint VBLZCandidate :=
  { name := "DEP[+high]"
  , family := .faithfulness
  , eval := fun | .uv => 1 | .iv => 1 | _ => 0 }

/-- The four variable constraints (excluding the undominated NOHIATUS
    and vacuous SPECIFY). These are permuted in the factorial typology. -/
def variableConstraints : List (NamedConstraint VBLZCandidate) :=
  [noShareBack, depBack, depLowHigh, depHigh]

/-- All six constraints in one list. -/
def allConstraints : List (NamedConstraint VBLZCandidate) :=
  [noHiatus, specify, noShareBack, depBack, depLowHigh, depHigh]

-- ============================================================================
-- § 3: Group-Specific Rankings
-- ============================================================================

/-- [ov] group ranking (Stojković 2026, (17)):
    NOHIATUS, SPECIFY ≫ *SHARE[−back] ≫ DEP[+high] ≫ DEP[+back] ≫ DEP[−high]

    *SHARE[−back] high: sharing [−back] from palatals is banned.
    DEP[+high] above DEP[−high]: [+high] epenthesis is costlier than [−high],
    making [−high] the default → mid vowel [o] surfaces. -/
def ovRanking : List (NamedConstraint VBLZCandidate) :=
  [noHiatus, specify, noShareBack, depHigh, depBack, depLowHigh]

/-- [ov]/[ev] group ranking (Stojković 2026, (21)):
    NOHIATUS, SPECIFY ≫ DEP[+back] ≫ DEP[+high] ≫ *SHARE[−back] ≫ DEP[−high]

    DEP[+back] high: epenthesising [+back] is banned. After palatals,
    sharing [−back] is the only option → [ev]. After non-palatals,
    [−high] epenthesis yields [ov] (in a separate non-palatal evaluation). -/
def ovEvRanking : List (NamedConstraint VBLZCandidate) :=
  [noHiatus, specify, depBack, depHigh, noShareBack, depLowHigh]

/-- [uv] group ranking (Stojković 2026, (29)):
    NOHIATUS, SPECIFY ≫ DEP[−high] ≫ *SHARE[−back] ≫ DEP[+back] ≫ DEP[+high]

    DEP[−high] high: epenthesising [−high] is banned → [+high] surfaces.
    *SHARE[−back] above DEP[+back]: epenthesising [+back] is cheaper
    than sharing [−back] → back vowel [u] surfaces. -/
def uvRanking : List (NamedConstraint VBLZCandidate) :=
  [noHiatus, specify, depLowHigh, noShareBack, depBack, depHigh]

-- ============================================================================
-- § 4: Optimality Theorems
-- ============================================================================

/-- The [ov] group ranking selects [ov] as the unique optimal candidate. -/
theorem ov_optimal :
    (buildTableau allCandidates ovRanking allCandidates_nonempty).optimal
      = [.ov] := by native_decide

/-- The [ov]/[ev] ranking selects [ev] as optimal in the palatal context.
    (In the non-palatal context, [ev] and [iv] are unavailable because
    there is no palatal to share [−back] from; [ov] wins trivially.) -/
theorem ev_optimal :
    (buildTableau allCandidates ovEvRanking allCandidates_nonempty).optimal
      = [.ev] := by native_decide

/-- The [uv] group ranking selects [uv] as the unique optimal candidate. -/
theorem uv_optimal :
    (buildTableau allCandidates uvRanking allCandidates_nonempty).optimal
      = [.uv] := by native_decide

-- ============================================================================
-- § 5: Factorial Typology
-- ============================================================================

set_option maxRecDepth 1024 in
/-- The factorial typology over the four variable constraints and four
    fission candidates produces exactly 4 distinct optimal sets.

    Three correspond to attested Slavic groups:
    - {[ov]}: *SHARE, DEP[+high] ranked high
    - {[ev]}: DEP[+back], DEP[+high] ranked high
    - {[uv]}: DEP[−high], *SHARE ranked high

    The fourth ({[iv]}) is unattested in Slavic. -/
theorem factorial_typology_size :
    factorialTypologySize fissionCandidates variableConstraints
      fissionCandidates_nonempty = 4 := by native_decide

set_option maxRecDepth 1024 in
/-- The four distinct optima are exactly the four singleton candidate sets. -/
theorem factorial_optima_are_singletons :
    factorialOptima fissionCandidates variableConstraints
      fissionCandidates_nonempty
    = [[.uv], [.iv], [.ov], [.ev]] := by native_decide

/-- The [iv] pattern (shared [−back] + [+high], giving a front high vowel)
    is the only unattested pattern among the four predicted by the
    factorial typology (Stojković 2026, (31f)). -/
def ivIsUnattested : Prop :=
  ∀ (l : SlavicLang), l.vblzGroup ≠ .ovGroup →
    l.vblzGroup ≠ .uvGroup → l.vblzGroup = .ovEvGroup

theorem iv_pattern_unattested : ivIsUnattested := by
  intro l h1 h2
  cases l <;> simp [SlavicLang.vblzGroup] at h1 h2 ⊢

-- ============================================================================
-- § 6: Bridge to Empirical Data
-- ============================================================================

/-- The [ov] group's OT-predicted form matches the empirical data. -/
theorem ov_matches_group :
    VBLZGroup.ovGroup.forms.contains "ov" = true := rfl

/-- The [uv] group's OT-predicted form matches the empirical data. -/
theorem uv_matches_group :
    VBLZGroup.uvGroup.forms.contains "uv" = true := rfl

/-- The [ov]/[ev] group's OT-predicted forms match the empirical data:
    [ev] in the palatal context (proved by `ev_optimal`), [ov] in the
    non-palatal context (where [ev] is unavailable). -/
theorem ovEv_matches_group :
    VBLZGroup.ovEvGroup.forms.contains "ev" = true ∧
    VBLZGroup.ovEvGroup.forms.contains "ov" = true := ⟨rfl, rfl⟩

/-- The surface form of each candidate. -/
def VBLZCandidate.surfaceForm : VBLZCandidate → String
  | .ov => "ov"
  | .ev => "ev"
  | .uv => "uv"
  | .iv => "iv"
  | .uHiatus => "u"

/-- The OT-optimal candidate for the [ov] group produces the attested form. -/
theorem ov_surface_correct :
    VBLZCandidate.ov.surfaceForm = "ov" := rfl

/-- The OT-optimal candidate for the [uv] group produces the attested form. -/
theorem uv_surface_correct :
    VBLZCandidate.uv.surfaceForm = "uv" := rfl

/-- The OT-optimal candidate for the [ov]/[ev] palatal context produces
    the attested palatal-conditioned form. -/
theorem ev_surface_correct :
    VBLZCandidate.ev.surfaceForm = "ev" := rfl

end Phenomena.Allomorphy.SlavicVerbalizer.Bridge.OTAnalysis
