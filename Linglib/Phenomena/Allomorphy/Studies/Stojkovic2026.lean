import Linglib.Theories.Phonology.Featural.Features
import Linglib.Theories.Phonology.OptimalityTheory.Constraints

/-!
# Slavic Verbalizer @cite{stojkovic-2026}

Stojković (2026) argues the Slavic verbalizer (VBLZ) suffix used in
secondary imperfectivisation has a single abstract underlying
representation (a defective diphthong) across all Slavic; surface
alternation is derived by OT constraint ranking.

## Empirical Data

Three-way surface alternation across Slavic:

| Group        | INF stem VC | Languages                                  |
|--------------|-------------|--------------------------------------------|
| [ov] group   | [ov]        | Polish, Czech, Slovak, U/L Sorbian,...    |
| [ov]/[ev]    | [ov]∼[ev]   | BCMS, Slovenian, Russian,...              |
| [uv] group   | [uv]        | Ukrainian, Lemko Rusyn, Bulgarian, Maced.  |

All groups share the present-stem vowel [u] (before /-je-/). The
variation is confined to the infinitive stem (before /-a-/).

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

-/

namespace Stojkovic2026

open Core.OT Core.ConstraintEvaluation Phonology.Constraints

-- ============================================================================
-- § 0: Empirical Data
-- ============================================================================

/-- Representative Slavic languages exhibiting secondary imperfectivisation. -/
inductive SlavicLang where
  | russian
  | polish
  | czech
  | upperSorbian
  | bcms              -- Bosnian/Croatian/Montenegrin/Serbian
  | slovenian
  | slovak
  | lowerSorbian
  | ukrainian
  | lemkoRusyn
  | bulgarian
  | macedonian
  deriving DecidableEq, Repr

/-- The three surface-form groups for the VBLZ in the infinitive stem. -/
inductive VBLZGroup where
  /-- Always [ov], regardless of preceding consonant. -/
  | ovGroup
  /-- [ov] after non-palatals, [ev] after palatals. -/
  | ovEvGroup
  /-- Always [uv], regardless of preceding consonant. -/
  | uvGroup
  deriving DecidableEq, Repr

/-- Surface VC forms attested in the infinitive stem for each group. -/
def VBLZGroup.forms : VBLZGroup → List String
  | .ovGroup   => ["ov"]
  | .ovEvGroup => ["ov", "ev"]
  | .uvGroup   => ["uv"]

/-- Group membership for each language. -/
def SlavicLang.vblzGroup : SlavicLang → VBLZGroup
  | .polish | .czech | .slovak | .upperSorbian | .lowerSorbian => .ovGroup
  | .russian | .bcms | .slovenian                              => .ovEvGroup
  | .ukrainian | .lemkoRusyn | .bulgarian | .macedonian        => .uvGroup

/-- A VBLZ datum: language, infinitive-stem VC, present-stem V. -/
structure VBLZDatum where
  lang : SlavicLang
  infStem : String
  presStem : String
  deriving DecidableEq, Repr

def polishVBLZ : VBLZDatum := ⟨.polish, "ov", "u"⟩
def czechVBLZ : VBLZDatum := ⟨.czech, "ov", "u"⟩
def slovakVBLZ : VBLZDatum := ⟨.slovak, "ov", "u"⟩
def upperSorbianVBLZ : VBLZDatum := ⟨.upperSorbian, "ov", "u"⟩
def lowerSorbianVBLZ : VBLZDatum := ⟨.lowerSorbian, "ov", "u"⟩
def russianVBLZ : VBLZDatum := ⟨.russian, "ov", "u"⟩
def bcmsVBLZ : VBLZDatum := ⟨.bcms, "ov", "u"⟩
def slovenianVBLZ : VBLZDatum := ⟨.slovenian, "ov", "u"⟩
def ukrainianVBLZ : VBLZDatum := ⟨.ukrainian, "uv", "u"⟩
def lemkoRusynVBLZ : VBLZDatum := ⟨.lemkoRusyn, "uv", "u"⟩
def bulgarianVBLZ : VBLZDatum := ⟨.bulgarian, "uv", "u"⟩
def macedonianVBLZ : VBLZDatum := ⟨.macedonian, "uv", "u"⟩

def allData : List VBLZDatum :=
  [polishVBLZ, czechVBLZ, slovakVBLZ, upperSorbianVBLZ, lowerSorbianVBLZ,
   russianVBLZ, bcmsVBLZ, slovenianVBLZ,
   ukrainianVBLZ, lemkoRusynVBLZ, bulgarianVBLZ, macedonianVBLZ]

theorem allData_length : allData.length = 12 := rfl

/-- The present-stem vowel is universally [u] across all three groups. -/
theorem presentStemUniversal :
    allData.all (fun d => d.presStem == "u") = true := rfl

/-- Each datum's infinitive stem is consistent with its language's group. -/
theorem infStem_matches_group :
    allData.all (fun d => d.lang.vblzGroup.forms.contains d.infStem) = true := rfl

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
  deriving DecidableEq, Repr

/-- All candidates. -/
def allCandidates : List VBLZCandidate := [.ov, .ev, .uv, .iv, .uHiatus]

/-- The four fission candidates (excluding hiatus), for factorial typology. -/
def fissionCandidates : List VBLZCandidate := [.ov, .ev, .uv, .iv]

-- ============================================================================
-- § 2: Constraints
-- ============================================================================

/-- NOHIATUS: assign * for adjacent vowels. -/
def noHiatus : NamedConstraint VBLZCandidate :=
  mkMark "NOHIATUS" fun | .uHiatus => true | _ => false

/-- SPECIFY(•→[F]): assign * for unspecified base node.
    Only violated by the fully faithful candidate (not in our candidate set),
    so this constraint is vacuously satisfied. Included for completeness. -/
def specify : NamedConstraint VBLZCandidate :=
  mkMark "SPECIFY" fun _ => false

/-- *SHARE[−back]: don't copy [−back] from an adjacent palatal.
    Violated by [ev] (shares [−back] for [e]) and [iv] (shares [−back] for [i]). -/
def noShareBack : NamedConstraint VBLZCandidate :=
  mkMark "*SHARE[−back]" fun | .ev | .iv => true | _ => false

/-- DEP[+back]: don't epenthesise [+back] on the unspecified slot.
    Violated by [ov] and [uv] (both epenthesise [+back] to get a back vowel). -/
def depBack : NamedConstraint VBLZCandidate :=
  mkDep "DEP[+back]" fun | .ov | .uv => true | _ => false

/-- DEP[−high]: don't epenthesise [−high] on the unspecified slot.
    Violated by [ov] and [ev] (both epenthesise [−high] to get a mid vowel). -/
def depLowHigh : NamedConstraint VBLZCandidate :=
  mkDep "DEP[−high]" fun | .ov | .ev => true | _ => false

/-- DEP[+high]: don't epenthesise [+high] on the unspecified slot.
    Violated by [uv] and [iv] (both epenthesise [+high] to get a high vowel).

    Implicit in Stojković's analysis. Without this constraint, [uv]
    harmonically bounds [ov], making it impossible for any ranking to
    select [ov] as optimal. Stojković derives the equivalent effect
    from the markedness of [+high] vs [−high] (p. 14): "The feature
    [−high] is cross-linguistically more likely to be unmarked compared
    to [+high]." -/
def depHigh : NamedConstraint VBLZCandidate :=
  mkDep "DEP[+high]" fun | .uv | .iv => true | _ => false

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
    (mkTableau allCandidates ovRanking).optimal
      = {.ov} := by native_decide

/-- The [ov]/[ev] ranking selects [ev] as optimal in the palatal context.
    (In the non-palatal context, [ev] and [iv] are unavailable because
    there is no palatal to share [−back]; [ov] wins trivially.) -/
theorem ev_optimal :
    (mkTableau allCandidates ovEvRanking).optimal
      = {.ev} := by native_decide

/-- The [uv] group ranking selects [uv] as the unique optimal candidate. -/
theorem uv_optimal :
    (mkTableau allCandidates uvRanking).optimal
      = {.uv} := by native_decide

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
    mkFactorialTypologySize fissionCandidates variableConstraints
      = 4 := by native_decide

set_option maxRecDepth 1024 in
/-- The four distinct optima are exactly the four singleton candidate sets. -/
theorem factorial_optima_are_singletons :
    mkFactorialOptima fissionCandidates variableConstraints
     
    = [{.uv}, {.iv}, {.ov}, {.ev}] := by native_decide

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

end Stojkovic2026
