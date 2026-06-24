import Linglib.Phonology.Features
import Linglib.Phonology.OptimalityTheory.Constraints

/-!
# Slavic Verbalizer [stojkovic-2026]

Stojković (2026) argues the Slavic verbalizer (VBLZ) suffix used in
secondary imperfectivisation has a single abstract underlying
representation (a defective diphthong) across all Slavic; surface
alternation is derived by OT constraint ranking.

## Empirical Data

Three-way surface alternation across Slavic:

| Group        | INF stem VC | Languages                                  |
|--------------|-------------|--------------------------------------------|
| [ov] group   | [ov]        | Polish, Czech, Slovak, U/L Sorbian,...     |
| [ov]/[ev]    | [ov]∼[ev]   | BCMS, Slovenian, Russian,...               |
| [uv] group   | [uv]        | Ukrainian, Lemko Rusyn, Bulgarian, Maced.  |

Where the VBLZ precedes the theme vowel /-je-/ in the present, the
present stem is the single vowel [u] and the VC alternation is confined
to the infinitive stem (before /-a-/). Bulgarian and Macedonian are the
exception: having lost the INF/PRS distinction, they have /-a-/ after the
VBLZ in both stems, so the VC sequence [uv] surfaces throughout (Table 1).

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
| [u]       | monophthong | delete the unspecified slot |

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

[stojkovic-2026]'s own factorial typology (31) ranks *three* constraints
(*SHARE[−back], DEP[+back], DEP[−high]) and derives the three attested
patterns — [ov], the context-sensitive [ov]~[ev], and [uv] — plus a
hypothetical [uv]~[iv] (31f). In pure OT those three constraints leave [uv]
harmonically bounding [ov] (§4.2, p. 14), which the paper resolves by the
markedness of [−high] epenthesis rather than a constraint. Making that
preference explicit as DEP[+high], the 4! = 24 permutations of the four
variable constraints here yield four singleton optima — {[ov]}, {[ev]},
{[uv]}, {[iv]} — the first three attested, [iv] unattested ((32): the
hypothetical Ukrainian [uv]~[iv] pairs).

-/

namespace Stojkovic2026

open Constraint OptimalityTheory Core.Optimization.Evaluation OptimalityTheory

/-! ### Candidates -/

/-- Candidate surface realisations of the VBLZ, each a resolution of the
    defective diphthong. This is the typed surface-form inventory used
    throughout the file (no stringly-typed forms). -/
inductive VBLZCandidate where
  /-- [ov]: diphthong fissions, slot 1 → [o] via epenthetic [+back, −high]. -/
  | ov
  /-- [ev]: diphthong fissions, slot 1 → [e] via shared [−back], epenthetic [−high]. -/
  | ev
  /-- [uv]: diphthong fissions, slot 1 → [u] via epenthetic [+back, +high]. -/
  | uv
  /-- [iv]: diphthong fissions, slot 1 → [i] via shared [−back], epenthetic [+high]. -/
  | iv
  /-- [u]: monophthong — the unspecified slot is deleted. Before a vowel this
      yields a hiatus ([u.a], penalised by NOHIATUS); before a consonant (the
      /-je-/ present) it is the licit single vowel [u]. -/
  | uMono
  deriving DecidableEq, Repr

/-- All candidates. -/
def allCandidates : List VBLZCandidate := [.ov, .ev, .uv, .iv, .uMono]

/-- The four fission candidates (excluding the monophthong), for factorial typology. -/
def fissionCandidates : List VBLZCandidate := [.ov, .ev, .uv, .iv]

/-! ### Empirical data -/

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

/-- Surface candidates attested in the infinitive stem for each group. -/
def VBLZGroup.forms : VBLZGroup → List VBLZCandidate
  | .ovGroup   => [.ov]
  | .ovEvGroup => [.ov, .ev]
  | .uvGroup   => [.uv]

/-- Group membership for each language. -/
def SlavicLang.vblzGroup : SlavicLang → VBLZGroup
  | .polish | .czech | .slovak | .upperSorbian | .lowerSorbian => .ovGroup
  | .russian | .bcms | .slovenian                              => .ovEvGroup
  | .ukrainian | .lemkoRusyn | .bulgarian | .macedonian        => .uvGroup

/-- A VBLZ datum: language, infinitive-stem and present-stem surface candidate. -/
structure VBLZDatum where
  lang : SlavicLang
  infStem : VBLZCandidate
  presStem : VBLZCandidate
  deriving DecidableEq, Repr

def polishVBLZ : VBLZDatum := ⟨.polish, .ov, .uMono⟩
def czechVBLZ : VBLZDatum := ⟨.czech, .ov, .uMono⟩
def slovakVBLZ : VBLZDatum := ⟨.slovak, .ov, .uMono⟩
def upperSorbianVBLZ : VBLZDatum := ⟨.upperSorbian, .ov, .uMono⟩
def lowerSorbianVBLZ : VBLZDatum := ⟨.lowerSorbian, .ov, .uMono⟩
def russianVBLZ : VBLZDatum := ⟨.russian, .ov, .uMono⟩
def bcmsVBLZ : VBLZDatum := ⟨.bcms, .ov, .uMono⟩
def slovenianVBLZ : VBLZDatum := ⟨.slovenian, .ov, .uMono⟩
def ukrainianVBLZ : VBLZDatum := ⟨.ukrainian, .uv, .uMono⟩
def lemkoRusynVBLZ : VBLZDatum := ⟨.lemkoRusyn, .uv, .uMono⟩
def bulgarianVBLZ : VBLZDatum := ⟨.bulgarian, .uv, .uv⟩
def macedonianVBLZ : VBLZDatum := ⟨.macedonian, .uv, .uv⟩

def allData : List VBLZDatum :=
  [polishVBLZ, czechVBLZ, slovakVBLZ, upperSorbianVBLZ, lowerSorbianVBLZ,
   russianVBLZ, bcmsVBLZ, slovenianVBLZ,
   ukrainianVBLZ, lemkoRusynVBLZ, bulgarianVBLZ, macedonianVBLZ]

theorem allData_length : allData.length = 12 := rfl

/-- Bulgarian and Macedonian lack the INF/PRS distinction: the VBLZ precedes the
    theme vowel /-a-/ in *both* stems, so the VC sequence [uv] surfaces in the
    present too. All other languages have /-je-/ in the present, where the VBLZ
    is the single vowel [u] ([stojkovic-2026], Table 1, §4.4). -/
def SlavicLang.HasVCPresent : SlavicLang → Prop
  | .bulgarian | .macedonian => True
  | _ => False

instance : DecidablePred SlavicLang.HasVCPresent := fun l => by
  cases l <;> unfold SlavicLang.HasVCPresent <;> infer_instance

/-- The present stem is the single vowel [u] exactly in the languages with a
    /-je-/ present; Bulgarian and Macedonian surface the VC sequence [uv]
    throughout — the paper's central cross-Slavic exception ([stojkovic-2026],
    Table 1, §4.4). -/
theorem presentStem_iff_VCPresent :
    ∀ d ∈ allData, d.lang.HasVCPresent ↔ d.presStem = .uv := by decide

/-- Each datum's infinitive stem is one of its language's group forms. -/
theorem infStem_mem_group_forms :
    ∀ d ∈ allData, d.infStem ∈ d.lang.vblzGroup.forms := by decide

/-! ### Constraints -/

/-- NOHIATUS: assign * for adjacent vowels. In the pre-vocalic evaluation the
    monophthong `.uMono` realises [u] next to /-a-/, creating the hiatus this
    constraint penalises. -/
def noHiatus : NamedConstraint VBLZCandidate :=
  mkMark "NOHIATUS" fun c => c = .uMono

/-- SPECIFY(•→[F]): assign * for an unspecified base node. Only the fully
    faithful candidate (not in our candidate set) violates it, so it is
    vacuously satisfied here; included for faithfulness to the paper's set. -/
def specify : NamedConstraint VBLZCandidate :=
  mkMark "SPECIFY" fun _ => False

/-- *SHARE[−back]: don't copy [−back] from an adjacent palatal.
    Violated by [ev] and [iv] (both share [−back]). -/
def noShareBack : NamedConstraint VBLZCandidate :=
  mkMark "*SHARE[−back]" fun c => c = .ev ∨ c = .iv

/-- DEP[+back]: don't epenthesise [+back]. Violated by [ov] and [uv]. -/
def depBack : NamedConstraint VBLZCandidate :=
  mkDep "DEP[+back]" fun c => c = .ov ∨ c = .uv

/-- DEP[−high]: don't epenthesise [−high]. Violated by [ov] and [ev] (mid vowels). -/
def depMinusHigh : NamedConstraint VBLZCandidate :=
  mkDep "DEP[−high]" fun c => c = .ov ∨ c = .ev

/-- DEP[+high]: don't epenthesise [+high]. Violated by [uv] and [iv] (high vowels).

    Implicit in [stojkovic-2026]: without it [uv] harmonically bounds [ov], so no
    ranking selects [ov]. The paper derives the same effect from the markedness
    of [+high] vs [−high] (p. 14: "The feature [−high] is cross-linguistically
    more likely to be unmarked compared to [+high]."). -/
def depHigh : NamedConstraint VBLZCandidate :=
  mkDep "DEP[+high]" fun c => c = .uv ∨ c = .iv

/-- The four variable constraints (excluding the undominated NOHIATUS and vacuous
    SPECIFY), permuted in the factorial typology. -/
def variableConstraints : List (NamedConstraint VBLZCandidate) :=
  [noShareBack, depBack, depMinusHigh, depHigh]

/-- All six constraints. -/
def allConstraints : List (NamedConstraint VBLZCandidate) :=
  [noHiatus, specify, noShareBack, depBack, depMinusHigh, depHigh]

/-! ### Group-specific rankings -/

/-- [ov]-group ranking, adapted from [stojkovic-2026] (17). The paper's (17) is
    `NOHIATUS; SPECIFY ≫ *SHARE[−back] ≫ DEP[−high] ≫ DEP[+back] ≫ MAX•`, with
    [ov]≻[uv] following from the markedness of [−high] epenthesis (p. 14) rather
    than a constraint; we make that preference explicit via DEP[+high], giving
    `*SHARE[−back] ≫ DEP[+high] ≫ DEP[+back] ≫ DEP[−high]`.

    *SHARE[−back] high: sharing [−back] from palatals is banned. DEP[+high] high:
    [+high] epenthesis is costly, so the unmarked [−high] surfaces → mid [o]. -/
def ovRanking : List (NamedConstraint VBLZCandidate) :=
  [noHiatus, specify, noShareBack, depHigh, depBack, depMinusHigh]

/-- [ov]/[ev]-group ranking, adapted from [stojkovic-2026] (21). The paper's (21)
    is `NOHIATUS; SPECIFY ≫ DEP[+back] ≫ DEP[−high] ≫ *SHARE[−back] ≫ MAX•`; with
    DEP[+high] made explicit: `DEP[+back] ≫ DEP[+high] ≫ *SHARE[−back] ≫ DEP[−high]`.

    DEP[+back] high: epenthesising [+back] is banned. After a palatal, sharing
    [−back] is the only option → [ev]; after a non-palatal, [−high] epenthesis
    yields [ov] (a separate, non-palatal evaluation — not modelled here). -/
def ovEvRanking : List (NamedConstraint VBLZCandidate) :=
  [noHiatus, specify, depBack, depHigh, noShareBack, depMinusHigh]

/-- [uv]-group ranking, adapted from [stojkovic-2026] (29). The paper's (29) is
    `NOHIATUS; SPECIFY ≫ DEP[−high] ≫ *SHARE[−back] ≫ DEP[+back] ≫ MAX•`; we keep
    that order and replace the bottom MAX• with the explicit DEP[+high]:
    `DEP[−high] ≫ *SHARE[−back] ≫ DEP[+back] ≫ DEP[+high]`.

    DEP[−high] high: epenthesising [−high] is banned → [+high] surfaces.
    *SHARE[−back] above DEP[+back]: epenthesising [+back] is cheaper than sharing
    [−back] → back vowel [u] surfaces. -/
def uvRanking : List (NamedConstraint VBLZCandidate) :=
  [noHiatus, specify, depMinusHigh, noShareBack, depBack, depHigh]

/-! ### Optimality theorems -/

/-- The [ov]-group ranking selects [ov] as the unique optimum. -/
theorem ov_optimal :
    (mkTableau allCandidates ovRanking).optimal = {.ov} := by decide

/-- The [ov]/[ev] ranking selects [ev] in the palatal context. (Non-palatally,
    [ev] and [iv] are unavailable — no palatal to share [−back] — and [ov] wins;
    that contextual split is not modelled in this single tableau.) -/
theorem ev_optimal :
    (mkTableau allCandidates ovEvRanking).optimal = {.ev} := by decide

/-- The [uv]-group ranking selects [uv] as the unique optimum. -/
theorem uv_optimal :
    (mkTableau allCandidates uvRanking).optimal = {.uv} := by decide

/-! ### Factorial typology -/

set_option maxRecDepth 1024 in
/-- This file's four-constraint factorial typology (the three sharing/epenthesis
    constraints plus the explicit DEP[+high]) over the four fission candidates
    produces exactly four distinct optimal sets: {[ov]}, {[ev]}, {[uv]}, {[iv]}.
    [stojkovic-2026]'s own typology (31) is over *three* constraints and yields
    the three attested groups (with [ov]~[ev] one context-sensitive grammar) plus
    a hypothetical [uv]~[iv]; see the module docstring. -/
theorem factorial_typology_size :
    mkFactorialTypologySize fissionCandidates variableConstraints = 4 := by decide

set_option maxRecDepth 1024 in
/-- The four distinct optima are exactly the four singleton candidate sets. -/
theorem factorial_optima_are_singletons :
    mkFactorialOptima fissionCandidates variableConstraints
      = [{.uv}, {.iv}, {.ov}, {.ev}] := by decide

/-- [iv] is the unattested optimum: the factorial typology predicts an [iv]
    grammar (`{.iv}` is among the optima), yet no attested Slavic language
    surfaces the [iv] form — every group's inventory is one of [ov]/[ev]/[uv]
    ([stojkovic-2026], (31f)–(32): the Ukrainian [uv]~[iv] pairs are
    hypothetical and unattested). -/
theorem iv_unattested :
    ({VBLZCandidate.iv} : Finset VBLZCandidate) ∈
        mkFactorialOptima fissionCandidates variableConstraints ∧
    ∀ d ∈ allData, VBLZCandidate.iv ∉ d.lang.vblzGroup.forms := by
  refine ⟨?_, by decide⟩
  rw [factorial_optima_are_singletons]; decide

/-! ### Bridge to empirical data -/

/-- The OT-optimal candidate for each group (`ov_optimal`/`ev_optimal`/`uv_optimal`)
    is among that group's attested forms; [ov] also figures in the [ov]/[ev]
    group's inventory. -/
theorem optimal_forms_attested :
    VBLZCandidate.ov ∈ VBLZGroup.ovGroup.forms ∧
    VBLZCandidate.ev ∈ VBLZGroup.ovEvGroup.forms ∧
    VBLZCandidate.ov ∈ VBLZGroup.ovEvGroup.forms ∧
    VBLZCandidate.uv ∈ VBLZGroup.uvGroup.forms := by decide

end Stojkovic2026
