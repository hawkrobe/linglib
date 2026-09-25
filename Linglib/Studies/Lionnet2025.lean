/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Tone.Register
public import Linglib.Fragments.Drubea.Prosody
public import Linglib.Fragments.Numee.Prosody
public import Linglib.Studies.Hyman2006
public import Linglib.Data.Examples.Lionnet2025
import all Init.Data.List.Scan.Basic
import all Init.Data.List.Control

/-!
# Lionnet (2025): Tonal languages without tone

This file formalizes [lionnet-2025]'s analysis of the word prosody of Drubea and Numèè
(Oceanic, New Caledonia) as register features alone: an underlying downstep `l` on the
mora, a postlexical epenthetic upstep `h`, and boundary features, with no tone feature.
The stems of the two fragments carry only downsteps (`stems_register_only`), at most one
per stem (`stems_culminative`, Rivierre's culminativity) though not per compound
(`compounds_not_culminative`), and their tiers are exactly the three stem patterns ∅, `l`,
∅`l` associated by the syllabic alignment of Table 4 (`stems_patterned`), the loanwords of
(54) being the one exception (`loans_unpatterned`). The alignment predicts that a
syllable-internal downstep occurs only in monosyllables (`associate_syllable_initial`);
the CVꜜV monosyllables are what makes the mora, not the syllable, the register-bearing
unit (`mora_is_rbu`).

The postlexical derivation is downstep displacement (§4.6), the boundary features h% of
Drubea and l% of Numèè (§4.8), and pre-downstep h-epenthesis (§4.4), realized by terracing
from the baseline with the utterance-initial downstep unrealized (§4.5). The realization
reproduces Rivierre's pitch levels where he transcribes whole steps ((11), (19), (20),
(24), (26), (30), (38), (53)) and, for every transcribed utterance, the direction of each
step between syllables (`rows_signs`); the double downstep of (25), (52) and (53b) is a
second `l` on one mora. Lionnet's rephrasing of [leben-2018]'s definitional properties of
downstep and his placement of Drubea in [hyman-2006]'s typology — tonal by definition (3)
but without stress accent, culminative in register while neither obligatory nor
syllable-dependent (`drubea_tonal`, `drubea_not_stressAccent`) — close the file.

## Implementation notes

* Shifts are unit steps, so the realization is ordinal: the source's half steps and the
  larger drops it transcribes after a raised syllable ((13b), (32), (62)), Rivierre's
  observation that raising rarely compensates the lowering, are not derived. The joins
  with the rows compare the sign of each step between syllables, a syllable's level being
  that of its last mora, over the tokens the source levels.
* Displacement and h-epenthesis are optional in the source; each derivation applies the
  steps its surface transcription shows. H-epenthesis targets a registerless mora before a
  downstep unless the mora's own syllable is downstepped before it, which is what keeps
  /ꜜgoo/ at the baseline in (33) and /ꜜɳii/ unraised in (12). Spreading h-epenthesis ((16))
  and the lh contour on a downstepped mora ((18), (63)) are stated on their own.
* The comparison with a tonal alternative (§5) is prose and is not represented.

## References

* [lionnet-2025]
* [leben-2018]
* [hyman-2006]
* [rivierre-1973]
-/

@[expose] public section

namespace Lionnet2025

open Tone Tone.Registered Data.Examples
open Prosody (Syllable)

/-- The weight a syllable contributes: its mora count. -/
abbrev μ : Syllable → ℕ+ := Prosody.Syllable.pnatMoraCount

/-! ### Stem patterns (§4.2, Tables 2–4) -/

/-- The three stem-level register patterns: no `l`, an `l` on the first syllable, an `l`
after a registerless syllable. -/
inductive StemPattern where
  | empty
  | l
  | emptyL
  deriving DecidableEq, Fintype

/-- A tier of registerless morae. -/
def registerless (shape : List ℕ) : RegisterTier := shape.flatMap fun n ↦ List.replicate n []

/-- The tier a pattern associates to a stem shape (Table 4): `l` on the leftmost mora of the
first syllable, or of the second syllable, or — in a monosyllable, for lack of a second
syllable — on its second mora; nothing when the shape has no mora for it. -/
def StemPattern.associate : StemPattern → List ℕ → Option RegisterTier
  | .empty, shape => some (registerless shape)
  | .l, [] => none
  | .l, n :: rest => some ([.downstep] :: registerless ((n - 1) :: rest))
  | .emptyL, [] => none
  | .emptyL, [n] => if 2 ≤ n then some ([] :: [.downstep] :: registerless [n - 2]) else none
  | .emptyL, n :: m :: rest =>
    some (registerless [n] ++ [.downstep] :: registerless ((m - 1) :: rest))

/-- Every native stem of Drubea bears one of the three patterns. -/
theorem stems_patterned :
    ∀ s ∈ Drubea.stems, ∃ p : StemPattern, p.associate (s.shape μ) = some s.tier := by
  decide

/-- So does every stem of Numèè. -/
theorem numee_stems_patterned :
    ∀ s ∈ Numee.stems, ∃ p : StemPattern, p.associate (s.shape μ) = some s.tier := by
  decide

/-- The loanwords of (54), CVꜜV.CV(V), bear none: Table 3's mapping (b), attested in recent
loans only. -/
theorem loans_unpatterned :
    ∀ s ∈ Drubea.loans, ∀ p : StemPattern, p.associate (s.shape μ) ≠ some s.tier := by
  decide

theorem mem_registerless {shape : List ℕ} {ns : List TRN} (h : ns ∈ registerless shape) :
    ns = [] := by
  obtain ⟨_, -, h⟩ := List.mem_flatMap.1 h
  exact List.eq_of_mem_replicate h

theorem getElem?_registerless (shape : List ℕ) (i : ℕ) :
    (registerless shape)[i]?.getD [] = [] := by
  rcases h : (registerless shape)[i]? with _ | ns
  · rfl
  · simpa using mem_registerless (List.mem_of_getElem? h)

/-- The prediction of §4.2: on a stem of two or more syllables, every pattern puts its `l` on
a syllable-initial mora, a boundary of the syllabification. Syllable-internal downstep is
confined to monosyllables. -/
theorem associate_syllable_initial (p : StemPattern) {shape : List ℕ} (h : 2 ≤ shape.length)
    {tier : RegisterTier} (ht : p.associate shape = some tier) :
    ∀ i ∈ RegisterTier.bearing .downstep tier, ∃ k, i = (shape.take k).sum := by
  intro i hi
  simp only [RegisterTier.bearing, List.mem_filter, List.mem_range, List.getD_eq_getElem?_getD]
    at hi
  obtain ⟨n, m, rest, rfl⟩ : ∃ n m rest, shape = n :: m :: rest := by
    match shape, h with
    | n :: m :: rest, _ => exact ⟨n, m, rest, rfl⟩
  obtain ⟨-, hi⟩ := hi
  cases p with
  | empty =>
    simp only [StemPattern.associate, Option.some.injEq] at ht
    subst ht
    simp [getElem?_registerless] at hi
  | l =>
    simp only [StemPattern.associate, Option.some.injEq] at ht
    subst ht
    refine ⟨0, ?_⟩
    rcases i with _ | i
    · rfl
    · simp [getElem?_registerless] at hi
  | emptyL =>
    simp only [StemPattern.associate, Option.some.injEq] at ht
    subst ht
    suffices i = n from ⟨1, by simp [this]⟩
    have hlen : (registerless [n]).length = n := by simp [registerless]
    rcases lt_trichotomy i n with hlt | rfl | hgt
    · rw [List.getElem?_append_left (by rw [hlen]; exact hlt), getElem?_registerless] at hi
      simp at hi
    · rfl
    · rw [List.getElem?_append_right (by rw [hlen]; exact hgt.le), hlen] at hi
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hgt
      rw [show n + j + 1 - n = j + 1 by omega, List.getElem?_cons_succ,
        getElem?_registerless] at hi
      simp at hi

/-! ### Culminativity, register-only inventories, and the register-bearing unit -/

/-- Register culminativity (§3.8, §3.10): at most one downstep per stem. -/
def IsCulminative {S : Type*} (r : Registered S) : Prop :=
  (RegisterTier.bearing .downstep r.tier).length ≤ 1

instance {S : Type*} (r : Registered S) : Decidable (IsCulminative r) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem stems_culminative : ∀ s ∈ Drubea.stems, IsCulminative s := by decide

theorem loans_culminative : ∀ s ∈ Drubea.loans, IsCulminative s := by decide

theorem numee_stems_culminative : ∀ s ∈ Numee.stems, IsCulminative s := by decide

/-- /koꜜo·ꜜmwa/ 'mound' ((55a)), field·house. -/
def mound : Registered Syllable := Drubea.kooPlace ++ Drubea.mwaHouse

/-- /ꜜʊʊ·ũ·pooꜜka/ 'blanket' ((55b)), mat·hair·animal. -/
def blanket : Registered Syllable := Drubea.uuMat ++ Drubea.uHair ++ Drubea.pookaAnimal

/-- /ꜜko·ꜜvuu-ɽe/ 'voice, language' ((55c)), manner·speak-ACT. -/
def voice : Registered Syllable := Drubea.koManner ++ Drubea.vuuSpeak ++ Drubea.reAct

/-- Culminativity holds of the stem, not of the morphological word: each compound of (55)
carries the downsteps of its members. -/
theorem compounds_not_culminative :
    ¬ IsCulminative mound ∧ ¬ IsCulminative blanket ∧ ¬ IsCulminative voice := by decide

/-- No stem specifies `[upper]`: the first attested register-only word-prosodic system
(§6.2). -/
theorem stems_register_only :
    ∀ s ∈ Drubea.stems ++ Numee.stems, IsRegisterOnly (RegisterTier.nodes s.tier) := by
  decide

/-- The two morae of the one syllable of /beꜜe/ differ in register, so the register-bearing
unit is the mora, not the syllable (§3.7, §4.2). -/
theorem mora_is_rbu : Drubea.beeNeg.syllableNodes μ = [[[], [.downstep]]] := by decide

/-! ### Hyman's typology (§6.2) -/

/-- The native stems of Drubea. -/
abbrev Stem := {s // s ∈ Drubea.stems}

/-- The downstep as a marking of morae: on each stem, the morae bearing `l`, assigned by
mora. -/
def drubea : Hyman2006.Marking Stem ℕ where
  units s := Finset.range (s.1.moraCount μ)
  marked s := (RegisterTier.bearing .downstep s.1.tier).toFinset
  marked_subset s i hi := by
    have h : s.1.tier.length = s.1.moraCount μ := Drubea.stems_aligned s.1 s.2
    simp only [List.mem_toFinset, RegisterTier.bearing, List.mem_filter, List.mem_range] at hi
    exact Finset.mem_range.2 (h ▸ hi.1)
  tbu := .mora

/-- The downstep is culminative: at most one per stem. -/
theorem drubea_culminative : Hyman2006.Culminative drubea := fun ⟨a, ha⟩ =>
  (show ∀ a ∈ Drubea.stems, (RegisterTier.bearing .downstep a.tier).toFinset.card ≤ 1 by
    decide) a ha

/-- It is not obligatory: /kuɽe/ 'forest' has none. -/
theorem drubea_not_obligatory : ¬ Hyman2006.Obligatory drubea := fun h =>
  (h ⟨Drubea.kureForest, by decide⟩).ne_empty (by decide)

/-- Neither of Hyman's inviolable criteria of stress accent holds: the register-bearing
unit is the mora and the downstep is not obligatory. -/
theorem drubea_not_stressAccent : ¬ Hyman2006.StressAccent drubea := fun h =>
  drubea_not_obligatory h.2.1

/-- The indication of pitch a stem carries: its tier, when a downstep is in it. -/
def pitch (s : Stem) : Option RegisterTier :=
  if RegisterTier.bearing .downstep s.1.tier = [] then none else some s.1.tier

/-- Tonal by Hyman's definition (3): pitch enters the lexical realization of /ꜜkuɽe/
'end'. -/
theorem drubea_tonal : Hyman2006.Tonal pitch := ⟨⟨Drubea.kureEnd, by decide⟩, by decide⟩

/-! ### The postlexical derivation -/

/-- Utterance-initial neutralisation (§3.5, §4.5): the downstep on the first mora is left
unrealized, there being no preceding register to contrast with; the feature is not
deleted, so it still blocks h-epenthesis on its syllable. -/
def neutralizeInitial (tier : RegisterTier) : RegisterTier :=
  tier.modifyHead (·.filter (· ≠ TRN.downstep))

/-- Pre-downstep h-epenthesis within a syllable (§4.4): a registerless mora immediately
before a downstepped one takes `h`, the syllable's own downstep blocking the rule on the
morae after it; `next` is whether the following syllable begins downstepped. -/
def raiseMorae (next : Bool) : List (List TRN) → List (List TRN)
  | [] => []
  | [ns] => [if ns = [] ∧ next then [TRN.upstep] else ns]
  | ns :: ms :: rest =>
    if TRN.downstep ∈ ns then ns :: ms :: rest
    else (if ns = [] ∧ TRN.downstep ∈ ms then [TRN.upstep] else ns) :: raiseMorae next (ms :: rest)

/-- H-epenthesis over the syllables of an utterance. -/
def raiseSyllables : List (List (List TRN)) → List (List (List TRN))
  | [] => []
  | [a] => [raiseMorae false a]
  | a :: b :: rest => raiseMorae (TRN.downstep ∈ b.headD []) a :: raiseSyllables (b :: rest)

/-- H-epenthesis over a word. -/
def raise (r : Registered Syllable) : Registered Syllable :=
  ⟨r.syllables, (raiseSyllables (r.syllableNodes μ)).flatten⟩

/-- Spreading h-epenthesis ((16)): the raising extends leftward over the whole registerless
stretch before the downstep. -/
def hSpread : RegisterTier → RegisterTier
  | [] => []
  | ms :: rest =>
    match hSpread rest with
    | [] => [ms]
    | ns :: rest' =>
      (if ms = [] ∧ (TRN.downstep ∈ ns ∨ ns = [TRN.upstep]) then [TRN.upstep] else ms) ::
        ns :: rest'

/-- Downstep displacement (§4.6): the `l` on the last mora of a bimoraic syllable spreads to
the first mora of the next syllable and delinks, stacking on an `l` already there; `carry`
is the node arriving from the syllable before. -/
def displaceSyllables (carry : List TRN) : List (List (List TRN)) → List (List (List TRN))
  | [] => []
  | a :: rest =>
    let a' := match a with
      | first :: ms => (first ++ carry) :: ms
      | [] => []
    if 2 ≤ a'.length ∧ TRN.downstep ∈ a'.getLastD [] ∧ rest ≠ [] then
      (a'.dropLast ++ [(a'.getLastD []).erase TRN.downstep]) ::
        displaceSyllables [TRN.downstep] rest
    else a' :: displaceSyllables [] rest

/-- Displacement over a word. -/
def displace (r : Registered Syllable) : Registered Syllable :=
  ⟨r.syllables, (displaceSyllables [] (r.syllableNodes μ)).flatten⟩

/-- A boundary feature docks on the final mora. -/
def dockFinal (t : TRN) (r : Registered Syllable) : Registered Syllable :=
  ⟨r.syllables, r.tier.modify (r.tier.length - 1) (· ++ [t])⟩

/-- Drubea's final raising (§3.3, §4.8): h% docks on an utterance-final registerless
syllable. -/
def drubeaFinal (r : Registered Syllable) : Registered Syllable :=
  if r.IsRegisterless μ (r.syllables.length - 1) then dockFinal .upstep r else r

/-- The condition of Numèè's final lowering (§3.4, §4.8): a light final syllable after a
registerless syllable. -/
def NumeeFinalApplies (r : Registered Syllable) : Prop :=
  (r.shape μ).getLast? = some 1 ∧ 2 ≤ r.syllables.length ∧
    r.IsRegisterless μ (r.syllables.length - 2)

instance (r : Registered Syllable) : Decidable (NumeeFinalApplies r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Numèè's final lowering: l% docks when its condition holds, on a registerless and on a
downstepped final alike. -/
def numeeFinal (r : Registered Syllable) : Registered Syllable :=
  if NumeeFinalApplies r then dockFinal .downstep r else r

/-- The surface form of a morpheme sequence under the postlexical steps its transcription
shows, in order. -/
def derive (steps : List (Registered Syllable → Registered Syllable))
    (ws : List (Registered Syllable)) : Registered Syllable :=
  steps.foldl (fun r f ↦ f r) (concat ws)

/-- The baseline: level 4 of the 1-to-5 scale (§3.5). -/
def baseline : Int := 4

/-- The level each mora reaches, the utterance-initial downstep unrealized. -/
def realize (r : Registered Syllable) : List Int :=
  RegisterTier.realize baseline (neutralizeInitial r.tier)

/-- The level of each syllable: that of its last mora. -/
def syllableLevels (r : Registered Syllable) (levels : List Int) : List Int :=
  (((r.shape μ).scanl (· + ·) 0).tail).map fun e ↦ levels.getD (e - 1) 0

/-! ### Drubea utterances -/

open Drubea in
/-- (11) /ꜜɳi ꜜmwa ꜜɳii ꜜme/ 'They said that…': four downsteps terrace, the first
unrealized — [ɳi4 mwa3 ɳii2 me1]. -/
theorem ex11_levels : realize (derive [] [ni3pl, mwaPfv, niiSay, meThat]) = [4, 3, 2, 2, 1] := by
  decide

open Drubea in
/-- (19) /ꜜtaa dɪɪ bee/ 'one small fish': the initial downstep unrealized and no final
raising, everything at the baseline — [taa4 dɪɪ4 bee4]. -/
theorem ex19_levels : realize (derive [] [taaOne, diiSmall, beeFish]) = [4, 4, 4, 4, 4, 4] := by
  decide

open Drubea in
/-- (20) /ꜜtaa bee pwi + ꜛ%/ 'one cooked fish': h% raises the final registerless syllable —
[taa4 bee4 pwi5]. -/
theorem ex20_levels :
    realize (derive [drubeaFinal] [taaOne, beeFish, pwiCooked]) = [4, 4, 4, 4, 5] := by
  decide

open Drubea in
/-- (30) /ko te tɪɪ-ɽe kuɽe/ 'I look at the bush.': registerless throughout, the baseline
throughout — [ko4 te4 tɪɪ4 -ɽe4 kuɽe4]. -/
theorem ex30_levels :
    realize (derive [] [ko1sg, teDescr, tiiLook, reAct, kureForest]) = [4, 4, 4, 4, 4, 4, 4] := by
  decide

open Drubea in
/-- (32) vs (33), /goo ꜜmie/ 'wet Hibbertia' vs /ꜜgoo ꜜmie/ 'wet tree' (§3.5, §4.5): before
a downstep, an initial registerless syllable is raised above the baseline while a
downstepped one is not, its unrealized `l` blocking h-epenthesis; the following
downstepped syllable is lower than the initial in both. -/
theorem ex32_ex33_contrast :
    (∃ x ∈ realize (derive [raise] [gooHibbertia, mieWet]), baseline < x) ∧
      (∀ x ∈ realize (derive [raise] [gooTree, mieWet]), x ≤ baseline) ∧
      realize (derive [raise] [gooTree, mieWet]) = [4, 4, 3, 3] := by
  decide

open Drubea in
/-- (32) and (33) differ in h-epenthesis alone: the surface tiers of (64) and (65). -/
theorem ex32_ex33_tiers :
    (derive [raise] [gooHibbertia, mieWet]).tier = [[], [.upstep], [.downstep], []] ∧
      (derive [raise] [gooTree, mieWet]).tier = [[.downstep], [], [.downstep], []] := by
  decide

open Drubea in
/-- (53) /koꜜo kwɛ-ɽe/ 'place of dancing' vs /koꜜo ꜜkwe-ɽe/ 'place of eating' (§3.7, §4.6):
the CVꜜV downstep displaces onto the next syllable, a single downstep on registerless
/kwɛ/, a double one on downstepped /ꜜkwe/ — [koo5 kwɛ4] vs [koo5 kwe3]. -/
theorem ex53_displacement :
    (derive [displace, raise] [kooPlace, kweDance, reAct]).tier =
        [[], [.upstep], [.downstep], []] ∧
      (derive [displace, raise] [kooPlace, kweEat, reAct]).tier =
        [[], [.upstep], [.downstep, .downstep], []] ∧
      realize (derive [displace, raise] [kooPlace, kweDance, reAct]) = [4, 5, 4, 4] ∧
      realize (derive [displace, raise] [kooPlace, kweEat, reAct]) = [4, 5, 3, 3] := by
  decide

open Drubea in
/-- (46) /ɲi beꜜe ŋa-ɽe/ 'he doesn't work': undisplaced, /beꜜe/ raises its own first mora
and lowers its second, the register of what follows — [ɲi ꜛbeꜜe ŋa-ɽe]. -/
theorem ex46_undisplaced :
    (derive [raise] [ni3sg, beeNeg, ngaWork, reAct]).tier =
        [[], [.upstep], [.downstep], [], []] ∧
      realize (derive [raise] [ni3sg, beeNeg, ngaWork, reAct]) = [4, 5, 4, 4, 4] := by
  decide

/-- Register copying (§3.9, §4.7): a verbal classifier prefix takes the nodes of the verb's
first mora. -/
def copyPrefix (prefix_ verb : Registered Syllable) : Registered Syllable :=
  ⟨prefix_.syllables, prefix_.tier.map fun _ ↦ verb.tier.getD 0 []⟩

open Drubea in
/-- (56): /ʈa-uɽu/ 'cut by hand' stays registerless, /ʈa-ꜜtie/ 'tear by hand' becomes
/ꜜʈa-ꜜtie/. -/
theorem ex56_copy :
    (copyPrefix taHand uruCut).tier = [[]] ∧
      (copyPrefix taHand tieTear).tier = [[.downstep]] := by
  decide

open Drubea in
/-- (57) /ko te ʈa-ꜜtie-ɽe/ 'I tear by hand.': the copied downstep raises the preceding
marker and still drops before the verb — [ko4 te4.5 ʈa4 ti3 e3 -ɽe3], the model's raised
step a whole one. -/
theorem ex57_levels :
    realize (derive [raise] [ko1sg, teDescr, copyPrefix taHand tieTear, tieTear, reAct]) =
      [4, 5, 4, 3, 3, 3] := by
  decide

/-- (16): spreading h-epenthesis raises the whole registerless stretch before /maꜜa/'s
downstep, the two morae of /ŋe-ɽe/ and the first of /maꜜa/. -/
theorem hSpread_stretch :
    hSpread [[], [], [], [.downstep]] = [[.upstep], [.upstep], [.upstep], [.downstep]] := by
  decide

/-! ### Numèè utterances -/

open Numee in
/-- (24) /jaa ɲĩ + ꜜ%/ 'coconut juice': l% docks on the light registerless final and raises
the syllable before — [ɟaa5 ɲĩ4]. -/
theorem ex24_levels :
    NumeeFinalApplies (concat [jaaJuice, niCoconut]) ∧
      realize (derive [numeeFinal, raise] [jaaJuice, niCoconut]) = [4, 5, 4] := by
  decide

open Numee in
/-- (25) /jaa ꜜɲĩ + ꜜ%/ 'breast milk': on a downstepped final, l% stacks a second downstep,
realized below the registerless final of (24) — [ɟaa5 ɲĩ3.5]. -/
theorem ex25_double :
    (derive [numeeFinal, raise] [jaaJuice, niBreast]).tier =
        [[], [.upstep], [.downstep, .downstep]] ∧
      realize (derive [numeeFinal, raise] [jaaJuice, niBreast]) = [4, 5, 3] := by
  decide

open Numee in
/-- (26) /dɛɳʊ a mii + ꜜ%/ 'lower jaw': a heavy final blocks l% — [dɛ4 ɳʊ4 a4 mii4]. -/
theorem ex26_heavy_blocks :
    ¬ NumeeFinalApplies (concat [denuJaw, aRel, miiLow]) ∧
      realize (derive [numeeFinal] [denuJaw, aRel, miiLow]) = [4, 4, 4, 4, 4] := by
  decide

open Numee in
/-- (28) and (29): a downstepped syllable before the final blocks l%. -/
theorem ex28_ex29_after_downstep_blocks :
    ¬ NumeeFinalApplies (concat [teeGirl, eProx, noGrill, betiiThree, kuYam]) ∧
      ¬ NumeeFinalApplies (concat [ni3sg, yuuBerth, aLoc, paaUp, kweSand]) := by
  decide

open Numee in
/-- (38) /ꜜcĩĩbu ꜜmwã ꜜku mwoɽo + ꜜ%/ 'The rat escaped safe and sound.': l% on the final,
h-epenthesis before each downstep — [cĩĩ4 bu5 mwã4 ku3 mwo4 ɽo3]. -/
theorem ex38_levels :
    realize (derive [numeeFinal, raise] [ciibuRat, mwaPfv, kuFlee, mworoAlive]) =
      [4, 4, 5, 4, 3, 4, 3] := by
  decide

open Numee in
/-- (52) /yaꜜa ꜜmẽ geꜜe ꜜmẽ ɲaꜜi/ 'We will not arrive.' (§4.6): both CVꜜV downsteps
displace onto downstepped /ꜜmẽ/, a double downstep each time, while the disyllable
/ɲa.ꜜi/ keeps its own. -/
theorem ex52_double :
    (derive [displace, raise] [yaaNeg, meThat, gee1plExcl, meFut, nyaiArrive]).tier =
      [[], [.upstep], [.downstep, .downstep], [], [.upstep], [.downstep, .downstep],
        [.upstep], [.downstep]] := by
  decide

/-- (18) /ꜜɳe ꜜmwa ꜜve/ 'They go.' ((63)): h-epenthesis on a downstepped mora makes an `lh`
contour, the rise after the drop, which lifts the register the next downstep lowers. -/
theorem ex18_contour :
    RegisterTier.realize baseline
        (neutralizeInitial [[.downstep], [.downstep, .upstep], [.downstep]]) =
      [4, 4, 3] := by
  decide

/-! ### Leben's properties of downstep (§6.1)

[leben-2018]'s definitional properties, as the paper rephrases them for a system without
tones, are theorems above: the drop changes the register for what follows and affects the
whole following domain (`ex11_levels`, `ex46_undisplaced`), it is cumulative without limit
(`ex11_levels`, `terrace_append`), it is neutralised utterance-initially (`ex19_levels`,
`ex32_ex33_contrast`), and it functions contrastively, lexically (`stems_patterned` on the
minimal triplets). -/

/-! ### The rows -/

/-- The space-separated tokens of a character string. -/
def tokens : List Char → List (List Char)
  | [] => [[]]
  | ' ' :: cs => [] :: tokens cs
  | c :: cs =>
    match tokens cs with
    | t :: ts => (c :: t) :: ts
    | [] => [[c]]

/-- A pitch level in half steps, from the source's whole or half numeral. -/
def halfSteps? (cs : List Char) : Option ℕ := go cs [] where
  /-- The digits read so far, reversed. -/
  go : List Char → List Char → Option ℕ
    | [], acc => (LinguisticExample.digits? acc.reverse).map (2 * ·)
    | ['.', '5'], acc => (LinguisticExample.digits? acc.reverse).map (2 * · + 1)
    | '.' :: _, _ => none
    | c :: cs, acc => go cs (c :: acc)

/-- The levels a row transcribes, in half steps. -/
def levels? (e : LinguisticExample) : Option (List ℕ) :=
  (e.feature? "levels").bind fun s ↦ (tokens s.toList).mapM halfSteps?

/-- The direction of each step. -/
def signs (xs : List Int) : List Int := (xs.zip xs.tail).map fun p ↦ Int.sign (p.2 - p.1)

/-- The derivation of each levelled row's utterance from the fragments, under the steps its
surface transcription shows. The two transcriptions of (13) are left out: their drop within
/ꜜbeɽu/ is a half step of declination on a registerless syllable, not a register shift. -/
def derivations : List (Registered Syllable × LinguisticExample) :=
  [(derive [] [Drubea.ni3pl, Drubea.mwaPfv, Drubea.niiSay, Drubea.meThat], Examples.ex11),
    (derive [] [Drubea.taaOne, Drubea.diiSmall, Drubea.beeFish], Examples.ex19),
    (derive [drubeaFinal] [Drubea.taaOne, Drubea.beeFish, Drubea.pwiCooked], Examples.ex20),
    (derive [] [Drubea.ko1sg, Drubea.teDescr, Drubea.tiiLook, Drubea.reAct, Drubea.kureForest],
      Examples.ex30),
    (derive [raise] [Drubea.gooHibbertia, Drubea.mieWet], Examples.ex32),
    (derive [raise] [Drubea.gooTree, Drubea.mieWet], Examples.ex33),
    (derive [displace, raise] [Drubea.kooPlace, Drubea.kweDance, Drubea.reAct], Examples.ex53a),
    (derive [displace, raise] [Drubea.kooPlace, Drubea.kweEat, Drubea.reAct], Examples.ex53b),
    (derive [raise] [Drubea.ko1sg, Drubea.teDescr, copyPrefix Drubea.taHand Drubea.tieTear,
      Drubea.tieTear, Drubea.reAct], Examples.ex57),
    (derive [numeeFinal, raise] [Numee.denuJaw, Numee.aRel, Numee.naUp], Examples.ex22),
    (derive [numeeFinal, raise] [Numee.jaaJuice, Numee.niCoconut], Examples.ex24),
    (derive [numeeFinal, raise] [Numee.jaaJuice, Numee.niBreast], Examples.ex25),
    (derive [numeeFinal] [Numee.denuJaw, Numee.aRel, Numee.miiLow], Examples.ex26),
    (derive [raise] [Numee.teeGirl, Numee.eProx, Numee.noGrill, Numee.betiiThree, Numee.kuYam],
      Examples.ex28),
    (derive [numeeFinal, raise] [Numee.ciibuRat, Numee.mwaPfv, Numee.kuFlee, Numee.mworoAlive],
      Examples.ex38),
    (derive [displace, raise]
      [Numee.yaaNeg, Numee.meThat, Numee.gee1plExcl, Numee.meFut, Numee.nyaiArrive],
      Examples.ex52),
    (derive [raise] [Numee.gu2sg, Numee.capeRaise, Numee.panaaMast, Numee.koOn, Numee.nyuBoat,
      Numee.wiiDown, Numee.toThere], Examples.ex62)]

/-- Every derivation rises and falls between syllables exactly where the source's levels
do, over the tokens it levels. -/
theorem rows_signs :
    ∀ d ∈ derivations, ∀ ls ∈ levels? d.2,
      (signs (syllableLevels d.1 (realize d.1))).take (ls.length - 1) =
        signs (ls.map (↑)) := by
  decide

end Lionnet2025
