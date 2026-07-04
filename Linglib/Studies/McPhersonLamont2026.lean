import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
import Linglib.Phonology.OptimalityTheory.HarmonicSerialism
import Linglib.Phonology.Tone.Constraints
import Linglib.Phonology.Tone.Grammatical
import Linglib.Fragments.Poko.Tone
import Linglib.Phonology.Autosegmental.Floating
import Mathlib.Tactic.Linarith

/-!
# Poko postlexical tone requires serial, directional evaluation
[mcpherson-lamont-2026], *Phonology* 43, e1.

Poko postlexical tone (lexical data in `Fragments.Poko.Tone`) resists
global constraint evaluation: no ranking or weighting of the paper's
four faithfulness constraints derives both `/nān + rī^H + nā/` ('I ate
a pig') and `/kāk^H + rī^H/` ('his pig'), while directional Harmonic
Serialism ([lamont-2022b]) with `*FLOAT` evaluated left-to-right
converges on every attested form. All step witnesses are
`decide`-checked (no `sorry`).

## Main results

* `parallel_OT_inadequate` — the eq. 59 support is ERC-inconsistent
  (ranking paradox), with W/L patterns derived from candidate
  violation profiles via `ercOfProfiles`, not stipulated.
* `weighted_HG_inadequate` — the paper's weighting contradiction:
  `MAX(H)` cannot both exceed and fall below the summed weights of
  `{DEP(link)/H, MAX(M), MAX(link)/M}`.
* `Fig3.fig3_LR_converged` / `Fig3.fig3_RL_converged` — LR converges
  to attested `[kāk rī dō]`, RL to the wrong `*[kāk rī dó]` (fig. 3);
  `Fig3.parallel_optimum_three_way_tie` — count-based `*FLOAT` yields
  a divergent tie ([pruitt-2009]).
* `Eq21`–`Eq30` — further tableaux (eqs. 21, 22, 24, 27, 30): `*FALL`
  repair, `*CROWD` blocking, `*M◁L`-forced tautomorphemic docking.
-/

namespace McPhersonLamont2026

open OptimalityTheory
open Core.Optimization.Evaluation
open Constraints Autosegmental Poko Tone

/-! ### Candidates (eqs. 57, 58) -/

/-- Winner/loser candidate pairs from [mcpherson-lamont-2026] eqs. 57 and 58. -/
inductive Cand
  /-- (57c) winner of `/nān + rī^H + nā/`: rī's H docks rightward onto nā. -/
  | nanWinner
  /-- (57b) loser: the floating H deletes instead. -/
  | nanLoser
  /-- (58c) winner of `/kāk^H + rī^H/`: both floating Hs delete. -/
  | kakWinner
  /-- (58b) unattested MAX(H)-dominant winner: one H docks, one deletes. -/
  | kakLoser
  deriving DecidableEq

/-! ### Constraints (eq. 7, eq. 59 columns) -/

/-- `MAX(H)` (eq. 7c): one violation per H tone deleted by GEN. -/
def maxH : Constraint Cand :=
  fun
    | .nanWinner => 0   -- H docks rightward (preserved)
    | .nanLoser  => 1   -- H deleted
    | .kakWinner => 2   -- both Hs deleted
    | .kakLoser  => 1   -- one H docks, one deletes

/-- `DEP(link)/H` (eq. 7a): one violation per inserted H-associated link. -/
def depLinkH : Constraint Cand :=
  fun
    | .nanWinner => 1   -- new H link inserted (docking)
    | .nanLoser  => 0
    | .kakWinner => 0
    | .kakLoser  => 1

/-- `MAX(M)` (eq. 7c analogue): one violation per M tone deleted. -/
def maxM : Constraint Cand :=
  fun
    | .nanWinner => 1   -- M overwritten by docking H
    | .nanLoser  => 0
    | .kakWinner => 0
    | .kakLoser  => 1

/-- `MAX(link)/M` (eq. 7b analogue): one violation per deleted M-tone link. -/
def maxLinkM : Constraint Cand :=
  fun
    | .nanWinner => 1
    | .nanLoser  => 0
    | .kakWinner => 0
    | .kakLoser  => 1

/-- The eq. 59 columns; `*FLOAT` factored out per the paper's candidate restriction. -/
def ranking : List (Constraint Cand) := [maxH, depLinkH, maxM, maxLinkM]

abbrev numConstraints : Nat := 4

example : ranking.length = numConstraints := rfl

/-- Constraint indices in `ranking`. -/
abbrev maxHIdx       : Fin numConstraints := 0
abbrev depLinkHIdx   : Fin numConstraints := 1
abbrev maxMIdx       : Fin numConstraints := 2
abbrev maxLinkMIdx   : Fin numConstraints := 3

/-! ### Derived ERCs -/

/-- ERC of a winner/loser pair via `ercOfProfiles` ([prince-2002]). -/
private def ercFor (winner loser : Cand) : ERC numConstraints :=
  ercOfProfiles (buildViolationProfile ranking.get winner)
    (buildViolationProfile ranking.get loser)

/-- ERC for the `/nān + rī^H + nā/` winner-loser pair. -/
def ercA : ERC numConstraints := ercFor .nanWinner .nanLoser

/-- ERC for the `/kāk^H + rī^H/` winner-loser pair. -/
def ercB : ERC numConstraints := ercFor .kakWinner .kakLoser

/-- The ranking-paradox support. -/
def pokoSupport : List (ERC numConstraints) := [ercA, ercB]

/-- The derived `ercA` matches eq. 59 row a: `[W, L, L, L]`. -/
example : ercA maxHIdx = .W ∧ ercA depLinkHIdx = .L ∧
          ercA maxMIdx = .L ∧ ercA maxLinkMIdx = .L := by decide

/-- The derived `ercB` matches eq. 59 row b: `[L, W, W, W]`. -/
example : ercB maxHIdx = .L ∧ ercB depLinkHIdx = .W ∧
          ercB maxMIdx = .W ∧ ercB maxLinkMIdx = .W := by decide

/-! ### The ranking paradox (eq. 59) -/

/-- **Parallel OT cannot model Poko** (eq. 59): the derived support is ERC-inconsistent.
    Structural proof — `Equiv.Perm (Fin n)`'s `Fintype` doesn't kernel-reduce under `decide`. -/
theorem parallel_OT_inadequate : ¬ ERCSet.Consistent pokoSupport := by
  rintro ⟨r, hr⟩
  have hA := (ERC.satisfiedBy_iff_dominance r ercA).mp (hr ercA (by simp [pokoSupport]))
  have hB := (ERC.satisfiedBy_iff_dominance r ercB).mp (hr ercB (by simp [pokoSupport]))
  -- per-position decide: reduction through `ercOfProfiles` stalls on the quantified form
  have ercA_only_W_at_zero : ∀ (w : Fin numConstraints), ercA w = .W → w = 0 := by
    intro w hw
    match w, hw with
    | 0, _ => rfl
    | 1, h => exact absurd h (by decide)
    | 2, h => exact absurd h (by decide)
    | 3, h => exact absurd h (by decide)
  have hMAX_H_dominates : ∀ (l : Fin numConstraints), ercA l = .L →
      r.symm 0 < r.symm l := by
    intro l hl
    obtain ⟨w, hwW, hdom⟩ := hA l hl
    rw [ercA_only_W_at_zero w hwW] at hdom
    exact hdom
  have h01 : r.symm 0 < r.symm 1 := hMAX_H_dominates 1 (by decide)
  have h02 : r.symm 0 < r.symm 2 := hMAX_H_dominates 2 (by decide)
  have h03 : r.symm 0 < r.symm 3 := hMAX_H_dominates 3 (by decide)
  -- ercB's Ws sit at positions 1-3; each contradicts h01/h02/h03
  obtain ⟨w, hwW, hdom⟩ := hB 0 (by decide)
  have hw_dom : r.symm w < r.symm 0 := hdom
  match w, hwW with
  | 0, h => exact absurd h (by decide)
  | 1, _ => omega
  | 2, _ => omega
  | 3, _ => omega

/-! ### Weighted HG inadequacy -/

/-- **Weighted HG cannot model Poko**: `MAX(H)` must both exceed and undercut the other
    three weights' sum (paper p. 32) — no ℚ-weighting satisfies both. -/
theorem weighted_HG_inadequate :
    ¬ ∃ w : Fin numConstraints → ℚ,
        w maxHIdx > w depLinkHIdx + w maxMIdx + w maxLinkMIdx ∧
        w depLinkHIdx + w maxMIdx + w maxLinkMIdx > w maxHIdx := by
  rintro ⟨_, h₁, h₂⟩
  linarith

/-! ### Shared fig. 2 ranking -/

/-- Non-float tail of the fig. 2 ranking, in (60) column order. -/
private def rankingTail : List (Constraint Form) :=
  [ starCrowd 2, starTautDock,
    maxTone TRN.H, starFall, depLinkTone TRN.H, maxTone TRN.M, maxLinkTone TRN.M ]

/-- The fig. 2 ranking (fig. 3 subset); only `*FLOAT^→` is directional. -/
def stdRanking (n : ℕ) : List (Constraint Form) := haveTone :: starFloatBlock n ++ rankingTail

/-- Left-to-right directional HS over `stdRanking` — the paper's positive analysis. -/
def lrDerivation (input : Form) : HSDerivation Form where
  gen := FloatingForm.gen
  ranking := stdRanking input.upper.len

/-! ### Fig. 3: LR vs RL over `/kāk^H + rī^H + dō^H/` -/

namespace Fig3

/-- Fig. 3 input `/kāk^H + rī^H + dō^H/`: each M linked, each H floating. -/
def fig3Input : Form :=
  let stems : List Syll := [.kak, .ri, .do]
  FloatingForm.mkInput (stems.map seg) (stems.flatMap Syll.melody)
    (links := {(0, 0), (2, 1), (4, 2)})

/-- Directional-LR derivation (`*FLOAT^→`). -/
def derivationLR : HSDerivation Form := lrDerivation fig3Input

/-- Mirror under `*FLOAT^←` (`starFloatBlockRev`) — the wrong-form counterexample. -/
def derivationRL : HSDerivation Form where
  gen := FloatingForm.gen
  ranking := haveTone :: starFloatBlockRev fig3Input.upper.len ++ rankingTail

/-- The LR final form `[kāk rī dō]`: all floating Hs deleted (fig. 3 thick line). -/
def attestedForm : Form :=
  fig3Input
    |>.deleteTierElem 1   -- delete H-kak
    |>.deleteTierElem 3   -- delete H-ri
    |>.deleteTierElem 5   -- delete H-do

/-- The RL final form `*[kāk rī dó]` (fig. 3; RL evaluation as in the two-stem eq. 61). -/
def starredForm : Form :=
  fig3Input
    |>.deleteTierElem 5    -- step 1: delete H-do
    |>.insertLink 3 2  -- step 2: dock H-ri to do (TBU 2)
    |>.deleteTierElem 1    -- step 3: delete H-kak
    |>.deleteTierElem 4    -- step 4: delete M-do (repair *FALL contour)

/-! ### Step witnesses -/

/-- LR step 1: H-kāk deletes — *TAUTDOCK and *CROWD block its dockings (60b). -/
theorem fig3_LR_step1 :
    derivationLR.stepOptimum fig3Input = {fig3Input.deleteTierElem 1} := by decide

/-- LR step 2: H-rī deletes — *CROWD (right), no-crossing (left), *TAUTDOCK (own). -/
theorem fig3_LR_step2 :
    derivationLR.stepOptimum (fig3Input.deleteTierElem 1) =
      {(fig3Input.deleteTierElem 1).deleteTierElem 3} := by decide

/-- LR step 3: H-dō deletes. -/
theorem fig3_LR_step3 :
    derivationLR.stepOptimum ((fig3Input.deleteTierElem 1).deleteTierElem 3) =
      {((fig3Input.deleteTierElem 1).deleteTierElem 3).deleteTierElem 5} := by decide

/-- LR converges on `attestedForm`. -/
theorem fig3_LR_converged : derivationLR.Converged attestedForm := by decide

/-- RL step 1: the rightmost floating H (H-dō) deletes. -/
theorem fig3_RL_step1 :
    derivationRL.stepOptimum fig3Input = {fig3Input.deleteTierElem 5} := by decide

/-- RL step 2 — the wrong-form seed: H-rī docks onto the now-uncrowded dō. -/
theorem fig3_RL_step2 :
    derivationRL.stepOptimum (fig3Input.deleteTierElem 5) =
      {(fig3Input.deleteTierElem 5).insertLink 3 2} := by decide

/-- RL step 3: H-kāk deletes. -/
theorem fig3_RL_step3 :
    derivationRL.stepOptimum ((fig3Input.deleteTierElem 5).insertLink 3 2) =
      {((fig3Input.deleteTierElem 5).insertLink 3 2).deleteTierElem 1} := by decide

/-- RL step 4: *FALL repairs dō's HM contour; MAX(H) ≫ MAX(M) deletes the M. -/
theorem fig3_RL_step4 :
    derivationRL.stepOptimum (((fig3Input.deleteTierElem 5).insertLink 3 2).deleteTierElem 1) =
      {(((fig3Input.deleteTierElem 5).insertLink 3 2).deleteTierElem 1).deleteTierElem 4} := by decide

/-- RL converges on `starredForm`. -/
theorem fig3_RL_converged : derivationRL.Converged starredForm := by decide

/-- **The empirical asymmetry**: LR and RL converge to distinct surface forms. -/
theorem fig3_attested_neq_starred : attestedForm ≠ starredForm := by
  intro h
  exact absurd (congrArg FloatingForm.deletedTier h) (by decide)

/-! ### Regular HS: the divergent tie (eq. 62) -/

/-- Regular-HS derivation: same ranking with count-based `starFloatCount` for `*FLOAT`. -/
def derivationParallel : HSDerivation Form where
  gen := FloatingForm.gen
  ranking := haveTone :: starFloatCount :: rankingTail

/-- The divergent tie ([pruitt-2009]): the three single-deletion candidates all tie.
    (The paper's "no tie-breaker whatsoever helps" strengthening stays editorial.) -/
theorem parallel_optimum_three_way_tie :
    derivationParallel.stepOptimum fig3Input =
      {fig3Input.deleteTierElem 1, fig3Input.deleteTierElem 3, fig3Input.deleteTierElem 5} := by
  decide

/-- The regular-HS optimum has three elements. -/
theorem parallel_optimum_card_three :
    (derivationParallel.stepOptimum fig3Input).card = 3 := by decide

/-- The directional-LR optimum is a singleton. -/
theorem directional_LR_optimum_card_one :
    (derivationLR.stepOptimum fig3Input).card = 1 := by decide

/-- **Headline**: regular HS strictly underdetermines the step that directional HS decides. -/
theorem only_directional_disambiguates_fig3 :
    (derivationLR.stepOptimum fig3Input).card <
      (derivationParallel.stepOptimum fig3Input).card := by decide

end Fig3

/-! ### Eq. (24): LR with *FALL repair -/

namespace Eq24

/-- Eq. (24) input `/nãn + rī^H + nã/`; H-rī is the only floating tone. -/
def eq24Input : Form :=
  let stems : List Syll := [.nan, .ri, .na]
  FloatingForm.mkInput (stems.map seg) (stems.flatMap Syll.melody)
    (links := {(0, 0), (1, 1), (3, 2)})

/-- Directional-LR derivation over `stdRanking`. -/
def derivationLR : HSDerivation Form := lrDerivation eq24Input

/-- Attested `[nãn rī ná]`: H-rī docks onto nã, then *FALL repair deletes M-nã. -/
def attestedForm : Form :=
  eq24Input
    |>.insertLink 2 2      -- dock H-rī rightward to nã
    |>.deleteTierElem 3    -- delete M-nã (repair HM contour)

/-- Step 1: H-rī docks rightward onto nã (24d). -/
theorem eq24_step1 :
    derivationLR.stepOptimum eq24Input = {eq24Input.insertLink 2 2} := by decide

/-- Step 2: *FALL repair — M-nã deletes, MAX(H) ≫ MAX(M) (24g). -/
theorem eq24_step2 :
    derivationLR.stepOptimum (eq24Input.insertLink 2 2) =
      {(eq24Input.insertLink 2 2).deleteTierElem 3} := by decide

/-- LR converges on `attestedForm`. -/
theorem eq24_converged : derivationLR.Converged attestedForm := by decide

end Eq24

/-! ### Eq. (21): phrase-final floating-H deletion -/

namespace Eq21

/-- Eq. (21) input `/nãn + rī^H/` (phrase-final): no rightward landing site. -/
def eq21Input : Form :=
  let stems : List Syll := [.nan, .ri]
  FloatingForm.mkInput (stems.map seg) (stems.flatMap Syll.melody)
    (links := {(0, 0), (1, 1)})

/-- Directional-LR derivation; eq. (20)'s `*FLOAT, *TAUTDOCK ≫ MAX(H)` is a sub-ranking. -/
def derivationLR : HSDerivation Form := lrDerivation eq21Input

/-- Attested `[nãn rī]`: the floating H deletes. -/
def attestedForm : Form := eq21Input.deleteTierElem 2

/-- Step 1: H-rī deletes (21b). -/
theorem eq21_step1 :
    derivationLR.stepOptimum eq21Input = {eq21Input.deleteTierElem 2} := by decide

/-- LR converges on `attestedForm` (21d). -/
theorem eq21_converged : derivationLR.Converged attestedForm := by decide

end Eq21

/-! ### Eq. (27): *CROWD blocks docking onto an MH stem -/

namespace Eq27

/-- Eq. (27) input `/kāk^H + kǎ/`; kǎ carries a linked MH contour. -/
def eq27Input : Form :=
  let stems : List Syll := [.kak, .ka]
  FloatingForm.mkInput (stems.map seg) (stems.flatMap Syll.melody)
    (links := {(0, 0), (2, 1), (3, 1)})

/-- Directional-LR derivation over `stdRanking`. -/
def derivationLR : HSDerivation Form := lrDerivation eq27Input

/-- Attested `[kāk kǎ]`: H-kāk deletes; the MH contour survives. -/
def attestedForm : Form := eq27Input.deleteTierElem 1

/-- Step 1: H-kāk deletes — *CROWD blocks docking onto the two-tone kǎ (27b). -/
theorem eq27_step1 :
    derivationLR.stepOptimum eq27Input = {eq27Input.deleteTierElem 1} := by decide

/-- LR converges on `attestedForm` (27e). -/
theorem eq27_converged : derivationLR.Converged attestedForm := by decide

end Eq27

/-! ### Eq. (30): *M◁L forces tautomorphemic docking -/

namespace Eq30

/-- Eq. (30) input `/kāk^H + ìlí/`; ìlí carries a linked LH contour (L% omitted). -/
def eq30Input : Form :=
  let stems : List Syll := [.kak, .ili]
  FloatingForm.mkInput (stems.map seg) (stems.flatMap Syll.melody)
    (links := {(0, 0), (2, 1), (3, 1)})

/-- Eq. (30) ranking: `stdRanking` plus `*M◁L` above *TAUTDOCK — the inversion that
    licenses tautomorphemic docking (30c). -/
def eq30Ranking : List (Constraint Form) :=
  haveTone :: starMlessL :: starFloatBlock eq30Input.upper.len ++
    [ starCrowd 2, starTautDock,
      maxTone TRN.H, starFall, depLinkTone TRN.H,
      maxTone TRN.M, maxTone TRN.L, maxLinkTone TRN.M ]

def derivationLR : HSDerivation Form where
  gen := FloatingForm.gen
  ranking := eq30Ranking

/-- Attested `[kǎk ìlí]`: H-kāk docks onto its own TBU, making an MH contour. -/
def attestedForm : Form := eq30Input.insertLink 1 0

/-- Step 1: tautomorphemic dock — deletion would create M◁L tier adjacency (30c). -/
theorem eq30_step1 :
    derivationLR.stepOptimum eq30Input = {eq30Input.insertLink 1 0} := by decide

/-- LR converges despite the standing *TAUTDOCK violation (30e). -/
theorem eq30_converged : derivationLR.Converged attestedForm := by decide

end Eq30

/-! ### Eq. (22): HAVETONE drives docking onto a toneless stem -/

namespace Eq22

/-- Eq. (22a) input `/nãn + rī^H + ne/`; ne is toneless. -/
def eq22Input : Form :=
  let stems : List Syll := [.nan, .ri, .ne]
  FloatingForm.mkInput (stems.map seg) (stems.flatMap Syll.melody)
    (links := {(0, 0), (1, 1)})

/-- Directional-LR derivation over `stdRanking`. -/
def derivationLR : HSDerivation Form := lrDerivation eq22Input

/-- Attested `[nãn rī né]`: H-rī docks onto toneless ne. -/
def attestedForm : Form := eq22Input.insertLink 2 2

/-- Step 1: H-rī docks onto ne — HAVETONE prefers docking over deletion. -/
theorem eq22_step1 :
    derivationLR.stepOptimum eq22Input = {eq22Input.insertLink 2 2} := by decide

/-- LR converges on `attestedForm`. -/
theorem eq22_converged : derivationLR.Converged attestedForm := by decide

end Eq22

/-! ### Deferred: GEN shift and insert-and-associate ops, L% boundary tone, §§3.3–3.4 tableaux -/

end McPhersonLamont2026

/-! ### `FloatingForm` strictly extends the [rolle-2018] overwrite encoding -/

namespace Autosegmental

open Tone (TBU TRN)

/-- Embed a `tonalOverwrite` output into `FloatingForm`: one morpheme `m`, links `(i, i)`. -/
def FloatingForm.ofTBUList {S : Type*} (host : List (TBU S)) (m : Morpheme) :
    FloatingForm S TRN where
  lower := .ofList (host.map (fun tbu => { seg := tbu.seg, morpheme := m }))
  upper := .ofList (host.map (fun tbu => { value := tbu.tone, morpheme := m }))
  links := ((List.range host.length).map (fun i => (i, i))).toFinset
  deletedTier := ∅
  surfaceLinks := ((List.range host.length).map (fun i => (i, i))).toFinset

/-- Embedded forms carry at most one surface tone per TBU. -/
theorem FloatingForm.ofTBUList_linksTo_subsingleton {S : Type*}
    (host : List (TBU S)) (m : Morpheme) (i : SegIdx) :
    ((FloatingForm.ofTBUList host m).linksTo i).length ≤ 1 := by
  have h_all : ∀ k ∈ (FloatingForm.ofTBUList host m).linksTo i, k = i := by
    intro k hk
    unfold FloatingForm.linksTo at hk
    rw [List.mem_filter] at hk
    obtain ⟨_, hPred⟩ := hk
    have hMem : (k, i) ∈ (FloatingForm.ofTBUList host m).surfaceLinks :=
      of_decide_eq_true hPred
    unfold FloatingForm.ofTBUList at hMem
    rw [List.mem_toFinset, List.mem_map] at hMem
    obtain ⟨j, _, hPair⟩ := hMem
    have hjk : j = k := ((Prod.mk.injEq _ _ _ _).mp hPair).1
    have hji : j = i := ((Prod.mk.injEq _ _ _ _).mp hPair).2
    exact hjk.symm.trans hji
  have h_nodup : ((FloatingForm.ofTBUList host m).linksTo i).Nodup := by
    unfold FloatingForm.linksTo
    exact List.nodup_range.sublist List.filter_sublist
  have h_count_le : ((FloatingForm.ofTBUList host m).linksTo i).count i ≤ 1 :=
    List.nodup_iff_count_le_one.mp h_nodup i
  have h_count_eq : ((FloatingForm.ofTBUList host m).linksTo i).count i =
                    ((FloatingForm.ofTBUList host m).linksTo i).length :=
    List.count_eq_length.mpr (fun b hb => (h_all b hb).symm)
  omega

/-- A `FloatingForm` with two surface tones on one TBU — unreachable by `ofTBUList`. -/
theorem FloatingForm.exists_multi_tone_TBU :
    ∃ f : FloatingForm Unit TRN, ∃ i : SegIdx, 2 ≤ (f.linksTo i).length := by
  refine ⟨?_, 0, ?_⟩
  · exact
    { lower := .ofList [{ seg := (), morpheme := { form := "m" } }]
      upper :=
        .ofList [{ value := TRN.H, morpheme := { form := "m" } },
         { value := TRN.L, morpheme := { form := "m" } }]
      links := ∅
      deletedTier := ∅
      surfaceLinks := {(0, 0), (1, 0)} }
  · decide

end Autosegmental
