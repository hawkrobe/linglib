import Linglib.Core.Constraint.OT.Basic
import Linglib.Core.Constraint.OT.ERC
import Linglib.Core.Constraint.OT.HarmonicSerialism
import Linglib.Theories.Phonology.Tone.Constraints
import Linglib.Fragments.Poko.Tone
import Mathlib.Tactic.Linarith

/-!
# Poko postlexical tone requires serial, directional evaluation
@cite{mcpherson-lamont-2026}

McPherson, L. & Lamont, A. (2026). *Phonology* 43, e1.

Poko (Skou; Sandaun Province, Papua New Guinea) has three contrastive
tone levels (L, M, H) plus toneless syllables and floating tones.
@cite{mcpherson-lamont-2026} argue that the postlexical tone system
cannot be modelled by classical parallel Optimality Theory or weighted
Harmonic Grammar, but **does** yield to directional Harmonic Serialism
(@cite{lamont-2022b}). The argument has two halves:

1. **Negative**: parallel OT/HG is empirically inadequate. Four
   faithfulness constraints needed to derive both `/nān + rī^H + nā/`
   ('I ate a pig') and `/kāk^H + rī^H/` ('his pig') admit no consistent
   ranking — the support is ERC-inconsistent (paper, eq. 59). The
   ranking paradox carries over to weighted HG via a specific inequality
   contradiction: deriving the first form requires the weight of `MAX(H)`
   to *exceed* the sum of `{DEP(link)/H, MAX(M), MAX(link)/M}`, while
   deriving the second requires the weight of `MAX(H)` to be *less* than
   that sum (paper, page 32).

2. **Positive**: directional HS, with `*FLOAT` evaluated left-to-right,
   selects the leftmost-floating-H deletion at each derivational step
   and converges on the attested form. Right-to-left evaluation yields
   the wrong `*[kāk rī dó]` (paper, fig. 3); standard HS produces a
   divergent tie (@cite{pruitt-2009} sense — the term is from Pruitt's
   2009 manuscript, cited at fig. 3 caption).

The eq. 59 support uses only four of the ~20 constraints in the paper's
Hasse diagram (fig. 2) because the paradox comparison is restricted to
candidates that all satisfy `*FLOAT` (paper, page 31). Markedness
constraints `*FLOAT`, `*CROWD`, `*FALL`, `*TAUTDOCK`, `*M<L`, `OCP(L)`
etc. are active in the broader analysis but factored out of eq. 59 by
this candidate restriction.

## Scope of this file

§§1–5 ship the **negative half**: the ranking-paradox theorem (eq. 59)
plus the companion HG inadequacy theorem on rationals. The W/L pattern
is derived from candidate violation profiles via `ercOfProfiles`, not
stipulated as a hand-typed `Fin 4 → ERCVal`.

§6 ships the **positive half**: the full multi-step LR convergence on
fig. 3's `/kāk^H + rī^H + dō^H/` over an autosegmental `FloatingForm`
candidate type with the paper's full constraint ranking, plus the RL
counter-example showing it converges to a different surface form. All
step witnesses are `decide`-checked (no `sorry`).
-/

namespace Phenomena.Tone.Studies.McPhersonLamont2026

open Core.Constraint.OT
open Core.Constraint.Evaluation

-- ============================================================================
-- § 1: Candidates from paper, eqs. 57 and 58
-- ============================================================================

/-- Four candidates for the parallel-OT ranking-paradox argument: two
    attested-winner / unattested-loser pairs from
    @cite{mcpherson-lamont-2026} eqs. 57 and 58. -/
inductive Cand
  /-- (57c) Attested winner of `/nān + rī^H + nā/` ('I ate a pig').
      The floating H from `/rī^H/` docks rightward onto `nā`,
      overwriting its M tone (creating an MH contour link). Surface
      tones: M MH L% over nan-ri-na. -/
  | nanWinner
  /-- (57b) Loser candidate for `/nān + rī^H + nā/`. The floating H is
      deleted instead of docked. Surface: M M M L%. -/
  | nanLoser
  /-- (58c) Attested winner of `/kāk^H + rī^H/` ('his pig'). Both
      floating H tones are deleted. Surface: M M L%. -/
  | kakWinner
  /-- (58b) Predicted-but-unattested winner under MAX(H)-dominant
      ranking. The H from `/rī^H/` docks (preserving one H), the other
      deletes. Surface: M H L%. -/
  | kakLoser
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Constraints (paper, eqs. 7 + 59 columns)
-- ============================================================================

/-- `MAX(H)` (paper, eq. 7c): assign one violation for every H tone
    deleted by GEN. -/
def maxH : NamedConstraint Cand :=
  mkFaithGrad "MAX(H)" fun
    | .nanWinner => 0   -- H docks rightward (preserved)
    | .nanLoser  => 1   -- H deleted
    | .kakWinner => 2   -- both Hs deleted
    | .kakLoser  => 1   -- one H docks, one deletes

/-- `DEP(link)/H` (paper, eq. 7a): assign one violation for every
    autosegmental link inserted by GEN associated with an H tone. -/
def depLinkH : NamedConstraint Cand :=
  mkFaithGrad "DEP(link)/H" fun
    | .nanWinner => 1   -- new H link inserted (docking)
    | .nanLoser  => 0
    | .kakWinner => 0
    | .kakLoser  => 1

/-- `MAX(M)` (analog of paper eq. 7c for M tones): one violation per M
    tone deleted. -/
def maxM : NamedConstraint Cand :=
  mkFaithGrad "MAX(M)" fun
    | .nanWinner => 1   -- M overwritten by docking H
    | .nanLoser  => 0
    | .kakWinner => 0
    | .kakLoser  => 1

/-- `MAX(link)/M` (analog of paper eq. 7b for M tones): one violation
    per M-tone autosegmental link deleted. -/
def maxLinkM : NamedConstraint Cand :=
  mkFaithGrad "MAX(link)/M" fun
    | .nanWinner => 1
    | .nanLoser  => 0
    | .kakWinner => 0
    | .kakLoser  => 1

/-- The four-constraint ranking from @cite{mcpherson-lamont-2026} eq. 59,
    in column order. `*FLOAT` is factored out per the paper because the
    relevant comparisons restrict to `*FLOAT`-satisfying candidates. -/
def ranking : List (NamedConstraint Cand) := [maxH, depLinkH, maxM, maxLinkM]

abbrev numConstraints : Nat := 4

example : ranking.length = numConstraints := rfl

/-- Constraint indices in `ranking`. -/
abbrev maxHIdx       : Fin numConstraints := 0
abbrev depLinkHIdx   : Fin numConstraints := 1
abbrev maxMIdx       : Fin numConstraints := 2
abbrev maxLinkMIdx   : Fin numConstraints := 3

-- ============================================================================
-- § 3: ERCs derived from candidate violation profiles
-- ============================================================================

/-- Derived ERC for a winner/loser candidate pair under the eq. 59
    `ranking`, via `ercOfProfiles` (the canonical `ViolationProfile → ERC`
    bridge from @cite{prince-2002}). -/
private def ercFor (winner loser : Cand) : ERC numConstraints :=
  ercOfProfiles (mkProfile ranking winner) (mkProfile ranking loser)

/-- ERC for the `/nān + rī^H + nā/` winner-loser pair. **Derived** from
    the candidates' violation profiles, not stipulated. -/
def ercA : ERC numConstraints := ercFor .nanWinner .nanLoser

/-- ERC for the `/kāk^H + rī^H/` winner-loser pair. -/
def ercB : ERC numConstraints := ercFor .kakWinner .kakLoser

/-- The ranking-paradox support. -/
def pokoSupport : List (ERC numConstraints) := [ercA, ercB]

/-- **Sanity check**: the derived `ercA` matches paper eq. 59 row a,
    `[W, L, L, L]`. Computed by `decide` from the candidate violation
    counts above. -/
example : ercA maxHIdx = .W ∧ ercA depLinkHIdx = .L ∧
          ercA maxMIdx = .L ∧ ercA maxLinkMIdx = .L := by decide

/-- **Sanity check**: the derived `ercB` matches paper eq. 59 row b,
    `[L, W, W, W]`. -/
example : ercB maxHIdx = .L ∧ ercB depLinkHIdx = .W ∧
          ercB maxMIdx = .W ∧ ercB maxLinkMIdx = .W := by decide

-- ============================================================================
-- § 4: The Ranking Paradox (eq. 59)
-- ============================================================================

/-- **Parallel OT cannot model Poko (ranking paradox).**
    @cite{mcpherson-lamont-2026} eq. 59. The support of the four
    faithfulness constraints is ERC-inconsistent: no ranking simultaneously
    satisfies both ERCs. `ercA` requires `MAX(H) ≫ {DEP(link)/H, MAX(M),
    MAX(link)/M}`; `ercB` requires `{DEP(link)/H, MAX(M), MAX(link)/M}
    ≫ MAX(H)`. The two conditions are contradictory, so no permutation of
    these four constraints derives both attested forms.

    The W/L patterns are derived from candidate violation counts (above),
    so this theorem expresses an empirical claim about Poko candidates
    under named constraints, not a tautology over a hand-typed support.

    Proven structurally rather than by `decide`: mathlib's `Fintype`
    instance for `Equiv.Perm (Fin n)` is built via `Quot.lift` and does
    not reduce well under kernel `decide`, so the existential search over
    24 rankings stalls. -/
theorem parallel_OT_inadequate : ¬ ERCSet.consistent pokoSupport := by
  rintro ⟨r, hr⟩
  -- Both ERCs are satisfied by `r`.
  have hA : ercA.satisfiedBy r := hr ercA (by simp [pokoSupport])
  have hB : ercB.satisfiedBy r := hr ercB (by simp [pokoSupport])
  -- ercA: only W is at position 0 (MAX(H)). Verified per-position by
  -- `decide` on the derived ERC; can't `decide` the ∀ directly because
  -- reduction through `ercOfProfiles + mkProfile` stalls.
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
  -- ercB: position 0 is L, so some W in ercB dominates it. ercB has W at
  -- positions 1, 2, 3. Each case contradicts h01/h02/h03.
  obtain ⟨w, hwW, hdom⟩ := hB 0 (by decide)
  have hw_dom : r.symm w < r.symm 0 := hdom
  match w, hwW with
  | 0, h => exact absurd h (by decide)
  | 1, _ => omega
  | 2, _ => omega
  | 3, _ => omega

-- ============================================================================
-- § 5: Weighted Harmonic Grammar Inadequacy
-- ============================================================================

/-- **Weighted HG cannot model Poko either.** @cite{mcpherson-lamont-2026}
    page 32 makes the inequality contradiction explicit: deriving
    `/nān + rī^H + nā/` requires the weight of `MAX(H)` to exceed the sum
    of the other three faithfulness weights; deriving `/kāk^H + rī^H/`
    requires the weight of `MAX(H)` to be less than that sum. No
    rational (or real) weighting satisfies both.

    Encoded structurally: there is no weighting `w : Fin 4 → ℚ` such that
    `w MAX_H > w DEP_link_H + w MAX_M + w MAX_link_M` AND
    `w DEP_link_H + w MAX_M + w MAX_link_M > w MAX_H`. The two
    inequalities directly contradict, independent of positivity
    assumptions on the weights. -/
theorem weighted_HG_inadequate :
    ¬ ∃ w : Fin numConstraints → ℚ,
        w maxHIdx > w depLinkHIdx + w maxMIdx + w maxLinkMIdx ∧
        w depLinkHIdx + w maxMIdx + w maxLinkMIdx > w maxHIdx := by
  rintro ⟨_, h₁, h₂⟩
  linarith

-- ============================================================================
-- § 6: Positive Half — Multi-Step Fig. 3 (Autosegmental, Mathlib-Style)
-- ============================================================================

/-! Paper, fig. 3 with the full constraint inventory and faithful
    autosegmental candidate type. Builds on three substrate pieces:
    - `Phonology.Autosegmental.Floating` for `FloatingForm` + GEN
      (autosegmental rep with multi-tone TBUs, no-crossing GEN)
    - `Phonology.Tone.Constraints` for the generic constraint constructors
    - `Fragments.Poko.Tone` for Poko-specific syllables and morpheme IDs

    This is the **deepest** version of the paper's claim — not the §7
    simplified single-constraint demo. It proves the empirical
    asymmetry: LR converges to attested `[kāk rī dō]` (all H deleted);
    RL converges to wrong `*[kāk rī dó]` (H of rī docks rightward to
    dō). The two final forms are distinct.

    ## Why the substrate is rich enough

    The paper's argument hinges on three substrate facts:
    1. *CROWD penalises stems with > 2 tones (own M + own floating H +
       docked H). Requires multi-tone TBUs.
    2. *TAUTDOCK penalises GEN-inserted same-morpheme docking. Requires
       morpheme IDs on tones and TBUs, plus underlying-link tracking.
    3. The no-crossing-association principle (Goldsmith 1976)
       restricts GEN to non-crossing link insertions. Required to
       block `dock-H-ri-to-kak` (which would cross the M-ri to TBU-ri
       link) — without it, RL would not reach the wrong form. -/

namespace Fig3

open Core.Constraint.OT
open Phonology.Autosegmental
open Phonology.Autosegmental.RegisterTier (TRN)
open Phonology.Tone (starFloat starTautDock starCrowd maxTone depLinkTone
                     maxLinkTone starFall haveTone)
open Fragments.Poko (Syll seg mTone hTone)

abbrev PokoForm := FloatingForm Syll

-- ============================================================================
-- § 6.1: Input
-- ============================================================================

/-- Input form for paper fig. 3: `/kāk^H + rī^H + dō^H/`.

    Tier order (`ulTones`): `[M-kak, H-kak, M-ri, H-ri, M-do, H-do]`.
    Each stem contributes its lexical M (linked to its TBU) and its
    floating H (no underlying link). -/
def fig3Input : PokoForm :=
  FloatingForm.mkInput
    (segs := [seg .kak, seg .ri, seg .do])
    (ulTones := [mTone .kak, hTone .kak, mTone .ri, hTone .ri, mTone .do, hTone .do])
    (ulLinks := {(0, 0), (2, 1), (4, 2)})

-- ============================================================================
-- § 6.2: Ranking
-- ============================================================================

/-- Constraint ranking from paper, fig. 2 (relevant subset for fig. 3).
    Order matches the (60) tableau columns:
    `HAVETONE ≫ *FLOAT^→ ≫ *CROWD(2) ≫ *TAUTDOCK ≫ MAX(H) ≫ *FALL ≫
    DEP(link)/H ≫ MAX(M) ≫ MAX(link)/M`.

    `*FLOAT` is the only genuinely directional constraint (left-to-right
    per paper §4); the rest are parallel-via-singleton. -/
def fig3Ranking : List (DirectionalConstraint PokoForm) :=
  [ haveTone, starFloat, starCrowd 2, starTautDock,
    maxTone TRN.H, starFall, depLinkTone TRN.H, maxTone TRN.M, maxLinkTone TRN.M ]

/-- DirectionalHSDerivation under `*FLOAT^→` (left-to-right). The
    paper's positive analysis. -/
def derivationLR : DirectionalHSDerivation PokoForm where
  gen := FloatingForm.gen
  ranking := fig3Ranking
  evalMode := .directional .leftToRight

/-- Mirror under `*FLOAT^←` (right-to-left). The paper's negative
    counterexample: yields the wrong surface form. -/
def derivationRL : DirectionalHSDerivation PokoForm :=
  { derivationLR with evalMode := .directional .rightToLeft }

-- ============================================================================
-- § 6.3: Attested LR Final Form
-- ============================================================================

/-- The attested surface form `[kāk rī dō]` (all H deleted, no docking).
    All three floating Hs (tier indices 1, 3, 5) are deleted; the
    underlying M-to-TBU links survive. Per paper, fig. 3 thick-line
    derivation. -/
def attestedForm : PokoForm :=
  fig3Input
    |>.deleteTone 1   -- delete H-kak
    |>.deleteTone 3   -- delete H-ri
    |>.deleteTone 5   -- delete H-do

/-- The starred surface form `*[kāk rī dó]` (H surfaces on dō).
    The RL derivation is 4 substantive steps:
    1. delete H-dō (idx 5, rightmost float)
    2. dock H-rī rightward to dō (idx 3 → TBU 2; now possible because
       dō has only M after step 1)
    3. delete H-kāk (idx 1, only remaining float)
    4. delete M-dō (idx 4) — **the *FALL repair step**: docking H-rī
       to dō created the falling-contour HM (in tier order, idx 3 H
       precedes idx 4 M); high-ranked *FALL forces deletion of one of
       the contour tones, and *MAX(H) ≫ MAX(M) selects the M for
       deletion.
    Final state: kāk surfaces with M, rī with M, dō with H alone (M
    deleted) — exactly the paper's `*[kāk rī dó]` per eq. (61) and
    fig. 3. -/
def starredForm : PokoForm :=
  fig3Input
    |>.deleteTone 5    -- step 1: delete H-do
    |>.insertLink 3 2  -- step 2: dock H-ri to do (TBU 2)
    |>.deleteTone 1    -- step 3: delete H-kak
    |>.deleteTone 4    -- step 4: delete M-do (repair *FALL contour)

-- ============================================================================
-- § 6.4: Per-Step Convergence Witnesses
-- ============================================================================

/-! Each LR/RL step's optimum is a singleton equality, proved by
    `decide`. Reduction works because `linksTo`, `haveTone`, `*FALL`,
    and `MAX(t)` were carefully implemented with `List.range`/`countP`
    and `(k, i) ∈ surfaceLinks` membership rather than
    `Finset.filter`/`Finset.image`/`Finset.sort`/`Finset.card`
    pipelines that don't reduce structurally in the Lean kernel. -/

set_option maxHeartbeats 4000000

-- ----- LR step witnesses -----

/-- LR step 1: leftmost H (idx 1, kak's H) cannot dock leftward
    (tautomorphic, blocked by *TAUTDOCK) or rightward (rī already has
    2 tones — own M + own floating H — adding kak's H gives 3,
    blocked by *CROWD); only deletion works. Paper, eq. (60b). -/
theorem fig3_LR_step1 :
    derivationLR.stepOptimum fig3Input = {fig3Input.deleteTone 1} := by decide

/-- LR step 2: from state with H-kak deleted, *FLOAT^→ addresses the
    next floating H (rī's, idx 3). Rightward docking to dō blocked by
    *CROWD; leftward docking to kak blocked by autosegmental
    no-crossing (would cross the M-rī to TBU-rī link); tautomorphic
    blocked by *TAUTDOCK. Deletion wins. -/
theorem fig3_LR_step2 :
    derivationLR.stepOptimum (fig3Input.deleteTone 1) =
      {(fig3Input.deleteTone 1).deleteTone 3} := by decide

/-- LR step 3: only H-dō (idx 5) remains floating. Cannot dock
    tautomorphically (*TAUTDOCK); cannot dock leftward (no-crossing
    through M-do link). Deletion wins. -/
theorem fig3_LR_step3 :
    derivationLR.stepOptimum ((fig3Input.deleteTone 1).deleteTone 3) =
      {((fig3Input.deleteTone 1).deleteTone 3).deleteTone 5} := by decide

/-- LR convergence: from the all-deletion state, GEN produces only the
    faithful candidate, so the optimum equals the input — fixed point. -/
theorem fig3_LR_converged : derivationLR.Converged attestedForm := by decide

-- ----- RL step witnesses -----

/-- RL step 1: rightmost H (idx 5, dō's H) wins under *FLOAT^← because
    its violation is at the rightmost position. Tautomorphic dock-5-to-2
    blocked by *TAUTDOCK; non-tautomorphic dockings of dō's H blocked
    by no-crossing. Deletion wins. -/
theorem fig3_RL_step1 :
    derivationRL.stepOptimum fig3Input = {fig3Input.deleteTone 5} := by decide

/-- RL step 2 — **the wrong-form-seeding step**: from state with H-dō
    deleted, *FLOAT^← addresses next rightmost floating H (rī's, idx 3).
    Now `dock-3-to-2` (rī's H to dō) is allowed: dō has only M after
    step 1 deletes its own H, so morpheme 2 has tones {3, 4} = 2,
    satisfying *CROWD. MAX(H) prefers docking over deletion (preserves
    the H), and DEP(link)/H is ranked low enough not to block it. -/
theorem fig3_RL_step2 :
    derivationRL.stepOptimum (fig3Input.deleteTone 5) =
      {(fig3Input.deleteTone 5).insertLink 3 2} := by decide

/-- RL step 3: only H-kak (idx 1) remains floating. Tautomorphic
    blocked; non-tautomorphic dockings blocked by no-crossing through
    the new (3, 2) link. Deletion wins. -/
theorem fig3_RL_step3 :
    derivationRL.stepOptimum ((fig3Input.deleteTone 5).insertLink 3 2) =
      {((fig3Input.deleteTone 5).insertLink 3 2).deleteTone 1} := by decide

/-- RL step 4 — **the *FALL repair step**: after step 2 docked H-rī to
    dō and step 3 deleted H-kāk, dō has the contour [H idx 3, M idx 4]
    in tier order (HM = falling). High-ranked *FALL forces deletion of
    one tone; MAX(H) ≫ MAX(M) selects M for deletion. Falls out of
    the substrate without per-step intervention. -/
theorem fig3_RL_step4 :
    derivationRL.stepOptimum (((fig3Input.deleteTone 5).insertLink 3 2).deleteTone 1) =
      {(((fig3Input.deleteTone 5).insertLink 3 2).deleteTone 1).deleteTone 4} := by decide

/-- RL convergence: with the *FALL contour repaired (M-dō deleted), no
    further GEN move improves on any constraint. Each TBU has exactly
    one tone (kāk: M-kāk linked, rī: M-rī linked, dō: H-rī docked
    only); deleting any creates a *HAVETONE violation. Fixed point. -/
theorem fig3_RL_converged : derivationRL.Converged starredForm := by decide

-- ============================================================================
-- § 6.5: Headline Theorem — The Empirical Asymmetry
-- ============================================================================

/-- **State-level asymmetry**: the LR final state `attestedForm`
    `[kāk rī dō]` and the RL final state `starredForm` `*[kāk rī dó]`
    are NOT equal. They differ on `deletedTones` (LR {1, 3, 5}; RL
    {1, 5}) and on `surfaceLinks` (RL has the extra rightward dock
    (3, 2)).

    Combined with the per-step witnesses (§ 6.4), this is the deepest
    version of @cite{mcpherson-lamont-2026}'s fig. 3 claim:
    directional EVAL must be left-to-right (LR) to derive the attested
    Poko surface form; right-to-left (RL) yields a different surface
    form. -/
theorem fig3_attested_neq_starred : attestedForm ≠ starredForm := by
  intro h
  exact absurd (congrArg FloatingForm.deletedTones h) (by decide)

end Fig3

-- ============================================================================
-- § 7: Eq. (24) — LR with *FALL repair (`/nãn rī^H + nã/`)
-- ============================================================================

/-! Paper, eq. (24) p. 14. Input `/nãn + rī^H + nã/` ('I ate a pig').
    Three syllables, three morphemes; rī's floating H docks rightward
    onto nã (creating an HM contour), then the substrate repairs the
    contour by deleting M-nã (because MAX(H) ≫ MAX(M)). Three-step LR
    derivation:

    1. Step 1: dock H-rī to nã (idx 2 → TBU 2). Tautomorphic dock to rī
       blocked by *TAUTDOCK; no-crossing blocks dock-to-nãn. Deletion
       loses to docking on MAX(H) (paper analysis: "(24d) is optimal,
       despite its falling contour tone").
    2. Step 2: delete M-nã (idx 3) — **the *FALL repair step**. The
       step-1 docking creates the tier-order pair [H, M] on TBU 2, a
       falling HM contour penalised by *FALL. MAX(H) ≫ MAX(M) selects
       M for deletion. Paper: "(24g) is optimal".
    3. Step 3: converged. nã has H alone (linked from idx 2); no GEN
       move improves on any constraint (haveTone blocks deletion of
       any of the surviving linked tones).

    This is the LR analogue of fig. 3's RL counter-example: same *FALL
    repair pattern, but here it produces the *attested* form rather
    than a starred one. Validates that the substrate's *FALL machinery
    isn't tuned to just one direction. -/

namespace Eq24

open Core.Constraint.OT
open Phonology.Autosegmental
open Phonology.Autosegmental.RegisterTier (TRN)
open Phonology.Tone (starFloat starTautDock starCrowd maxTone depLinkTone
                     maxLinkTone starFall haveTone)
open Fragments.Poko (Syll seg mTone hTone)

abbrev PokoForm := FloatingForm Syll

/-- Input form for eq. (24): `/nãn + rī^H + nã/`. Tier order
    (`ulTones`): `[M-nãn, M-rī, H-rī, M-nã]`. The H of rī is the only
    floating tone. -/
def eq24Input : PokoForm :=
  FloatingForm.mkInput
    (segs := [seg .nan, seg .ri, seg .na])
    (ulTones := [mTone .nan, mTone .ri, hTone .ri, mTone .na])
    (ulLinks := {(0, 0), (1, 1), (3, 2)})

/-- Same ranking as fig. 3 (paper, fig. 2 Hasse): `HAVETONE ≫
    *FLOAT^→ ≫ *CROWD ≫ *TAUTDOCK ≫ MAX(H) ≫ *FALL ≫ DEP(link)/H ≫
    MAX(M) ≫ MAX(link)/M`. -/
def eq24Ranking : List (DirectionalConstraint PokoForm) :=
  [ haveTone, starFloat, starCrowd 2, starTautDock,
    maxTone TRN.H, starFall, depLinkTone TRN.H, maxTone TRN.M, maxLinkTone TRN.M ]

def derivationLR : DirectionalHSDerivation PokoForm where
  gen := FloatingForm.gen
  ranking := eq24Ranking
  evalMode := .directional .leftToRight

/-- Attested surface form `[nãn rī ná]` — H of rī docked to nã, M of
    nã deleted by *FALL repair. -/
def attestedForm : PokoForm :=
  eq24Input
    |>.insertLink 2 2  -- step 1: dock H-rī rightward to nã
    |>.deleteTone 3    -- step 2: delete M-nã (repair HM contour)

set_option maxHeartbeats 4000000

/-- Eq. (24) step 1: H-rī docks rightward to nã. Tautomorphic dock
    blocked by *TAUTDOCK; no-crossing blocks leftward dock; deletion
    loses to docking on MAX(H). Paper, candidate (24d). -/
theorem eq24_step1 :
    derivationLR.stepOptimum eq24Input = {eq24Input.insertLink 2 2} := by decide

/-- Eq. (24) step 2: M-nã deletes to repair the HM contour created by
    step 1. *FALL fires on TBU 2's [H, M] tier sequence; MAX(H) ≫
    MAX(M) selects M for deletion. Paper, candidate (24g). -/
theorem eq24_step2 :
    derivationLR.stepOptimum (eq24Input.insertLink 2 2) =
      {(eq24Input.insertLink 2 2).deleteTone 3} := by decide

/-- Eq. (24) convergence: from the post-repair state, no GEN move
    improves on any constraint — the only remaining moves are
    deletions of surviving linked tones (each blocked by haveTone). -/
theorem eq24_converged : derivationLR.Converged attestedForm := by decide

end Eq24

end Phenomena.Tone.Studies.McPhersonLamont2026
