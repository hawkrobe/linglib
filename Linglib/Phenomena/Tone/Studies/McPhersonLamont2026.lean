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

-- ============================================================================
-- § 6.6: Regular HS Counter-Example — Divergent Ties
-- ============================================================================

/-! Paper, eq. (62) p. 35. The third leg of the @cite{mcpherson-lamont-2026}
    trifecta: parallel OT can't (ranking paradox §§1-5), weighted HG
    can't (§5), and **regular HS** (serial GEN with non-directional
    *FLOAT counting) can't either, because at step 1 from
    `/kāk^H + rī^H + dō^H/` the three single-H-deletion candidates all
    tie under count-based *FLOAT (each removes exactly one floating
    tone). MAX(H) and lower constraints don't disambiguate either —
    each candidate has identical violation profile. The optimum is a
    3-element set, so HS produces a "divergent tie"
    (@cite{pruitt-2009}): subsequent steps depend on which candidate
    is picked, and only the leftmost-deletion path reaches the
    attested form.

    The substrate proves this directly by switching `evalMode` on the
    fig.3 derivation from `.directional .leftToRight` to `.parallel`,
    and showing the optimum has 3 elements. The full fig.3 ranking
    (HAVETONE ≫ *FLOAT ≫ *CROWD ≫ *TAUTDOCK ≫ MAX(H) ≫ *FALL ≫
    DEP(link)/H ≫ MAX(M) ≫ MAX(link)/M) is preserved — only the EVAL
    semantics changes — confirming the paper's claim that ranking
    gymnastics alone cannot fix the divergence; only directional EVAL
    can.

    Beyond cardinality: the paper's broader claim is that ANY
    non-directional tie-breaker fails to consistently pick the
    leftmost-deletion path. Formalising "any tie-breaker" requires
    quantifying over `pick : Finset C → Option C`. The cardinality
    theorem here is the load-bearing fact (the optimum is genuinely
    underdetermined); the broader claim is editorial. -/

/-- Fig.3 ranking with `starFloatCount` substituted for `starFloat` —
    the count-based *FLOAT used in regular (non-directional) HS.
    Architectural note (per `starFloatCount` docstring): the substrate's
    parallel-vs-directional distinction lives in the *constraint*
    (count vs indicator), not the EVAL mode flag, so simply switching
    `evalMode := .parallel` while keeping the indicator-emitting
    `starFloat` would not change behaviour. The genuine "regular HS"
    counterpart of `derivationLR` requires a count-emitting *FLOAT. -/
def fig3RankingCount : List (DirectionalConstraint PokoForm) :=
  [ haveTone, Phonology.Tone.starFloatCount, starCrowd 2, starTautDock,
    maxTone TRN.H, starFall, depLinkTone TRN.H, maxTone TRN.M, maxLinkTone TRN.M ]

/-- The fig.3 derivation under regular HS (count-based *FLOAT, parallel
    EVAL). Same GEN as `derivationLR`; differs in ranking (`starFloat`
    → `starFloatCount`) and `evalMode`. -/
def derivationParallel : DirectionalHSDerivation PokoForm where
  gen := FloatingForm.gen
  ranking := fig3RankingCount
  evalMode := .parallel

/-- **The divergent tie**: under parallel *FLOAT, the three depth-1
    deletion candidates each remove exactly one floating tone, scoring
    identically on *FLOAT (count = 2). No higher-ranked or lower-ranked
    constraint distinguishes them, so all three are optimal. -/
theorem parallel_optimum_three_way_tie :
    derivationParallel.stepOptimum fig3Input =
      {fig3Input.deleteTone 1, fig3Input.deleteTone 3, fig3Input.deleteTone 5} := by
  decide

/-- Cardinality: the parallel optimum has exactly 3 elements. -/
theorem parallel_optimum_card_three :
    (derivationParallel.stepOptimum fig3Input).card = 3 := by decide

/-- Cardinality: the directional-LR optimum has exactly 1 element
    (recapping `fig3_LR_step1` at the cardinality level). -/
theorem directional_LR_optimum_card_one :
    (derivationLR.stepOptimum fig3Input).card = 1 := by decide

/-- **Headline (counter-example)**: regular HS strictly underdetermines
    the next step relative to directional HS. Combined with the
    negative-half theorems (§§1-5: parallel OT and weighted HG cannot
    model both `/nãn rī^H + nā/` and `/kāk^H + rī^H/`) and the
    positive-half theorem (§6 fig.3: directional LR converges to the
    attested form), this completes @cite{mcpherson-lamont-2026}'s
    trifecta argument: only directional Harmonic Serialism succeeds. -/
theorem only_directional_disambiguates_fig3 :
    (derivationLR.stepOptimum fig3Input).card <
      (derivationParallel.stepOptimum fig3Input).card := by decide

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

-- ============================================================================
-- § 8: Eq. (21) — Phrase-final floating-H deletion (smoke test)
-- ============================================================================

/-! Paper, eq. (21) p. 13. Input `/nãn + rī^H/` ('my pig'), no following
    stem. The floating H of rī cannot dock leftward (would cross the
    M-nãn link, blocked by autosegmental no-crossing) or tautomorphically
    (blocked by *TAUTDOCK). Only deletion remains. The simplest
    substantive case in the paper — 1 HS step + 1 fixed-point detection.
    Paper writes ranking as `*FLOAT, *TAUTDOCK ≫ MAX(H)` (eq. 20).

    The same substrate as fig. 3 / eq. (24) handles this case without
    modification. Tableau (21) candidates:
    - (21a) faithful: H still floating — *FLOAT violation
    - (21b) ☞ delete H — MAX(H) violation only; WINNER
    - (21c) tautomorphic dock H to rī — *TAUTDOCK + DEP(link)/H
    - (21d) the converged step from (21b) — fixed point

    Smoke-test value: confirms the substrate's simplest derivation
    works without depending on *CROWD, *FALL, or any of the
    fig. 3-specific machinery. -/

namespace Eq21

open Core.Constraint.OT
open Phonology.Autosegmental
open Phonology.Autosegmental.RegisterTier (TRN)
open Phonology.Tone (starFloat starTautDock starCrowd maxTone depLinkTone
                     maxLinkTone starFall haveTone)
open Fragments.Poko (Syll seg mTone hTone)

abbrev PokoForm := FloatingForm Syll

/-- Input form for eq. (21): `/nãn + rī^H/`. Tier order: `[M-nãn,
    M-rī, H-rī]`; H-rī is the only floating tone. No following stem
    (phrase-final), so the H has no rightward landing site. -/
def eq21Input : PokoForm :=
  FloatingForm.mkInput
    (segs := [seg .nan, seg .ri])
    (ulTones := [mTone .nan, mTone .ri, hTone .ri])
    (ulLinks := {(0, 0), (1, 1)})

/-- Same fig. 2 ranking as fig. 3 / eq. (24). Eq. (20)'s minimal
    statement `*FLOAT, *TAUTDOCK ≫ MAX(H)` is a sub-ranking of this. -/
def eq21Ranking : List (DirectionalConstraint PokoForm) :=
  [ haveTone, starFloat, starCrowd 2, starTautDock,
    maxTone TRN.H, starFall, depLinkTone TRN.H, maxTone TRN.M, maxLinkTone TRN.M ]

def derivationLR : DirectionalHSDerivation PokoForm where
  gen := FloatingForm.gen
  ranking := eq21Ranking
  evalMode := .directional .leftToRight

/-- Attested surface form `[nãn rī]` — H deleted, both lexical Ms
    intact and linked. -/
def attestedForm : PokoForm := eq21Input.deleteTone 2


/-- Eq. (21) step 1: H-rī (idx 2) deletes. Tautomorphic dock blocked
    by *TAUTDOCK; leftward dock to nãn blocked by no-crossing (would
    cross the M-rī to TBU-rī link); no rightward stem to dock onto.
    Paper, candidate (21b). -/
theorem eq21_step1 :
    derivationLR.stepOptimum eq21Input = {eq21Input.deleteTone 2} := by decide

/-- Eq. (21) convergence: from the post-deletion state, no GEN move
    improves on any constraint. Paper, candidate (21d). -/
theorem eq21_converged : derivationLR.Converged attestedForm := by decide

end Eq21

-- ============================================================================
-- § 9: Eq. (27) — *CROWD blocks rightward dock onto MH-toned stem
-- ============================================================================

/-! Paper, eq. (27) p. 16. Input `/kāk^H + kā/` ('his friend'), where
    the second stem `kā` has lexical /MH/ melody (M and H both linked
    to its single TBU). The floating H of `kāk` cannot dock rightward
    onto kā: docking would put a third tone on kā's TBU (own M, own H,
    plus docked H from kāk), violating *CROWD. Tautomorphic dock to
    kāk's own TBU is blocked by *TAUTDOCK. Only deletion remains.

    Empirical-substrate value: this isolates the *CROWD mechanism that
    makes fig. 3 work. In fig. 3 *CROWD blocks rightward docking
    because each stem already has 2 tones (M + own floating H). Eq.
    (27) shows the same blocking with a different tonal structure (MH
    contour on the receiving stem) — confirming *CROWD's per-morpheme
    counting handles both the floating-H case (fig. 3) and the
    contour case (here) without modification. Paper, candidate (27b). -/

namespace Eq27

open Core.Constraint.OT
open Phonology.Autosegmental
open Phonology.Autosegmental.RegisterTier (TRN)
open Phonology.Tone (starFloat starTautDock starCrowd maxTone depLinkTone
                     maxLinkTone starFall haveTone)
open Fragments.Poko (Syll seg mTone hTone)

abbrev PokoForm := FloatingForm Syll

/-- Input form for eq. (27): `/kāk^H + kā/`. Tier order: `[M-kāk,
    H-kāk, M-kā, H-kā]`. M-kāk linked to TBU 0 (kāk); M-kā and H-kā
    both linked to TBU 1 (kā), forming the lexical MH contour on kā.
    H-kāk is the only floating tone. -/
def eq27Input : PokoForm :=
  FloatingForm.mkInput
    (segs := [seg .kak, seg .ka])
    (ulTones := [mTone .kak, hTone .kak, mTone .ka, hTone .ka])
    (ulLinks := {(0, 0), (2, 1), (3, 1)})

/-- Same fig. 2 ranking as fig. 3 / eq. (24). The relevant constraints
    for eq. (27) are *FLOAT, *CROWD, *TAUTDOCK, MAX(H), DEP(link)/H. -/
def eq27Ranking : List (DirectionalConstraint PokoForm) :=
  [ haveTone, starFloat, starCrowd 2, starTautDock,
    maxTone TRN.H, starFall, depLinkTone TRN.H, maxTone TRN.M, maxLinkTone TRN.M ]

def derivationLR : DirectionalHSDerivation PokoForm where
  gen := FloatingForm.gen
  ranking := eq27Ranking
  evalMode := .directional .leftToRight

/-- Attested surface form `[kāk kā]` — H-kāk deleted; kā retains its
    lexical MH contour. -/
def attestedForm : PokoForm := eq27Input.deleteTone 1


/-- Eq. (27) step 1: H-kāk (idx 1) deletes. Tautomorphic dock to kāk
    blocked by *TAUTDOCK; rightward dock to kā blocked by *CROWD
    (would create 3 tones on kā's morpheme). Paper, candidate (27b). -/
theorem eq27_step1 :
    derivationLR.stepOptimum eq27Input = {eq27Input.deleteTone 1} := by decide

/-- Eq. (27) convergence: from the post-deletion state, no GEN move
    improves on any constraint. Paper, candidate (27e). -/
theorem eq27_converged : derivationLR.Converged attestedForm := by decide

end Eq27

-- ============================================================================
-- § 10: Eq. (30) — *M<L forces tautomorphic docking
-- ============================================================================

/-! Paper, eq. (30) p. 17. Input `/kāk^H + ìlí/` ('his bamboo'), where
    `ìlí` has lexical /LH/ melody. Without *M<L, the floating H of kāk
    would delete (it can't dock right onto ìlí without *CROWD violation
    on the LH stem, and tautomorphic dock costs *TAUTDOCK). With *M<L,
    the post-deletion form `M LH L%` has surface ML adjacency on the
    tier (M-kāk followed by L-ìlí), violating *M<L. Tautomorphic dock
    of H to kāk's TBU breaks the ML adjacency by creating an MH
    contour on kāk; surface is `M HLH L%`. *M<L ≫ *TAUTDOCK is the
    crucial ranking that makes this work.

    Substrate-substantive value: this is the first tableau requiring a
    constraint outside the fig. 3 ranking. *M<L (paper, eq. 29) was
    added to `Theories/Phonology/Tone/Constraints.lean` for this case.
    The *M<L analysis depends on the surviving-tier subsequence after
    deletions — exercising the substrate's `IsAlive`-filtered tier
    semantics (not just the surface link state). -/

namespace Eq30

open Core.Constraint.OT
open Phonology.Autosegmental
open Phonology.Autosegmental.RegisterTier (TRN)
open Phonology.Tone (starFloat starTautDock starCrowd maxTone depLinkTone
                     maxLinkTone starFall haveTone starMlessL)
open Fragments.Poko (Syll seg mTone hTone lTone)

abbrev PokoForm := FloatingForm Syll

/-- Input form for eq. (30): `/kāk^H + ìlí/`. Tier order: `[M-kāk,
    H-kāk, L-ìlí, H-ìlí]`. M-kāk linked to TBU 0, L-ìlí and H-ìlí
    both linked to TBU 1 (forming the LH lexical contour on ìlí).
    H-kāk is the only floating tone. We omit the L% boundary tone
    since it sits at the right edge and doesn't affect the *M<L
    M-then-L adjacency analysis here (L% comes after the existing L,
    and only M-then-L pairs trigger *M<L). -/
def eq30Input : PokoForm :=
  FloatingForm.mkInput
    (segs := [seg .kak, seg .ili])
    (ulTones := [mTone .kak, hTone .kak, lTone .ili, hTone .ili])
    (ulLinks := {(0, 0), (2, 1), (3, 1)})

/-- Eq. (30) ranking: `*M<L ≫ *FLOAT^→ ≫ *CROWD ≫ *TAUTDOCK ≫
    MAX(H) ≫ DEP(link)/H ≫ *FALL`. Note *M<L on top, ABOVE *TAUTDOCK
    — the inverted *TAUTDOCK position is what licences tautomorphic
    docking in this context (paper text: "this constraint outranks
    *TAUTDOCK, candidate (30c) with tautomorphic docking is selected
    as the output"). -/
def eq30Ranking : List (DirectionalConstraint PokoForm) :=
  [ haveTone, starMlessL, starFloat, starCrowd 2, starTautDock,
    maxTone TRN.H, starFall, depLinkTone TRN.H,
    maxTone TRN.M, maxTone TRN.L, maxLinkTone TRN.M ]

def derivationLR : DirectionalHSDerivation PokoForm where
  gen := FloatingForm.gen
  ranking := eq30Ranking
  evalMode := .directional .leftToRight

/-- Attested surface form `[kāk ìlí]` — H-kāk docked tautomorphically
    onto kāk's TBU (creating an MH contour on kāk), ìlí unchanged. -/
def attestedForm : PokoForm := eq30Input.insertLink 1 0


/-- Eq. (30) step 1: H-kāk (idx 1) docks tautomorphically to kāk's
    TBU. Deletion would leave M-kāk adjacent to L-ìlí on the tier,
    violating high-ranked *M<L. Rightward dock to ìlí blocked by
    *CROWD (would put 3 tones on ìlí: own L, own H, plus docked H).
    The MH contour created on kāk doesn't violate *M<L (the new H
    separates M from L). Paper, candidate (30c). -/
theorem eq30_step1 :
    derivationLR.stepOptimum eq30Input = {eq30Input.insertLink 1 0} := by decide

/-- Eq. (30) convergence: from the post-docking state, no GEN move
    improves on the active constraints. Note that the surface form
    has a *TAUTDOCK violation (the inserted (1, 0) link is
    tautomorphic), but eliminating it would require deleting H-kāk —
    which would re-introduce the *M<L violation. Paper, candidate
    (30e). -/
theorem eq30_converged : derivationLR.Converged attestedForm := by decide

end Eq30

-- ============================================================================
-- § 11: Eq. (22) — rightward dock onto toneless stem (HAVETONE drives docking)
-- ============================================================================

/-! Paper, eq. (22a) p. 13. Input `/nãn rī^H + ne/` ('I made a pig'),
    where `ne` is a toneless verb stem. The floating H of rī docks
    rightward onto ne — unlike the cases in fig. 3 / eq. (24) / eq.
    (27) where rightward docking is blocked, here `ne` is empty so
    *CROWD doesn't fire and *FALL has no contour to penalise. The
    novel mechanism: HAVETONE penalises ne's toneless surface, so
    docking the floating H onto ne is preferred even over deletion
    (which would leave ne tonal-empty).

    Empirical-substrate value: the **only** case in this study file
    where rightward docking is the winning move. Confirms the
    substrate's HAVETONE constraint actively drives docking when
    there's a toneless host available — distinct from the H-deletion
    cases where there isn't. -/

namespace Eq22

open Core.Constraint.OT
open Phonology.Autosegmental
open Phonology.Autosegmental.RegisterTier (TRN)
open Phonology.Tone (starFloat starTautDock starCrowd maxTone depLinkTone
                     maxLinkTone starFall haveTone)
open Fragments.Poko (Syll seg mTone hTone)

abbrev PokoForm := FloatingForm Syll

/-- Input form for eq. (22a): `/nãn + rī^H + ne/`. Tier order:
    `[M-nãn, M-rī, H-rī]`. M-nãn linked to TBU 0, M-rī linked to
    TBU 1; H-rī floating; TBU 2 (ne) starts toneless. -/
def eq22Input : PokoForm :=
  FloatingForm.mkInput
    (segs := [seg .nan, seg .ri, seg .ne])
    (ulTones := [mTone .nan, mTone .ri, hTone .ri])
    (ulLinks := {(0, 0), (1, 1)})

/-- Same fig. 2 ranking as fig. 3 / eq. (24). The relevant constraints
    are HAVETONE (drives docking onto ne), *FLOAT, *TAUTDOCK, MAX(H). -/
def eq22Ranking : List (DirectionalConstraint PokoForm) :=
  [ haveTone, starFloat, starCrowd 2, starTautDock,
    maxTone TRN.H, starFall, depLinkTone TRN.H, maxTone TRN.M, maxLinkTone TRN.M ]

def derivationLR : DirectionalHSDerivation PokoForm where
  gen := FloatingForm.gen
  ranking := eq22Ranking
  evalMode := .directional .leftToRight

/-- Attested surface form `[nãn rī né]` — H-rī docked rightward to TBU
    2 (ne), giving ne its only tone (H). -/
def attestedForm : PokoForm := eq22Input.insertLink 2 2

/-- Eq. (22a) step 1: H-rī (idx 2) docks rightward to ne (TBU 2).
    Tautomorphic dock to rī blocked by *TAUTDOCK; leftward dock to nãn
    blocked by no-crossing (would cross M-rī to TBU-rī link); deletion
    leaves ne toneless (HAVETONE violation). Rightward dock to ne
    leaves no contour (ne was toneless), so *FALL doesn't fire and
    HAVETONE is satisfied. -/
theorem eq22_step1 :
    derivationLR.stepOptimum eq22Input = {eq22Input.insertLink 2 2} := by decide

/-- Eq. (22a) convergence: from the post-docking state, no GEN move
    improves on any constraint. Each TBU has exactly one tone. -/
theorem eq22_converged : derivationLR.Converged attestedForm := by decide

end Eq22

-- ============================================================================
-- § 12: Substrate Scope — What This File Covers and What's Deferred
-- ============================================================================

/-! ### Coverage

§§1–5: **negative half** — parallel OT inadequacy (ranking paradox eq.
59), weighted HG inadequacy (page 32 inequality contradiction).

§6: **positive half** — fig. 3 LR/RL asymmetry over the autosegmental
substrate; LR converges to attested `[kāk rī dō]`, RL diverges to
starred `*[kāk rī dó]`. Includes §6.6 regular-HS divergent-tie
counter-example (`derivationParallel` with count-based `*FLOAT`).

§§7–11: additional tableaux exercising the substrate across the paper:
- §7 eq. 24: LR + *FALL repair (`/nãn rī^H + nã/` → `[nãn rī ná]`)
- §8 eq. 21: phrase-final H deletion (smoke test)
- §9 eq. 27: *CROWD blocks docking onto MH-toned host
- §10 eq. 30: *M<L forces tautomorphic dock against *TAUTDOCK
- §11 eq. 22: HAVETONE drives rightward dock onto toneless host

### Deferred

The substrate hosts the deepest faithful version of the paper's
central trifecta argument. Coverage extensions not in this file:

- **GEN op (6e) shift**: `shiftLink k i j` — moves an existing link's
  target from TBU `i` to TBU `j`. Paper's eq. (24j) is a shift
  candidate that loses; we don't currently generate it. ~20 LOC
  substrate addition.
- **GEN op (6d) insert+associate**: tone insertion (M-epenthesis used
  in §3.4 toneless-stem analyses). Adds tones not in `ulTones`,
  requires either a separate "epenthetic tones" list or relaxing the
  immutable-`ulTones` invariant.
- **Boundary tone L%**: currently omitted (sits at right edge after
  existing L tones, doesn't affect the M-then-L adjacency analyses
  here). Needed for paper §3.3 LH-rising-tone tableaux (eq. 33–50).
- **Other Hasse constraints**: `*LongTone`, `*L̃T̃<L`, `DEP(H)`,
  `DEP(M)`, `DEP(link)/L`, `DEP(link)/L%`. Marginal value for the
  central argument; needed for some §3.3 / §3.4 tableaux.
- **Paper §3.3 (rising tones)** and **§3.4 (toneless stems)**: full
  empirical coverage of these subsections. Each section adds 5+
  tableaux and several constraints. -/

end Phenomena.Tone.Studies.McPhersonLamont2026
