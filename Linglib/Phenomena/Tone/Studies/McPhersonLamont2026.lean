import Linglib.Core.Constraint.OT.Basic
import Linglib.Core.Constraint.OT.ERC
import Linglib.Core.Constraint.OT.HarmonicSerialism
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

This file ships the **negative half** only — the ranking-paradox theorem
plus the companion HG inadequacy theorem on rationals. The directional-HS
positive demonstration on the `/kāk^H + rī^H + dō^H/ → [kāk rī dō]`
derivation, the autosegmental floating-tone extension, and the full
Hasse diagram (paper, fig. 2) are deferred to a follow-up study file
once a `DirectionalTableau` consumer materialises in the substrate.

## Derivation discipline

The W/L pattern in eq. 59 is **derived from candidate violation profiles**
via the canonical `ercOfProfiles` bridge from `Core.Constraint.OT.ERC`,
not stipulated as a hand-typed `Fin 4 → ERCVal`. Candidates and their
violation counts are encoded directly from paper, eq. 57 and eq. 58.
This makes the theorem genuinely about *constraint behavior on
candidates* rather than about the W/L matrix per se.
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
-- § 6: Positive Half — Vanilla HS Convergence on Tableau (21)
-- ============================================================================

/-! Paper, eq. 21 page 13. Input `/nān + rī^H/` ('my pig'). The floating
    H tone fails to dock leftward (would violate `*TAUTDOCK` since `rī`
    is the morpheme that introduced the floating H — paper, eq. 15) and
    cannot dock rightward (no following stem in this phrase-final form),
    so it deletes. Vanilla parallel HS converges in 1 substantive step
    under the ranking `*FLOAT, *TAUTDOCK ≫ MAX(H)` (paper, eq. 20). This
    is the simplest non-trivial HS demonstration in the paper and the
    first real consumer of the `HSDerivation` substrate beyond the
    Core/ smoke test. -/

namespace Tableau21

open Core.Constraint.OT

/-- Three candidates for the single-floating-H deletion derivation. -/
inductive Cand21
  /-- Faithful input: `M M L%` with floating H (between M and L%).
      Violates `*FLOAT` (one floating tone). -/
  | input
  /-- Floating H deleted: `M M L%`. Violates `MAX(H)` (one H deleted). -/
  | deleted
  /-- Floating H docked tautomorphically onto `rī` (the stem that
      introduced it), creating an MH contour. Violates `*TAUTDOCK` (paper,
      eq. 15) and `DEP(link)/H` (one new H link). -/
  | dockedTauto
  deriving DecidableEq, Repr

/-- Ordering for `Finset.min'`. The order is incidental — it just fixes
    which element of a tied optimal set the tie-breaker returns. -/
def Cand21.toNat : Cand21 → Nat
  | .input => 0
  | .deleted => 1
  | .dockedTauto => 2

instance : LinearOrder Cand21 := LinearOrder.lift' Cand21.toNat
  (fun a b h => by cases a <;> cases b <;> simp_all [Cand21.toNat])

-- Constraints from paper, eqs. 7, 15, 16. Names are local to `Tableau21`.

/-- `*FLOAT` (paper, eq. 16): one violation per tone not associated to a syllable. -/
def floatStar : NamedConstraint Cand21 := mkMarkGrad "*FLOAT" fun
  | .input => 1
  | .deleted => 0
  | .dockedTauto => 0

/-- `*TAUTDOCK` (paper, eq. 15, after Wolf 2007): one violation per
    tautomorphemic docking of an underlyingly floating tone. -/
def tautDockStar : NamedConstraint Cand21 := mkMarkGrad "*TAUTDOCK" fun
  | .input => 0
  | .deleted => 0
  | .dockedTauto => 1

/-- `MAX(H)` for the demo (cf. paper, eq. 7c). -/
def maxH : NamedConstraint Cand21 := mkFaithGrad "MAX(H)" fun
  | .input => 0
  | .deleted => 1
  | .dockedTauto => 0

/-- `DEP(link)/H` for the demo (cf. paper, eq. 7a). -/
def depLinkH : NamedConstraint Cand21 := mkFaithGrad "DEP(link)/H" fun
  | .input => 0
  | .deleted => 0
  | .dockedTauto => 1

/-- Ranking from paper eq. 20: `*FLOAT, *TAUTDOCK ≫ MAX(H)`. The
    `DEP(link)/H` constraint sits below MAX(H); `(*FLOAT, *TAUTDOCK)` are
    co-dominant since the comparison only requires both to outrank
    `MAX(H)`. -/
def ranking : List (NamedConstraint Cand21) :=
  [floatStar, tautDockStar, maxH, depLinkH]

/-- One-step GEN. Models the relevant atomic operations from paper
    eq. 6: tone deletion, autosegmental link insertion. -/
def gen : Cand21 → Finset Cand21
  | .input => {.input, .deleted, .dockedTauto}
  | .deleted => {.deleted}
  | .dockedTauto => {.dockedTauto, .deleted}

/-- The Poko HS derivation for tableau (21). -/
def derivation : HSDerivation Cand21 :=
  { gen := gen, ranking := ranking }

/-- One HS step from the input picks the H-deletion candidate as the
    unique optimum: under `*FLOAT, *TAUTDOCK ≫ MAX(H)`, the faithful
    input fatally violates `*FLOAT` and the docking candidate fatally
    violates `*TAUTDOCK`, leaving only `.deleted`. -/
theorem step1_stepOptimum_is_deleted : derivation.stepOptimum .input = {.deleted} := by
  decide

/-- The H-deleted form is a fixed point: GEN produces only itself, so
    the optimal set is the singleton `{.deleted}`. -/
theorem deleted_converged : derivation.Converged .deleted := by
  decide

/-- **Positive half**: vanilla HS converges on `/nān + rī^H/` to the
    H-deletion form in 2 iterations of `derive` (1 substantive HS step +
    1 fixed-point detection). Paper, eq. 21. Uses the substrate's
    `pickByOrder` utility for tie-breaking under the derived
    `LinearOrder Cand21`. -/
theorem converges_to_deleted :
    derivation.derive pickByOrder .input 2 = some .deleted := by
  decide

end Tableau21

end Phenomena.Tone.Studies.McPhersonLamont2026
