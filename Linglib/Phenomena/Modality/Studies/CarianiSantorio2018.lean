import Linglib.Theories.Semantics.Modality.Selectional
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Core.FinitePMF

/-!
# @cite{cariani-santorio-2018} — *Will* done Better

Cariani, F. & Santorio, P. (2018). Will done Better: Selection Semantics,
Future Credence, and Indeterminacy. *Mind* 127(505): 129–165.

## Core Claim

The future modal *will* is best analyzed as a **selectional** operator:
`will A` is true at `w` iff `A` holds at the unique world picked out by
a selection function from a set of historical alternatives. This rejects
both the pure-tense view (*will A* = *A* holds at a future time) and the
universal view (*will A* = *A* at every historical alternative).

## Three Constraints (the desiderata)

@cite{cariani-santorio-2018} argue that an adequate theory must satisfy:

1. **Modal character** — *will* embeds, takes scope, and interacts with
   negation/quantifiers. Pure tense fails.
2. **Scopelessness** — `¬ will A ↔ will ¬ A` in matrix uses.
   Universal quantification over a non-trivial modal base fails (the
   asymmetry between `¬∀` and `∀¬`).
3. **Cognitive role** — sincere assertion of `will A` requires
   non-extreme credence, not credence 1. Universal-base accounts make
   the assertion conditions too strong.

The selectional analysis satisfies all three by construction.

## Verified predictions

| # | Prediction | Theorem |
|---|-----------|---------|
| 1 | Sports Fan: Cynthia thinks Warriors will win | `cynthia_will_win` |
| 2 | Will Excluded Middle holds at every world | `will_em_at_w0` |
| 3 | Negation Swap: ¬will A ↔ will ¬A | `swap_at_w0` |
| 4 | Speaker w/o w in modal base ≠ collapse | `nonmember_no_collapse` |
| 5 | Speaker with w in modal base ⇒ collapse | `member_collapses` |
| 6 | Selectional `will`: μ(‖will Warriors‖) = 1/2 | `cynthia_credence_half` |
| 7 | Universal `will`: μ(‖∀Warriors‖) = 0 (collapse) | `universal_will_credence_zero` |
-/

set_option autoImplicit false

namespace Phenomena.Modality.Studies.CarianiSantorio2018

open _root_.Core (SelectionFunction FinitePMF)
open Semantics.Modality.Selectional

-- ============================================================================
-- §1. The Sports Fan model
-- ============================================================================

/-- Three worlds:
- `w0`: Warriors win the game (the actual world from Cynthia's perspective).
- `w1`: Warriors lose the game (counterfactual continuation).
- `w2`: Game is cancelled — Warriors neither win nor lose. -/
inductive W where
  | w0 | w1 | w2
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Cynthia's modal parameter: the historical alternatives compatible
    with what's settled at game-time. The cancelled world `w2` is *not*
    among them — the game's occurrence is settled. -/
def histAlt : Set W := { .w0, .w1 }

/-- Proposition: "Warriors win." -/
def warriorsWin : W → Prop
  | .w0 => True
  | .w1 => False
  | .w2 => False

/-- Bool-valued indicator for `warriorsWin`, used for credence
    computations via `Core.FinitePMF.probOf`. -/
def warriorsWinB : W → Bool
  | .w0 => true
  | .w1 => false
  | .w2 => false

/-- The underlying selection function: prefer `w` if `w ∈ A`,
    otherwise the first available element in the order w0, w1, w2.
    This is total because `W` is exhausted by `{w0, w1, w2}`. -/
noncomputable def selFn (w : W) (A : Set W) : W :=
  open Classical in
  if w ∈ A then w else
  if (W.w0 : W) ∈ A then .w0 else
  if (W.w1 : W) ∈ A then .w1 else .w2

/-- A selection function picking the actual-world Warriors-win
    continuation from `w0` and the loss-world from `w1`, with `w2`
    fixed to itself.

    This is the simplest selection function compatible with
    @cite{cariani-santorio-2018}'s Sports Fan scenario. -/
theorem selFn_inclusion (w : W) (A : Set W) (hA : A.Nonempty) :
    selFn w A ∈ A := by
  unfold selFn
  split_ifs with hw h0 h1
  · exact hw
  · exact h0
  · exact h1
  · obtain ⟨x, hx⟩ := hA
    cases x
    · exact absurd hx h0
    · exact absurd hx h1
    · exact hx

theorem selFn_centering (w : W) (A : Set W) (hw : w ∈ A) :
    selFn w A = w := by
  unfold selFn
  rw [if_pos hw]

noncomputable def cynthiaSel : SelectionFunction W where
  sel := selFn
  inclusion := selFn_inclusion
  centering := selFn_centering

-- ============================================================================
-- §2. Sports Fan predictions
-- ============================================================================

/-- **Prediction 1**: From the actual world `w0` (where Warriors win),
    Cynthia's assertion *Warriors will win* is true.

    `willSem cynthiaSel warriorsWin histAlt w0` reduces by Centering
    (since `w0 ∈ histAlt`) to `warriorsWin w0 = True`. -/
theorem cynthia_will_win :
    willSem cynthiaSel warriorsWin histAlt .w0 := by
  rw [unembedded_collapse cynthiaSel warriorsWin histAlt .w0
      (by simp [histAlt])]
  trivial

/-- **Prediction 2** (Will Excluded Middle): at every world,
    `will warriorsWin ∨ will ¬warriorsWin` holds. -/
theorem will_em_at_w0 :
    willSem cynthiaSel warriorsWin histAlt .w0 ∨
    willSem cynthiaSel (fun w => ¬ warriorsWin w) histAlt .w0 :=
  will_excluded_middle cynthiaSel warriorsWin histAlt .w0

/-- **Prediction 3** (Negation Swap): under selectional semantics,
    `¬ will A ↔ will ¬ A`. This is what makes *will* "scopeless"
    in matrix uses — failing under universal quantification. -/
theorem swap_at_w0 :
    willSem cynthiaSel (fun w => ¬ warriorsWin w) histAlt .w0 ↔
    ¬ willSem cynthiaSel warriorsWin histAlt .w0 :=
  negation_swap cynthiaSel warriorsWin histAlt .w0

-- ============================================================================
-- §3. Modal subordination — collapse only with membership
-- ============================================================================

/-- A modal parameter that *excludes* the actual world `w0`: the
    speaker is reasoning about a counterfactual continuation. -/
def counterfactualAlt : Set W := { .w1 }

/-- **Prediction 4**: when the evaluation world `w0` is *not* in the
    modal parameter, *no* collapse — `will A` may diverge from `A w`.

    Here `will warriorsWin` evaluated at `w0` against `counterfactualAlt`
    selects `w1` (by Inclusion + the construction of `cynthiaSel`),
    where `warriorsWin` is False. So the assertion is False even
    though `warriorsWin w0 = True`. -/
theorem nonmember_no_collapse :
    ¬ willSem cynthiaSel warriorsWin counterfactualAlt .w0 := by
  -- w0 ∉ counterfactualAlt, w0 ≠ w1, so cynthiaSel.sel w0 {w1} = w1
  show ¬ warriorsWin (selFn .w0 counterfactualAlt)
  unfold selFn counterfactualAlt warriorsWin
  simp

/-- **Prediction 5** (= @cite{cariani-santorio-2018} eq. (17) collapse):
    when `w` is in the modal parameter, `will A` collapses to `A w`. -/
theorem member_collapses (A : W → Prop) (w : W) (hw : w ∈ histAlt) :
    willSem cynthiaSel A histAlt w ↔ A w :=
  unembedded_collapse cynthiaSel A histAlt w hw

-- ============================================================================
-- §4. Cognitive role: μ(‖will A‖) vs μ(‖∀A‖)
-- ============================================================================

/-- **Cynthia's credence** over the historical alternatives. Uniform
    on `histAlt = {w0, w1}`; the cancelled world `w2` has zero credence. -/
def cynthiaPMF : FinitePMF W where
  mass
    | .w0 => 1/2
    | .w1 => 1/2
    | .w2 => 0
  mass_nonneg w := by cases w <;> norm_num
  mass_sum_one := by decide

/-- `cynthiaPMF` is supported on `histAlt`: every world outside
    `histAlt` has zero mass. -/
theorem cynthiaPMF_support : ∀ w ∉ histAlt, cynthiaPMF.mass w = 0 := by
  intro w hw
  cases w with
  | w0 => exact absurd (Or.inl rfl : (.w0 : W) ∈ histAlt) hw
  | w1 => exact absurd (Or.inr rfl : (.w1 : W) ∈ histAlt) hw
  | w2 => rfl

/-- **Prediction 6** (selectional cognitive role, paper §8.1):
    Cynthia's credence in *Warriors will win* equals her credence in
    *Warriors win*. Both are 1/2 — non-extreme credence licenses the
    *will*-assertion.

    This is the selectional analysis's distinctive prediction, and the
    direct application of `Selectional.cognitive_role`. -/
theorem cynthia_credence_half :
    cynthiaPMF.probOf
      (fun w => warriorsWinB (cynthiaSel.sel w histAlt)) = 1/2 := by
  rw [cognitive_role cynthiaSel warriorsWinB histAlt cynthiaPMF
      cynthiaPMF_support]
  decide

/-- The universal-quantifier reading of *will Warriors-win* is false at
    every world: `histAlt` contains `w1` where Warriors lose, so the
    universal `∀ w' ∈ histAlt, warriorsWin w'` cannot hold. -/
theorem universalWill_warriors_const_false (w : W) :
    ¬ universalWill warriorsWin histAlt w := by
  intro h
  exact (h .w1 (by simp [histAlt]) : warriorsWin .w1)

/-- Bool reflection of the always-false universal reading. Used to
    pass through `FinitePMF.probOf`. -/
def universalWillWarriorsB : W → Bool := fun _ => false

/-- The `universalWillWarriorsB` indicator faithfully reflects the
    universal-quantifier reading on this model: both are constantly false. -/
theorem universalWillWarriorsB_correct (w : W) :
    universalWillWarriorsB w = true ↔ universalWill warriorsWin histAlt w :=
  ⟨fun h => absurd h (by decide),
   fun h => absurd h (universalWill_warriors_const_false w)⟩

/-- **Prediction 7** (universal-base credence collapse, paper §8.1):
    under the universal-quantifier reading, Cynthia's credence in
    *will Warriors-win* is **0**, because the universal is false at
    every world (the loss world `w1` is in `histAlt`).

    Contrast with the selectional reading (`cynthia_credence_half`),
    which gives 1/2 — the empirically attested value. The
    selectional/universal split here is the substantive cognitive-role
    argument from @cite{cariani-santorio-2018} §8.1. -/
theorem universal_will_credence_zero :
    cynthiaPMF.probOf universalWillWarriorsB = 0 := by
  unfold FinitePMF.probOf universalWillWarriorsB
  simp

end Phenomena.Modality.Studies.CarianiSantorio2018
