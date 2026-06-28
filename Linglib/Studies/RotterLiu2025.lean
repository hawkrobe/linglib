import Linglib.Studies.LiuRotter2025
import Linglib.Data.Examples.RotterLiu2025
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# [rotter-liu-2025]: A Register Approach to Modal (Non-)Concord in English

Modal concord (MC) doubles a modal verb and a modal adverb of the same force
(*may possibly*, *must certainly*) versus the single modal (SM, *may* / *must*).
[rotter-liu-2025] asks whether MC differs from SM in meaning and social
perception, and whether that difference is **register-sensitive** (varies with
situational context). Its Experiment 1 is the no-context study [liu-rotter-2025]
(formalized in `Studies/LiuRotter2025`); Experiment 2, formalized here, adds a
CONTEXT factor — interlocutor relation, close vs distant — in a 2×2×2
(NUMBER × FORCE × CONTEXT) design (306 participants, Prolific).

Two analyses make precise, divergent predictions ([rotter-liu-2025] (3a)/(3b)):

* **concord** ([zeijlstra-2007]): MC ≡ SM, so doubling has no commitment effect,
  for any force.
* **modal spread** ([giannakidou-mari-2018]): for universal modals doubling
  *strengthens* commitment (*must certainly* > *must*); for existential modals it
  merely *maintains* the default (*may possibly* = *may*).

They differ only for universal modals. Experiment 2 replicates Experiment 1: the
necessity strengthening (which adjudicates for spread), the possibility weakening
(a residual *neither* analysis predicts, [rotter-liu-2025] §4.1), the
confidence crossover, the warmth penalty, and lower grammaticality/appropriateness
for MC. Crucially (RQ4) **no NUMBER × CONTEXT interaction** appears for any
measure: MC's effect is not register-sensitive to interlocutor relation.

## Main definitions
* `concordPred` / `spreadPred` — the two analyses as `ModalForce → SignType`.
* `RegisterSensitive` — a concord effect whose sign differs between contexts.
* `observedShift` — the MC − SM cell-mean shift from `Data.Examples.RotterLiu2025`.

## Main results
* `analyses_diverge_only_on_necessity` — concord and spread agree on possibility,
  differ on necessity: the single locus the data can adjudicate.
* `necessity_adjudicates` — the necessity strengthening matches spread, not concord.
* `possibility_residual` — the possibility weakening matches neither analysis.
* `context_main_effect_preserves_sign` / `not_registerSensitive_of_main_effect` —
  an additive CONTEXT main effect cancels in MC − SM, so it yields no
  NUMBER × CONTEXT interaction: the structural reason for the RQ4 null.
* `possibility_observed_vs_predicted` — the observed weakening ([liu-rotter-2025]'s
  `spreadEffect`, −1) versus the spread *prediction* (0) is exactly the residual.

## Implementation notes
Reuses the sign-prediction machinery of `Studies/LiuRotter2025`
(`ShiftObservation`, `cellMean`, `forceKey`, the rival accounts). Cell means live
in `Data.Examples.RotterLiu2025` (×100, on the 1–7 scale); they do not reduce in
the kernel, so concrete shifts are *computed* via `#eval` while the
kernel-checkable content is each analysis's systematic prediction.
-/

namespace RotterLiu2025

open Semantics.Modality (ModalForce)
open Data.Examples (LinguisticExample)
open LiuRotter2025 (ShiftObservation vacuityEffect spreadEffect cellMean forceKey)

/-! ### The two analyses (precise predictions) -/

/-- The concord analysis ([zeijlstra-2007]): MC is truth-conditionally
    equivalent to SM, so doubling has no commitment effect — the force-blind null
    `LiuRotter2025.vacuityEffect`. -/
abbrev concordPred : ModalForce → SignType := vacuityEffect

/-- The modal-spread analysis ([giannakidou-mari-2018]) as [rotter-liu-2025]
    state it ((3a)/(3b)): doubling strengthens commitment for universal modals
    (*must certainly* > *must*) but only maintains the default for existential
    modals (*may possibly* = *may*). -/
def spreadPred : ModalForce → SignType
  | .necessity     => 1
  | .weakNecessity => 1
  | .possibility   => 0

@[simp] theorem spreadPred_necessity : spreadPred .necessity = 1 := rfl
@[simp] theorem spreadPred_possibility : spreadPred .possibility = 0 := rfl

/-- The two analyses agree for existential modals (no change) and differ only
    for universal modals — the single locus where the data can adjudicate
    ([rotter-liu-2025] (3a) vs (3b)). -/
theorem analyses_diverge_only_on_necessity :
    concordPred .possibility = spreadPred .possibility ∧
    concordPred .necessity ≠ spreadPred .necessity := by decide

/-! ### Predicting against the data

Each cell of `Data.Examples.RotterLiu2025` carries the Experiment 2 means
(×100) for one CONTEXT × FORCE × NUMBER combination. An analysis predicts the
*sign* of the concord shift MC − SM per force; the observed sign is read off the
paired cell means. -/

/-- The cell with the given `context` / `force` / `number` `paperFeatures`. -/
def findCell (context force number : String) : Option LinguisticExample :=
  Examples.all.find? fun e =>
    e.paperFeatures.lookup "context" == some context &&
    e.paperFeatures.lookup "force" == some force &&
    e.paperFeatures.lookup "number" == some number

/-- The observed MC − SM shift for `measure` in `context` under `force`. -/
def observedShift (measure context : String) (force : ModalForce) :
    Option ShiftObservation := do
  let mc ← findCell context (forceKey force) "MC"
  let sm ← findCell context (forceKey force) "SM"
  let mcv ← cellMean measure mc
  let smv ← cellMean measure sm
  pure { force := force, mcMean := mcv, smMean := smv }

/-- The universal case adjudicates: *must certainly* > *must* carries the
    strengthening sign the spread analysis predicts and the concord analysis
    does not. -/
theorem necessity_adjudicates (o : ShiftObservation)
    (hf : o.force = .necessity) (h : o.smMean < o.mcMean) :
    o.observedSign = spreadPred o.force ∧ o.observedSign ≠ concordPred o.force := by
  have hs : o.observedSign = 1 := by
    show SignType.sign (o.mcMean - o.smMean) = 1
    exact sign_pos (by linarith)
  rw [hs, hf]; decide

/-- The existential weakening is a residual: *may possibly* < *may* carries a
    sign that *neither* analysis predicts — both predict maintenance
    ([rotter-liu-2025] §4.1). -/
theorem possibility_residual (o : ShiftObservation)
    (hf : o.force = .possibility) (h : o.mcMean < o.smMean) :
    o.observedSign ≠ spreadPred o.force ∧ o.observedSign ≠ concordPred o.force := by
  have hs : o.observedSign = -1 := by
    show SignType.sign (o.mcMean - o.smMean) = -1
    exact sign_neg (by linarith)
  rw [hs, hf]; decide

/-! ### Register (in)sensitivity — RQ4

The headline null result: no NUMBER × CONTEXT interaction. Structurally, a
CONTEXT main effect shifts the MC and SM means by the same amount, so it cancels
in the concord contrast MC − SM and cannot change its sign. -/

/-- A concord effect is register-sensitive (for this CONTEXT parameter) when its
    shift differs in sign between the close and distant contexts — a
    NUMBER × CONTEXT interaction at the level of sign. -/
def RegisterSensitive (close distant : ShiftObservation) : Prop :=
  close.observedSign ≠ distant.observedSign

/-- A CONTEXT main effect (the same additive shift `c` on MC and SM) leaves the
    concord shift's sign unchanged: it cancels in MC − SM. -/
theorem context_main_effect_preserves_sign (o : ShiftObservation) (c : ℚ) :
    ShiftObservation.observedSign ⟨o.force, o.mcMean + c, o.smMean + c⟩
      = o.observedSign := by
  show SignType.sign (o.mcMean + c - (o.smMean + c)) = SignType.sign (o.mcMean - o.smMean)
  congr 1; ring

/-- RQ4 ([rotter-liu-2025]): when contexts differ only by a main effect, the
    concord shift is *not* register-sensitive — close and distant carry the same
    sign, so no NUMBER × CONTEXT interaction arises. -/
theorem not_registerSensitive_of_main_effect (o : ShiftObservation) (c : ℚ) :
    ¬ RegisterSensitive o ⟨o.force, o.mcMean + c, o.smMean + c⟩ := by
  unfold RegisterSensitive
  rw [context_main_effect_preserves_sign]
  simp

/-! ### Relationship to Experiment 1 ([liu-rotter-2025])

The replication is exact at the level of accounts on the necessity side, and the
one mismatch on the possibility side is precisely the residual: [liu-rotter-2025]'s
`spreadEffect` records the *observed* weakening (−1), whereas the spread
*analysis* predicts maintenance (0). -/

/-- On necessity, Experiment 2's strengthening matches the spread prediction and
    the crossover sign [liu-rotter-2025] reports for Experiment 1. -/
theorem necessity_matches_experiment1 :
    spreadPred .necessity = LiuRotter2025.spreadEffect .necessity := by decide

/-- On possibility, [liu-rotter-2025]'s observed `spreadEffect` (−1) diverges
    from the spread analysis's prediction (0): the gap is the residual that
    `possibility_residual` isolates. -/
theorem possibility_observed_vs_predicted :
    LiuRotter2025.spreadEffect .possibility ≠ spreadPred .possibility := by decide

/-! ### The observed shifts

The `#eval`s exhibit Experiment 2's findings (means do not reduce in the kernel,
so these are computed). The commitment and confidence crossovers and the warmth
and appropriateness penalties hold in *both* contexts, and the commitment sign is
context-invariant per force — the RQ4 null in the data. -/

-- Commitment crossover replicates in both contexts (necessity +1, possibility −1):
#eval (observedShift "commitment" "close" .necessity).map fun o => (o.observedSign : ℤ)     -- some 1
#eval (observedShift "commitment" "distant" .necessity).map fun o => (o.observedSign : ℤ)    -- some 1
#eval (observedShift "commitment" "close" .possibility).map fun o => (o.observedSign : ℤ)    -- some -1
#eval (observedShift "commitment" "distant" .possibility).map fun o => (o.observedSign : ℤ)  -- some -1
-- Confidence tracks commitment (same crossover):
#eval (observedShift "confidence" "close" .necessity).map fun o => (o.observedSign : ℤ)      -- some 1
#eval (observedShift "confidence" "distant" .possibility).map fun o => (o.observedSign : ℤ)  -- some -1
-- Warmth penalty (−1) and appropriateness penalty (−1), force/context-blind:
#eval (observedShift "warmth" "close" .necessity).map fun o => (o.observedSign : ℤ)          -- some -1
#eval (observedShift "appropriateness" "distant" .possibility).map fun o => (o.observedSign : ℤ) -- some -1
-- RQ4: the commitment shift sign is context-invariant (close == distant) per force:
#eval (do
  let c ← observedShift "commitment" "close" .necessity
  let d ← observedShift "commitment" "distant" .necessity
  pure ((c.observedSign : ℤ) == (d.observedSign : ℤ)))                                       -- some true
#eval (do
  let c ← observedShift "commitment" "close" .possibility
  let d ← observedShift "commitment" "distant" .possibility
  pure ((c.observedSign : ℤ) == (d.observedSign : ℤ)))                                       -- some true

end RotterLiu2025
