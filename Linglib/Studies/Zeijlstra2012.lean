import Linglib.Semantics.Tense.Reichenbach
import Linglib.Semantics.Tense.Finset Ordering
import Linglib.Semantics.Tense.Basic
import Linglib.Syntax.Minimalist.Features

/-!
# [zeijlstra-2012]: sequence of tense as upward Agree

[zeijlstra-2012] analyzes Sequence of Tense (SOT) as syntactic concord,
structurally parallel to Negative Concord. Subordinate past morphemes carry
uninterpretable `[uPAST]`; they Agree *upward* with a c-commanding interpretable
`[iPAST]`. The subordinate past morphology is semantically vacuous — it is Agree
spell-out, not semantic past. The account builds on [chomsky-2000]'s Agree,
reversing its c-command direction.

## Main declarations

* `TenseHead` — a tense head carrying a `Finset Ordering` value and an `Interpretability`.
* `TenseHead.IsSemanticallyActive` — only interpretable heads contribute to LF.
* `UpwardAgree` — the reverse-Agree configuration: the goal c-commands the probe.
* `SOTAgreeConfig` — one interpretable `[iPAST]` over a list of `[uPAST]` heads.
* `TenseHead.toGramFeature` — maps a tense head into the Minimalist `GramFeature`
  infrastructure (interpretable ↦ valued, uninterpretable ↦ unvalued).

## Implementation notes

* **The interpretable past is an abstract operator, not the matrix verb.** In
  [zeijlstra-2012] (§5.3) the `[iPAST]` sits on an abstract operator
  (Op_PAST, after von Stechow); *all* finite verbal morphology, the matrix verb
  included, is `[uPAST]`. `SOTAgreeConfig` simplifies by treating `matrixT` as
  the `[iPAST]` bearer and abstracting the matrix verb's own `[uPAST]`.
* **SOT crosses CP.** [zeijlstra-2012] (§5.3) holds SOT to be *not*
  clause-bounded — unlike Negative Concord it crosses a CP, because the
  embedding C itself carries `[uT]` and so participates in the phase edge.
* **Embedded `[uPAST]` is modeled as pure simultaneity.** `zeijlstra_derives_simultaneous`
  yields `simultaneousFrame` (R' = P' = matrix E). [zeijlstra-2012] fn. 9
  treats embedded `[uPAST]` as a relative non-future ("no later than") licensing
  *both* the simultaneous and a back-shifted reading (not forward); that
  refinement is not formalized here.
* `zeijlstra_derives_shifted` derives the back-shifted reading from an
  *independent* embedded `[iPAST]` — one source of back-shift, distinct from the
  fn. 9 `[uPAST]`-as-non-future route.
* Zeijlstra's parameter — whether embedded `T` may carry `[uPAST]` — is the
  substrate `SOTParameter`; that SOT languages (`relative`) license the
  simultaneous reading is `Tense.sot_simultaneous_available`.

## Todo

* Temporal de re, counterfactual tense, and relative-clause tense are not addressed.
-/

open Time

namespace Zeijlstra2012

open Tense
open Minimalist (FeatureVal GramFeature Interpretability)

/-! ### Tense feature interpretability -/

/-- A tense head: a `Finset Ordering` value together with an `Interpretability`
    status. Following [zeijlstra-2012], `[iPAST]` (`.interpretable`)
    contributes past semantics; `[uPAST]` (`.uninterpretable`) is checked by
    Agree and is semantically vacuous. -/
structure TenseHead where
  /-- The tense value (past/present/future). -/
  tense : Finset Ordering
  /-- Whether this tense feature is interpretable or uninterpretable. -/
  status : Interpretability
  deriving DecidableEq, Repr

/-- A tense head is semantically active iff its feature is interpretable. -/
def TenseHead.IsSemanticallyActive (th : TenseHead) : Prop :=
  th.status = .interpretable

instance (th : TenseHead) : Decidable th.IsSemanticallyActive :=
  inferInstanceAs (Decidable (th.status = .interpretable))

/-! ### Upward Agree -/

/-- Zeijlstra's upward Agree: the goal c-commands the probe, reversing standard
    [chomsky-2000] Agree. The uninterpretable `[uF]` probe sits low and is
    valued by a c-commanding interpretable `[iF]` goal. -/
structure UpwardAgree where
  /-- The embedded `T` with `[uT]` (probe). -/
  probe : TenseHead
  /-- The matrix `T` with `[iT]` (goal). -/
  goal : TenseHead
  /-- The probe carries an uninterpretable feature. -/
  probe_uninterpretable : probe.status = .uninterpretable
  /-- The goal carries an interpretable feature. -/
  goal_interpretable : goal.status = .interpretable
  /-- The tense values match. -/
  tense_match : probe.tense = goal.tense
  deriving Repr

/-- Upward Agree makes the probe semantically vacuous: its feature is
    uninterpretable, so it does not contribute to LF. -/
theorem upwardAgree_probe_vacuous (ua : UpwardAgree) :
    ¬ ua.probe.IsSemanticallyActive := by
  simp [TenseHead.IsSemanticallyActive, ua.probe_uninterpretable]

/-- The goal's tense is semantically active. -/
theorem upwardAgree_goal_active (ua : UpwardAgree) :
    ua.goal.IsSemanticallyActive :=
  ua.goal_interpretable

/-! ### SOT Agree configuration -/

/-- An SOT configuration: one interpretable `[iPAST]` head over a list of
    uninterpretable `[uPAST]` heads ([zeijlstra-2012], ex. 22–23) — the
    `[iF] > [uF] (> [uF])` upward-Agree schema. See the module notes: the
    interpretable head is really an abstract operator, and matrix verbal
    morphology is itself `[uPAST]`. -/
structure SOTAgreeConfig where
  /-- Matrix head bearing `[iPAST]`. -/
  matrixT : TenseHead
  /-- Embedded heads bearing `[uPAST]`. -/
  embeddedTs : List TenseHead
  /-- The matrix head is interpretable. -/
  matrix_is_interpretable : matrixT.status = .interpretable
  /-- All embedded heads are uninterpretable. -/
  embedded_all_uninterpretable : ∀ t ∈ embeddedTs, t.status = .uninterpretable
  deriving Repr

/-- In an SOT configuration only the matrix head contributes past semantics;
    all embedded past morphology is vacuous concord. -/
theorem sotConfig_only_matrix_active (cfg : SOTAgreeConfig) :
    cfg.matrixT.IsSemanticallyActive ∧
    ∀ t ∈ cfg.embeddedTs, ¬ t.IsSemanticallyActive := by
  refine ⟨cfg.matrix_is_interpretable, fun t ht => ?_⟩
  simp [TenseHead.IsSemanticallyActive, cfg.embedded_all_uninterpretable t ht]

/-! ### Derivation theorems -/

/-- The simultaneous reading: embedded `[uPAST]` is vacuous, so the embedded
    clause has no independent past — it is interpreted at the matrix event
    time, giving `simultaneousFrame` (R' = P' = matrix E). See the module notes
    on the fn. 9 non-future refinement. -/
theorem zeijlstra_derives_simultaneous {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time)
    (embeddedT : TenseHead)
    (h_u : embeddedT.status = .uninterpretable) :
    ¬ embeddedT.IsSemanticallyActive ∧
    (simultaneousFrame matrixFrame embeddedE).isPresent := by
  refine ⟨?_, ?_⟩
  · simp [TenseHead.IsSemanticallyActive, h_u]
  · rfl

/-- The back-shifted reading: when embedded `T` bears an independent `[iPAST]`
    (no Agree), it contributes genuine past semantics, giving `shiftedFrame`
    (R' < P'). -/
theorem zeijlstra_derives_shifted {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time)
    (embeddedR embeddedE : Time)
    (embeddedT : TenseHead)
    (h_i : embeddedT.status = .interpretable)
    (h_shifted : embeddedR < matrixFrame.eventTime) :
    embeddedT.IsSemanticallyActive ∧
    (shiftedFrame matrixFrame embeddedR embeddedE).isPast := by
  refine ⟨h_i, ?_⟩
  simp only [shiftedFrame, ReichenbachFrame.isPast]
  exact h_shifted

/-- Upward Agree fixes the directionality: the goal `[iPAST]` is active and the
    probe `[uPAST]` is vacuous. -/
theorem zeijlstra_upward_direction (ua : UpwardAgree) :
    ua.goal.IsSemanticallyActive ∧ ¬ ua.probe.IsSemanticallyActive :=
  ⟨upwardAgree_goal_active ua, upwardAgree_probe_vacuous ua⟩

/-! ### Mapping to the Minimalist Agree features -/

/-- Map a `TenseHead` into the Minimalist `GramFeature` infrastructure:
    interpretable ↦ valued, uninterpretable ↦ unvalued. In the SOT domain the
    ±interpretable and ±valued axes coincide ([chomsky-1995]); they are
    orthogonal in general (see `Minimalist.Features`). -/
def TenseHead.toGramFeature (th : TenseHead) : GramFeature :=
  match th.status with
  | .interpretable => .valued (.tense true)
  | .uninterpretable => .unvalued (.tense true)

/-- Interpretable tense heads map to valued features. -/
theorem zeijlstra_bridge_interpretable (th : TenseHead)
    (h : th.status = .interpretable) :
    th.toGramFeature = .valued (.tense true) := by
  simp [TenseHead.toGramFeature, h]

/-- Uninterpretable tense heads map to unvalued features. -/
theorem zeijlstra_bridge_uninterpretable (th : TenseHead)
    (h : th.status = .uninterpretable) :
    th.toGramFeature = .unvalued (.tense true) := by
  simp [TenseHead.toGramFeature, h]

end Zeijlstra2012
