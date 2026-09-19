/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Dynamic.UpdateSemantics.Default

/-!
# Necessity modals over expectation states

This file defines the two necessity modals over an expectation state and compares each with the
acceptance condition of the corresponding update.

Portner's mood unification operates on a partially ordered set of worlds, a pair of a context
set and an ordering. This is Veltman's expectation state read at the level of discourse, with
`info` as the Stalnakerian context set and `order` as the Kratzerian ordering source.
Informational necessity is truth throughout the information, and preferential necessity is
truth at the optimal worlds. Veltman says that a state accepts a sentence when updating with it
changes nothing, a condition that Portner, following Farkas, reformulates for *believe* and
*want*. Acceptance of an assertion is informational necessity. Acceptance of a promotion
implies preferential necessity when the ordering is total and the information contains a
witness, which is Veltman's *normally φ ⊩ presumably φ*. The converse fails, and orderings that
are not total, Veltman's ambiguous states, break this direction too.

The preference structures of Condoravdi and Lauer order propositions, one type level above the
ordering of worlds here, and states built on them consume `PreferenceStructure.maxPreorder`.

## Main definitions

* `ExpState.boxCs`: informational necessity `□_cs`, truth throughout the information state.
* `ExpState.boxLe`: preferential necessity `□_≤`, truth at all optimal worlds.
* `NormalModality`: necessitation together with the K-axiom.

## Main results

* `le_assert_iff_boxCs`: a state accepts an assertion exactly when the asserted proposition is
  informationally necessary.
* `boxLe_of_respects`: a total ordering that respects a proposition with a witness in the
  information makes the proposition preferentially necessary.

## References

* [P. Portner, *Mood* (2018)][portner-2018]
* [F. Veltman, *Defaults in Update Semantics* (1996)][veltman-1996]
* [R. C. Stalnaker, *Assertion* (1978)][stalnaker-1978]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [D. F. Farkas, *Assertion, belief and mood choice* (2003)][farkas-2003]
* [C. Condoravdi and S. Lauer, *Imperatives: Meaning and Illocutionary Force*
  (2012)][condoravdi-lauer-2012]
-/

namespace UpdateSemantics.Default.ExpState

variable {W : Type*}

/-- Informational necessity `□_cs` holds of `p` when `p` holds at every world of the information
state. This is entailment by the Stalnakerian context set and Portner's semantics of *believe*. -/
def boxCs (σ : ExpState W) (p : W → Prop) : Prop :=
  ∀ w ∈ σ.info, p w

/-- Preferential necessity `□_≤` holds of `p` when `p` holds at every optimal world of the
information state, the worlds with no better-ranked competitor. This is Portner's semantics of
*want*, the Kratzerian deontic and bouletic necessity, and the condition that Veltman's *presumably*
tests (`presumablyTest`). -/
def boxLe (σ : ExpState W) (p : W → Prop) : Prop :=
  ∀ w ∈ σ.optimal, p w

/-- `□_cs` is upward monotone. -/
theorem boxCs_mono (σ : ExpState W) (p q : W → Prop)
    (h : ∀ w, p w → q w) : σ.boxCs p → σ.boxCs q :=
  fun hp w hw ↦ h w (hp w hw)

/-- `□_≤` is upward monotone. -/
theorem boxLe_mono (σ : ExpState W) (p q : W → Prop)
    (h : ∀ w, p w → q w) : σ.boxLe p → σ.boxLe q :=
  fun hp w hw ↦ h w (hp w hw)

/-- After asserting `p`, `p` is informationally necessary, the Stalnakerian principle that asserting
`p` makes `p` common ground. -/
theorem boxCs_assert_self (σ : ExpState W) (p : W → Prop) :
    (σ.assert p).boxCs p :=
  fun _ hw ↦ hw.2

/-- Refining the state strengthens informational necessity. `boxLe` admits no parallel result, since
refinement changes which worlds are best, in either direction. -/
theorem boxCs_anti {σ τ : ExpState W} (h : σ ≤ τ) (p : W → Prop) :
    τ.boxCs p → σ.boxCs p :=
  fun hbox w hw ↦ hbox w (h.1 hw)

/-- A state accepts its own assertion of `p` iff `p` is already informationally necessary. This is
Veltman's acceptance for the `+`-update and the core of Farkas's assertive characterization of the
contexts that license the indicative. -/
theorem le_assert_iff_boxCs (σ : ExpState W) (p : W → Prop) :
    σ ≤ σ.assert p ↔ σ.boxCs p :=
  σ.le_assert_iff p

/-- If the pattern already respects `p`, which is the support condition for `promote`
(`ExpState.le_promote_iff`), and is total, and the information state has a `p`-world, then `p` holds
at every optimal world. This is Veltman's *normally φ ⊩ presumably φ*, and it connects Portner's
fixpoint semantics for *want* with his modal semantics. The converse fails, and without totality so
does this direction, as in Veltman's ambiguous states. -/
theorem boxLe_of_respects (σ : ExpState W) (p : W → Prop)
    (hresp : Respects σ.order p) (hconn : Std.Total σ.order.le)
    (hex : ∃ w ∈ σ.info, p w) : σ.boxLe p :=
  fun _ hw ↦ (minimals_subset_of_respects hresp hconn hex hw).2

end UpdateSemantics.Default.ExpState

namespace UpdateSemantics.Default

variable {W : Type*}

/-! ### Normal modality structure

`boxCs` and `boxLe` are both normal modalities — one shape of the
inf-preservation pattern that `∀` over any subset enjoys. The third
State modal `boxAns` is *not* normal (see `Semantics/Mood/State.lean`);
it has its own closure structure under boolean operations instead. -/

/-- A normal modality in the sense of basic modal logic is a unary box over predicates `W → Prop`
that satisfies necessitation (`box ⊤`) and the K-axiom (`box (p → q) → box p → box q`). -/
class NormalModality (W : Type*) (box : (W → Prop) → Prop) : Prop where
  /-- The box always holds for `⊤` (necessitation). -/
  necessitation : box (fun _ ↦ True)
  /-- The box distributes over implication (the K-axiom). -/
  K : ∀ p q : W → Prop, box (fun w ↦ p w → q w) → box p → box q

instance (σ : ExpState W) : NormalModality W σ.boxCs where
  necessitation := fun _ _ ↦ trivial
  K _ _ hpq hp w hcs := hpq w hcs (hp w hcs)

instance (σ : ExpState W) : NormalModality W σ.boxLe where
  necessitation := fun _ _ ↦ trivial
  K _ _ hpq hp w hopt := hpq w hopt (hp w hopt)

end UpdateSemantics.Default
