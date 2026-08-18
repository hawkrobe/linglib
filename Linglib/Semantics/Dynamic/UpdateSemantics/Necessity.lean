/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Dynamic.UpdateSemantics.Default

/-!
# Necessity modals over expectation states

[portner-2018]'s partially ordered set of worlds — the pair `⟨cs, ≤⟩`
his mood unification operates on — is [veltman-1996]'s `ExpState` read
at the discourse level: `info` is the Stalnakerian context set
([stalnaker-1978]), `order` the Kratzerian ordering source
([kratzer-1981]). This file adds the modal half of that API: the
necessity modals over the two components, and the comparison of each
with its update's acceptance fixpoint ([veltman-1996]'s `σ ⊩ φ` iff
`σ[φ] = σ`, reformulated by [portner-2018] for *believe* and *want*
following [farkas-2003]).

## Main definitions

- `ExpState.boxCs`: informational necessity `□_cs` — truth throughout
  the information state (Portner's *believe*).
- `ExpState.boxLe`: preferential necessity `□_≤` — truth at all optimal
  worlds (Portner's *want*, Kratzerian deontic/bouletic modals
  ([condoravdi-lauer-2012]), and the test condition of [veltman-1996]'s
  *presumably*).
- `NormalModality`: necessitation plus the K-axiom.

## Main results

- `le_assert_iff_boxCs`: support of `assert` *is* `boxCs` — the fixpoint
  [farkas-2003] uses to characterize indicative-licensing contexts.
- `boxLe_of_respects`: support of `promote` (`Normality.respects`)
  implies `boxLe` on connected orders with a witness — [veltman-1996]'s
  *normally φ ⊩ presumably φ*. The converse fails, and disconnected
  orders (Veltman's ambiguous states) break this direction too.

[condoravdi-lauer-2012]'s preference structures order *propositions*,
one type level above the world ordering here; POSW-style states consume
`PreferenceStructure.maxInducedLe` rather than instantiating
them.
-/

namespace UpdateSemantics.Default.ExpState

open Core.Order

variable {W : Type*}

/-- **Informational necessity** `□_cs` ([portner-2018]): `p`
    holds at every world in the information state — the Stalnakerian
    context-set entailment, and Portner's semantics of *believe*. -/
def boxCs (σ : ExpState W) (p : W → Prop) : Prop :=
  ∀ w ∈ σ.info, p w

/-- **Preferential necessity** `□_≤` ([portner-2018]): `p`
    holds at every optimal (best-ranked) world of the information
    state — Portner's best-world set is `ExpState.optimal`, the worlds
    with no higher-ranked competitors. The semantics of
    *want* and Kratzerian deontic/bouletic modals
    ([kratzer-1981], [condoravdi-lauer-2012]); also exactly the test
    condition of [veltman-1996]'s *presumably* (`presumablyTest`). -/
def boxLe (σ : ExpState W) (p : W → Prop) : Prop :=
  ∀ w ∈ σ.optimal, p w

/-- `□_cs` is upward monotone. -/
theorem boxCs_mono (σ : ExpState W) (p q : W → Prop)
    (h : ∀ w, p w → q w) : σ.boxCs p → σ.boxCs q :=
  fun hp w hw => h w (hp w hw)

/-- `□_≤` is upward monotone. -/
theorem boxLe_mono (σ : ExpState W) (p q : W → Prop)
    (h : ∀ w, p w → q w) : σ.boxLe p → σ.boxLe q :=
  fun hp w hw => h w (hp w hw)

/-- After asserting `p`, `p` is informationally necessary. The
    Stalnakerian assertion principle: asserting `p` makes `p` common
    ground. [stalnaker-1978]; [portner-2018]. -/
theorem boxCs_assert_self (σ : ExpState W) (p : W → Prop) :
    (σ.assert p).boxCs p :=
  fun _ hw => hw.2

/-- Refining the state *strengthens* informational necessity. `boxLe`
    admits no parallel result: refinement changes which worlds are
    best, in either direction. -/
theorem boxCs_anti {σ τ : ExpState W} (h : σ ≤ τ) (p : W → Prop) :
    τ.boxCs p → σ.boxCs p :=
  fun hbox w hw => hbox w (h.1 hw)

/-- **Assertive fixed-point**: the input refines its own assertion iff
    the proposition is already informationally necessary —
    [veltman-1996]'s acceptance for the `+`-update, and the formal
    core of [farkas-2003]'s assertive characterization of
    indicative-licensing contexts. -/
theorem le_assert_iff_boxCs (σ : ExpState W) (p : W → Prop) :
    σ ≤ σ.assert p ↔ σ.boxCs p :=
  σ.le_assert_iff p

/-- **Support implies preferential necessity on connected orders**
    ([veltman-1996]'s *normally φ ⊩ presumably φ*, and the bridge
    between [portner-2018]'s fixpoint semantics for *want* and
    his modal semantics): if the ordering already respects `p`
    (the `promote`-support condition, `ExpState.le_promote_iff`) and
    is connected, and the information state has a `p`-world, then `p`
    holds at every optimal world. The converse fails, and without
    connectedness so does this direction — Veltman's ambiguous
    states. -/
theorem boxLe_of_respects (σ : ExpState W) (p : W → Prop)
    (hresp : Normality.respects σ.order p)
    (hconn : Normality.connected σ.order)
    (hex : ∃ w ∈ σ.info, p w) : σ.boxLe p :=
  fun _ hw =>
    (Normality.optimal_of_respects_connected σ.order p σ.info hresp hconn hex
      hw).2

end UpdateSemantics.Default.ExpState

namespace UpdateSemantics.Default

variable {W : Type*}

/-! ### Normal modality structure

`boxCs` and `boxLe` are both normal modalities — one shape of the
inf-preservation pattern that `∀` over any subset enjoys. The third
State modal `boxAns` is *not* normal (see `Semantics/Mood/State.lean`);
it has its own closure structure under boolean operations instead. -/

/-- A **normal modality** in the sense of basic modal logic: a unary box
    over `W → Prop` predicates satisfying necessitation (`box ⊤`) and
    the K-axiom (`box (p → q) → box p → box q`). -/
class NormalModality (W : Type*) (box : (W → Prop) → Prop) : Prop where
  /-- Necessitation: the box always holds for `⊤`. -/
  necessitation : box (fun _ => True)
  /-- The K-axiom: distribution of the box over implication. -/
  K : ∀ p q : W → Prop, box (fun w => p w → q w) → box p → box q

instance (σ : ExpState W) : NormalModality W σ.boxCs where
  necessitation := fun _ _ => trivial
  K _ _ hpq hp w hcs := hpq w hcs (hp w hcs)

instance (σ : ExpState W) : NormalModality W σ.boxLe where
  necessitation := fun _ _ => trivial
  K _ _ hpq hp w hopt := hpq w hopt (hp w hopt)

end UpdateSemantics.Default
