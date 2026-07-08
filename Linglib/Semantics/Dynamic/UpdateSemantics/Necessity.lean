/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Dynamic.UpdateSemantics.Default

/-!
# Necessity modals over expectation states

[portner-2018]'s **partially ordered set of worlds** (posw) — the pair
`⟨cs, ≤⟩` of a context set and an ordering that his mood unification has
verbal mood, sentence mood, and modal flavor operate on — is
[veltman-1996]'s expectation state `ExpState` read at the discourse
level, a lineage Portner makes explicit by crediting Veltman's update
logic for his update operations and writing the promotion update via
Veltman's `∘` refinement. `info` is the Stalnakerian context set
([stalnaker-1978]), `order` the Kratzerian ordering source
([kratzer-1981]), `ExpState.assert` Portner's assertive update, and
`ExpState.promote` his ordering-refinement update ([portner-2004]'s
To-Do-List update). Portner's central architectural insight — belief vs.
desire is `□_cs` vs. `□_≤` over the same agent's state, assertion vs.
directive is the informational vs. the preferential update over the
discourse state — becomes: the two updates touch disjoint components
(`ExpState.assert_order`, `ExpState.promote_info`), and the two modals
quantify over them.

This file adds the *modal* half of that API: the necessity modals
`□_cs` (`boxCs`) and `□_≤` (`boxLe`), the `best` worlds the latter
quantifies over, their normality in the modal-logic sense
(`NormalModality`), and the support/necessity comparison relating
each modal to its update's acceptance fixpoint.

## Support vs necessity

[veltman-1996]'s acceptance (`σ ⊩ φ` iff `σ[φ] = σ`) gives each
update a *support* condition (`ExpState.le_assert_iff`,
`ExpState.le_promote_iff`). Comparing support with necessity:

- **informational**: support of `assert` *is* `boxCs`
  (`le_assert_iff_boxCs`) — the fixpoint [farkas-2003] uses to
  characterize indicative-licensing (assertive) contexts.
- **preferential**: support of `promote` is `Normality.respects`
  ("φ is already on the To-Do List"), which is *not* equivalent to
  `boxLe` and implies it only on connected orders with a φ-witness
  (`boxLe_of_respects` — [veltman-1996]'s *normally φ ⊩ presumably
  φ*). Connectedness can be destroyed by `promote` itself; Veltman's
  ambiguous states are exactly the disconnected ones.

The support conditions are linguistically load-bearing:
[portner-2018] reformulates the attitudes as update fixpoints —
*believe* as `m + φ = m` and *want* as `m ⋆ φ = m`, extending
[farkas-2003]'s Heim-style assertive fixpoint to the preferential
side — so his fixpoint clauses are exactly `ExpState.le_assert_iff` /
`ExpState.le_promote_iff`, and `boxLe_of_respects` is the formal
relation between his two semantics for *want* (modal vs. fixpoint).
That the informational component is the one where support and
necessity coincide is the type-level face of assertion's special
status among the updates.

**Caveat** on the preferential side: [condoravdi-lauer-2012]'s
*preference structures* are strict partial orders on **propositions**,
one type level above the world ordering here; see
`Core.Order.PreferenceStructure`. POSW-style states consume the
maximal-element-induced world preorder
(`Core.Order.PreferenceStructure.maxInducedLe`) rather than
instantiating them.
-/

namespace Semantics.Dynamic.Default.ExpState

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

end Semantics.Dynamic.Default.ExpState

namespace Semantics.Dynamic.Default

variable {W : Type*}

/-! ### Normal modality structure

`boxCs` and `boxLe` are both **normal modalities** in the modal-logic
sense: each satisfies necessitation (`□⊤`) and the K-axiom
(`□(p→q) → □p → □q`) — one shape of the inf-preservation pattern that
`∀` over any subset enjoys. The third State modal `boxAns` is *not*
normal (see `Semantics/Mood/State.lean`); it has its own closure
structure under boolean operations instead. -/

/-- A **normal modality** in the sense of basic modal logic:
    quantifies a unary box over `W → Prop` predicates, satisfying
    necessitation (`box ⊤`) and the K-axiom (`box (p → q) → box p
    → box q`). The two universal modals `ExpState.boxCs` and
    `ExpState.boxLe` are normal; `State.boxAns` is not. -/
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

end Semantics.Dynamic.Default
