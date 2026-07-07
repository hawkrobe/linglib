import Linglib.Semantics.Dynamic.UpdateSemantics.Default

/-!
# POSW: Portner's Modal API over Expectation States
[portner-2018] [veltman-1996] [kratzer-1981] [stalnaker-1978] [condoravdi-lauer-2012]

[portner-2018]'s **partially ordered set of worlds** (POSW) — the pair
`⟨cs, ≤⟩` of a context set and an ordering that his mood unification
(Ch. 4) has verbal mood (Ch. 2), sentence mood (Ch. 3), and modal
flavor operate on — is [veltman-1996]'s expectation state `ExpState`
read at the discourse level: `info` is the Stalnakerian context set
([stalnaker-1978]), `order` the Kratzerian ordering source
([kratzer-1981]), `ExpState.assert` the `+`-update, and
`ExpState.promote` the `⋆`-update ([portner-2004]'s To-Do-List
update). Portner's central architectural insight — belief vs. desire
is `□_cs` vs. `□_≤` over the same agent's state, assertion vs.
directive is `+` vs. `⋆` over the discourse state — becomes: the two
updates touch disjoint components (`ExpState.assert_order`,
`ExpState.promote_info`), and the two modals quantify over them.

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

/-- **Informational necessity** `□_cs` ([portner-2018], Ch. 2): `p`
    holds at every world in the information state. The semantics of
    `believe` and the Stalnakerian context-set entailment. -/
def boxCs (σ : ExpState W) (p : W → Prop) : Prop :=
  ∀ w ∈ σ.info, p w

/-- Portner's **best** worlds: members of the information state at
    least as good as every other member — `IsLeast σ.info` under the
    state's ordering, as `ExpState.optimal` is its `Minimal`. These
    are [veltman-1996]'s *normal* worlds relativized to the fact set;
    his *optimal* worlds (`ExpState.optimal`) require only
    non-domination, so `best ⊆ optimal`, with equality on connected
    orders. -/
def best (σ : ExpState W) : Set W :=
  {w ∈ σ.info | ∀ v ∈ σ.info, σ.order.le w v}

/-- **Preferential necessity** `□_≤` ([portner-2018], Ch. 2): `p`
    holds at every `≤`-best world of the information state. The
    semantics of `want` and Kratzerian deontic/bouletic modals
    ([kratzer-1981], [condoravdi-lauer-2012]). -/
def boxLe (σ : ExpState W) (p : W → Prop) : Prop :=
  ∀ w ∈ σ.best, p w

theorem best_subset_optimal (σ : ExpState W) : σ.best ⊆ σ.optimal :=
  fun _ hw => ⟨hw.1, fun v hv _ => hw.2 v hv⟩

theorem best_eq_optimal_of_connected (σ : ExpState W)
    (hconn : Normality.connected σ.order) : σ.best = σ.optimal :=
  Set.Subset.antisymm σ.best_subset_optimal
    (fun w hw => ⟨hw.1, fun v hv => (hconn w v).elim id (fun h => hw.2 hv h)⟩)

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
    ([veltman-1996]'s *normally φ ⊩ presumably φ*): if the ordering
    already respects `p` (the `promote`-support condition,
    `ExpState.le_promote_iff`) and is connected, and the information
    state has a `p`-world, then `p` holds at every best world. The
    converse fails, and without connectedness so does this direction —
    Veltman's ambiguous states. -/
theorem boxLe_of_respects (σ : ExpState W) (p : W → Prop)
    (hresp : Normality.respects σ.order p)
    (hconn : Normality.connected σ.order)
    (hex : ∃ w ∈ σ.info, p w) : σ.boxLe p :=
  fun _ hw =>
    (Normality.optimal_of_respects_connected σ.order p σ.info hresp hconn hex
      (σ.best_subset_optimal hw)).2

end Semantics.Dynamic.Default.ExpState

namespace Semantics.Mood

open Semantics.Dynamic.Default

universe u
variable {W : Type u}

/-! ### Normal modality structure

`boxCs` and `boxLe` are both **normal modalities** in the modal-logic
sense: each satisfies necessitation (`□⊤`) and the K-axiom
(`□(p→q) → □p → □q`) — one shape of the inf-preservation pattern that
`∀` over any subset enjoys. The third POSWQ modal `boxAns` is *not*
normal (see `Semantics/Mood/POSWQ.lean`); it has its own closure
structure under boolean operations instead. -/

/-- A **normal modality** in the sense of basic modal logic:
    quantifies a unary box over `W → Prop` predicates, satisfying
    necessitation (`box ⊤`) and the K-axiom (`box (p → q) → box p
    → box q`). The two universal modals `ExpState.boxCs` and
    `ExpState.boxLe` are normal; `POSWQ.boxAns` is not. -/
class NormalModality (W : Type u) (box : (W → Prop) → Prop) : Prop where
  /-- Necessitation: the box always holds for `⊤`. -/
  necessitation : box (fun _ => True)
  /-- The K-axiom: distribution of the box over implication. -/
  K : ∀ p q : W → Prop, box (fun w => p w → q w) → box p → box q

instance (σ : ExpState W) : NormalModality W σ.boxCs where
  necessitation := fun _ _ => trivial
  K _ _ hpq hp w hcs := hpq w hcs (hp w hcs)

instance (σ : ExpState W) : NormalModality W σ.boxLe where
  necessitation := fun _ _ => trivial
  K _ _ hpq hp w hbest := hpq w hbest (hp w hbest)

end Semantics.Mood
