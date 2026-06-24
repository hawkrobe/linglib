import Linglib.Syntax.Minimalist.Probe.Basic

/-!
# Transmission: the Agree state-update on a found goal
[chomsky-2000] [deal-2024]

`Probe` (`Probe/Basic.lean`) models the *search* half of Agree. This file adds
the *transmission* half — what a successful Agree does once a goal is found —
realizing the `Probe.agreeWith` TODO. An **Agree operation** is a `Probe` plus a
state-update `xmit`:

`Probe.transmit p xmit init goals` searches `goals`; if the probe Agrees with an
active goal `g`, it updates the state via `xmit g`; otherwise it leaves the state
unchanged — **Agree fails gracefully**, no crash ([preminger-2014]).

The *direction* of transmission is the choice of `xmit`/state, not a separate
axis: goal→probe copy (φ-valuation; `Agree.applyAgree` is recognized as this
instance in `Agree.lean`), probe→goal assignment (dependent case), or sharing.
Multiple-goal assignment (a clause's worth of case) is a *fold* of `transmit`s —
the composition axis (`cascade`/ordered stack), not a single transmit.
-/

namespace Minimalist

variable {α σ : Type*}

/-- An Agree operation: search (`Probe`) + a transmission `xmit` applied to the
    active goal it finds. No active goal ⇒ state unchanged (graceful failure). -/
def Probe.transmit (p : Probe α) (xmit : α → σ → σ) (init : σ) (goals : List α) :
    σ :=
  (p.agree goals).elim init (fun g => xmit g init)

variable {p : Probe α} {xmit : α → σ → σ} {init : σ} {goals : List α}

@[simp] theorem Probe.transmit_nil : p.transmit xmit init [] = init := rfl

/-- **Agree fails gracefully**: with no goal to value the probe, the state is
    left unchanged ([preminger-2014] — failure to Agree does not crash). -/
theorem Probe.transmit_eq_init_of_agree_none (h : p.agree goals = none) :
    p.transmit xmit init goals = init := by
  rw [Probe.transmit, h]; rfl

/-- An inactive closest goal absorbs the probe without transmission
    ([deal-2024]: satisfaction without interaction). -/
theorem Probe.transmit_eq_init_of_inactive {a : α}
    (hs : p.search goals = some a) (ha : p.act a = false) :
    p.transmit xmit init goals = init :=
  Probe.transmit_eq_init_of_agree_none (Probe.agree_eq_none_of_inactive hs ha)

/-- When the probe Agrees with `a`, transmission applies `xmit a` to the state. -/
theorem Probe.transmit_eq_of_agree {a : α} (h : p.agree goals = some a) :
    p.transmit xmit init goals = xmit a init := by
  rw [Probe.transmit, h]; rfl

/-- For a probe with no activity restriction (`ofVis`), transmission fires on
    the structurally closest visible goal. -/
theorem Probe.transmit_ofVis_eq_of_search {vis : α → Bool} {a : α}
    (h : (Probe.ofVis vis).search goals = some a) :
    (Probe.ofVis vis).transmit xmit init goals = xmit a init :=
  Probe.transmit_eq_of_agree (by rw [Probe.agree_eq_search_of_act (fun _ => rfl), h])

end Minimalist
