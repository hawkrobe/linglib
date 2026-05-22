import Linglib.Core.Causal.SEM.Counterfactual

/-!
# Nadathur 2024: Causal Semantics for Implicative Verbs
@cite{nadathur-2024}

Causal Semantics for Implicative Verbs. Journal of Semantics 40: 311–358.

## Summary

Derives the inferential profile of implicative verbs from causal structure
(structural equation models, @cite{pearl-2000}; @cite{schulz-2011}).
Builds on @cite{baglini-francez-2016}'s causal analysis of *manage* but
extends to the full implicative class: lexically-specific two-way verbs
(*dare*, *bother*), one-way verbs (*jaksaa*, *pystyä*), and polarity-
reversing verbs (*fail*, *hesitate*).

## Core Contribution: Proposal 32

The **prerequisite account** decomposes implicative meaning into:
- (32i)   Presuppose: ∃ prerequisite A(x) causally necessary for P(x)
- (32ii)  Assert: x did A
- (32iii) Presuppose (two-way only): A(x) causally sufficient for P(x)

One-way implicatives lack (32iii); their positive implicature arises
via circumscription/antiperfection.

## Dreyfus Scenario (§6.1.1, Figure 3)

Eight-vertex SCM illustrating how causal structure determines
implicative felicity:

- INT: Dreyfus intends to spy
- NRV: Dreyfus has the nerve
- SEC: Dreyfus collects secrets    (= INT)
- MSG: Dreyfus sends a radio message (= INT ∧ NRV)
- LST: A German is listening on the correct frequency
- BRK: The message is garbled
- COM: Dreyfus establishes communication (= MSG ∧ LST ∧ ¬BRK)
- SPY: Dreyfus spies for the Germans (= SEC ∧ COM)

Background: INT = true, SEC = true, BRK = false. NRV/LST undetermined.
The question is whether NRV (the unresolved prerequisite) is sufficient
for the various effects.

The legacy `CausalDynamics`-based Dreyfus model + Karttunen/Finnish
classification machinery were deleted in Phase D-H. Necessity-side
claims (manage_send_msg_felicitous etc.) require V2's polymorphic
`causallyNecessary` over multi-parent mechanisms with negative
preconditions; deferred until the supersituation enumeration handles
multi-parent disjunctive cases.
-/

namespace Nadathur2024

open Core.Causal Core.Causal.Mechanism Core.Causal.SEM

/-- Dreyfus scenario vertices (@cite{nadathur-2024} §6.1.1, Figure 3). -/
inductive V | INT | NRV | LST | BRK | SEC | MSG | COM | SPY
  deriving DecidableEq, Fintype, Repr

def varList : List V :=
  [.INT, .NRV, .LST, .BRK, .SEC, .MSG, .COM, .SPY]

/-- Graph: SEC←{INT}, MSG←{INT,NRV}, COM←{MSG,LST,BRK}, SPY←{SEC,COM}. -/
def graph : CausalGraph V := ⟨fun
  | .INT => ∅
  | .NRV => ∅
  | .LST => ∅
  | .BRK => ∅
  | .SEC => {.INT}
  | .MSG => {.INT, .NRV}
  | .COM => {.MSG, .LST, .BRK}
  | .SPY => {.SEC, .COM}⟩

/-- Dreyfus SEM with the negative `¬BRK` precondition encoded directly
    in the COM mechanism — first-class on V2's Boolean substrate. -/
noncomputable def dreyfusSEM : BoolSEM V :=
  { graph := graph
    mech := fun
      | .INT => const (G := graph) false
      | .NRV => const (G := graph) false
      | .LST => const (G := graph) false
      | .BRK => const (G := graph) false
      | .SEC => deterministic (fun ρ => ρ ⟨.INT, by simp [graph]⟩)
      | .MSG => deterministic (fun ρ =>
          ρ ⟨.INT, by simp [graph]⟩ && ρ ⟨.NRV, by simp [graph]⟩)
      | .COM => deterministic (fun ρ =>
          ρ ⟨.MSG, by simp [graph]⟩ && ρ ⟨.LST, by simp [graph]⟩ &&
          !ρ ⟨.BRK, by simp [graph]⟩)
      | .SPY => deterministic (fun ρ =>
          ρ ⟨.SEC, by simp [graph]⟩ && ρ ⟨.COM, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic dreyfusSEM where
  mech_det v := match v with
    | .INT => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .NRV => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .LST => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .BRK => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .SEC => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .MSG => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .COM => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .SPY => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Background: Dreyfus intends, has collected secrets, channel intact. -/
def dreyfusBg : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .INT true |>.extend .SEC true |>.extend .BRK false

/-- (34a) **dare felicitous for MSG**: NRV is sufficient for MSG.
    With INT already true and BRK irrelevant for MSG, adding NRV=true
    yields MSG=true. -/
theorem nrv_sufficient_for_msg :
    (developDetOn dreyfusSEM varList 1 (dreyfusBg.extend .NRV true)).hasValue .MSG true := by
  rfl

/-- (34c) **dare INFELICITOUS for COM**: NRV is NOT sufficient for COM.
    Even with NRV=true, COM also requires LST=true (which is undetermined
    in `dreyfusBg`), so COM does not develop to true. -/
theorem nrv_not_sufficient_for_com :
    ¬ (developDetOn dreyfusSEM varList 2
        (dreyfusBg.extend .NRV true)).hasValue .COM true := by
  intro h
  exact Bool.false_ne_true (Option.some.inj h)

/-- (34d) **dare INFELICITOUS for SPY**: NRV is NOT sufficient for SPY
    (SPY depends on COM, which requires LST). -/
theorem nrv_not_sufficient_for_spy :
    ¬ (developDetOn dreyfusSEM varList 3
        (dreyfusBg.extend .NRV true)).hasValue .SPY true := by
  intro h
  exact Bool.false_ne_true (Option.some.inj h)

end Nadathur2024
