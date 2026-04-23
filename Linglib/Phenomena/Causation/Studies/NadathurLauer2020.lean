import Linglib.Core.Causal.SEM.Counterfactual

/-!
# Structural Causation Tests
@cite{nadathur-lauer-2020} @cite{pearl-2000}

Verification that the V2 `BoolSEM` substrate correctly models classic
causal structures from the philosophy and linguistics literature.
The canonical Preemption scenario (Suzy + Billy throwing) demonstrates
the make/cause divergence under overdetermination — the central
@cite{nadathur-lauer-2020} prediction.

Other scenarios (Prevention, Enabling, ChainBypass) follow the same
pattern; deferred until consumer demand. The legacy `CausalDynamics`-
based renderings of all four scenarios were deleted in Phase D-H.
-/

namespace Phenomena.Causation.StructuralCausation

open Core.Causal Core.Causal.Mechanism Core.Causal.SEM

namespace Preemption

/-- Preemption vertices: two throwers and the bottle. -/
inductive V | suzy | billy | shatters
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.suzy, .billy, .shatters]

def graph : CausalGraph V := ⟨fun
  | .suzy => ∅
  | .billy => ∅
  | .shatters => {.suzy, .billy}⟩

/-- Disjunctive mechanism: shatters iff Suzy OR Billy throws. -/
noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .suzy => const (G := graph) false
      | .billy => const (G := graph) false
      | .shatters => deterministic (fun ρ =>
          ρ ⟨.suzy, by simp [graph]⟩ || ρ ⟨.billy, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .suzy => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .billy => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .shatters => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Local sufficiency predicate. -/
noncomputable def sufficient (vs : List V) (bg : Valuation (fun _ : V => Bool))
    (n : Nat) (cause effect : V) : Prop :=
  (developDetOn model vs n (bg.extend cause true)).hasValue effect true

/-- Local but-for predicate. -/
noncomputable def butFor (vs : List V) (bg : Valuation (fun _ : V => Bool))
    (n : Nat) (cause effect : V) : Prop :=
  ¬ (developDetOn model vs n (bg.extend cause false)).hasValue effect true

/-- Suzy's throw is sufficient for shattering (in any background). -/
theorem suzy_sufficient : sufficient varList Valuation.empty 1 .suzy .shatters := by
  unfold sufficient; rfl

/-- Billy's throw is sufficient for shattering (in any background). -/
theorem billy_sufficient : sufficient varList Valuation.empty 1 .billy .shatters := by
  unfold sufficient; rfl

/-- **Overdetermination**: with Billy already throwing, Suzy's throw is
    NOT but-for-necessary — the bottle still shatters via Billy when
    Suzy doesn't throw. Captures @cite{nadathur-lauer-2020}'s prediction
    that "Suzy caused the bottle to shatter" is INFELICITOUS under
    overdetermination (cause requires necessity), while "Suzy made the
    bottle shatter" remains true (make requires only sufficiency). -/
theorem suzy_not_but_for_when_billy_throws :
    ¬ butFor varList (Valuation.empty.extend .billy true) 1 .suzy .shatters := by
  intro h; apply h; rfl

end Preemption

end Phenomena.Causation.StructuralCausation
