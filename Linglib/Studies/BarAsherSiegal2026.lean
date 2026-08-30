import Linglib.Semantics.Causation.CCSelection

/-!
# Bar-Asher Siegal 2026: causation and causal relations

A review of how natural language encodes causation, from causative constructions and
conditionals to discourse coherence and the progressive, arguing that language is evidence
for the architecture of causal cognition. Its central proposal takes causal knowledge to be a
structural equation model in which several sets of conditions are each sufficient for an
effect: the door of Figure 1 opens when the handle is turned with the lock off, or when the
circuit is closed with the power on and the lock off. Causative constructions then differ in
which condition they may select as the cause. A change-of-state verb selects the temporally
final condition of a sufficient set, *cause* selects any of its conditions, and both select
only from the one sufficient set completed in the world of evaluation. Fodor's entailment from
*Sam opened the door* to *Sam caused the door to open* follows, its converse fails, and when
two sufficient sets are completed at once neither construction applies.

## References

* [bar-asher-siegal-2026]
* [baglini-bar-asher-siegal-2025]
* [fodor-1970]
-/

namespace BarAsherSiegal2026

open Causation Causation.Mechanism Causation.SEM Causation.CCSelection

/-- The variables of Figure 1. -/
inductive V | handle | lock | circuit | electricity | button | doorOpens
  deriving DecidableEq, Fintype, Repr

/-- The button closes the circuit; handle, lock, circuit and power bear on the door. -/
def graph : CausalGraph V := ⟨λ
  | .circuit => {.button}
  | .doorOpens => {.handle, .lock, .circuit, .electricity}
  | _ => ∅⟩

def rank : CausalGraph.Ranking graph :=
  ⟨λ | .circuit => 1 | .doorOpens => 2 | _ => 0,
    by intro u v h; revert h; cases u <;> cases v <;> decide⟩

instance : CausalGraph.IsDAG graph := rank.isDAG

/-- The structural entailments G, H and I: the circuit closes when the button is pressed, and
the door opens manually (handle on, lock off) or automatically (circuit and power on, lock
off). -/
noncomputable def model : BoolSEM V where
  graph := graph
  mech
    | .circuit => deterministic λ ρ => ρ ⟨.button, by simp [graph]⟩
    | .doorOpens => deterministic λ ρ =>
        let h := ρ ⟨.handle, by simp [graph]⟩
        let l := ρ ⟨.lock, by simp [graph]⟩
        let c := ρ ⟨.circuit, by simp [graph]⟩
        let e := ρ ⟨.electricity, by simp [graph]⟩
        (h && !l) || (c && e && !l)
    | _ => const (G := graph) false

noncomputable instance : SEM.IsDeterministic model where
  mech_det
    | .circuit => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .doorOpens => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .handle | .lock | .button | .electricity =>
        inferInstanceAs (Mechanism.IsDeterministic (const _))

instance : CausalGraph.IsDAG model.graph := inferInstanceAs (CausalGraph.IsDAG graph)

/-- A valuation from a list of settings. -/
def valuation (l : List (V × Bool)) : Valuation (λ _ : V => Bool) :=
  l.foldl (λ s p => s.extend p.1 p.2) Valuation.empty

/-- Sufficient set I: handle on, lock off. -/
def manual := valuation [(.handle, true), (.lock, false)]

/-- Sufficient set H: circuit and power on, lock off. -/
def automatic := valuation [(.circuit, true), (.electricity, true), (.lock, false)]

/-- The world in which the handle is turned on an unlocked, unpowered door. -/
def handleWorld := valuation
  [(.handle, true), (.lock, false), (.button, false), (.electricity, false), (.circuit, false),
    (.doorOpens, true)]

/-- The overdetermined world: handle turned and button pressed on a powered, unlocked door. -/
def bothWorld := valuation
  [(.handle, true), (.lock, false), (.button, true), (.electricity, true), (.circuit, true),
    (.doorOpens, true)]

/-- The lock was disengaged first, the handle turned last. -/
def time : V → ℕ | .lock => 0 | .handle => 2 | _ => 1

theorem rank_lt : ∀ v, rank v < 3 := by decide

theorem manual_minimal : IsMinimalSufficientSet model manual .doorOpens true :=
  (isMinimalSufficientSet_iff_fuel model 3 rank rank_lt _ _ _).2 (by decide +kernel)

theorem automatic_minimal : IsMinimalSufficientSet model automatic .doorOpens true :=
  (isMinimalSufficientSet_iff_fuel model 3 rank rank_lt _ _ _).2 (by decide +kernel)

/-- *John opened the door*, *John caused the door to open*: the handle is the final condition
of the only completed set. -/
theorem handle_selectsFinal : SelectsFinal model handleWorld time .handle .doorOpens true :=
  (selectsFinal_iff_fuel model 3 rank rank_lt _ _ _ _ _).2 (by decide +kernel)

theorem handle_selectsMember : SelectsMember model handleWorld .handle .doorOpens true :=
  handle_selectsFinal.selectsMember

/-- The converse of Fodor's entailment fails: the unlocked lock is a condition *cause* may
select but not the final one. -/
theorem lock_selectsMember : SelectsMember model handleWorld .lock .doorOpens true :=
  (selectsMember_iff_fuel model 3 rank rank_lt _ _ _ _).2 (by decide +kernel)

theorem lock_not_selectsFinal : ¬ SelectsFinal model handleWorld time .lock .doorOpens true :=
  λ h => absurd ((selectsFinal_iff_fuel model 3 rank rank_lt _ _ _ _ _).1 h) (by decide +kernel)

/-- With both sets completed, neither construction can select the handle. -/
theorem overdetermined : ¬ SelectsMember model bothWorld .handle .doorOpens true :=
  not_selectsMember_of_two manual_minimal automatic_minimal (by decide) (by decide) (by decide)

end BarAsherSiegal2026
