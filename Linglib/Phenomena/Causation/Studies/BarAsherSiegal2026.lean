import Linglib.Core.Causal.SEM.Counterfactual

/-!
# @cite{bar-asher-siegal-2026}: Causation and Causal Relations
@cite{bar-asher-siegal-2026} @cite{baglini-bar-asher-siegal-2025} @cite{baglini-bar-asher-siegal-2020}

Formalization of the door-opening scenario from @cite{bar-asher-siegal-2026}
Figure 1: a structural equation model with two alternative sufficient sets
for a single effect (the door opening).

## The Door-Opening Model

Variables:
- handle: handle is turned
- lock: lock is engaged (effect needs ¬lock)
- circuit: circuit is closed
- electricity: electricity is running
- button: button is pressed
- doorOpens: door opens (the effect)

Mechanism: `doorOpens = (handle ∧ ¬lock) ∨ (circuit ∧ electricity ∧ ¬lock)`,
plus `circuit := button` for the automatic pathway. Two sufficient sets:

- **Manual** (handle ∧ ¬lock) ⊨ doorOpens
- **Automatic** (circuit ∧ electricity ∧ ¬lock) ⊨ doorOpens

## Key Result

The model demonstrates CC-selection at work — completion mode (CoS verbs
like *open*) succeeds when handle alone is the active pathway, but FAILS
under overdetermination (both pathways active simultaneously). This
captures @cite{bar-asher-siegal-2026}'s point that *open* is infelicitous
when an alternative explanation exists.

The legacy `CausalDynamics`-based door scenario, situational-necessity
(Def 12b) machinery, and the Sloman-style member-mode divergence theorem
were deleted in Phase D-H. Member-mode (Def 10b causally-necessary)
divergence between *open* and *cause* awaits V2's `causallyNecessary`
infrastructure for multi-parent disjunctive mechanisms.
-/

namespace BarAsherSiegal2026

open Core.Causal Core.Causal.Mechanism Core.Causal.SEM

/-- Six-vertex door scenario. Inductive enum so `Fintype.elems`
    gives a fixed canonical order and `developDet` reduces structurally. -/
inductive V | handle | lock | circuit | electricity | button | doorOpens
  deriving DecidableEq, Fintype, Repr

def varList : List V :=
  [.handle, .lock, .button, .electricity, .circuit, .doorOpens]

/-- Full graph: button → circuit; (handle, lock) → doorOpens (manual);
    (circuit, electricity, lock) → doorOpens (automatic). -/
def fullGraph : CausalGraph V := ⟨fun
  | .handle => ∅
  | .lock => ∅
  | .button => ∅
  | .electricity => ∅
  | .circuit => {.button}
  | .doorOpens => {.handle, .lock, .circuit, .electricity}⟩

/-- Manual-only graph: drops the automatic pathway entirely. -/
def manualGraph : CausalGraph V := ⟨fun
  | .handle => ∅
  | .lock => ∅
  | .button => ∅
  | .electricity => ∅
  | .circuit => ∅
  | .doorOpens => {.handle, .lock}⟩

/-- Door-opens mechanism (full model): manual OR automatic, both need ¬lock. -/
noncomputable def doorOpensFullMech : Mechanism fullGraph (fun _ => Bool) .doorOpens :=
  deterministic (fun ρ =>
    let h := ρ ⟨.handle, by simp [fullGraph]⟩
    let l := ρ ⟨.lock, by simp [fullGraph]⟩
    let c := ρ ⟨.circuit, by simp [fullGraph]⟩
    let e := ρ ⟨.electricity, by simp [fullGraph]⟩
    (h && !l) || (c && e && !l))

/-- Door-opens mechanism (manual model): just handle ∧ ¬lock. -/
noncomputable def doorOpensManualMech : Mechanism manualGraph (fun _ => Bool) .doorOpens :=
  deterministic (fun ρ =>
    let h := ρ ⟨.handle, by simp [manualGraph]⟩
    let l := ρ ⟨.lock, by simp [manualGraph]⟩
    h && !l)

noncomputable def fullModel : BoolSEM V :=
  { graph := fullGraph
    mech := fun
      | .handle => const (G := fullGraph) false
      | .lock => const (G := fullGraph) false
      | .button => const (G := fullGraph) false
      | .electricity => const (G := fullGraph) false
      | .circuit => deterministic (fun ρ => ρ ⟨.button, by simp [fullGraph]⟩)
      | .doorOpens => doorOpensFullMech }

noncomputable def manualModel : BoolSEM V :=
  { graph := manualGraph
    mech := fun
      | .handle => const (G := manualGraph) false
      | .lock => const (G := manualGraph) false
      | .button => const (G := manualGraph) false
      | .electricity => const (G := manualGraph) false
      | .circuit => const (G := manualGraph) false
      | .doorOpens => doorOpensManualMech }

noncomputable instance : SEM.IsDeterministic fullModel where
  mech_det v := match v with
    | .handle => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .lock => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .button => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .electricity => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .circuit => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .doorOpens => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

noncomputable instance : SEM.IsDeterministic manualModel where
  mech_det v := match v with
    | .handle => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .lock => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .button => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .electricity => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .circuit => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .doorOpens => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Background: lock disengaged. -/
def unlocked : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .lock false

/-- Local sufficiency predicate: with `cause = true` under `bg`,
    `developDetOn` of `M` produces `effect = true`. -/
noncomputable def sufficient (M : BoolSEM V) [SEM.IsDeterministic M]
    (vs : List V) (bg : Valuation (fun _ : V => Bool)) (n : Nat)
    (cause effect : V) : Prop :=
  (developDetOn M vs n (bg.extend cause true)).hasValue effect true

/-- Local completion predicate: sufficient + but-for. -/
noncomputable def completes (M : BoolSEM V) [SEM.IsDeterministic M]
    (vs : List V) (bg : Valuation (fun _ : V => Bool)) (n : Nat)
    (cause effect : V) : Prop :=
  sufficient M vs bg n cause effect ∧
  ¬ (developDetOn M vs n (bg.extend cause false)).hasValue effect true

/-- **Manual-only model**: handle completes the sufficient set for
    doorOpens (full *open* and *cause* felicity, per @cite{bar-asher-siegal-2026}).
    Both completion and member modes succeed because there's no
    alternative pathway. -/
theorem handle_completes_manual :
    completes manualModel varList unlocked 1 .handle .doorOpens := by
  refine ⟨?_, ?_⟩
  · unfold sufficient; rfl
  · intro h; exact Bool.false_ne_true (Option.some.inj h)

/-- **Full model with handle alone**: handle completes the manual
    sufficient set, satisfying *open*-style completion CC-selection.
    The automatic pathway doesn't fire because button=false in `unlocked`. -/
theorem handle_completes_full :
    completes fullModel varList unlocked 2 .handle .doorOpens := by
  refine ⟨?_, ?_⟩
  · unfold sufficient; rfl
  · intro h; exact Bool.false_ne_true (Option.some.inj h)

/-- **Overdetermination in the full model**: when both pathways are
    independently activated (button=true, electricity=true alongside
    handle=true), removing handle still leaves doorOpens true via the
    automatic pathway — completion CC-selection FAILS for handle.
    This captures @cite{bar-asher-siegal-2026}'s point that *open* is
    infelicitous under overdetermination. -/
theorem handle_no_completion_overdetermined :
    ¬ completes fullModel varList
        (unlocked.extend .button true |>.extend .electricity true)
        2 .handle .doorOpens := by
  intro ⟨_, hNot⟩
  apply hNot
  rfl

end BarAsherSiegal2026
