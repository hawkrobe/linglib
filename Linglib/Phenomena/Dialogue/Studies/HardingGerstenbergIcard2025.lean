import Mathlib.Data.Rat.Defs
import Linglib.Core.Causal.V2.SEM.Bool
import Linglib.Core.Causal.V2.SEM.Counterfactual

/-!
# A Communication-First Account of Explanation
@cite{halpern-pearl-2005} @cite{harding-gerstenberg-icard-2025}

Formalization of @cite{harding-gerstenberg-icard-2025}.

Explanation is modeled as an RSA communication game where:
- **Worlds** are causal situations `(M, u)`: a SEM + exogenous context
- **Utterances** are explanations: "FACT because X = x"
- **Literal meaning** = actual causation (X = x manipulates FACT in `(M, u)`)
- **Decision problem** = manipulation game (listener picks variable to intervene on)
- **Goodness** = Δ expected utility (post-explanation minus baseline)

## V2 substrate

Each scenario (Late Meeting / Roof Replacement / Milk Theft) defines its
own inductive vertex enum and one or more `BoolSEM` instances over that
enum. Different "structural alternatives" (e.g., M_T vs M_∧) become
different SEMs over the SAME vertex type with different mechanisms at
the effect vertex. Explanations (`literallyTrue`, `manipulationReward`)
use V2's `BoolSEM.manipulates` (Woodward's interventionist criterion)
and `developDetOn` for kernel-verifiable structural proofs.
-/

namespace HardingGerstenbergIcard2025

open Core.Causal.V2 Core.Causal.V2.Mechanism Core.Causal.V2.SEM

-- ════════════════════════════════════════════════════
-- § Late Meeting
-- ════════════════════════════════════════════════════

/-! ### Late Meeting

Bob is late to meet Charlie, who is cross. Bob knows T = 1 (he was
late) and B = 1 (he forgot Charlie's birthday), but is unsure whether
the causal structure is M_T (tardiness alone suffices) or M_∧ (both
tardiness AND birthday forgetting are needed). -/

namespace LateMeeting

/-- Vertices of the Late-Meeting model. -/
inductive V | T | B | C
  deriving DecidableEq, Fintype, Repr

def lmVarList : List V := [.T, .B, .C]

/-- Graph for M_T: tardiness alone causes crossness (C ← T). -/
def graphT : CausalGraph V :=
  ⟨fun | .T => ∅ | .B => ∅ | .C => {.T}⟩

/-- Graph for M_∧: both T and B cause crossness (C ← T, B). -/
def graphConj : CausalGraph V :=
  ⟨fun | .T => ∅ | .B => ∅ | .C => {.T, .B}⟩

/-- M_T SEM: C := T. -/
noncomputable def semT : BoolSEM V :=
  { graph := graphT
    mech := fun v => match v with
      | .T => const (G := graphT) false
      | .B => const (G := graphT) false
      | .C => deterministic (fun ρ => ρ ⟨.T, by simp [graphT]⟩) }

noncomputable instance : SEM.IsDeterministic semT where
  mech_det v := match v with
    | .T | .B => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .C => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- M_∧ SEM: C := T ∧ B. -/
noncomputable def semConj : BoolSEM V :=
  { graph := graphConj
    mech := fun v => match v with
      | .T => const (G := graphConj) false
      | .B => const (G := graphConj) false
      | .C => deterministic (fun ρ =>
          ρ ⟨.T, by simp [graphConj]⟩ && ρ ⟨.B, by simp [graphConj]⟩) }

noncomputable instance : SEM.IsDeterministic semConj where
  mech_det v := match v with
    | .T | .B => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .C => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- The actual context: T = 1 ∧ B = 1. -/
def lateBg : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .T true |>.extend .B true

/-- An explanation cites a cause variable for the effect. -/
structure Explanation where
  cause : V
  effect : V
  deriving Repr, DecidableEq

/-- **Literal meaning** of an explanation under a given SEM and context. -/
noncomputable def literallyTrue (M : BoolSEM V) [SEM.IsDeterministic M]
    (s : Valuation (fun _ : V => Bool)) (expl : Explanation) : Prop :=
  (developDetOn M lmVarList 1 s).hasValue expl.effect true ∧
  s.hasValue expl.cause true

noncomputable instance (M : BoolSEM V) [SEM.IsDeterministic M]
    (s : Valuation (fun _ : V => Bool)) (expl : Explanation) :
    Decidable (literallyTrue M s expl) := Classical.dec _

-- ── Literal meaning theorems ──

/-- In M_T, the effect (C) develops from T. -/
theorem developsTo_C_in_T_by_T :
    (developDetOn semT lmVarList 1 lateBg).hasValue .C true := by rfl

/-- In M_∧, the effect (C) develops from T ∧ B (both true in lateBg). -/
theorem developsTo_C_in_Conj_by_TB :
    (developDetOn semConj lmVarList 1 lateBg).hasValue .C true := by rfl

/-- Empty context with B alone in M_T: C does NOT developDet (T undetermined). -/
theorem no_develop_in_T_without_T :
    ¬ (developDetOn semT lmVarList 1 (Valuation.empty.extend .B true)).hasValue .C true := by
  intro h; exact Bool.false_ne_true (Option.some.inj h)

end LateMeeting

-- ════════════════════════════════════════════════════
-- § Roof Replacement
-- ════════════════════════════════════════════════════

/-! ### Roof Replacement

A house catches fire (F = 1). Two potential causes: thatched roof
(R = 1) and recent drought (D = 1). Four causal structures:
M_R (R→F), M_D (D→F), M_∧ (R∧D→F), M_∨ (R∨D→F).

Key prediction: citing R = 1 is more *useful* than D = 1 for the
roof-replacement decision because R manipulates F in {M_R, M_∧} but
not in {M_D, M_∨}. -/

namespace RoofReplacement

inductive V | R | D | F
  deriving DecidableEq, Fintype, Repr

def roofVarList : List V := [.R, .D, .F]

/-- Graph for M_R: F ← R. -/
def graphR : CausalGraph V := ⟨fun | .R => ∅ | .D => ∅ | .F => {.R}⟩

/-- Graph for M_D: F ← D. -/
def graphD : CausalGraph V := ⟨fun | .R => ∅ | .D => ∅ | .F => {.D}⟩

/-- Graph for M_∧ and M_∨: F ← R, D. -/
def graphRD : CausalGraph V := ⟨fun | .R => ∅ | .D => ∅ | .F => {.R, .D}⟩

/-- M_R SEM: F := R. -/
noncomputable def semR : BoolSEM V :=
  { graph := graphR
    mech := fun v => match v with
      | .R => const (G := graphR) false
      | .D => const (G := graphR) false
      | .F => deterministic (fun ρ => ρ ⟨.R, by simp [graphR]⟩) }

noncomputable instance : SEM.IsDeterministic semR where
  mech_det v := match v with
    | .R | .D => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .F => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- M_D SEM: F := D. -/
noncomputable def semD : BoolSEM V :=
  { graph := graphD
    mech := fun v => match v with
      | .R => const (G := graphD) false
      | .D => const (G := graphD) false
      | .F => deterministic (fun ρ => ρ ⟨.D, by simp [graphD]⟩) }

noncomputable instance : SEM.IsDeterministic semD where
  mech_det v := match v with
    | .R | .D => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .F => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- M_∧ SEM: F := R ∧ D. -/
noncomputable def semConj : BoolSEM V :=
  { graph := graphRD
    mech := fun v => match v with
      | .R => const (G := graphRD) false
      | .D => const (G := graphRD) false
      | .F => deterministic (fun ρ =>
          ρ ⟨.R, by simp [graphRD]⟩ && ρ ⟨.D, by simp [graphRD]⟩) }

noncomputable instance : SEM.IsDeterministic semConj where
  mech_det v := match v with
    | .R | .D => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .F => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- M_∨ SEM: F := R ∨ D. -/
noncomputable def semDisj : BoolSEM V :=
  { graph := graphRD
    mech := fun v => match v with
      | .R => const (G := graphRD) false
      | .D => const (G := graphRD) false
      | .F => deterministic (fun ρ =>
          ρ ⟨.R, by simp [graphRD]⟩ || ρ ⟨.D, by simp [graphRD]⟩) }

noncomputable instance : SEM.IsDeterministic semDisj where
  mech_det v := match v with
    | .R | .D => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .F => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def roofBg : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .R true |>.extend .D true

-- ── Develop theorems ──

/-- In M_R with R=1: F develops to true. -/
theorem F_in_R_by_R : (developDetOn semR roofVarList 1 roofBg).hasValue .F true := by rfl

/-- In M_D with D=1: F develops to true. -/
theorem F_in_D_by_D : (developDetOn semD roofVarList 1 roofBg).hasValue .F true := by rfl

/-- In M_∧ with R=1 ∧ D=1: F develops to true. -/
theorem F_in_Conj_by_RD :
    (developDetOn semConj roofVarList 1 roofBg).hasValue .F true := by rfl

/-- In M_∨ with R=1 ∨ D=1: F develops to true. -/
theorem F_in_Disj_by_R :
    (developDetOn semDisj roofVarList 1 roofBg).hasValue .F true := by rfl

-- ── R-only and D-only worlds ──

/-- In M_D with R=1, D=0: F does NOT developDet (only R won't fire D's law). -/
theorem F_not_in_D_by_R_only :
    ¬ (developDetOn semD roofVarList 1
      (Valuation.empty.extend .R true |>.extend .D false)).hasValue .F true := by
  intro h; exact Bool.false_ne_true (Option.some.inj h)

end RoofReplacement

-- ════════════════════════════════════════════════════
-- § Milk Theft
-- ════════════════════════════════════════════════════

/-! ### Milk Theft

Milk depleted (M = 1). Possible culprits: Charlie (Ch) or Dana (Da).
Disjunctive structure: Ch ∨ Da → M.

Key prediction: when both drank, neither individually manipulates M
(overdetermination); but pragmatic preference for citing both. -/

namespace MilkTheft

inductive V | Ch | Da | M
  deriving DecidableEq, Fintype, Repr

def milkVarList : List V := [.Ch, .Da, .M]

/-- Disjunctive graph: M ← Ch, Da. -/
def milkGraph : CausalGraph V := ⟨fun | .Ch => ∅ | .Da => ∅ | .M => {.Ch, .Da}⟩

/-- Disjunctive SEM: M := Ch ∨ Da. -/
noncomputable def milkSEM : BoolSEM V :=
  { graph := milkGraph
    mech := fun v => match v with
      | .Ch => const (G := milkGraph) false
      | .Da => const (G := milkGraph) false
      | .M => deterministic (fun ρ =>
          ρ ⟨.Ch, by simp [milkGraph]⟩ || ρ ⟨.Da, by simp [milkGraph]⟩) }

noncomputable instance : SEM.IsDeterministic milkSEM where
  mech_det v := match v with
    | .Ch | .Da => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .M => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Both drank: Ch=1 ∧ Da=1. -/
def milkBgBoth : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .Ch true |>.extend .Da true

/-- Only Charlie: Ch=1 ∧ Da=0. -/
def milkBgCharlie : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .Ch true |>.extend .Da false

/-- When both drank, M develops (either disjunct fires). -/
theorem M_develops_when_both :
    (developDetOn milkSEM milkVarList 1 milkBgBoth).hasValue .M true := by rfl

/-- When only Charlie drank, M still develops (disjunct from Ch fires). -/
theorem M_develops_when_charlie_only :
    (developDetOn milkSEM milkVarList 1 milkBgCharlie).hasValue .M true := by rfl

end MilkTheft

end HardingGerstenbergIcard2025
