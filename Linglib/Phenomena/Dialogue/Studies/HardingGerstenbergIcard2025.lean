import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Linglib.Core.Causal.SEM.Bool
import Linglib.Core.Causal.SEM.Counterfactual

/-!
# A Communication-First Account of Explanation
@cite{halpern-pearl-2005} @cite{harding-gerstenberg-icard-2025} @cite{sumers-etal-2023} @cite{frank-goodman-2012}

Formalization of @cite{harding-gerstenberg-icard-2025} §3:
"why FACT?" / "FACT because X = x" modeled as an RSA communication
game where the literal listener interprets via Halpern-Pearl actual
causation, the speaker reasons about a downstream decision problem
(the *manipulation game* of Def 3), and Goodness (eq. 8) is Δ expected
utility under the pragmatic listener.

## The framework (paper §3)

- **Worlds**: pairs `(M, u)` of a structural causal model with an
  exogenous context. `K` is a finite set of such pairs (the listener's
  epistemic state).
- **Messages**: "FACT because X = x". Semantic value is `actualCause`
  at `(M, u)`. We use a simple existential-witness form (paper p. 8
  licenses any extant actual-cause account); the existential ranges
  over Boolean valuations and reduces structurally on the concrete
  scenarios. UNVERIFIED: the full HP definition with off-pathway
  W-witnesses is stronger; for the disjunctive Milk-Theft case the
  two definitions agree on which messages are true.
- **L0** (eq. 2): `P_{L0}(M, u | m) ∝ Prior(M, u) · 1_{(M,u) ⊨ m}`.
- **Manipulation Game** (Def 3): action set `A` = endogenous variables
  other than FACT; reward `R(X, M, u) = E_{u'}[Manipulates(X, FACT | M, u')]`
  built from `BoolSEM.manipulates`.
- **Speaker** (eqs. 3-5): `π_{L0}(a | m) ∝ exp(β_L · E_{P_{L0}}[R(a, M, u)])`,
  `U_S(m, M, u) = Σ_a π_{L0}(a | m) · R(a, M, u)`,
  `P_S(m | M, u) ∝ exp(β_S · U_S(m, M, u))`.
- **Pragmatic Listener** (eq. 7): `P_L(M, u | m) ∝ Prior(M, u) · P_S(m | M, u)`.
- **Goodness** (eq. 8): `Σ_a π_L(a | m) · R(a, M, u) - Σ_a π_Prior(a) · R(a, M, u)`.

We work in the β → ∞ regime the paper adopts most often ("agents are
maximizing"): policies become argmax over expected reward, and the
softmax collapses. This makes the worked theorems exact-rational and
kernel-decidable.

## Scenarios

Each scenario lives in its own namespace with a per-scenario `World`
type, `ExplanationGame` instance, message inventory, and worked
predictions:

- **Late Meeting** (Example 5, p. 13): K = {M_T, M_∧} × {u = (T=1, B=1)}.
  Predicts: citing T (tardiness) is the unique best explanation under M_T;
  citing B fails the manipulation game in M_T because B doesn't manipulate
  C there.
- **Roof Replacement** (Example 3, p. 10): K = 4 structures × {u = (R=1, D=1)}.
  Predicts: citing R (thatched roof) and citing D (drought) have the same
  manipulation reward profile under the manipulation game, but a
  decision-relevant downstream task (e.g., "what to repair") breaks the tie
  toward R.
- **Milk Theft** (Example 4, p. 11): K = {M_∨} × {u_C, u_D, u_{C,D}}.
  Predicts: in u_{C,D} (overdetermination), neither single-cite uniquely
  manipulates; the conjoint message "Ch and Da" gets a higher Goodness.
-/

namespace HardingGerstenbergIcard2025

open Core.Causal Core.Causal.Mechanism Core.Causal.SEM
open BoolSEM (causallySufficientOn completesForEffectOn manipulates)

/-! ## §3 Substrate: ExplanationGame -/

/-- A configuration for the explanation framework: a finite world space
    of causal-situation pairs `(M, u)`, with prior, plus a designated
    explanandum variable. -/
structure ExplanationGame (V W : Type*)
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] where
  /-- World w → its structural causal model. -/
  modelOf : W → BoolSEM V
  /-- World w → its exogenous context (a partial valuation over V). -/
  contextOf : W → Valuation (fun _ : V => Bool)
  /-- Vertex list for `developDetOn` (typically all of V in some order). -/
  vs : List V
  /-- Iteration depth for `developDetOn` (typically `Fintype.card V`). -/
  n : Nat
  /-- Each world's model is deterministic. -/
  isDet : ∀ w, SEM.IsDeterministic (modelOf w)
  /-- Each world's graph is acyclic. -/
  isDag : ∀ w, CausalGraph.IsDAG (modelOf w).graph
  /-- Unnormalized world prior. -/
  prior : W → ℚ
  prior_nonneg : ∀ w, 0 ≤ prior w
  /-- The explanandum FACT (single variable, value = true assumed). -/
  factVar : V

/-! ### Actual causation (literal meaning of "because")

Simplified Halpern-Pearl: `cause` is an actual cause of `effect`
under `(M, u)` iff there exists a witness valuation under which
`cause = true` is but-for `effect = true` (sufficiency + non-redundance).

This collapses to plain but-for when `u` itself is the witness, and
extends to overdetermination cases via off-actual witnesses (see
Milk-Theft Example 4). -/

/-- Halpern-Pearl-style actual causation, simplified to existential
    Boolean witness. AC1: `cause` and `effect` both fired at `(M, u)`.
    AC2 (witness form): some valuation `s'` makes `cause` but-for
    `effect` via `BoolSEM.completesForEffectOn`. -/
noncomputable def actualCause {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [SEM.IsDeterministic M]
    (vs : List V) (u : Valuation (fun _ : V => Bool)) (n : Nat)
    (cause effect : V) : Prop :=
  u.hasValue cause true ∧
  (developDetOn M vs n u).hasValue effect true ∧
  ∃ s' : Valuation (fun _ : V => Bool),
    completesForEffectOn M vs s' n cause effect

noncomputable instance {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [SEM.IsDeterministic M]
    (vs : List V) (u : Valuation (fun _ : V => Bool)) (n : Nat)
    (cause effect : V) :
    Decidable (actualCause M vs u n cause effect) := Classical.dec _

/-! ### Messages and meaning -/

/-- A "FACT because X = x" message. Restricts to the Boolean case where
    the cited cause-value and explanandum-value are both `true` (paper's
    convention for the worked examples). -/
structure Message (V : Type*) where
  cause : V
  deriving DecidableEq, Repr

section ExplanationGameMethods
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Whether `m` is true at world `w`: `actualCause` of `factVar` by `m.cause`. -/
noncomputable def ExplanationGame.meaning (G : ExplanationGame V W)
    (m : Message V) (w : W) : Prop :=
  haveI := G.isDet w
  haveI := G.isDag w
  actualCause (G.modelOf w) G.vs (G.contextOf w) G.n m.cause G.factVar

noncomputable instance ExplanationGame.meaning_decidable
    (G : ExplanationGame V W) (m : Message V) (w : W) :
    Decidable (G.meaning m w) := Classical.dec _

/-! ### §3.1 L0 posterior

`P_{L0}(w | m) ∝ Prior(w) · 1_{w ⊨ m}` (eq. 2). We provide both the
unnormalized score and the normalized posterior. -/

/-- Unnormalized L0 weight: prior × meaning indicator. -/
noncomputable def ExplanationGame.l0Score (G : ExplanationGame V W)
    (m : Message V) (w : W) : ℚ :=
  if G.meaning m w then G.prior w else 0

/-- Normalizer: sum of L0 scores over the world fintype. -/
noncomputable def ExplanationGame.l0Z (G : ExplanationGame V W)
    (m : Message V) : ℚ :=
  ∑ w : W, G.l0Score m w

/-- Normalized L0 posterior. Returns 0 when the normalizer is 0
    (vacuous message). -/
noncomputable def ExplanationGame.l0 (G : ExplanationGame V W)
    (m : Message V) (w : W) : ℚ :=
  if G.l0Z m = 0 then 0 else G.l0Score m w / G.l0Z m

/-! ### §3.3 Manipulation Game (Def 3)

`R(X, M, u') = 1` iff X manipulates FACT in `(M, u')` (some Boolean
intervention on X flips FACT). Aggregated reward over the world space:
`R(X, w) = E_{w'}[1_{Manipulates(X, FACT | M_{w'}, u_{w'})}]` weighted
by prior on `w'`.

Note: paper's Def 3 averages over `u'` for fixed M; here we average
over the entire world `w'` (including model uncertainty), matching the
formalization choices made for the listener's epistemic state. -/

/-- Whether action variable `X` manipulates FACT at world `w`. -/
noncomputable def ExplanationGame.worldManipulates (G : ExplanationGame V W)
    (X : V) (w : W) : Prop :=
  haveI := G.isDet w
  haveI := G.isDag w
  manipulates (G.modelOf w) (G.contextOf w) X G.factVar

noncomputable instance (G : ExplanationGame V W) (X : V) (w : W) :
    Decidable (G.worldManipulates X w) := Classical.dec _

/-- Manipulation-game reward for action `X`: prior-weighted indicator
    of `X` manipulating FACT across worlds. -/
noncomputable def ExplanationGame.reward (G : ExplanationGame V W) (X : V) : ℚ :=
  ∑ w : W, G.prior w * (if G.worldManipulates X w then 1 else 0)

/-- Conditional reward: prior-weighted manipulation under L0's posterior. -/
noncomputable def ExplanationGame.condReward (G : ExplanationGame V W)
    (X : V) (m : Message V) : ℚ :=
  ∑ w : W, G.l0 m w * (if G.worldManipulates X w then 1 else 0)

/-! ### §3.2 Speaker (β = ∞ specialization)

In the β → ∞ regime, `π_{L0}(a | m)` puts all mass on
`argmax_a condReward(a, m)`. We expose the argmax as a predicate
`isBestAction` (any action whose conditional reward dominates all
others); when the argmax is unique, `uS` reduces to that action's
actual-world reward. -/

/-- An action `X` is L0's best response to message `m`:
    its conditional reward dominates every other action. -/
noncomputable def ExplanationGame.isBestAction (G : ExplanationGame V W)
    (m : Message V) (X : V) : Prop :=
  ∀ Y : V, G.condReward Y m ≤ G.condReward X m

noncomputable instance (G : ExplanationGame V W) (m : Message V) (X : V) :
    Decidable (G.isBestAction m X) := Classical.dec _

/-- Speaker utility (β = ∞) at world `w`, given an L0 best response
    `bestAction` selected by the caller (typically a witness for
    `isBestAction m bestAction`): the reward of `bestAction` at `w`. -/
noncomputable def ExplanationGame.uS (G : ExplanationGame V W)
    (bestAction : V) (w : W) : ℚ :=
  haveI := G.isDet w
  haveI := G.isDag w
  if manipulates (G.modelOf w) (G.contextOf w) bestAction G.factVar then 1 else 0

/-! ### §3.4 Pragmatic Listener and Goodness (eq. 8)

In the β → ∞ regime, `P_S` puts all mass on argmax-utility messages,
and `π_L` behaves like `π_{L0}` after Bayesian inversion against the
speaker's choice. We collapse Goodness (eq. 8) to a single comparable
scalar at the actual world `w*`: post-explanation reward of the chosen
best action minus the prior-best action's reward. Positive Goodness
means the explanation strictly improved the listener's expected
outcome at `w*`. -/

/-- Goodness of message `m` at the actual world `w*`, given the
    pre-explanation prior-best action (`priorBest`) and the post-
    explanation L0-best action (`postBest`). Δ expected utility at
    the actual world (β = ∞). -/
noncomputable def ExplanationGame.goodness (G : ExplanationGame V W)
    (priorBest postBest : V) (wStar : W) : ℚ :=
  G.uS postBest wStar - G.uS priorBest wStar

end ExplanationGameMethods

-- ════════════════════════════════════════════════════
-- § Example 5: Late Meeting (paper p. 13)
-- ════════════════════════════════════════════════════

/-! Bob is late (T = 1) and forgot Charlie's birthday (B = 1); Charlie
    is cross (C = 1). K = {(M_T, u), (M_∧, u)} where M_T has C ← T and
    M_∧ has C ← T ∧ B. Actual world is M_T. -/

namespace LateMeeting

/-- Endogenous variables. -/
inductive V | T | B | C
  deriving DecidableEq, Fintype, Repr

def lmVarList : List V := [.T, .B, .C]

def graphT : CausalGraph V :=
  ⟨fun | .T => ∅ | .B => ∅ | .C => {.T}⟩

def graphConj : CausalGraph V :=
  ⟨fun | .T => ∅ | .B => ∅ | .C => {.T, .B}⟩

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

instance : CausalGraph.IsDAG semT.graph :=
  CausalGraph.IsDAG.of_depth _ (fun | .T => 0 | .B => 0 | .C => 1) <| by
    intro u v h; cases v <;> simp_all [graphT, semT]

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

instance : CausalGraph.IsDAG semConj.graph :=
  CausalGraph.IsDAG.of_depth _ (fun | .T => 0 | .B => 0 | .C => 1) <| by
    intro u v h; cases v <;> simp_all [graphConj, semConj]
    rcases h with rfl | rfl <;> decide

/-- Single shared exogenous context: T = 1, B = 1. -/
def lateBg : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .T true |>.extend .B true

/-- World enum: which structural alternative (single shared context). -/
inductive World | mT | mConj
  deriving DecidableEq, Fintype, Repr

/-- Per-world structural model (pattern match unfolds by iota). -/
@[reducible] noncomputable def modelOf : World → BoolSEM V
  | .mT => semT
  | .mConj => semConj

noncomputable instance (w : World) : SEM.IsDeterministic (modelOf w) := by
  cases w <;> infer_instance

instance (w : World) : CausalGraph.IsDAG (modelOf w).graph := by
  cases w <;> infer_instance

noncomputable def game : ExplanationGame V World where
  modelOf := modelOf
  contextOf _ := lateBg
  vs := lmVarList
  n := 1
  isDet w := inferInstance
  isDag w := inferInstance
  prior _ := 1  -- uniform
  prior_nonneg _ := by norm_num
  factVar := V.C

/-- Tardiness manipulates crossness in the actual world (M_T). -/
theorem T_manipulates_in_mT : game.worldManipulates V.T .mT := by
  unfold ExplanationGame.worldManipulates
  show BoolSEM.manipulates semT lateBg V.T V.C
  unfold BoolSEM.manipulates SEM.manipulates; decide

/-- Forgotten birthday does NOT manipulate crossness in M_T (B doesn't
    appear in C's mechanism in M_T). -/
theorem B_doesnt_manipulate_in_mT : ¬ game.worldManipulates V.B .mT := by
  unfold ExplanationGame.worldManipulates
  show ¬ BoolSEM.manipulates semT lateBg V.B V.C
  unfold BoolSEM.manipulates SEM.manipulates
  intro h; apply h; rfl

/-- Tardiness manipulates crossness in M_∧ (with B = 1 fixed by `lateBg`). -/
theorem T_manipulates_in_mConj : game.worldManipulates V.T .mConj := by
  unfold ExplanationGame.worldManipulates
  show BoolSEM.manipulates semConj lateBg V.T V.C
  unfold BoolSEM.manipulates SEM.manipulates; decide

/-- Forgotten birthday manipulates crossness in M_∧ (with T = 1 fixed
    by `lateBg`, flipping B flips C from `true` to `false`). -/
theorem B_manipulates_in_mConj : game.worldManipulates V.B .mConj := by
  unfold ExplanationGame.worldManipulates
  show BoolSEM.manipulates semConj lateBg V.B V.C
  unfold BoolSEM.manipulates SEM.manipulates; decide

/-- The "because T" message is true at the actual world M_T:
    T = 1 is an actual cause of C = 1 there. -/
theorem msg_T_true_in_mT : game.meaning ⟨V.T⟩ .mT := by
  unfold ExplanationGame.meaning actualCause
  refine ⟨?_, ?_, lateBg, ?_, ?_⟩
  · decide                              -- AC1a: lateBg has T = true
  · decide                              -- AC1b: develops C = true
  · unfold causallySufficientOn; rfl    -- witness: sufficiency at lateBg
  · intro h; exact Bool.false_ne_true (Option.some.inj h)

/-- The "because T" message is also true at M_∧: T = 1 is an actual
    cause of C = 1 (with B = 1 fixed by lateBg, flipping T flips C). -/
theorem msg_T_true_in_mConj : game.meaning ⟨V.T⟩ .mConj := by
  unfold ExplanationGame.meaning actualCause
  refine ⟨?_, ?_, lateBg, ?_, ?_⟩
  · decide
  · decide
  · unfold causallySufficientOn; rfl
  · intro h; exact Bool.false_ne_true (Option.some.inj h)

/-- B is not but-for C in M_T even at the actual context `lateBg`:
    flipping B from 1 to 0 leaves C at `true`, since semT's mechanism
    for C reads only T. (The full `¬ meaning ⟨B⟩ mT` claim — that NO
    witness valuation makes B but-for C — requires a witness-irrelevance
    lemma about C's parent set; deferred.) -/
theorem B_not_butFor_at_lateBg :
    ¬ completesForEffectOn semT lmVarList lateBg 1 V.B V.C := by
  rintro ⟨_, hNotBut⟩
  apply hNotBut; rfl

end LateMeeting

-- ════════════════════════════════════════════════════
-- § Example 3: Roof Replacement (paper p. 10)
-- ════════════════════════════════════════════════════

/-! Two potential causes (R = thatched roof, D = drought) of one effect
    (F = fire). K = {(M_R, u), (M_D, u), (M_∧, u), (M_∨, u)} where
    u = (R = 1, D = 1). The framework predicts that under the actual
    structure M_R, citing R "tracks" F's manipulation more reliably
    than citing D — even though both are equally informative under the
    bare manipulation game (a downstream-relevant decision such as
    "what to repair" breaks the tie). -/

namespace RoofReplacement

inductive V | R | D | F
  deriving DecidableEq, Fintype, Repr

def roofVarList : List V := [.R, .D, .F]

def graphR : CausalGraph V := ⟨fun | .R => ∅ | .D => ∅ | .F => {.R}⟩
def graphD : CausalGraph V := ⟨fun | .R => ∅ | .D => ∅ | .F => {.D}⟩
def graphRD : CausalGraph V := ⟨fun | .R => ∅ | .D => ∅ | .F => {.R, .D}⟩

noncomputable def semR : BoolSEM V :=
  { graph := graphR
    mech := fun
      | .R => const (G := graphR) false
      | .D => const (G := graphR) false
      | .F => deterministic (fun ρ => ρ ⟨.R, by simp [graphR]⟩) }

noncomputable def semD : BoolSEM V :=
  { graph := graphD
    mech := fun
      | .R => const (G := graphD) false
      | .D => const (G := graphD) false
      | .F => deterministic (fun ρ => ρ ⟨.D, by simp [graphD]⟩) }

noncomputable def semConj : BoolSEM V :=
  { graph := graphRD
    mech := fun
      | .R => const (G := graphRD) false
      | .D => const (G := graphRD) false
      | .F => deterministic (fun ρ =>
          ρ ⟨.R, by simp [graphRD]⟩ && ρ ⟨.D, by simp [graphRD]⟩) }

noncomputable def semDisj : BoolSEM V :=
  { graph := graphRD
    mech := fun
      | .R => const (G := graphRD) false
      | .D => const (G := graphRD) false
      | .F => deterministic (fun ρ =>
          ρ ⟨.R, by simp [graphRD]⟩ || ρ ⟨.D, by simp [graphRD]⟩) }

noncomputable instance : SEM.IsDeterministic semR where
  mech_det v := match v with
    | .R | .D => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .F => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
noncomputable instance : SEM.IsDeterministic semD where
  mech_det v := match v with
    | .R | .D => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .F => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
noncomputable instance : SEM.IsDeterministic semConj where
  mech_det v := match v with
    | .R | .D => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .F => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
noncomputable instance : SEM.IsDeterministic semDisj where
  mech_det v := match v with
    | .R | .D => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .F => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

private def depth : V → Nat | .R => 0 | .D => 0 | .F => 1

instance : CausalGraph.IsDAG semR.graph :=
  CausalGraph.IsDAG.of_depth _ depth <| by
    intro u v h; cases v <;> simp_all [graphR, semR, depth]
instance : CausalGraph.IsDAG semD.graph :=
  CausalGraph.IsDAG.of_depth _ depth <| by
    intro u v h; cases v <;> simp_all [graphD, semD, depth]
instance : CausalGraph.IsDAG semConj.graph :=
  CausalGraph.IsDAG.of_depth _ depth <| by
    intro u v h; cases v <;> simp_all [graphRD, semConj, depth]
    rcases h with rfl | rfl <;> decide
instance : CausalGraph.IsDAG semDisj.graph :=
  CausalGraph.IsDAG.of_depth _ depth <| by
    intro u v h; cases v <;> simp_all [graphRD, semDisj, depth]
    rcases h with rfl | rfl <;> decide

def roofBg : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .R true |>.extend .D true

inductive World | mR | mD | mConj | mDisj
  deriving DecidableEq, Fintype, Repr

@[reducible] noncomputable def modelOf : World → BoolSEM V
  | .mR => semR | .mD => semD | .mConj => semConj | .mDisj => semDisj

noncomputable instance (w : World) : SEM.IsDeterministic (modelOf w) := by
  cases w <;> infer_instance
instance (w : World) : CausalGraph.IsDAG (modelOf w).graph := by
  cases w <;> infer_instance

noncomputable def game : ExplanationGame V World where
  modelOf := modelOf
  contextOf _ := roofBg
  vs := roofVarList
  n := 1
  isDet w := inferInstance
  isDag w := inferInstance
  prior _ := 1
  prior_nonneg _ := by norm_num
  factVar := V.F

/-- R manipulates F in M_R (the actual structure). -/
theorem R_manipulates_in_mR : game.worldManipulates V.R .mR := by
  unfold ExplanationGame.worldManipulates
  show BoolSEM.manipulates semR roofBg V.R V.F
  unfold BoolSEM.manipulates SEM.manipulates; decide

/-- R does NOT manipulate F in M_D (only D matters there). -/
theorem R_doesnt_manipulate_in_mD : ¬ game.worldManipulates V.R .mD := by
  unfold ExplanationGame.worldManipulates
  show ¬ BoolSEM.manipulates semD roofBg V.R V.F
  unfold BoolSEM.manipulates SEM.manipulates; intro h; apply h; rfl

/-- R manipulates F in M_∧ (both are needed; with D = 1 fixed, R is but-for). -/
theorem R_manipulates_in_mConj : game.worldManipulates V.R .mConj := by
  unfold ExplanationGame.worldManipulates
  show BoolSEM.manipulates semConj roofBg V.R V.F
  unfold BoolSEM.manipulates SEM.manipulates; decide

/-- R does NOT manipulate F in M_∨ at the actual context (overdetermination:
    D = 1 alone fires F regardless of R). -/
theorem R_doesnt_manipulate_in_mDisj :
    ¬ game.worldManipulates V.R .mDisj := by
  unfold ExplanationGame.worldManipulates
  show ¬ BoolSEM.manipulates semDisj roofBg V.R V.F
  unfold BoolSEM.manipulates SEM.manipulates; intro h; apply h; rfl

/-- D manipulates F in M_D (the symmetric case). -/
theorem D_manipulates_in_mD : game.worldManipulates V.D .mD := by
  unfold ExplanationGame.worldManipulates
  show BoolSEM.manipulates semD roofBg V.D V.F
  unfold BoolSEM.manipulates SEM.manipulates; decide

end RoofReplacement

-- ════════════════════════════════════════════════════
-- § Example 4: Milk Theft (paper p. 11)
-- ════════════════════════════════════════════════════

/-! Single causal model M_∨: M ← Ch ∨ Da. K varies over the exogenous
    context: u_C (Charlie alone), u_D (Dana alone), u_{C,D} (both).
    Actual world: u_{C,D}. Predicts overdetermination: in u_{C,D},
    neither single variable manipulates M. The conjunctive message
    "Ch ∧ Da" would be needed to manipulate M as a joint intervention —
    the action set must include subsets of V; deferred. -/

namespace MilkTheft

inductive V | Ch | Da | M
  deriving DecidableEq, Fintype, Repr

def milkVarList : List V := [.Ch, .Da, .M]

def milkGraph : CausalGraph V := ⟨fun | .Ch => ∅ | .Da => ∅ | .M => {.Ch, .Da}⟩

noncomputable def semDisj : BoolSEM V :=
  { graph := milkGraph
    mech := fun
      | .Ch => const (G := milkGraph) false
      | .Da => const (G := milkGraph) false
      | .M => deterministic (fun ρ =>
          ρ ⟨.Ch, by simp [milkGraph]⟩ || ρ ⟨.Da, by simp [milkGraph]⟩) }

noncomputable instance : SEM.IsDeterministic semDisj where
  mech_det v := match v with
    | .Ch | .Da => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .M => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

instance : CausalGraph.IsDAG semDisj.graph :=
  CausalGraph.IsDAG.of_depth _ (fun | .Ch => 0 | .Da => 0 | .M => 1) <| by
    intro u v h; cases v <;> simp_all [milkGraph, semDisj]
    rcases h with rfl | rfl <;> decide

def bgC : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .Ch true |>.extend .Da false
def bgD : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .Ch false |>.extend .Da true
def bgBoth : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .Ch true |>.extend .Da true

inductive World | uC | uD | uBoth
  deriving DecidableEq, Fintype, Repr

@[reducible] noncomputable def modelOf : World → BoolSEM V := fun _ => semDisj

@[reducible] def contextOf : World → Valuation (fun _ : V => Bool)
  | .uC => bgC | .uD => bgD | .uBoth => bgBoth

noncomputable instance (w : World) : SEM.IsDeterministic (modelOf w) := by
  cases w <;> infer_instance
instance (w : World) : CausalGraph.IsDAG (modelOf w).graph := by
  cases w <;> infer_instance

noncomputable def game : ExplanationGame V World where
  modelOf := modelOf
  contextOf := contextOf
  vs := milkVarList
  n := 1
  isDet w := inferInstance
  isDag w := inferInstance
  prior _ := 1
  prior_nonneg _ := by norm_num
  factVar := V.M

/-- Charlie manipulates M when only Charlie drank (u_C). -/
theorem Ch_manipulates_in_uC : game.worldManipulates V.Ch .uC := by
  unfold ExplanationGame.worldManipulates
  show BoolSEM.manipulates semDisj bgC V.Ch V.M
  unfold BoolSEM.manipulates SEM.manipulates; decide

/-- Dana does NOT manipulate M when only Charlie drank (Dana = 0 in u_C). -/
theorem Da_doesnt_manipulate_in_uC : ¬ game.worldManipulates V.Da .uC := by
  unfold ExplanationGame.worldManipulates
  show ¬ BoolSEM.manipulates semDisj bgC V.Da V.M
  unfold BoolSEM.manipulates SEM.manipulates; intro h; apply h; rfl

/-- Overdetermination: Charlie does NOT manipulate M when both drank
    (Da = 1 still fires M regardless of Ch). The paper's Milk-Theft
    point. -/
theorem Ch_doesnt_manipulate_in_uBoth : ¬ game.worldManipulates V.Ch .uBoth := by
  unfold ExplanationGame.worldManipulates
  show ¬ BoolSEM.manipulates semDisj bgBoth V.Ch V.M
  unfold BoolSEM.manipulates SEM.manipulates; intro h; apply h; rfl

/-- Symmetric overdetermination: Dana does NOT manipulate M when both drank. -/
theorem Da_doesnt_manipulate_in_uBoth : ¬ game.worldManipulates V.Da .uBoth := by
  unfold ExplanationGame.worldManipulates
  show ¬ BoolSEM.manipulates semDisj bgBoth V.Da V.M
  unfold BoolSEM.manipulates SEM.manipulates; intro h; apply h; rfl

/-- "Charlie because M" is true at u_C: Charlie's drinking actually caused
    M (sole cause; lateBg-as-witness suffices). -/
theorem msg_Ch_true_in_uC : game.meaning ⟨V.Ch⟩ .uC := by
  unfold ExplanationGame.meaning actualCause
  refine ⟨?_, ?_, bgC, ?_, ?_⟩
  · decide
  · decide
  · unfold causallySufficientOn; rfl
  · intro h; exact Bool.false_ne_true (Option.some.inj h)

/-- HP-style actual cause via off-actual witness: Charlie IS an actual
    cause of M at u_{C,D} despite not being but-for there. Witness:
    `bgC` (sets Da = false off-actual), where Charlie becomes but-for. -/
theorem msg_Ch_true_in_uBoth : game.meaning ⟨V.Ch⟩ .uBoth := by
  unfold ExplanationGame.meaning actualCause
  refine ⟨?_, ?_, bgC, ?_, ?_⟩
  · decide
  · decide
  · unfold causallySufficientOn; rfl
  · intro h; exact Bool.false_ne_true (Option.some.inj h)

end MilkTheft

end HardingGerstenbergIcard2025
