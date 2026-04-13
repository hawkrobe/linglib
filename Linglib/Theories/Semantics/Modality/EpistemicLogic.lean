import Linglib.Core.Semantics.Proposition
import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Logic.ModalLogic
import Linglib.Core.Scales.EpistemicScale.Defs

/-!
# Multi-Agent Epistemic Logic

@cite{halpern-2003} @cite{fagin-halpern-1994}

Multi-agent epistemic operators from @cite{halpern-2003}: individual
knowledge (Kᵢ), everyone knows (E_G), common knowledge (C_G),
distributed knowledge (D_G), and their doxastic (KD45 belief) counterparts.

Connects to Stalnaker's common ground via `CG.groundedIn`: a common
ground is grounded when its context set equals what is commonly known.

## Operators

| Operator | Symbol | Definition |
|----------|--------|------------|
| Individual knowledge | Kᵢ(φ) | φ at all i-accessible worlds |
| Everyone knows | E_G(φ) | ∧ᵢ∈G Kᵢ(φ) |
| Common knowledge | C_G(φ) | φ ∧ E(φ) ∧ E(E(φ)) ∧... |
| Distributed knowledge | D_G(φ) | φ at all (∩ᵢ Rᵢ)-accessible worlds |

## Architecture

This file lives in `Theories/Semantics/Modality/` because it makes
substantive theoretical commitments (S5 for knowledge, KD45 for belief,
fixed-point characterization of common knowledge). The framework-agnostic
context management (`ContextSet`, `CG`, `BContextSet`) remains in
`Core/Semantics/CommonGround.lean`.
-/

namespace Semantics.Modality.EpistemicLogic

open Core.Proposition (BProp FiniteWorlds)
open Core.ModalLogic (AccessRel AgentAccessRel kripkeEval)
open Core.CommonGround (CG)

/-! ## Individual Knowledge

Agent i knows φ at world w iff φ holds at all worlds accessible to i.
This re-uses `kripkeEval` from `ModalLogic.lean` with agent-indexed
accessibility relations. -/

/-- Agent i knows φ at world w: Kᵢ(φ)(w) = □ᵢ φ(w). -/
def knows {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (i : E) (φ : BProp W) (w : W) : Bool :=
  kripkeEval (Rs i) .necessity φ w

/-! ## Everyone Knows

E_G(φ) holds at w iff every agent in group G knows φ at w.
E_G(φ) = ∧ᵢ∈G Kᵢ(φ). -/

/-- Everyone in group G knows φ at w. -/
def everyoneKnows {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W) (w : W) : Bool :=
  group.all fun i => knows Rs i φ w

/-- Everyone knows implies each individual knows. -/
theorem everyoneKnows_implies_knows {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W) (w : W)
    (i : E) (hi : i ∈ group)
    (h : everyoneKnows Rs group φ w = true) :
    knows Rs i φ w = true := by
  unfold everyoneKnows at h
  exact List.all_eq_true.mp h i hi

/-! ## Common Knowledge

C_G(φ) is the greatest fixed point of X = φ ∧ E_G(X). Equivalently,
C_G(φ) = φ ∧ E_G(φ) ∧ E_G(E_G(φ)) ∧... (infinite conjunction).

For computation on finite worlds, we iterate E_G until fixpoint. Since
there are finitely many truth assignments, this terminates. -/

/-- Iterate "everyone knows" n times: E^n_G(φ). -/
def everyoneKnowsIter {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W) : ℕ → BProp W
  | .zero => φ
  | .succ n => everyoneKnows Rs group (everyoneKnowsIter Rs group φ n)

/-- Common knowledge as a finite approximation: C_G(φ)(w) iff
    E^n_G(φ)(w) for all n up to the iteration bound.

    For finite W with |W| = k, the fixed point is reached within
    2^k iterations (since each iteration can only shrink the set
    of satisfying worlds). -/
def commonKnowledge {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W)
    (bound : ℕ) (w : W) : Bool :=
  (List.range (bound + 1)).all fun n => everyoneKnowsIter Rs group φ n w

/-- Common knowledge implies everyone knows (at depth 1). -/
theorem commonKnowledge_implies_everyoneKnows {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W)
    (bound : ℕ) (w : W) (_hbound : 0 < bound)
    (h : commonKnowledge Rs group φ bound w = true) :
    everyoneKnows Rs group φ w = true := by
  unfold commonKnowledge at h
  exact List.all_eq_true.mp h 1 (List.mem_range.mpr (by omega))

/-- Common knowledge implies the proposition itself (depth 0). -/
theorem commonKnowledge_implies_prop {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W)
    (bound : ℕ) (w : W)
    (h : commonKnowledge Rs group φ bound w = true) :
    φ w = true := by
  unfold commonKnowledge at h
  exact List.all_eq_true.mp h 0 (List.mem_range.mpr (Nat.zero_lt_succ bound))

/-! ## Distributed Knowledge

D_G(φ) holds at w iff φ holds at all worlds accessible to EVERY agent
in G simultaneously. The accessibility relation is the intersection:
R_D = ∩ᵢ∈G Rᵢ.

Distributed knowledge is what the group WOULD know if they pooled all
their information. It is stronger than individual knowledge but weaker
than common knowledge in the opposite direction:
D_G(φ) → Kᵢ(φ) for each i, but C_G(φ) → E_G(φ) → Kᵢ(φ). -/

/-- Intersection of accessibility relations for a group. -/
def groupAccessRel {W E : Type*}
    (Rs : AgentAccessRel W E) (group : List E) : AccessRel W :=
  fun w v => group.all fun i => Rs i w v

/-- Distributed knowledge: D_G(φ)(w) = □_{∩R} φ(w). -/
def distributedKnowledge {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W) (w : W) : Bool :=
  kripkeEval (groupAccessRel Rs group) .necessity φ w

/-- Individual knowledge implies distributed knowledge: the intersection
    of accessibility relations is a subset of each component, so every
    group-accessible world is also i-accessible. Therefore if φ holds
    at all i-accessible worlds, it holds at all group-accessible worlds. -/
theorem knows_implies_distributedKnowledge {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W) (w : W)
    (i : E) (hi : i ∈ group)
    (h : knows Rs i φ w = true) :
    distributedKnowledge Rs group φ w = true := by
  -- Kᵢ(φ) → D_G(φ): every group-accessible world is i-accessible
  unfold distributedKnowledge knows kripkeEval at *
  rw [List.all_eq_true] at h ⊢
  intro v hv
  apply h
  rw [List.mem_filter] at hv ⊢
  exact ⟨hv.1, List.all_eq_true.mp hv.2 i hi⟩

/-! ## KD45 Belief Operators

Parallel to the S5 knowledge operators above, but with KD45
accessibility (serial + transitive + Euclidean, not reflexive).

Knowledge (S5) is veridical: Kφ → φ. Belief (KD45) is not: an
agent can believe φ without φ being true. But belief is consistent
(Bφ → ◇φ, from seriality), positively introspective (Bφ → BBφ,
from transitivity), and negatively introspective (¬Bφ → B¬Bφ,
from Euclideanness).

The connection Kφ → Bφ requires R_B ⊆ R_K: every belief-accessible
world is knowledge-accessible. Since S5 frames are reflexive (more
accessible worlds), knowledge is harder to achieve than belief. -/

/-- Agent i believes φ at world w: Bᵢ(φ)(w) = □ᵢ φ(w).
    Same evaluation as knows, but the accessibility relation
    satisfies KD45 (serial + transitive + Euclidean) rather than
    S5 (reflexive + Euclidean). -/
def believes {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (i : E) (φ : BProp W) (w : W) : Bool :=
  kripkeEval (Rs i) .necessity φ w

/-- Everyone in group G believes φ at w. -/
def everyoneBelieves {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W) (w : W) : Bool :=
  group.all fun i => believes Rs i φ w

/-- Iterate "everyone believes" n times: EB^n_G(φ). -/
def everyoneBeliefIter {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W) : ℕ → BProp W
  | .zero => φ
  | .succ n => everyoneBelieves Rs group (everyoneBeliefIter Rs group φ n)

/-- Common belief: CB_G(φ)(w) iff EB^n_G(φ)(w) for all n up to bound. -/
def commonBelief {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W)
    (bound : ℕ) (w : W) : Bool :=
  (List.range (bound + 1)).all fun n => everyoneBeliefIter Rs group φ n w

/-- Distributed belief: DB_G(φ)(w) = □_{∩R_B} φ(w). -/
def distributedBelief {W E : Type*} [FiniteWorlds W]
    (Rs : AgentAccessRel W E) (group : List E) (φ : BProp W) (w : W) : Bool :=
  kripkeEval (groupAccessRel Rs group) .necessity φ w

/-- A knowledge-belief frame bundles S5 knowledge relations and KD45
    belief relations for each agent, with the constraint that belief
    accessibility is a subset of knowledge accessibility.

    R_B(i) ⊆ R_K(i) ensures Kφ → Bφ: if φ holds at all
    knowledge-accessible worlds (a superset), it holds at all
    belief-accessible worlds. -/
structure KnowledgeBeliefFrame (W E : Type*) where
  /-- Knowledge accessibility relations (should satisfy S5: reflexive + Euclidean) -/
  knowsRel : AgentAccessRel W E
  /-- Belief accessibility relations (should satisfy KD45: serial + transitive + Euclidean) -/
  believesRel : AgentAccessRel W E
  /-- Belief accessibility implies knowledge accessibility -/
  believes_sub_knows : ∀ i w v, believesRel i w v = true → knowsRel i w v = true

/-- Knowledge implies belief: Kᵢ(φ) → Bᵢ(φ).

    Since every belief-accessible world is knowledge-accessible
    (R_B ⊆ R_K), if φ holds at all knowledge-accessible worlds
    then it holds at all belief-accessible worlds. -/
theorem knows_implies_believes {W E : Type*} [FiniteWorlds W]
    (frame : KnowledgeBeliefFrame W E) (i : E) (φ : BProp W) (w : W)
    (h : knows frame.knowsRel i φ w = true) :
    believes frame.believesRel i φ w = true := by
  unfold believes knows kripkeEval at *
  rw [List.all_eq_true] at h ⊢
  intro v hv
  apply h
  rw [List.mem_filter] at hv ⊢
  exact ⟨hv.1, frame.believes_sub_knows i w v hv.2⟩

/-- Belief is consistent: Bᵢ(φ) → ◇ᵢφ (the D axiom).
    Follows from seriality of the belief accessibility relation. -/
theorem believes_consistent {W E : Type*} [FiniteWorlds W]
    {Rs : AgentAccessRel W E} (i : E)
    (hSerial : Core.ModalLogic.Serial (Rs i))
    (φ : BProp W) (w : W)
    (h : believes Rs i φ w = true) :
    kripkeEval (Rs i) .possibility φ w = true :=
  Core.ModalLogic.D_of_serial hSerial φ w h

/-- Positive introspection: Bᵢ(φ) → Bᵢ(Bᵢ(φ)) (the 4 axiom).
    Follows from transitivity of the belief accessibility relation. -/
theorem believes_positive_introspection {W E : Type*} [FiniteWorlds W]
    {Rs : AgentAccessRel W E} (i : E)
    (hTrans : Core.ModalLogic.Trans (Rs i))
    (φ : BProp W) (w : W)
    (h : believes Rs i φ w = true) :
    believes Rs i (believes Rs i φ) w = true :=
  Core.ModalLogic.four_of_trans hTrans φ w h

/-- Negative introspection: ¬Bᵢ(φ) → Bᵢ(¬Bᵢ(φ)) (the 5 axiom).
    Follows from Euclideanness of the belief accessibility relation.

    Stated contrapositively using ◇: if ◇ᵢBᵢ(φ) then Bᵢ(φ).
    Equivalently: ◇Bφ → □◇Bφ, which combined with ¬Bφ → ¬◇Bφ → □¬Bφ
    gives the standard negative introspection. -/
theorem believes_negative_introspection {W E : Type*} [FiniteWorlds W]
    {Rs : AgentAccessRel W E} (i : E)
    (hEucl : Core.ModalLogic.Eucl (Rs i))
    (φ : BProp W) (w : W)
    (h : kripkeEval (Rs i) .possibility φ w = true) :
    kripkeEval (Rs i) .necessity (kripkeEval (Rs i) .possibility φ) w = true :=
  Core.ModalLogic.five_of_eucl hEucl φ w h

/-- Belief is not veridical: there exist frames where Bᵢ(φ) ∧ ¬φ.
    Unlike knowledge (which requires reflexivity), belief frames are
    serial but not reflexive, so an agent can believe φ at a world
    where φ is false. -/
theorem believes_not_veridical :
    ∃ (W : Type) (E : Type) (_ : FiniteWorlds W) (Rs : AgentAccessRel W E)
      (i : E) (φ : BProp W) (w : W),
      believes Rs i φ w = true ∧ φ w = false := by
  -- 2-world counterexample: W = Bool, agent sees only `true` from both worlds
  refine ⟨Bool, Unit, ?_, fun _ w _ => w, (), fun w => w, false, ?_⟩
  · exact {
      worlds := [true, false]
      complete := fun w => by cases w <;> simp
    }
  · constructor
    · -- believes: at false, accessible worlds = {true, false} filtered by R
      -- R false v = v (the identity on Bool viewed as: v itself)
      -- So accessible = filter (fun v => v) [true, false] = [true]
      -- all [true] (fun w => w) = true
      decide
    · rfl

/-! ## Common Ground as Common Knowledge

@cite{stalnaker-2002}: the common ground is the set of propositions that
are common knowledge among the discourse participants. -/

/-- A common ground is grounded in common knowledge when its context
    set equals the intersection of what is commonly known. -/
def _root_.Core.CommonGround.CG.groundedIn {W E : Type*} [FiniteWorlds W]
    (cg : CG W) (Rs : AgentAccessRel W E) (group : List E)
    (bound : ℕ) : Prop :=
  ∀ w, cg.contextSet w ↔
    (cg.propositions.all fun p =>
      commonKnowledge Rs group p bound w) = true

/-! ## Bridge to EpistemicScale

An S5 frame (reflexive + Euclidean accessibility) induces an
`EpistemicSystemW` via Lewis's l-lifting. This connects the
syntactic side (Kripke frames, correspondence theorems in
`ModalLogic.lean`) to the algebraic side (plausibility measures,
representation theorems in `EpistemicScale/`). -/

/-- An S5 accessibility relation induces a world ordering for
    `halpernLift`: w ≥ v iff w is accessible from v. -/
def s5ToWorldOrder {W : Type*} (R : AccessRel W) (w v : W) : Prop :=
  R v w = true

/-- An S5 frame yields an `EpistemicSystemW` via l-lifting.

    The reflexivity of R gives reflexivity of the world ordering;
    `halpernSystemW` does the rest. -/
def s5ToSystemW {W : Type*}
    (R : AccessRel W) (hRefl : Core.ModalLogic.Refl R) :
    Core.Scale.EpistemicSystemW W :=
  Core.Scale.halpernSystemW (s5ToWorldOrder R) (fun w => hRefl w)

end Semantics.Modality.EpistemicLogic
