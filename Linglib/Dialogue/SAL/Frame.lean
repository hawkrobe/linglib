import Mathlib.Data.Set.Basic
import Linglib.Core.Logic.Intensional.Defs

/-!
# SAL Commitment-State Frame
@cite{van-der-leer-2026} @cite{bary-2025} @cite{cohen-krifka-2014}
@cite{krifka-2015} @cite{krifka-2024} @cite{geurts-2019}
@cite{asher-lascarides-2008}

`CommitmentState W A` is van der Leer 2026 Definition 2: the basic
discourse state for **SAL** (Speech Act Logic). A multi-relational
Kripke frame with separate doxastic and deontic accessibility
relations, indexed respectively by single agents and ordered agent
pairs:

```
c = ⟨W^c, {B^c_a}_{a∈A}, {O^c_{a,b}}_{(a,b)∈A²}, I^c⟩
```

* `W^c` — possible worlds at this state
* `B^c_a` — agent `a`'s doxastic accessibility (KD45: serial,
  transitive, Euclidean) → standard belief axioms
* `O^c_{a,b}` — agent `a`'s commitment-towards-`b` accessibility
  (K4 + Eucl., **NOT serial** — to allow commitment violations)
* `I^c` — atomic-proposition valuation

The intentional weakening of seriality on the deontic relation is
the substrate-level fact that lets SAL express commitment violation
(van der Leer 2026 §2.2, around Theorem 33).

## Why a separate frame from existing Kripke substrate

`Core/Logic/Intensional/Defs.lean` provides single-relation Kripke
infrastructure (`AccessRel W`, `IsTransitive`, `IsEuclidean`,
`IsSerial`, ...). SAL needs a multi-relational frame: belief AND
commitment, the latter indexed by ordered agent pairs. This file
bundles both relation families with their KD45/K4 frame conditions
and the valuation, into one record per discourse state.

## Relation to existing dialogue substrate

`Dialogue/CommitmentSpace.lean` (Krifka 2015) treats a
"commitment state" as a list of `IndexedCommitment`s (set-of-
propositions). SAL refines this: each Krifka-state is now a full
Kripke frame whose deontic relation is restricted to commitment-
satisfying worlds. The Krifka level is recoverable as the projection
that intersects all `O_{a,b}`-accessible worlds.

## Frame conditions reuse

We reuse the existing `Core.Logic.Intensional.{IsTransitive,
IsEuclidean, IsSerial}` substrate — no fresh predicates.
-/

namespace Dialogue.SAL

open Core.Logic.Intensional (AccessRel AgentAccessRel IsTransitive IsEuclidean IsSerial)

/-- Pair-indexed deontic accessibility: each ordered agent pair has its
    own commitment-relation over worlds. The deontic counterpart of
    `Core.Logic.Intensional.AgentAccessRel`, which is unary (only one
    accessing agent). The pair indexing reflects van der Leer 2026's
    point that commitment is ternary `C_{a,b} π` — `a` is committed
    *towards* `b` to `π`. No analogue exists in linglib's existing
    epistemic substrate (`Semantics/Modality/EpistemicLogic.lean`),
    which only formalises unary belief/knowledge. -/
abbrev PairAccessRel (W A : Type*) := A → A → AccessRel W

/-- A commitment state: the multi-relational Kripke frame at the heart
    of van der Leer 2026's **SAL**.

    `W` is the world type (typically a finite or countable set of
    possible discourse worlds). `A` is the agent type.

    The frame conditions are recorded as separate `Prop`-valued
    field-companions (rather than as typeclass instances) because the
    same `CommitmentState` may need to be inspected for partial
    properties — e.g. Theorem 33 produces a state where `O_{a,b}`
    is empty (the violation), so seriality of `O` is intentionally
    not required. -/
structure CommitmentState (W : Type*) (A : Type*) where
  /-- Doxastic accessibility per agent. Reuses
      `Core.Logic.Intensional.AgentAccessRel` so any consumer of
      epistemic / doxastic substrate (`EpistemicLogic.knows`,
      `everyoneKnows`, `commonBelief`, etc.) can be applied directly
      via `c.belief`. -/
  belief : AgentAccessRel W A
  /-- Commitment relation per ordered agent pair: `commitment a b w v`
      means at world `w`, world `v` is among those compatible with
      everything `a` is committed to towards `b`. Uses the SAL-specific
      `PairAccessRel` (no equivalent in `Core.Logic.Intensional` —
      commitment is genuinely ternary). -/
  commitment : PairAccessRel W A
  /-- Atomic-proposition valuation. -/
  interp : String → Set W
  -- Frame conditions on belief (KD45):
  belief_trans : ∀ a, IsTransitive (belief a)
  belief_eucl : ∀ a, IsEuclidean (belief a)
  belief_serial : ∀ a, IsSerial (belief a)
  -- Frame conditions on commitment (K4 + Eucl., NOT serial — by design):
  commitment_trans : ∀ a b, IsTransitive (commitment a b)
  commitment_eucl : ∀ a b, IsEuclidean (commitment a b)

namespace CommitmentState

variable {W : Type*} {A : Type*}

/-- The trivial state where every world is doxastically accessible
    from every world for every agent, and similarly for commitment.
    All atoms are true everywhere. Useful as a baseline against which
    discourse updates restrict. -/
def trivial : CommitmentState W A where
  belief := fun _ _ _ => True
  commitment := fun _ _ _ _ => True
  interp := fun _ => Set.univ
  belief_trans := fun _ _ _ _ _ _ => True.intro
  belief_eucl := fun _ _ _ _ _ _ => True.intro
  belief_serial := fun _ w => ⟨w, True.intro⟩
  commitment_trans := fun _ _ _ _ _ _ _ => True.intro
  commitment_eucl := fun _ _ _ _ _ _ _ => True.intro

/-- A state's commitment relation between two agents is *empty* when
    no world is accessible from any other — operationally, the agent
    is committed to a contradiction. This is the witness for
    van der Leer 2026 Definition 16 (Violation). -/
def commitmentEmpty (c : CommitmentState W A) (a b : A) : Prop :=
  ∀ w v, ¬ c.commitment a b w v

/-- Update the commitment relation between `a` and `b` to retain only
    those edges that point to worlds in `restrict`.

    Mathematical content: `O^c[π]_{a,b} = O^c_{a,b} ∩ {(w, v) | v ∈ π}`.

    This is the lift of van der Leer 2026 Definition 4 (commitment
    state update with proposition `π`) to the level of the underlying
    set of worlds. The full SAL update consumes a *truth set* `π : Set
    W` and restricts the commitment edges to π-worlds.

    All other relations are preserved. The frame conditions on the
    restricted relation are immediate from the unrestricted ones
    (intersection preserves transitivity/Euclideanness; we re-prove
    them locally for clarity). -/
def restrictCommitment (c : CommitmentState W A) (a b : A) (π : Set W) :
    CommitmentState W A where
  belief := c.belief
  -- Narrow the (a,b) edge to π-targets; leave other edges alone.
  -- Encoded as a conjunction with an implication so we don't need
  -- `DecidableEq A` (every relation projects through `c.commitment`
  -- and conjoins π-membership only when the agent pair matches).
  commitment := fun a' b' w v =>
    c.commitment a' b' w v ∧ ((a' = a ∧ b' = b) → v ∈ π)
  interp := c.interp
  belief_trans := c.belief_trans
  belief_eucl := c.belief_eucl
  belief_serial := c.belief_serial
  commitment_trans := by
    intro a' b' w v u hwv hvu
    refine ⟨c.commitment_trans a' b' w v u hwv.1 hvu.1, ?_⟩
    intro h
    exact hvu.2 h
  commitment_eucl := by
    intro a' b' w v u hwv hwu
    refine ⟨c.commitment_eucl a' b' w v u hwv.1 hwu.1, ?_⟩
    intro h
    exact hwu.2 h

/-- Restricting commitment by `π` only narrows the (a,b) edge: for
    other pairs, the unchanged relation is recovered (the conjoined
    implication is vacuously true). -/
@[simp] theorem restrictCommitment_other
    (c : CommitmentState W A) (a b : A) (π : Set W) (a' b' : A)
    (h : ¬ (a' = a ∧ b' = b)) (w v : W) :
    (c.restrictCommitment a b π).commitment a' b' w v ↔ c.commitment a' b' w v := by
  simp only [restrictCommitment]
  exact ⟨fun ⟨hcom, _⟩ => hcom, fun hcom => ⟨hcom, fun hh => absurd hh h⟩⟩

/-- Belief is unchanged by a commitment-restriction. -/
@[simp] theorem restrictCommitment_belief
    (c : CommitmentState W A) (a b : A) (π : Set W) :
    (c.restrictCommitment a b π).belief = c.belief := rfl

/-- The valuation is unchanged by a commitment-restriction. -/
@[simp] theorem restrictCommitment_interp
    (c : CommitmentState W A) (a b : A) (π : Set W) :
    (c.restrictCommitment a b π).interp = c.interp := rfl

end CommitmentState

end Dialogue.SAL
