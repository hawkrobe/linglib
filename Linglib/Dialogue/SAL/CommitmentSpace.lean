import Mathlib.Order.Basic
import Linglib.Dialogue.SAL.Modal

/-!
# SAL Commitment Spaces
@cite{van-der-leer-2026} @cite{cohen-krifka-2014} @cite{krifka-2015}

van der Leer 2026 Definitions 7–8: a **commitment space** is a set of
commitment states organised by a *cooperative continuation order*
`⊑`, with a unique ⊑-minimal **root** representing the current
discourse state. The non-root members are *projected futures*
representing admissible continuations.

```
c ⊑ c'  iff  W^c = W^c'
              ∧ B^c'_a ⊆ B^c_a       (for all a)
              ∧ O^c'_{a,b} ⊆ O^c_{a,b} (for all a, b)
              ∧ at least one inclusion is strict
```

i.e. `c'` is a *tightening* of `c` — beliefs and commitments only
narrow (or stay the same) as discourse progresses; the world type is
fixed across the space.

The improper version `⊑'` is `⊑ ∪ {(c,c)}` (reflexive closure).

## Heritage and projection

Krifka's commitment-space framework treats a "state" as a list of
indexed commitments. Here a state is a full Kripke frame whose
relations encode the same content. The Krifka level is recoverable
by intersecting all `O_{a,b}`-accessible worlds at the root state —
that intersection IS the propositions Krifka tracks.

Bary 2025's 5-tuple `⟨c, cg, dc_A, dc_B, P, Q⟩` likewise projects:
`cg` is the intersection of all `B_a`-accessible worlds at the root,
`dc_x` is the intersection of `O_{x,y}` for the relevant `y`.
-/

namespace Dialogue.SAL

variable {W : Type*} {A : Type*}

/-- van der Leer 2026 Definition 7 (cooperative continuation, strict
    `⊑`): `c'` cooperatively extends `c` iff:

    1. They share the world type (`W^c = W^c'` is enforced
       structurally — both have type `CommitmentState W A`).
    2. `c'`'s belief relations are sub-relations of `c`'s.
    3. `c'`'s commitment relations are sub-relations of `c`'s.
    4. At least one inclusion is strict somewhere — i.e. `c ≠ c'`.

    The strict-extension flag (`c ≠ c'`) is the formal counterpart
    of paper-(7)'s "at least one strict inclusion" — under the
    sub-relation conjunction, equality everywhere collapses to
    `c = c'`. -/
def CooperativeExt (c c' : CommitmentState W A) : Prop :=
  (∀ a w v, c'.belief a w v → c.belief a w v) ∧
  (∀ a b w v, c'.commitment a b w v → c.commitment a b w v) ∧
  (c.interp = c'.interp) ∧
  c ≠ c'

/-- van der Leer 2026 improper-cooperative-extension: `c ⊑' c'` iff
    `c = c'` or `c ⊑ c'`. -/
def CooperativeExtRefl (c c' : CommitmentState W A) : Prop :=
  c = c' ∨ CooperativeExt c c'

/-- The improper extension is reflexive. -/
theorem cooperativeExtRefl_refl (c : CommitmentState W A) :
    CooperativeExtRefl c c := Or.inl rfl

/-- Cooperative extension is irreflexive (it requires `c ≠ c'`). -/
theorem not_cooperativeExt_self (c : CommitmentState W A) :
    ¬ CooperativeExt c c := fun h => h.2.2.2 rfl

/-- van der Leer 2026 Definition 8: a **commitment space** is a set of
    commitment states with a unique ⊑-minimal element (the root).

    The root is the *current* state of the discourse; the non-root
    members are *projected futures* representing admissible
    continuations (per the Collaborative Principle: silence after a
    speech act extends the space by tightening relations to those
    consistent with implicit acceptance). -/
structure CommitmentSpace (W : Type*) (A : Type*) where
  /-- The set of commitment states comprising the space. -/
  states : Set (CommitmentState W A)
  /-- The root: a distinguished current state. -/
  root : CommitmentState W A
  /-- The root is in the space. -/
  root_mem : root ∈ states
  /-- The root is ⊑'-below every state in the space (it is the
      ⊑-minimum: every other state cooperatively extends it). -/
  root_minimal : ∀ c ∈ states, CooperativeExtRefl root c

namespace CommitmentSpace

variable {W : Type*} {A : Type*}

/-- The trivial commitment space: a single state (the root) with no
    proper extensions. Useful as a baseline; corresponds to "no
    commitments yet, no projected futures". -/
def singleton (root : CommitmentState W A) : CommitmentSpace W A where
  states := {root}
  root := root
  root_mem := rfl
  root_minimal := fun c hc => by
    simp only [Set.mem_singleton_iff] at hc
    exact Or.inl hc.symm

@[simp] theorem singleton_root (c : CommitmentState W A) :
    (singleton c).root = c := rfl

@[simp] theorem singleton_states (c : CommitmentState W A) :
    (singleton c).states = {c} := rfl

/-- A proposition is **mutually committed** in a commitment space iff
    every agent is committed to every other agent at every state of
    the space. The Geurts 2019 fixed-point characterisation, lifted
    over the commitment-space level (van der Leer 2026 §2.1). -/
def MutuallyCommitted (C : CommitmentSpace W A) (π : Set W) : Prop :=
  ∀ c ∈ C.states, ∀ a b w, Committed c a b π w

/-- A proposition is **commonly believed** at world `w` of state `c`
    in the space iff `EpistemicLogic.commonBelief` holds for the given
    agent group up to the iteration bound. Delegates to the existing
    `Semantics/Modality/EpistemicLogic.commonBelief` substrate
    rather than re-stipulating; the SAL-side wrapper just selects the
    state's belief relation. -/
def CommonlyBelieved (c : CommitmentState W A) (group : List A)
    (π : Set W) (bound : ℕ) (w : W) : Prop :=
  Semantics.Modality.EpistemicLogic.commonBelief c.belief group
    (fun v => v ∈ π) bound w

end CommitmentSpace

end Dialogue.SAL
