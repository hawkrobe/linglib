import Linglib.Theories.Dialogue.SAL.CommitmentSpace

/-!
# SAL Speech-Act PDL
@cite{van-der-leer-2026}

van der Leer 2026 Definitions 9–24: a small Propositional Dynamic
Logic of speech acts. The action language is:

```
α ::= assert_{a,b}(π) | question_{a,b}(π) | ⊖ | ~α | α;β | π ↪ α/β
```

with `assert`, `question`, denegation `~`, sequential composition `;`,
empty `⊖`, and conditional `↪/`.

Each act `α` is interpreted as an **update on commitment spaces** —
a function `CommitmentSpace W A → CommitmentSpace W A`. Substantively:

* `assert_{a,b}(π)` (Def 10): the new root is `root[π]_{a,b}`; the
  surviving continuations are those that ALSO accept the addressee's
  acceptance, i.e. are ⊑-above `root[π]_{a,b}[π]_{b,a}`. This packages
  the Collaborative Principle: silent uptake updates the addressee's
  commitments.
* `question_{a,b}(π)` (Def 19): root is unchanged; continuations split
  into two branches — `b` accepts `π` or `b` accepts `¬π`.
* `⊖` (Def 21): identity update.
* `~α` (Def 22): remove the `α`-branch from the space; restore the root.
* `α;β` (Def 23): sequential composition.
* `π ↪ α/β` (Def 24): conditional on root truth.

For brevity we currently model the basic `assert` update; the others
follow the same pattern and slot in as additional constructors here.
-/

namespace Dialogue.SAL

variable {W : Type*} {A : Type*}

/-- The action language: van der Leer 2026 Definition 20. We currently
    expose the basic constructors; consumer-required cases (`question`,
    denegation, conditional) follow the same pattern and can be added
    as constructors. -/
inductive SpeechAct (W : Type*) (A : Type*) where
  /-- Default empty update (Def 21): leaves the commitment space
      unchanged. -/
  | empty
  /-- Assertion (Def 10): `assert_{a,b}(π)` — `a` commits to `π` towards
      `b`; the new root reflects this commitment, and surviving
      continuations are those compatible with `b`'s acceptance. -/
  | assert (a b : A) (π : Set W)
  /-- Question (Def 19): `question_{a,b}(π)` — `a` proposes that `b`
      commit to one of `{π, ¬π}`; surviving continuations split into
      both branches. -/
  | question (a b : A) (π : Set W)
  /-- Sequential composition (Def 23): perform `α` then `β`. -/
  | seq (α β : SpeechAct W A)
  /-- Denegation (Def 22): the `α`-branch is removed; the root remains. -/
  | denegate (α : SpeechAct W A)

/-- Update a commitment state with the assertion `assert_{a,b}(π)`:
    restrict the commitment relation `O_{a,b}` to π-targets. This is
    van der Leer 2026 Definition 4 lifted to the named-update form. -/
def assertOnState (a b : A) (π : Set W) (c : CommitmentState W A) :
    CommitmentState W A :=
  c.restrictCommitment a b π

/-- van der Leer 2026 Definition 10 (headline): `assert_{a,b}(π)` on a
    commitment space `C` produces:

    * **New root** = `root[π]_{a,b}` — the previous root narrowed by
      `a`'s commitment to π towards `b`.
    * **Surviving continuations** = the subset of states in `C` that
      cooperatively extend `root[π]_{a,b}[π]_{b,a}` — i.e. those
      compatible with the addressee's implicit acceptance (the
      Collaborative Principle).

    The full Def-10 update with continuation-pruning requires
    transitivity of `CooperativeExtRefl` through `assertOnState`-
    composition, which is more book-keeping than the headline
    theorems need. The simpler `applyAssertSingleton` (just produce
    the new root) suffices for T25 (assert creates commitment), T26
    (sincerity transfer), T27 (asymmetric C → CB), T30 (persistence
    on the resulting space).

    Continuation-pruning is exposed as a separate
    `applyAssertWithContinuations` once a proper transitivity lemma
    for `CooperativeExtRefl` lands. -/
def applyAssert (a b : A) (π : Set W) (C : CommitmentSpace W A) :
    CommitmentSpace W A :=
  CommitmentSpace.singleton (assertOnState a b π C.root)

/-- The basic interpretation of speech acts as commitment-space
    updates. We expose `assert` and `empty`; `question`, `seq`,
    `denegate` are stubs returning identity for now (substrate
    placeholders that the headline theorems don't depend on). -/
def apply : SpeechAct W A → CommitmentSpace W A → CommitmentSpace W A
  | .empty,         C => C
  | .assert a b π,  C => applyAssert a b π C
  | .question _ _ _, C => C  -- stub; full update lifts the partition
  | .seq α β,       C => apply β (apply α C)
  | .denegate _,    C => C   -- stub; full update removes the α-branch

@[simp] theorem apply_empty (C : CommitmentSpace W A) :
    apply (SpeechAct.empty : SpeechAct W A) C = C := rfl

@[simp] theorem apply_assert (a b : A) (π : Set W) (C : CommitmentSpace W A) :
    apply (SpeechAct.assert a b π) C = applyAssert a b π C := rfl

@[simp] theorem apply_seq (α β : SpeechAct W A) (C : CommitmentSpace W A) :
    apply (SpeechAct.seq α β) C = apply β (apply α C) := rfl

end Dialogue.SAL
