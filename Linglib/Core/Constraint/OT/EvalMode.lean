import Linglib.Core.Constraint.Evaluation

/-!
# OT — Evaluation Mode (Parallel vs Directional)
@cite{eisner-2000} @cite{eisner-2002} @cite{lamont-2022a} @cite{lamont-2022b}

Encodes @cite{lamont-2022b}'s reframing: directionality is a property of
EVAL, not of constraints. We do **not** define
`DirectionalConstraint C := C → List Nat` — that is the obsolete
constraint-side encoding. Instead, an `EvalMode` parameter governs how
violation profiles are lex-compared.

## Encoding convention

A constraint's violation profile is a `List Nat` interpreted as an
**indicator vector**: position `i` of the list records the violation
status at *position `i` of the form*. For binary violations, entries
are `0` (no violation) or `1` (violation present). For gradient
violations, entries are arbitrary `Nat`s.

Under this convention:
- `parallel`     — classical OT: profile is conventionally a singleton
                   `[count]` (total violation count). `le` uses
                   `LexLE`, which on singletons reduces to `Nat ≤`.
- `directional .leftToRight` — @cite{eisner-2000}'s left-to-right
                   evaluation. Indicator vector is in left-to-right
                   position order; `LexLE` compares from the leftmost
                   position. The candidate without a violation at the
                   first differing left position wins.
- `directional .rightToLeft` — mirror. `LexLE` compares the *reversed*
                   indicator vectors, so the rightmost-position
                   comparison fires first.

## Why no sorting

An earlier version of this file sorted position vectors ascending
before lex-comparing under `directional .leftToRight`. That destroyed
the position information: for input `/kāk^H + rī^H + dō^H/` (paper,
fig. 3), the three depth-1 candidates have indicator vectors
`[0,1,1]`, `[1,0,1]`, `[1,1,0]` — all sort to `[0,1,1]`, making them
indistinguishable. The correct semantics is plain `LexLE` on the
position-ordered indicator (no sorting): then `[0,1,1] < [1,0,1] <
[1,1,0]` lex, picking the leftmost-deletion candidate as the winner —
which is what @cite{mcpherson-lamont-2026} require.

The forgetful map `count := positions.length` lets a counting constraint
embed cleanly into the directional setting as the degenerate case where
every violation collapses to a single tally. The `EvalMode.le_singleton`
theorem is the structural soundness statement: when comparing two
single-violation profiles, all `EvalMode`s agree with `Nat ≤`. **Note**:
multi-violation profiles distinguish the modes — the paper's whole
argument (paper, eqs. 60–62) hinges on parallel and directional eval
giving different winners for `/kāk^H + rī^H + dō^H/`.

## Why this lives in `Core/Constraint/OT/` rather than `Phonology/`

`EvalMode` is a property of the OT evaluation procedure, not of the
phonology-specific candidate type. Like `ERC`, it lives at the framework
layer so that future phonology-, syntax-, and pragmatics-side users can
share one notion of directional EVAL.

## Sibling, not refactor

This file does **not** modify `NamedConstraint.eval : C → Nat` (which is
load-bearing for `Weighted.lean`/`MaxEnt.lean`/`NoisyHG.lean` — see
`Core/Constraint/Evaluation.lean`). The directional dispatch is consumed
by `HarmonicSerialism.lean`'s combinator, which currently routes the
`directional` arm to the parallel optimum as a stub; a true
`DirectionalTableau` consumer lands when a study file requires it.
-/

namespace Core.Constraint.OT

/-- Direction of lex comparison on violation position vectors.
    @cite{eisner-2000} §3, @cite{eisner-2002}. -/
inductive Direction
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr, Inhabited

/-- Evaluation mode for the OT EVAL function.

    `parallel` is classical @cite{prince-smolensky-1993} OT. `directional`
    instances correspond to @cite{eisner-2000}'s direction of evaluation;
    @cite{lamont-2022b} reframes directionality as a property of EVAL
    (not of constraints), and shows it is needed to break ties locally
    without invoking globally-aware tie-breakers. -/
inductive EvalMode
  | parallel
  | directional (dir : Direction)
  deriving DecidableEq, Repr, Inhabited

namespace EvalMode

open Core.Constraint.Evaluation in
/-- Compare two indicator-vector violation profiles under an `EvalMode`,
    returning a `Prop` (decidable). The result `EvalMode.le m a b` reads
    "candidate `a` is at least as harmonic as candidate `b` under `m`."

    Convention: `a, b : List Nat` are indicator vectors with positions
    in left-to-right order (entry `i` = violation status at position `i`
    of the form). For parallel constraints, the convention is a
    singleton `[count]`; the modes coincide on singletons.

    - `parallel`: `LexLE a b` directly (Layered Grounding).
    - `directional .leftToRight`: `LexLE a b` — same as `parallel`,
      because the convention puts positions in left-to-right order
      already, and `LexLE` compares from the leftmost entry.
    - `directional .rightToLeft`: `LexLE a.reverse b.reverse` — compare
      from the rightmost entry by reversing both vectors.

    The substrate keeps `parallel` and `directional .leftToRight` as
    distinct EvalMode cases (even though `le` is the same function for
    them) so that downstream consumers can dispatch on the mode at
    higher levels (e.g., a `DirectionalTableau` may ONLY accept
    `directional` modes; a count-based `Tableau` may ONLY accept
    `parallel`). -/
def le : EvalMode → List Nat → List Nat → Prop
  | .parallel,                a, b => LexLE a b
  | .directional .leftToRight, a, b => LexLE a b
  | .directional .rightToLeft, a, b => LexLE a.reverse b.reverse

instance (m : EvalMode) (a b : List Nat) : Decidable (le m a b) := by
  cases m with
  | parallel => exact (inferInstance : Decidable (Core.Constraint.Evaluation.LexLE a b))
  | directional dir =>
    cases dir with
    | leftToRight =>
      exact (inferInstance : Decidable (Core.Constraint.Evaluation.LexLE a b))
    | rightToLeft =>
      exact (inferInstance : Decidable (Core.Constraint.Evaluation.LexLE a.reverse b.reverse))

/-- Single-element `LexLE` reduces to `Nat ≤`. Local helper used to
    close `le_singleton`; not promoted to `Core/Constraint/Evaluation.lean`
    because that file is not in scope for substrate-extension. -/
private theorem lexLE_singleton_iff (k k' : Nat) :
    Core.Constraint.Evaluation.LexLE [k] [k'] ↔ k ≤ k' := by
  refine ⟨fun h => ?_, fun hle => ?_⟩
  · rcases h with hlt | ⟨heq, _⟩
    exacts [Nat.le_of_lt hlt, heq.le]
  · rcases lt_or_eq_of_le hle with hlt | heq
    exacts [Or.inl hlt, Or.inr ⟨heq, trivial⟩]

/-- **Single-violation degeneracy.** When comparing two profiles each
    consisting of a single violation count `[k]` and `[k']`, all
    `EvalMode`s agree with `Nat ≤`. This is the structural reason that
    a counting constraint (which records `[k]` for `k` violations as a
    single position-vector slot) embeds cleanly into the directional
    setting as a degenerate case — and the algebraic justification for
    why `NamedConstraint.eval : C → Nat` (count-based) and the
    directional indicator-vector encoding agree on simple cases. -/
theorem le_singleton (m : EvalMode) (k k' : Nat) :
    le m [k] [k'] ↔ k ≤ k' := by
  rcases m with _ | (_ | _) <;> exact lexLE_singleton_iff k k'

end EvalMode

end Core.Constraint.OT
