import Linglib.Core.IntensionalLogic.Premise
import Mathlib.Data.Fintype.Basic

/-!
# Kratzer (1977) — Premise semantics worked example

@cite{kratzer-1977} @cite{kratzer-2012}

A concrete formalization of the New Zealand judgments scenario from §1.3
of @cite{kratzer-1977} (= Chapter 1 of @cite{kratzer-2012}), exercising
the API of `Core.IntensionalLogic.Premise`.

## The scenario

@cite{kratzer-1977} imagines a country whose entire common law consists
of three judgments:

1. *Murder is a crime.* — call this proposition `p`.
2. *Deer are personally responsible for damage they inflict on young
   trees.* — call this proposition `q`.
3. *Deer are not personally responsible for damage they inflict on young
   trees.* — proposition `¬q`.

The premise set `A = [p, q, ¬q]` is **inconsistent** (its intersection
is empty: no world makes `q` and `¬q` both true). Yet our intuitions
about modal claims relativized to *what the New Zealand judgments
provide* are crisp:

- (7) "Murder must be a crime." — TRUE
- (8) "It must be that murder is not a crime." — FALSE
- (9) "It is possible that deer are responsible." — TRUE
- (10) "It is possible that deer are not responsible." — TRUE
- (14) "It is possible that murder is not a crime." — FALSE

Kratzer's original Defs 5–6 (necessity = consequence, possibility =
compatibility) collapse on inconsistent `A`: by *ex falso quodlibet*,
**everything** follows from `A`, so `must p` and `must ¬p` are both
true, and **nothing** is compatible with `A`, so `can q` and `can ¬q`
are both false. Defs 7–8 — quantifying over the consistent subsets of
`A` and asking for an extension that supports the conclusion — recover
the intuitive predictions.

## What this study is

A Phenomenon-layer **integration test** for `Core.IntensionalLogic.Premise`:
it picks the worked example Kratzer uses to motivate the revision from
Defs 5–6 to Defs 7–8 and verifies, by `decide`, that the formalization
gets each prediction right and that the unrevised definitions fail in
exactly the way Kratzer says they do.
-/

namespace Phenomena.Modality.Studies.Kratzer1977

open Core.IntensionalLogic.Premise

/-! ## §1. The model

A four-world frame, indexed by `Fin 4`, that distinguishes the two
contingent dimensions of the scenario: whether murder is a crime
(`p`) and whether deer are responsible (`q`). All four combinations
are represented so that every singleton premise — `p`, `q`, `¬q`, `¬p`
— is individually consistent.

| world | p (murder is a crime) | q (deer responsible) |
|-------|-----------------------|----------------------|
| `w₀`  | true                  | true                 |
| `w₁`  | true                  | false                |
| `w₂`  | false                 | true                 |
| `w₃`  | false                 | false                |
-/

/-- "Murder is a crime." True at `w₀` and `w₁`. -/
def p : Fin 4 → Bool
  | 0 => true
  | 1 => true
  | 2 => false
  | 3 => false

/-- "Deer are personally responsible for damage they inflict on young trees."
    True at `w₀` and `w₂`. -/
def q : Fin 4 → Bool
  | 0 => true
  | 1 => false
  | 2 => true
  | 3 => false

/-- "Deer are not personally responsible…". The Boolean negation of `q`. -/
def negQ : Fin 4 → Bool := fun w => !(q w)

/-- "Murder is not a crime." The Boolean negation of `p`. -/
def negP : Fin 4 → Bool := fun w => !(p w)

/-- The premise set `A` of @cite{kratzer-1977} §1.3 — *what the New Zealand
    judgments provide*: the three rulings, taken together. -/
def A : List (Fin 4 → Bool) := [p, q, negQ]

/-- The constant modal restriction: at every world, the premise set is `A`.
    The scenario abstracts away from world-to-world variation in the
    judgments. -/
def f : Fin 4 → List (Fin 4 → Bool) := fun _ => A

/-! ## §2. `A` is inconsistent

The premise set contains both `q` and its Boolean negation, so its
intersection is empty. -/

theorem A_inconsistent : isConsistent A = false := by decide

/-! ## §3. Unrevised Defs 5–6 give paradoxical predictions

These two theorems are the formal counterpart of Kratzer's diagnosis
of the original definitions: they trivialize over an inconsistent `A`. -/

/-- Under the original Def 5 (`mustInView`), the inconsistent `A`
    entails *every* proposition — including `¬p`. This is the paradox
    of *ex falso quodlibet* that motivates the revision to Def 7. -/
theorem must_negP_under_def5 : mustInView f negP 0 = true := by decide

/-- Under the original Def 6 (`canInView`), nothing is compatible with
    the inconsistent `A` — including `q`, which intuitively *is*
    possible in view of the judgments. -/
theorem can_q_under_def6 : canInView f q 0 = false := by decide

/-! ## §4. Revised Defs 7–8 give the intuitive predictions

Each theorem corresponds to a sentence number from @cite{kratzer-1977}
§1.3, with the predicted truth value Kratzer argues for. -/

/-- (7) "Murder must be a crime" — TRUE under Def 7. The extension
    `[p, q]` (or `[p, ¬q]`) of any consistent subset of `A` entails `p`. -/
theorem sentence_7_must_p : mustInView' f p 0 = true := by decide

/-- (8) "It must be that murder is not a crime" — FALSE under Def 7.
    No consistent subset of `A` containing `p` extends to one entailing `¬p`. -/
theorem sentence_8_not_must_negP : mustInView' f negP 0 = false := by decide

/-- (9) "It is possible that deer are responsible" — TRUE under Def 8.
    Witness: take `B = [q]`; every consistent extension already contains `q`,
    so adding `q` preserves consistency. -/
theorem sentence_9_can_q : canInView' f q 0 = true := by decide

/-- (10) "It is possible that deer are not responsible" — TRUE under Def 8.
    Symmetric to (9), with witness `B = [¬q]`. -/
theorem sentence_10_can_negQ : canInView' f negQ 0 = true := by decide

/-- (14) "It is possible that murder is not a crime" — FALSE under Def 8.
    Every consistent subset of `A` extends to one containing `p`, and
    adding `¬p` to such a set is never consistent. -/
theorem sentence_14_not_can_negP : canInView' f negP 0 = false := by decide

/-! ## §5. The contrast in one place

Two theorems pinning the bug-vs-fix asymmetry: the revised definitions
agree with intuition exactly where the original definitions trivialize. -/

/-- Def 5 wrongly accepts `must ¬p`; Def 7 correctly rejects it. -/
theorem def5_vs_def7_negP :
    mustInView f negP 0 = true ∧ mustInView' f negP 0 = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Def 6 wrongly rejects `can q`; Def 8 correctly accepts it. -/
theorem def6_vs_def8_q :
    canInView f q 0 = false ∧ canInView' f q 0 = true := by
  refine ⟨?_, ?_⟩ <;> decide

end Phenomena.Modality.Studies.Kratzer1977
