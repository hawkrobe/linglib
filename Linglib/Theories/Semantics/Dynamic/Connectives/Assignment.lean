import Linglib.Core.Assignment
import Linglib.Theories.Semantics.Dynamic.Connectives.Defs

/-!
# Dynamic Quantification over `Assignment E`
@cite{groenendijk-stokhof-1991} @cite{muskens-1996}

Substrate operations specialized to the Tarski-style assignment state
`Assignment E := Nat → E` (from `Core.Assignment`).

`AssignmentStructure` (in `Dynamic/Core/DynamicTy2.lean`) takes abstract drefs
`S → E`, but only *projection* drefs (`fun g => g n`) make sense for the concrete
`Assignment E` type — there's no canonical way to extend `g : Assignment E` along
an arbitrary `(λ g => g 0 + g 1) : Assignment ℕ → ℕ`. So the typeclass cannot be
instantiated for `Assignment E` directly.

This file provides the natural-number-indexed operators that DPL, CDRT, FCS,
PLA, and ICDRT all use under different paper-anchored names. They're substrate
because they're fully generic over `E`, taking any `Nat` index.

| Operator | Paper-anchored alias | Type |
|---|---|---|
| `randomAssignAt n` | DPL `[x_n]`, FCS file-card opening | `DRS (Assignment E)` |
| `existsAt n φ` | DPL `∃x_n.φ`, CDRT `[u_n]; φ` | `DRS (Assignment E) → DRS (Assignment E)` |
| `forallAt n φ` | DPL `∀x_n.φ` | `DRS (Assignment E) → DRS (Assignment E)` |
| `closeAt φ` | DPL `◇φ`, K&R existential closure | `DRS (Assignment E) → DRS (Assignment E)` |

The `existsAt` / `forallAt` decomposition is mathlib-style: `existsAt n` is
`dseq` after `randomAssignAt n`; `forallAt n` is `test ∘ dneg ∘ existsAt n ∘ test ∘ dneg`.
The decomposition lemmas are immediate by definitional unfolding.
-/

namespace Semantics.Dynamic.Core

open _root_.Core (Assignment)
open Semantics.Dynamic.Core.DynProp

variable {E : Type*}

-- ════════════════════════════════════════════════════════════════
-- § 1. Random Assignment at a Nat Index
-- ════════════════════════════════════════════════════════════════

/-- The "open file card n" operation: `g[n↦?]` non-deterministically. -/
def randomAssignAt (n : Nat) : DRS (Assignment E) :=
  fun g h => ∃ d : E, h = g.update n d

-- ════════════════════════════════════════════════════════════════
-- § 2. Dynamic Existential at a Nat Index
-- ════════════════════════════════════════════════════════════════

/-- `existsAt n φ` is `dseq (randomAssignAt n) φ`. Holds at `(g, h)` iff
some witness `d : E` makes `φ` accept the input `g[n↦d]` and produce `h`. -/
def existsAt (n : Nat) (φ : DRS (Assignment E)) : DRS (Assignment E) :=
  dseq (randomAssignAt n) φ

/-- The decomposition: `existsAt = dseq ∘ randomAssignAt`. -/
@[simp] theorem existsAt_eq_dseq (n : Nat) (φ : DRS (Assignment E)) :
    existsAt n φ = dseq (randomAssignAt n) φ := rfl

/-- Direct unfolding: `existsAt n φ g h ↔ ∃ d : E, φ (g.update n d) h`. -/
theorem existsAt_iff (n : Nat) (φ : DRS (Assignment E)) (g h : Assignment E) :
    existsAt n φ g h ↔ ∃ d : E, φ (g.update n d) h := by
  simp only [existsAt, dseq, randomAssignAt]
  constructor
  · rintro ⟨k, ⟨d, rfl⟩, hφ⟩; exact ⟨d, hφ⟩
  · rintro ⟨d, hφ⟩; exact ⟨g.update n d, ⟨d, rfl⟩, hφ⟩

-- ════════════════════════════════════════════════════════════════
-- § 3. Dynamic Universal at a Nat Index
-- ════════════════════════════════════════════════════════════════

/-- `forallAt n φ`: a test that requires `φ` to succeed for every value at `n`.
Definitionally `test (dneg (existsAt n (test (dneg φ))))` — the standard
DPL/Muskens reduction `∀ ≈ ¬∃¬`. -/
def forallAt (n : Nat) (φ : DRS (Assignment E)) : DRS (Assignment E) :=
  test (dneg (existsAt n (test (dneg φ))))

/-- Direct truth condition: `forallAt n φ g h ↔ g = h ∧ ∀ d, ∃ k, φ (g.update n d) k`. -/
theorem forallAt_iff (n : Nat) (φ : DRS (Assignment E)) (g h : Assignment E) :
    forallAt n φ g h ↔ g = h ∧ ∀ d : E, ∃ k, φ (g.update n d) k := by
  simp only [forallAt, test, dneg, existsAt, dseq, randomAssignAt]
  constructor
  · rintro ⟨rfl, hneg⟩
    refine ⟨rfl, fun d => ?_⟩
    by_contra hne
    push_neg at hne
    exact hneg ⟨g.update n d, ⟨g.update n d, ⟨d, rfl⟩, rfl, fun ⟨k, hφ⟩ => hne k hφ⟩⟩
  · rintro ⟨rfl, hall⟩
    refine ⟨rfl, ?_⟩
    rintro ⟨_, ⟨_, ⟨d, rfl⟩, rfl, hneg⟩⟩
    exact hneg (hall d)

-- ════════════════════════════════════════════════════════════════
-- § 4. Existential Closure (◇)
-- ════════════════════════════════════════════════════════════════

/-- `closeAt φ`: a test that succeeds iff `φ` has any output. Equals
`test (closure φ)` from `Connectives.Defs`. -/
def closeAt (φ : DRS (Assignment E)) : DRS (Assignment E) :=
  test (closure φ)

@[simp] theorem closeAt_eq (φ : DRS (Assignment E)) :
    closeAt φ = test (closure φ) := rfl

end Semantics.Dynamic.Core
