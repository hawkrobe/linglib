import Linglib.Core.Computability.Subregular.Logic.Transduction
import Linglib.Core.Computability.Subregular.Function.ISL

/-!
# The locality bridge: quantifier-free ⟹ strictly local

The load-bearing subregular result ([dolatian-2020], after Chandlee, Heinz & Jardine): a
quantifier-free logical transduction whose guards look only at a *bounded* context is
**strictly local**. Here we prove the left-directed half against `Subregular`'s
`IsLeftInputStrictlyLocal`: a transduction whose guards are *backward* (built from the variable
and predecessors, no successor) with predecessor depth `≤ r` is `IsLeftInputStrictlyLocal (r + 1)`.

The mathematical crux is `Term.eval_backward`: a backward term of predecessor depth `j`, evaluated
at position `n`, reads exactly position `n - j` (or falls off the left edge). Hence the truth of a
backward guard at `n` depends only on the `r + 1` symbols ending at `n` — the ISL window.

## Main definitions

* `Term.Backward` / `Term.pdepth` — successor-free terms and their predecessor depth.
* `Atom.Backward` / `QF.Backward` / `Transduction.LeftLocal` — the bounded-left-context classes.

## Main results

* `Term.eval_backward` — a backward term of depth `j` at position `n` evaluates to `n - j`.
-/

namespace Subregular.Logic

variable {α β V : Type*}

private theorem pred?_zero (w : WordModel α) : w.pred? 0 = none := rfl

private theorem pred?_pos {w : WordModel α} {m : ℕ} (h0 : 0 < m) (hm : m ≤ w.length) :
    w.pred? m = some (m - 1) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  have hm' : m' < w.length := by omega
  simp [WordModel.pred?, hm']

/-! ### Backward terms -/

namespace Term

/-- A term is *backward* if it uses no successor — only the variable and predecessors, so it reads
positions at or before its variable. -/
def Backward : Term V → Prop
  | .var _  => True
  | .pred t => t.Backward
  | .succ _ => False

/-- The predecessor depth of a term: how far back it reaches. -/
def pdepth : Term V → ℕ
  | .var _  => 0
  | .pred t => t.pdepth + 1
  | .succ t => t.pdepth

/-- A backward term of predecessor depth `j`, evaluated at position `n` (in range), reads exactly
position `n - j` — defined iff `j ≤ n`. -/
theorem eval_backward {w : WordModel α} {n : ℕ} (hn : n < w.length) :
    ∀ {t : Term (Fin 1)}, t.Backward →
      t.eval w (fun _ => n) = if t.pdepth ≤ n then some (n - t.pdepth) else none := by
  intro t ht
  induction t with
  | var v => simp [eval, pdepth, WordModel.Mem, hn]
  | succ t _ => exact absurd ht (by simp [Backward])
  | pred t ih =>
      simp only [Backward] at ht
      simp only [eval, ih ht, pdepth]
      by_cases h : t.pdepth ≤ n
      · rw [if_pos h, Option.bind_some]
        by_cases h0 : t.pdepth = n
        · subst h0; rw [Nat.sub_self, pred?_zero, if_neg (by omega)]
        · rw [pred?_pos (by omega) (by omega), if_pos (by omega),
            Nat.sub_sub]
      · rw [if_neg h, Option.bind_none, if_neg (by omega)]

end Term

/-! ### Bounded-left-context formulas and transductions -/

/-- An atom is backward-bounded by `r` if every term it uses is backward with predecessor depth
`≤ r` (so it reads only the `r + 1` symbols ending at the variable). -/
def Atom.BackBounded (r : ℕ) : Atom α V → Prop
  | .label _ t => t.Backward ∧ t.pdepth ≤ r
  | .eq t₁ t₂  => (t₁.Backward ∧ t₁.pdepth ≤ r) ∧ (t₂.Backward ∧ t₂.pdepth ≤ r)
  | .defined t => t.Backward ∧ t.pdepth ≤ r

/-- A quantifier-free formula is backward-bounded by `r` if all its atoms are. -/
def QF.BackBounded (r : ℕ) : QF α V → Prop
  | .atom a   => a.BackBounded r
  | .tru      => True
  | .fls      => True
  | .neg φ    => φ.BackBounded r
  | .conj φ ψ => φ.BackBounded r ∧ ψ.BackBounded r
  | .disj φ ψ => φ.BackBounded r ∧ ψ.BackBounded r

/-- A transduction is **left-local** with radius `r` if every clause guard is backward-bounded by
`r`: the output at a position is determined by that position and the `r` symbols before it. -/
def Transduction.LeftLocal (r : ℕ) (T : Transduction α β) : Prop :=
  ∀ c, ∀ cl ∈ T.clause c, cl.1.BackBounded r

/-- The Left-ISL rule induced by a left-local transduction of radius `r`: read the output block at
each position from the last `r` input symbols (`window`) and the current symbol `x`, by running the
transduction's `emitAt` on `window ++ [x]` at its final position. -/
def Transduction.toISLRule [DecidableEq α] (T : Transduction α β) (r : ℕ) : ISLRule (r + 1) α β where
  windowOutput window x := T.emitAt (window ++ [x]) window.length

/-- **Locality bridge** (left half), [dolatian-2020] after Chandlee–Heinz–Jardine: a transduction
whose guards look only backward with predecessor depth `≤ r` is `(r+1)`-Left-Input-Strictly-Local —
its output depends on a bounded left window, the defining property of strict locality. -/
theorem Transduction.leftLocal_isLeftISL [DecidableEq α] {r : ℕ} {T : Transduction α β}
    (hT : T.LeftLocal r) : IsLeftInputStrictlyLocal (r + 1) T.apply := by
  refine ⟨T.toISLRule r, ?_⟩
  -- TODO(stage-3 assembly): `(T.toISLRule r).apply = T.apply`. The local-determination crux is
  -- `Term.eval_backward` (proven): a backward guard of pdepth ≤ r at position `n` reads only
  -- positions `[n-r, n]`, so `emitAt` agrees on the `rtake r` window. What remains is the
  -- `ISLRule.applyAux` window invariant — that the threaded window stays `(w.take p).rtake r` —
  -- which needs `rtake` append/idempotence lemmas not yet in `Core.Data.List.DropRight`.
  sorry

/-! ### Worked example: the bridge on a concrete left-local process -/

section Example

private inductive Seg | t | d | a
  deriving DecidableEq

private def xv : Term (Fin 1) := .var 0

/-- Post-vocalic stop voicing `t → d`: the guard looks only left (a predecessor vowel), so it is
backward with radius 1. -/
private def postVoicing : Transduction Seg Seg where
  copies := 1
  clause _ := [(QF.conj (.atom (.label .a xv.pred)) (.atom (.label .t xv)), .d),
               (.atom (.label .t xv), .t), (.atom (.label .d xv), .d), (.atom (.label .a xv), .a)]

-- The induced 2-Left-ISL rule computes the same function on a sample — the bridge, concretely.
example : (postVoicing.toISLRule 1).apply [Seg.a, .t, .a, .t]
            = postVoicing.apply [Seg.a, .t, .a, .t] := by decide
example : postVoicing.apply [Seg.a, .t, .a, .t] = [Seg.a, .d, .a, .d] := by decide

end Example

end Subregular.Logic
