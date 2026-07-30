import Linglib.Phonology.Subregular.Transduction
import Linglib.Phonology.Subregular.ISL

/-!
# The locality bridge: left-local ⟹ input strictly local

A local transduction whose guards look only at a *bounded left* context is **input strictly
local**: a transduction that is `LeftLocal r` (guards backward-bounded by `r`) is
`IsLeftInputStrictlyLocal (r + 1)`.

The mathematical crux is upstream (`Transduction.emitAt_eq_of_agree`, resting on
`Term.eval_backward`): a left-local transduction emits the same block at positions whose bounded
left contexts agree. This file threads that fact through the ISL window: the window maintained by
`ISLRule.applyAux` stays exactly the bounded left context, so the induced rule reproduces the
transduction's output.

## Main results

* `Transduction.toISLRule`: the ISL rule induced by a left-local transduction.
* `Transduction.leftLocal_isLeftISL`: a `LeftLocal r` transduction is
  `(r+1)`-Left-Input-Strictly-Local.
-/

namespace Subregular

variable {α β : Type*}

/-- The Left-ISL rule induced by a left-local transduction of radius `r`: read the output block at
each position from the last `r` input symbols (`window`) and the current symbol `x`, by running the
transduction's `emitAt` on `window ++ [x]` at its final position. -/
def Transduction.toISLRule [DecidableEq α] (T : Transduction α β) (r : ℕ) : ISLRule (r + 1) α β where
  windowOutput window x := T.emitAt (window ++ [x]) window.length

/-- The block a left-local transduction emits at position `p` depends only on the `r + 1` input
symbols ending at `p`: it equals the block emitted at the last position of that window. -/
private theorem Transduction.emitAt_local [DecidableEq α] {r : ℕ} {T : Transduction α β}
    (hT : T.LeftLocal r) {input : List α} {p : ℕ} (hp : p < input.length) :
    T.emitAt input p = T.emitAt ((input.take (p + 1)).rtake (r + 1)) (min r p) := by
  apply Transduction.emitAt_eq_of_agree hT hp
  · rw [List.length_rtake, List.length_take]; omega
  · intro j hj
    have hlen : (input.take (p + 1)).length = p + 1 := by rw [List.length_take]; omega
    rw [show (input.take (p + 1)).rtake (r + 1)
          = (input.take (p + 1)).drop ((input.take (p + 1)).length - (r + 1)) from rfl,
        List.getElem?_drop, hlen, List.getElem?_take, if_pos (by omega)]
    congr 1
    omega
  · intro j hj; omega

/-- Two nested tail-takes collapse to one: `(l.rtake m).rtake n = l.rtake (min n m)`. -/
private theorem rtake_rtake {γ : Type*} (l : List γ) (m n : ℕ) :
    (l.rtake m).rtake n = l.rtake (min n m) := by
  simp only [List.rtake_eq_reverse_take_reverse, List.reverse_reverse, List.take_take]

/-- Tail-taking a length-`r` window extended by one symbol re-takes the underlying list extended by
that symbol — the step that keeps the threaded ISL window equal to the bounded left context. -/
private theorem rtake_concat_rtake {γ : Type*} (l : List γ) (x : γ) (r : ℕ) :
    (l.rtake r ++ [x]).rtake r = (l ++ [x]).rtake r := by
  cases r with
  | zero => simp [List.rtake_zero]
  | succ r' =>
    rw [List.rtake_concat_succ, List.rtake_concat_succ, rtake_rtake,
        Nat.min_eq_left (Nat.le_succ r')]

/-- `toISLRule`'s window output is, by definition, `emitAt` on the window plus the current symbol. -/
private theorem Transduction.windowOutput_toISLRule [DecidableEq α] {r : ℕ} (T : Transduction α β)
    (window : List α) (x : α) :
    (T.toISLRule r).windowOutput window x = T.emitAt (window ++ [x]) window.length := rfl

/-- **Window-threading invariant.** Running the induced ISL rule from the bounded left context
`(input.take p).rtake r` over the remaining suffix `s` reproduces the transduction's own block
sequence over the input positions `p, p+1, …`. The induction maintains that the threaded window
stays exactly the `r`-symbol left context. -/
private theorem Transduction.applyAux_toISLRule_eq [DecidableEq α] {r : ℕ} {T : Transduction α β}
    (hT : T.LeftLocal r) (input : List α) :
    ∀ (s : List α) (p : ℕ), input = input.take p ++ s → p = (input.take p).length →
      ISLRule.applyAux (T.toISLRule r) ((input.take p).rtake r) s
        = (List.range' p s.length).flatMap (T.emitAt input) := by
  intro s
  induction s with
  | nil => intro p _ _; simp
  | cons x s' ih =>
    intro p hsplit hplen
    have hp : p < input.length := by
      have hcl := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons] at hcl
      omega
    have hx : input[p]? = some x := by
      rw [hsplit, List.getElem?_append_right (by omega)]
      simp [← hplen]
    have hpx : input.take (p + 1) = input.take p ++ [x] := by
      rw [List.take_add_one, hx]; rfl
    have hwin : ((input.take p).rtake r ++ [x]).rtake r = (input.take (p + 1)).rtake r := by
      rw [rtake_concat_rtake, hpx]
    have hw2 : (input.take (p + 1)).rtake (r + 1) = (input.take p).rtake r ++ [x] := by
      rw [hpx, List.rtake_concat_succ]
    have hlen : ((input.take p).rtake r).length = min r p := by
      rw [List.length_rtake, ← hplen]
    have hsplit' : input = input.take (p + 1) ++ s' := by
      rw [hpx, List.append_assoc, List.singleton_append]; exact hsplit
    have hplen' : p + 1 = (input.take (p + 1)).length := by
      rw [List.length_take]; omega
    rw [ISLRule.applyAux_cons, Transduction.windowOutput_toISLRule, Nat.add_sub_cancel, hlen, hwin,
        ih (p + 1) hsplit' hplen', List.length_cons, List.range'_succ, List.flatMap_cons]
    congr 1
    rw [Transduction.emitAt_local hT hp, hw2]

/-- **Locality bridge** (left half): a transduction whose guards look only backward with
predecessor depth `≤ r` is `(r+1)`-Left-Input-Strictly-Local — its output depends on a bounded
left window, the defining property of strict locality. -/
theorem Transduction.leftLocal_isLeftISL [DecidableEq α] {r : ℕ} {T : Transduction α β}
    (hT : T.LeftLocal r) : IsLeftInputStrictlyLocal (r + 1) T.apply := by
  refine ⟨T.toISLRule r, ?_⟩
  funext input
  have h := Transduction.applyAux_toISLRule_eq hT input input 0 (by simp) (by simp)
  rw [List.take_zero, List.rtake_nil] at h
  rw [ISLRule.apply, Transduction.apply, List.range_eq_range']
  exact h

/-! ### Worked example: the bridge on a concrete left-local process -/

section Example

private inductive Sym | a | b | c
  deriving DecidableEq

private def xv : Term := .var

/-- Relabel `b → c` immediately after an `a`: the guard looks only left (a predecessor `a`), so it
is backward with radius 1. -/
private def afterA : Transduction Sym Sym where
  copies := 1
  clause _ := [(QF.conj (.label .a xv.pred) (.label .b xv), .c),
               (.label .b xv, .b), (.label .c xv, .c), (.label .a xv, .a)]

-- The induced 2-Left-ISL rule computes the same function on a sample — the bridge, concretely.
example : (afterA.toISLRule 1).apply [Sym.a, .b, .a, .b]
            = afterA.apply [Sym.a, .b, .a, .b] := by decide
example : afterA.apply [Sym.a, .b, .a, .b] = [Sym.a, .c, .a, .c] := by decide

end Example

end Subregular
