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
* `Transduction.leftLocal_isLeftISL` — a backward-bounded (radius `r`) transduction is
  `(r+1)`-Left-Input-Strictly-Local.
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

/-! ### Locality of `emitAt` and the window-threading invariant

The bridge reduces to two facts: a backward-bounded guard reads only the `r + 1` symbols ending at
its position (`emitAt` agrees on positions with matching bounded left context), and the ISL window
threaded by `applyAux` stays exactly that bounded left context. -/

/-- A backward-bounded atom reads only the `r + 1` symbols ending at its position: it has the same
truth value at `(w, n)` and `(w', n')` whenever their bounded left contexts (the labels at offsets
`0 … r`, and which of those offsets stay in range) agree. -/
private theorem Atom.realize_eq_of_agree [DecidableEq α] {r : ℕ} {a : Atom α (Fin 1)}
    (ha : a.BackBounded r) {w w' : WordModel α} {n n' : ℕ}
    (hn : n < w.length) (hn' : n' < w'.length)
    (hlbl : ∀ j ≤ r, w.label? (n - j) = w'.label? (n' - j))
    (hedge : ∀ j ≤ r, (j ≤ n ↔ j ≤ n')) :
    a.Realize w (fun _ => n) ↔ a.Realize w' (fun _ => n') := by
  cases a with
  | label c t =>
    obtain ⟨ht, hb⟩ := ha
    simp only [Atom.Realize, Term.eval_backward hn ht, Term.eval_backward hn' ht]
    by_cases h : t.pdepth ≤ n
    · rw [if_pos h, if_pos ((hedge t.pdepth hb).mp h)]
      simp only [Option.bind_some]
      rw [hlbl t.pdepth hb]
    · rw [if_neg h, if_neg (fun hh => h ((hedge t.pdepth hb).mpr hh)),
          Option.bind_none, Option.bind_none]
  | eq t₁ t₂ =>
    obtain ⟨⟨ht₁, hb₁⟩, ht₂, hb₂⟩ := ha
    have e1 := hedge t₁.pdepth hb₁
    have e2 := hedge t₂.pdepth hb₂
    simp only [Atom.Realize, Term.eval_backward hn ht₁, Term.eval_backward hn ht₂,
               Term.eval_backward hn' ht₁, Term.eval_backward hn' ht₂]
    by_cases h₁ : t₁.pdepth ≤ n
    · by_cases h₂ : t₂.pdepth ≤ n
      · rw [if_pos h₁, if_pos h₂, if_pos (e1.mp h₁), if_pos (e2.mp h₂)]
        have := e1.mp h₁; have := e2.mp h₂
        simp only [Option.some.injEq, ne_eq, reduceCtorEq, not_false_eq_true, and_true]
        omega
      · rw [if_pos h₁, if_neg h₂, if_pos (e1.mp h₁), if_neg (fun hh => h₂ (e2.mpr hh))]; simp
    · by_cases h₂ : t₂.pdepth ≤ n
      · rw [if_neg h₁, if_pos h₂, if_neg (fun hh => h₁ (e1.mpr hh)), if_pos (e2.mp h₂)]; simp
      · rw [if_neg h₁, if_neg h₂, if_neg (fun hh => h₁ (e1.mpr hh)),
            if_neg (fun hh => h₂ (e2.mpr hh))]
  | defined t =>
    obtain ⟨ht, hb⟩ := ha
    simp only [Atom.Realize, Term.eval_backward hn ht, Term.eval_backward hn' ht]
    by_cases h : t.pdepth ≤ n
    · rw [if_pos h, if_pos ((hedge t.pdepth hb).mp h)]; simp
    · rw [if_neg h, if_neg (fun hh => h ((hedge t.pdepth hb).mpr hh))]

/-- A backward-bounded quantifier-free formula reads only the `r + 1` symbols ending at its
position — the boolean-combination lift of `Atom.realize_eq_of_agree`. -/
private theorem QF.realize_eq_of_agree [DecidableEq α] {r : ℕ}
    {w w' : WordModel α} {n n' : ℕ}
    (hn : n < w.length) (hn' : n' < w'.length)
    (hlbl : ∀ j ≤ r, w.label? (n - j) = w'.label? (n' - j))
    (hedge : ∀ j ≤ r, (j ≤ n ↔ j ≤ n')) :
    ∀ {φ : QF α (Fin 1)}, φ.BackBounded r →
      (φ.Realize w (fun _ => n) ↔ φ.Realize w' (fun _ => n')) := by
  intro φ
  induction φ with
  | atom a => exact fun hφ => Atom.realize_eq_of_agree hφ hn hn' hlbl hedge
  | tru => intro _; simp [QF.Realize]
  | fls => intro _; simp [QF.Realize]
  | neg φ ih => intro hφ; simp only [QF.Realize, ih hφ]
  | conj φ ψ ihφ ihψ => intro hφ; obtain ⟨h1, h2⟩ := hφ; simp only [QF.Realize, ihφ h1, ihψ h2]
  | disj φ ψ ihφ ihψ => intro hφ; obtain ⟨h1, h2⟩ := hφ; simp only [QF.Realize, ihφ h1, ihψ h2]

/-- Pointwise congruence for `List.findSome?`: agreeing on the list's members suffices. -/
private theorem findSome?_congr {γ δ : Type*} {f g : γ → Option δ} :
    ∀ {l : List γ}, (∀ x ∈ l, f x = g x) → l.findSome? f = l.findSome? g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    rw [List.findSome?_cons, List.findSome?_cons, h a List.mem_cons_self]
    cases g a with
    | none => exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    | some b => rfl

/-- A left-local transduction emits the same block at positions whose bounded left contexts agree:
every clause guard is backward-bounded, so its firing is determined by that context. -/
private theorem Transduction.emitAt_eq_of_agree [DecidableEq α] {r : ℕ} {T : Transduction α β}
    (hT : T.LeftLocal r) {w w' : WordModel α} {n n' : ℕ}
    (hn : n < w.length) (hn' : n' < w'.length)
    (hlbl : ∀ j ≤ r, w.label? (n - j) = w'.label? (n' - j))
    (hedge : ∀ j ≤ r, (j ≤ n ↔ j ≤ n')) :
    T.emitAt w n = T.emitAt w' n' := by
  unfold Transduction.emitAt
  apply List.filterMap_congr
  intro c _
  apply findSome?_congr
  intro cl hcl
  have hb := hT c cl hcl
  by_cases h : cl.1.Realize w (fun _ => n)
  · rw [if_pos h, if_pos ((QF.realize_eq_of_agree hn hn' hlbl hedge hb).mp h)]
  · rw [if_neg h, if_neg (fun hh => h ((QF.realize_eq_of_agree hn hn' hlbl hedge hb).mpr hh))]

/-- The block a left-local transduction emits at position `p` depends only on the `r + 1` input
symbols ending at `p`: it equals the block emitted at the last position of that window. -/
private theorem Transduction.emitAt_local [DecidableEq α] {r : ℕ} {T : Transduction α β}
    (hT : T.LeftLocal r) {input : WordModel α} {p : ℕ} (hp : p < input.length) :
    T.emitAt input p = T.emitAt ((input.take (p + 1)).rtake (r + 1)) (min r p) := by
  apply Transduction.emitAt_eq_of_agree hT hp
  · rw [List.length_rtake, List.length_take]; omega
  · intro j hj
    have hlen : (input.take (p + 1)).length = p + 1 := by rw [List.length_take]; omega
    simp only [WordModel.label?_eq_getElem?]
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
    (hT : T.LeftLocal r) (input : WordModel α) :
    ∀ (s : WordModel α) (p : ℕ), input = input.take p ++ s → p = (input.take p).length →
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

/-- **Locality bridge** (left half), [dolatian-2020] after Chandlee–Heinz–Jardine: a transduction
whose guards look only backward with predecessor depth `≤ r` is `(r+1)`-Left-Input-Strictly-Local —
its output depends on a bounded left window, the defining property of strict locality. -/
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
