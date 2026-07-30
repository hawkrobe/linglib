/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic

/-!
# Quantifier-free position tests

The quantifier-free apparatus of the subregular program ([chandlee-2014],
[chandlee-jardine-2019]): a `Subregular.Term` walks successor/predecessor steps from a position,
and a `Subregular.QF` formula is a boolean combination of label and definedness tests on such
walks. Because successor and predecessor are *functions*, a term reaches a bounded neighbourhood
of its position with no quantifiers — the syntactic source of strict locality. Satisfaction is
decidable, and a formula whose walks are backward with depth `≤ r` reads only the `r + 1`
symbols ending at its position (`BackBounded.realize_congr`). These formulas are the guards of
logical transductions (`Transduction.lean`) and the term language of boolean monadic recursive
schemes (`BMRS.lean`).

## Main definitions

* `Subregular.succ?` / `Subregular.pred?`: the next/previous position, as partial functions.
* `Subregular.Term`: walks; `Term.eval` reads the position a walk reaches, `none` off an edge.
* `Term.Backward` / `Term.Forward` / `Term.pdepth`: one-sided walks and how far back one reaches.
* `Subregular.QF`: label/definedness tests on walks, closed under boolean combination;
  `QF.Realize` is decidable satisfaction; `initial`/`final` are the derived edge tests.
* `QF.BackBounded`: every walk backward with depth `≤ r`.

## Main results

* `Term.eval_backward`: a backward walk of depth `j` from position `n` reads exactly `n - j`.
* `BackBounded.realize_congr`: a backward-bounded formula cannot distinguish positions whose
  bounded left contexts agree.

## Implementation notes

The logic is monadic — one position variable, so `Term.eval` takes a position rather than an
assignment — since every consumer (transduction guards, BMRS) is; and there is no equality atom:
with a single position variable, two walks from one origin agree exactly when both are defined
with equal displacement, so equality tests reduce to definedness tests. It is a bespoke syntax
rather than a fragment of `FirstOrder.Language`: over a relational word signature,
quantifier-free formulas cannot leave their variables, so bounded-window reach requires
successor and predecessor as *function* symbols — but a mathlib `Structure` interprets function
symbols totally, whereas falling off an edge is the semantics here (`defined`, `initial`,
`final`).
-/

namespace Subregular

variable {α : Type*}

/-! ### Positions -/

/-- Successor as a partial function: the position after `n`, defined iff it is in range. -/
def succ? (w : List α) (n : ℕ) : Option ℕ :=
  if n + 1 < w.length then some (n + 1) else none

/-- Predecessor as a partial function: the position before `n`, defined iff `n > 0`. -/
def pred? (w : List α) : ℕ → Option ℕ
  | 0 => none
  | n + 1 => if n < w.length then some n else none

theorem succ?_eq_some_iff {w : List α} {n m : ℕ} :
    succ? w n = some m ↔ m = n + 1 ∧ n + 1 < w.length := by
  unfold succ?
  split <;> simp_all
  all_goals omega

theorem pred?_eq_some_iff {w : List α} {n m : ℕ} :
    pred? w n = some m ↔ n = m + 1 ∧ m < w.length := by
  cases n with
  | zero => simp [pred?]
  | succ k =>
    unfold pred?
    split <;> simp_all
    all_goals omega

@[simp] theorem pred?_zero (w : List α) : pred? w 0 = none := rfl

theorem pred?_of_pos {w : List α} {m : ℕ} (h0 : 0 < m) (hm : m ≤ w.length) :
    pred? w m = some (m - 1) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  have hm' : m' < w.length := by omega
  simp [pred?, hm']

/-- The successor structure depends only on the length. -/
theorem succ?_congr {w w' : List α} (h : w.length = w'.length) : succ? w = succ? w' := by
  funext n; simp [succ?, h]

/-- The predecessor structure depends only on the length. -/
theorem pred?_congr {w w' : List α} (h : w.length = w'.length) : pred? w = pred? w' := by
  funext n; cases n <;> simp [pred?, h]

/-! ### Walks -/

/-- A **term**: a walk of successor/predecessor steps from the position variable. Chains of
`succ`/`pred` give bounded-window reach with no quantifier apparatus. -/
inductive Term where
  | var : Term
  | succ : Term → Term
  | pred : Term → Term
  deriving DecidableEq

namespace Term

/-- The position a term reads, walking from position `n` of `w`; `none` once the walk falls off
an edge. -/
def eval (w : List α) (n : ℕ) : Term → Option ℕ
  | .var => if n < w.length then some n else none
  | .succ t => (eval w n t).bind (succ? w)
  | .pred t => (eval w n t).bind (pred? w)

variable {w w' : List α} {n v : ℕ} {t u : Term}

@[simp] theorem eval_succ : t.succ.eval w n = (t.eval w n).bind (succ? w) := rfl

@[simp] theorem eval_pred : t.pred.eval w n = (t.eval w n).bind (pred? w) := rfl

theorem eval_var_eq_some_iff : Term.var.eval w n = some v ↔ v = n ∧ n < w.length := by
  rw [eval]
  split <;> simp_all [eq_comm]
  omega

/-- The variable reads its own in-domain position. -/
@[simp] theorem eval_var (h : n < w.length) : Term.var.eval w n = some n := if_pos h

/-- Terms read in-domain positions. -/
theorem eval_lt : ∀ {t : Term} {v : ℕ}, t.eval w n = some v → v < w.length
  | .var, _, h => by
    obtain ⟨rfl, hlt⟩ := eval_var_eq_some_iff.mp h
    exact hlt
  | .succ t, _, h => by
    obtain ⟨u, -, hu⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, hlt⟩ := succ?_eq_some_iff.mp hu
    exact hlt
  | .pred t, _, h => by
    obtain ⟨u, -, hu⟩ := Option.bind_eq_some_iff.mp h
    exact (pred?_eq_some_iff.mp hu).2

/-- A one-step successor walk reads the successor position. -/
@[simp] theorem eval_succ_var : Term.var.succ.eval w n = succ? w n := by
  rcases Nat.lt_or_ge n w.length with h | h
  · rw [eval_succ, eval_var h, Option.bind_some]
  · rw [eval_succ, eval, if_neg (by simpa using h), Option.bind_none, eq_comm,
      Option.eq_none_iff_forall_ne_some]
    intro m hm
    have := (succ?_eq_some_iff.mp hm).2
    omega

/-- A one-step predecessor walk reads the predecessor position (in-domain: off the right edge
`pred?` is still defined at `w.length` but the variable is not). -/
theorem eval_pred_var (h : n < w.length) : Term.var.pred.eval w n = pred? w n := by
  rw [eval_pred, eval_var h, Option.bind_some]

/-- Terms read only the length, so their reads transport across equal-length words. -/
theorem eval_congr (hlen : w.length = w'.length) : ∀ t : Term, t.eval w n = t.eval w' n
  | .var => by simp [eval, hlen]
  | .succ t => by rw [eval_succ, eval_succ, eval_congr hlen t, succ?_congr hlen]
  | .pred t => by rw [eval_pred, eval_pred, eval_congr hlen t, pred?_congr hlen]

/-- Substitution: `t.comp u` walks `u` first, then `t`. -/
def comp : Term → Term → Term
  | .var, u => u
  | .succ t, u => .succ (t.comp u)
  | .pred t, u => .pred (t.comp u)

/-- Composite terms read sequenced positions. -/
theorem eval_comp : ∀ t u : Term, (t.comp u).eval w n = (u.eval w n).bind fun v => t.eval w v
  | .var, u => by
    cases hu : u.eval w n with
    | none => simp [comp, hu]
    | some v => simp [comp, hu, eval_var (eval_lt hu)]
  | .succ t, u => by simp only [comp, eval_succ, eval_comp t u, Option.bind_assoc]
  | .pred t, u => by simp only [comp, eval_pred, eval_comp t u, Option.bind_assoc]

/-! ### Directed walks -/

/-- A term is *backward* if it uses no successor — only the variable and predecessors, so it
reads positions at or before its variable. -/
def Backward : Term → Prop
  | .var => True
  | .pred t => t.Backward
  | .succ _ => False

/-- A term is *forward* if it uses no predecessor, so it reads positions at or after its
variable. -/
def Forward : Term → Prop
  | .var => True
  | .pred _ => False
  | .succ t => t.Forward

/-- The predecessor depth of a term: how far back it reaches. -/
def pdepth : Term → ℕ
  | .var => 0
  | .pred t => t.pdepth + 1
  | .succ t => t.pdepth

instance instDecidableBackward : ∀ t : Term, Decidable t.Backward
  | .var => .isTrue trivial
  | .pred t => instDecidableBackward t
  | .succ _ => .isFalse not_false

instance instDecidableForward : ∀ t : Term, Decidable t.Forward
  | .var => .isTrue trivial
  | .pred _ => .isFalse not_false
  | .succ t => instDecidableForward t

/-- Backward terms only move left. -/
theorem eval_le_of_backward :
    ∀ {t : Term}, t.Backward → ∀ {v}, t.eval w n = some v → v ≤ n
  | .var, _, v, h => Nat.le_of_eq (eval_var_eq_some_iff.mp h).1
  | .pred t, ht, v, h => by
    obtain ⟨u, hu, huv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := pred?_eq_some_iff.mp huv
    exact Nat.le_of_succ_le (eval_le_of_backward (t := t) ht hu)

/-- Forward terms only move right. -/
theorem le_eval_of_forward :
    ∀ {t : Term}, t.Forward → ∀ {v}, t.eval w n = some v → n ≤ v
  | .var, _, v, h => Nat.le_of_eq (eval_var_eq_some_iff.mp h).1.symm
  | .succ t, ht, v, h => by
    obtain ⟨u, hu, huv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := succ?_eq_some_iff.mp huv
    exact Nat.le_trans (le_eval_of_forward (t := t) ht hu) (Nat.le_succ u)

/-- A backward term of predecessor depth `j`, read from an in-range position `n`, reads exactly
position `n - j` — defined iff `j ≤ n`. -/
theorem eval_backward (hn : n < w.length) :
    ∀ {t : Term}, t.Backward →
      t.eval w n = if t.pdepth ≤ n then some (n - t.pdepth) else none := by
  intro t ht
  induction t with
  | var => simp [eval, pdepth, hn]
  | succ t _ => exact absurd ht (by simp [Backward])
  | pred t ih =>
    simp only [Backward] at ht
    simp only [eval_pred, ih ht, pdepth]
    by_cases h : t.pdepth ≤ n
    · rw [if_pos h, Option.bind_some]
      by_cases h0 : t.pdepth = n
      · subst h0; rw [Nat.sub_self, pred?_zero, if_neg (by omega)]
      · rw [pred?_of_pos (by omega) (by omega), if_pos (by omega), Nat.sub_sub]
    · rw [if_neg h, Option.bind_none, if_neg (by omega)]

end Term

/-! ### Quantifier-free formulas -/

/-- A **quantifier-free formula**: a boolean combination of label and definedness tests on term
walks from a single position. -/
inductive QF (α : Type*) where
  | label : α → Term → QF α
  | defined : Term → QF α
  | tru : QF α
  | fls : QF α
  | neg : QF α → QF α
  | conj : QF α → QF α → QF α
  | disj : QF α → QF α → QF α

namespace QF

/-- Satisfaction of a formula at position `n` of `w`; tests on an undefined walk are false. -/
def Realize (w : List α) (n : ℕ) : QF α → Prop
  | .label a t => (t.eval w n).bind (w[·]?) = some a
  | .defined t => t.eval w n ≠ none
  | .tru => True
  | .fls => False
  | .neg φ => ¬ φ.Realize w n
  | .conj φ ψ => φ.Realize w n ∧ ψ.Realize w n
  | .disj φ ψ => φ.Realize w n ∨ ψ.Realize w n

instance instDecidableRealize [DecidableEq α] (w : List α) (n : ℕ) :
    (φ : QF α) → Decidable (φ.Realize w n)
  | .label _ t => inferInstanceAs (Decidable ((t.eval w n).bind _ = _))
  | .defined t => inferInstanceAs (Decidable (t.eval w n ≠ none))
  | .tru => isTrue trivial
  | .fls => isFalse not_false
  | .neg φ => @instDecidableNot _ (instDecidableRealize w n φ)
  | .conj φ ψ => @instDecidableAnd _ _ (instDecidableRealize w n φ) (instDecidableRealize w n ψ)
  | .disj φ ψ => @instDecidableOr _ _ (instDecidableRealize w n φ) (instDecidableRealize w n ψ)

/-- `t` reads an initial position: in-domain with no predecessor. -/
def initial (t : Term) : QF α := .conj (.defined t) (.neg (.defined t.pred))

/-- `t` reads a final position: in-domain with no successor. -/
def final (t : Term) : QF α := .conj (.defined t) (.neg (.defined t.succ))

/-! ### Backward-bounded formulas read only a left window -/

/-- A formula is backward-bounded by `r` if every term it uses is backward with predecessor
depth `≤ r`, so it reads only the `r + 1` positions ending at its own. -/
def BackBounded (r : ℕ) : QF α → Prop
  | .label _ t => t.Backward ∧ t.pdepth ≤ r
  | .defined t => t.Backward ∧ t.pdepth ≤ r
  | .tru => True
  | .fls => True
  | .neg φ => φ.BackBounded r
  | .conj φ ψ => φ.BackBounded r ∧ ψ.BackBounded r
  | .disj φ ψ => φ.BackBounded r ∧ ψ.BackBounded r

/-- A backward-bounded formula reads only the `r + 1` symbols ending at its position: it has the
same truth value at `(w, n)` and `(w', n')` whenever their bounded left contexts — the labels at
offsets `0 … r`, and which of those offsets stay in range — agree. -/
theorem BackBounded.realize_congr {r : ℕ} {w w' : List α} {n n' : ℕ}
    (hn : n < w.length) (hn' : n' < w'.length)
    (hlbl : ∀ j ≤ r, w[n - j]? = w'[n' - j]?)
    (hedge : ∀ j ≤ r, (j ≤ n ↔ j ≤ n')) :
    ∀ {φ : QF α}, φ.BackBounded r → (φ.Realize w n ↔ φ.Realize w' n') := by
  intro φ
  induction φ with
  | label a t =>
    rintro ⟨ht, hb⟩
    simp only [Realize, Term.eval_backward hn ht, Term.eval_backward hn' ht]
    by_cases h : t.pdepth ≤ n
    · rw [if_pos h, if_pos ((hedge t.pdepth hb).mp h)]
      simp only [Option.bind_some]
      rw [hlbl t.pdepth hb]
    · rw [if_neg h, if_neg (fun hh => h ((hedge t.pdepth hb).mpr hh)),
        Option.bind_none, Option.bind_none]
  | defined t =>
    rintro ⟨ht, hb⟩
    simp only [Realize, Term.eval_backward hn ht, Term.eval_backward hn' ht]
    by_cases h : t.pdepth ≤ n
    · rw [if_pos h, if_pos ((hedge t.pdepth hb).mp h)]; simp
    · rw [if_neg h, if_neg (fun hh => h ((hedge t.pdepth hb).mpr hh))]
  | tru => intro _; simp [Realize]
  | fls => intro _; simp [Realize]
  | neg φ ih => intro hφ; simp only [Realize, ih hφ]
  | conj φ ψ ihφ ihψ => rintro ⟨h1, h2⟩; simp only [Realize, ihφ h1, ihψ h2]
  | disj φ ψ ihφ ihψ => rintro ⟨h1, h2⟩; simp only [Realize, ihφ h1, ihψ h2]

end QF

/-! ### Worked example -/

section Example

private inductive Sym | a | b deriving DecidableEq

/-- The position is flanked by `a`s — a bounded two-sided context stated by walks, with no
quantifier. -/
private def flankedByA : QF Sym :=
  .conj (.label .a (.pred .var)) (.label .a (.succ .var))

private def aba : List Sym := [Sym.a, Sym.b, Sym.a]

-- Position 1 (the `b`) is flanked by `a`s; position 0 is not (no predecessor).
example : flankedByA.Realize aba 1 := by decide
example : ¬ flankedByA.Realize aba 0 := by decide
-- The edge tests compute as expected.
example : (QF.initial (α := Sym) .var).Realize aba 0 := by decide
example : (QF.final (α := Sym) .var).Realize aba 2 := by decide

end Example

end Subregular
