/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Logic.QFLogic
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy
import Mathlib.Data.Finset.Basic

/-!
# Boolean Monadic Recursive Schemes

BMRS ([bhaskar-jardine-chandlee-oakden-2020]; [bhaskar-chandlee-jardine-2023];
phonological modelling in [chandlee-jardine-2021]): programs of mutually recursive
Boolean-valued unary predicates over word models, built from `if…then…else`, the
edge tests `initial`/`final` (the literature's `min`/`max`), input class tests, and
recursive calls. Terms are the
quantifier-free terms of `Logic/QFLogic.lean` at a single index variable.

Two symbol types dissolve the literature's `sig(P)` bookkeeping: input labels `α` get
the lookup rule, rule heads `F` get the unfolding rule, and a `Program` is a total map
`F → Expr α F`.

Semantics is the derivation system of [yolyan-comer-2026] (Fig. 6–7), an inductive
judgment `Eval` — faithful to partiality: a non-halting program (`f := g, g := f`)
derives nothing. `evalFuel` is its computable face, related by `eval_iff_evalFuel`.

## Main definitions

* `BMRS.Expr`, `BMRS.Program` — syntax; `BMRS.tden` — term denotation at an index.
* `BMRS.Eval` — the derivation system; `BMRS.evalFuel` — the fuel-bounded evaluator.
* `Expr.Backward` / `Program.Backward` (dually `Forward`) — the one-sided fragments
  `BMRSᵖ` / `BMRSˢ` of [bhaskar-jardine-chandlee-oakden-2020].
* `BMRS.combine` / `BMRS.combineC` — the value combinators of simultaneous application
  (⊙, [yolyan-2025] Def. 4.1) and its conjunctive dual (⊘, Def. 6.5).

## Main results

* `Eval.deterministic` — an expression has at most one value.
* `eval_iff_evalFuel` — adequacy of the fuel evaluator.
* `Eval.congr_agreeUpto` / `Eval.congr_agreeFrom` — **one-sided locality**: a
  backward program evaluated at `i` reads only positions `≤ i`, so equal-length words
  agreeing there evaluate identically (dually for forward). The engine of
  [yolyan-2025]'s negative results (Thm. 5.2–5.5).
* `combine_comm`, `combine_assoc`, `combine_id` — the ⊙-algebra
  ([yolyan-2025] Prop. 4.4), extensionally at the value level.
-/

namespace Subregular.Logic.BMRS

open Subregular (AgreeUpto AgreeFrom)

variable {α F : Type*}

/-! ### Syntax -/

/-- BMRS expressions: edge tests `initial`/`final` (the literature's `min(T)`/`max(T)`),
input **class tests** `label` (the lookup rule; a `Finset` of symbols, so featural
predicates like V or N over a segment alphabet are single atoms — a symbol test is the
singleton case), rule-head calls `call` (the unfolding rule), and `if…then…else`.
Terms are the single-variable quantifier-free terms of `Logic/QFLogic.lean`. -/
inductive Expr (α F : Type*) where
  | tru
  | fls
  | initial (t : Term Unit)
  | final (t : Term Unit)
  | label (s : Finset α) (t : Term Unit)
  | call (f : F) (t : Term Unit)
  | ite (c e₁ e₂ : Expr α F)
  deriving DecidableEq

/-- A BMRS program: one defining expression per rule head. -/
abbrev Program (α F : Type*) := F → Expr α F

/-- Conjunction as `if…then…else` ([yolyan-2025] (3.6)). -/
def Expr.and (e₁ e₂ : Expr α F) : Expr α F := .ite e₁ e₂ .fls

/-- Disjunction as `if…then…else` ([yolyan-2025] (3.7)). -/
def Expr.or (e₁ e₂ : Expr α F) : Expr α F := .ite e₁ .tru e₂

/-- Negation as `if…then…else` ([yolyan-2025] (3.8)). -/
def Expr.not (e : Expr α F) : Expr α F := .ite e .fls .tru

/-! ### Term denotation -/

/-- Denotation of a BMRS term at index `i` (the judgment `w, i ⊢ T → v`). -/
def tden (w : WordModel α) (i : ℕ) (t : Term Unit) : Option ℕ := t.eval w fun _ => i

section TermDenotation

variable {w : WordModel α} {i v : ℕ} {t u : Term Unit}

@[simp] theorem tden_succ :
    tden w i t.succ = (tden w i t).bind w.succ? := rfl

@[simp] theorem tden_pred :
    tden w i t.pred = (tden w i t).bind w.pred? := rfl

theorem tden_var_eq_some_iff : tden w i (.var ()) = some v ↔ v = i ∧ i < w.length := by
  rw [tden, Term.eval]
  split
  · simp_all [WordModel.mem_iff, eq_comm]
  · simp_all [WordModel.mem_iff]

/-- Term denotations are in-domain. -/
theorem tden_lt : ∀ {t : Term Unit} {v : ℕ}, tden w i t = some v → v < w.length
  | .var _, _, h => by
    obtain ⟨rfl, hlt⟩ := tden_var_eq_some_iff.mp h
    exact hlt
  | .succ t, _, h => by
    obtain ⟨u, -, hu⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, hlt⟩ := WordModel.succ?_eq_some_iff.mp hu
    exact hlt
  | .pred t, _, h => by
    obtain ⟨u, -, hu⟩ := Option.bind_eq_some_iff.mp h
    exact (WordModel.pred?_eq_some_iff.mp hu).2

/-- The variable denotes its own in-domain position. -/
@[simp] theorem tden_var (h : i < w.length) : tden w i (.var ()) = some i := if_pos h

/-- A one-step successor term denotes the successor position. -/
@[simp] theorem tden_succ_var : tden w i ((Term.var ()).succ) = w.succ? i := by
  rcases lt_or_ge i w.length with h | h
  · rw [tden_succ, tden_var h, Option.bind_some]
  · rw [tden_succ, tden, Term.eval, if_neg (by simpa [WordModel.Mem] using h),
      Option.bind_none, eq_comm, Option.eq_none_iff_forall_ne_some]
    intro m hm
    have := (WordModel.succ?_eq_some_iff.mp hm).2
    omega

/-- A one-step predecessor term denotes the predecessor position (in-domain: off the
right edge `pred?` is still defined at `w.length` but the variable is not). -/
theorem tden_pred_var (h : i < w.length) : tden w i ((Term.var ()).pred) = w.pred? i := by
  rw [tden_pred, tden_var h, Option.bind_some]

/-- Composed terms denote sequenced denotations. -/
theorem tden_comp :
    ∀ t u : Term Unit, tden w i (t.comp u) = (tden w i u).bind fun v => tden w v t
  | .var _, u => by
    cases hu : tden w i u with
    | none => simp [Term.comp, hu]
    | some v => simp [Term.comp, hu, tden_var (tden_lt hu)]
  | .succ t, u => by simp only [Term.comp, tden_succ, tden_comp t u, Option.bind_assoc]
  | .pred t, u => by simp only [Term.comp, tden_pred, tden_comp t u, Option.bind_assoc]

end TermDenotation

/-! ### The derivation system -/

/-- The derivation system for BMRS expressions ([yolyan-comer-2026] Fig. 7):
`Eval P w i e b` is `w, i ⊢_P e → b`. Partial by design: a non-halting program
derives nothing. -/
inductive Eval (P : Program α F) (w : WordModel α) : ℕ → Expr α F → Bool → Prop
  | tru {i} : Eval P w i .tru true
  | fls {i} : Eval P w i .fls false
  | initial_true {i t} (h : tden w i t = some 0) : Eval P w i (.initial t) true
  | initial_false {i t v} (h : tden w i t = some v) (hv : 0 < v) :
      Eval P w i (.initial t) false
  | final_true {i t} (h : tden w i t = some (w.length - 1)) : Eval P w i (.final t) true
  | final_false {i t v} (h : tden w i t = some v) (hv : v < w.length - 1) :
      Eval P w i (.final t) false
  | label_true {i s t v a} (h : tden w i t = some v) (hl : w[v]? = some a) (has : a ∈ s) :
      Eval P w i (.label s t) true
  | label_false {i s t v a} (h : tden w i t = some v) (hl : w[v]? = some a) (has : a ∉ s) :
      Eval P w i (.label s t) false
  | call {i f t v b} (h : tden w i t = some v) (he : Eval P w v (P f) b) :
      Eval P w i (.call f t) b
  | ite_true {i c e₁ e₂ b} (hc : Eval P w i c true) (h₁ : Eval P w i e₁ b) :
      Eval P w i (.ite c e₁ e₂) b
  | ite_false {i c e₁ e₂ b} (hc : Eval P w i c false) (h₂ : Eval P w i e₂ b) :
      Eval P w i (.ite c e₁ e₂) b

variable {P : Program α F} {w w' : WordModel α} {i v n m : ℕ} {t u : Term Unit}
  {e : Expr α F} {b b' : Bool}

/-- Boolean-form introduction for the edge test: the value is the comparison. -/
theorem Eval.initial (h : tden w i t = some v) : Eval P w i (.initial t) (v == 0) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · exact .initial_true h
  · rw [beq_eq_false_iff_ne.mpr (by omega)]
    exact .initial_false h hv

/-- Boolean-form introduction for the final test. -/
theorem Eval.final (h : tden w i t = some v) : Eval P w i (.final t) (v == w.length - 1) := by
  rcases eq_or_ne v (w.length - 1) with rfl | hne
  · rw [beq_self_eq_true]
    exact .final_true h
  · rw [beq_eq_false_iff_ne.mpr hne]
    exact .final_false h (by have := tden_lt h; omega)

/-- Boolean-form introduction for the class test. -/
theorem Eval.label [DecidableEq α] {s : Finset α} {a : α} (h : tden w i t = some v)
    (hl : w[v]? = some a) : Eval P w i (.label s t) (decide (a ∈ s)) := by
  by_cases has : a ∈ s
  · rw [decide_eq_true has]
    exact .label_true h hl has
  · rw [decide_eq_false has]
    exact .label_false h hl has

/-- The derivation system is deterministic: an expression has at most one value. -/
theorem Eval.deterministic (h : Eval P w i e b) (h' : Eval P w i e b') : b = b' := by
  induction h generalizing b' with
  | call h he ih => cases h' with
    | call h₂ he₂ => rw [h] at h₂; cases h₂; exact ih he₂
  | ite_true hc h₁ ihc ih₁ => cases h' with
    | ite_true hc₂ h₂ => exact ih₁ h₂
    | ite_false hc₂ h₂ => exact absurd (ihc hc₂) (by simp)
  | ite_false hc h₂ ihc ih₂ => cases h' with
    | ite_true hc₂ h₁ => exact absurd (ihc hc₂) (by simp)
    | ite_false hc₂ h₁ => exact ih₂ h₁
  | _ => cases h' <;> simp_all

/-- A program is **total on `w`** when every rule head is defined at every position. -/
def Program.TotalOn (P : Program α F) (w : WordModel α) : Prop :=
  ∀ f, ∀ i < w.length, ∃ b, Eval P w i (.call f (.var ())) b

/-! ### The fuel evaluator -/

/-- Fuel-bounded evaluator: the computable face of `Eval`. -/
def evalFuel [DecidableEq α] (P : Program α F) (w : WordModel α) :
    ℕ → ℕ → Expr α F → Option Bool
  | 0, _, _ => none
  | _ + 1, _, .tru => some true
  | _ + 1, _, .fls => some false
  | _ + 1, i, .initial t => (tden w i t).map (· == 0)
  | _ + 1, i, .final t => (tden w i t).map (· == w.length - 1)
  | _ + 1, i, .label s t => (tden w i t).bind fun v => (w[v]?).map fun a => decide (a ∈ s)
  | fuel + 1, i, .call f t => (tden w i t).bind fun v => evalFuel P w fuel v (P f)
  | fuel + 1, i, .ite c e₁ e₂ =>
      (evalFuel P w fuel i c).bind fun b =>
        if b then evalFuel P w fuel i e₁ else evalFuel P w fuel i e₂

/-- More fuel never changes a defined answer. -/
theorem evalFuel_mono [DecidableEq α] (hnm : n ≤ m)
    (h : evalFuel P w n i e = some b) : evalFuel P w m i e = some b := by
  induction n generalizing m i e b with
  | zero => simp [evalFuel] at h
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases e with
    | call f t =>
      simp only [evalFuel, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨v, hv, hrec⟩ := h
      exact ⟨v, hv, ih (by omega) hrec⟩
    | ite c e₁ e₂ =>
      simp only [evalFuel, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨bc, hbc, hbr⟩ := h
      refine ⟨bc, ih (by omega) hbc, ?_⟩
      cases bc <;> simpa using ih (by omega) (by simpa using hbr)
    | _ => exact h

/-- Soundness of the fuel evaluator against the derivation system. -/
theorem evalFuel_sound [DecidableEq α] (h : evalFuel P w n i e = some b) :
    Eval P w i e b := by
  induction n generalizing i e b with
  | zero => simp [evalFuel] at h
  | succ n ih =>
    cases e with
    | tru => simp [evalFuel] at h; exact h ▸ .tru
    | fls => simp [evalFuel] at h; exact h ▸ .fls
    | initial t =>
      simp only [evalFuel, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      exact .initial hv
    | final t =>
      simp only [evalFuel, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      exact .final hv
    | label s t =>
      simp only [evalFuel, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, a, ha, rfl⟩ := h
      exact .label hv ha
    | call f t =>
      simp only [evalFuel, Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, hrec⟩ := h
      exact .call hv (ih hrec)
    | ite c e₁ e₂ =>
      simp only [evalFuel, Option.bind_eq_some_iff] at h
      obtain ⟨bc, hbc, hbr⟩ := h
      cases bc with
      | true => exact .ite_true (ih hbc) (ih (by simpa using hbr))
      | false => exact .ite_false (ih hbc) (ih (by simpa using hbr))

/-- Completeness: every derivation is reached at some fuel. -/
theorem evalFuel_complete [DecidableEq α] (h : Eval P w i e b) :
    ∃ n, evalFuel P w n i e = some b := by
  induction h with
  | tru => exact ⟨1, rfl⟩
  | fls => exact ⟨1, rfl⟩
  | initial_true h => exact ⟨1, by simp [evalFuel, h]⟩
  | initial_false h hv => exact ⟨1, by simp [evalFuel, h]; omega⟩
  | final_true h => exact ⟨1, by simp [evalFuel, h]⟩
  | final_false h hv => exact ⟨1, by simp [evalFuel, h]; omega⟩
  | label_true h hl has => exact ⟨1, by simp [evalFuel, h, hl, has]⟩
  | label_false h hl has => exact ⟨1, by simp [evalFuel, h, hl, has]⟩
  | call h he ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [evalFuel, h, hn]⟩
  | ite_true hc h₁ ihc ih₁ =>
    obtain ⟨n₁, hn₁⟩ := ihc
    obtain ⟨n₂, hn₂⟩ := ih₁
    exact ⟨max n₁ n₂ + 1, by
      simp only [evalFuel, Option.bind_eq_some_iff]
      exact ⟨true, evalFuel_mono (le_max_left _ _) hn₁, by
        simpa using evalFuel_mono (le_max_right _ _) hn₂⟩⟩
  | ite_false hc h₂ ihc ih₂ =>
    obtain ⟨n₁, hn₁⟩ := ihc
    obtain ⟨n₂, hn₂⟩ := ih₂
    exact ⟨max n₁ n₂ + 1, by
      simp only [evalFuel, Option.bind_eq_some_iff]
      exact ⟨false, evalFuel_mono (le_max_left _ _) hn₁, by
        simpa using evalFuel_mono (le_max_right _ _) hn₂⟩⟩

/-- **Adequacy**: the derivation system and the fuel evaluator define the same values. -/
theorem eval_iff_evalFuel [DecidableEq α] :
    Eval P w i e b ↔ ∃ n, evalFuel P w n i e = some b :=
  ⟨evalFuel_complete, fun ⟨_, hn⟩ => evalFuel_sound hn⟩

/-! ### Substitution -/

/-- Substitute a term for the variable throughout an expression: `e.subst u` is
`e[u/x]`, the operation the μ-calculus translation writes `tr(φ)[s(x)]`. -/
def Expr.subst : Expr α F → Term Unit → Expr α F
  | .tru, _ => .tru
  | .fls, _ => .fls
  | .initial t, u => .initial (t.comp u)
  | .final t, u => .final (t.comp u)
  | .label s t, u => .label s (t.comp u)
  | .call f t, u => .call f (t.comp u)
  | .ite c e₁ e₂, u => .ite (c.subst u) (e₁.subst u) (e₂.subst u)

/-- Term denotations sequence through composition. -/
private theorem tden_comp_of {z : ℕ} (hu : tden w i u = some v)
    (h : tden w v t = some z) :
    tden w i (t.comp u) = some z := by
  rw [tden_comp, hu]
  exact h

/-- Transport a derivation through substitution: evaluating `e[u/x]` at `i` is
evaluating `e` at the position `u` denotes. -/
theorem Eval.subst (hu : tden w i u = some v) (h : Eval P w v e b) :
    Eval P w i (e.subst u) b := by
  induction h with
  | tru => exact .tru
  | fls => exact .fls
  | initial_true h => exact .initial_true (tden_comp_of hu h)
  | initial_false h hv => exact .initial_false (tden_comp_of hu h) hv
  | final_true h => exact .final_true (tden_comp_of hu h)
  | final_false h hv => exact .final_false (tden_comp_of hu h) hv
  | label_true h hl has => exact .label_true (tden_comp_of hu h) hl has
  | label_false h hl has => exact .label_false (tden_comp_of hu h) hl has
  | call h he ih => exact .call (tden_comp_of hu h) he
  | ite_true hc h₁ ihc ih₁ => exact .ite_true (ihc hu) (ih₁ hu)
  | ite_false hc h₂ ihc ih₂ => exact .ite_false (ihc hu) (ih₂ hu)

/-! ### One-sided fragments and locality

`BMRSᵖ`-programs (successor-free) compute left-subsequentially, `BMRSˢ`-programs
(predecessor-free) right-subsequentially ([bhaskar-jardine-chandlee-oakden-2020]). The
locality lemmas below are what those inclusions rest on and are the engine of
[yolyan-2025]'s negative results: the flags of a one-sided program cannot see across
the target. Equal length is load-bearing — `min`/`max` atoms read `w.length`. -/

/-- Backward expressions: every term is backward. -/
def Expr.Backward : Expr α F → Prop
  | .tru | .fls => True
  | .initial t | .final t => t.Backward
  | .label _ t => t.Backward
  | .call _ t => t.Backward
  | .ite c e₁ e₂ => c.Backward ∧ e₁.Backward ∧ e₂.Backward

/-- Forward expressions. -/
def Expr.Forward : Expr α F → Prop
  | .tru | .fls => True
  | .initial t | .final t => t.Forward
  | .label _ t => t.Forward
  | .call _ t => t.Forward
  | .ite c e₁ e₂ => c.Forward ∧ e₁.Forward ∧ e₂.Forward

instance Expr.instDecidableBackward : ∀ e : Expr α F, Decidable e.Backward
  | .tru | .fls => .isTrue trivial
  | .initial t | .final t => inferInstanceAs (Decidable t.Backward)
  | .label _ t | .call _ t => inferInstanceAs (Decidable t.Backward)
  | .ite c e₁ e₂ =>
      @instDecidableAnd _ _ (Expr.instDecidableBackward c)
        (@instDecidableAnd _ _ (Expr.instDecidableBackward e₁) (Expr.instDecidableBackward e₂))

instance Expr.instDecidableForward : ∀ e : Expr α F, Decidable e.Forward
  | .tru | .fls => .isTrue trivial
  | .initial t | .final t => inferInstanceAs (Decidable t.Forward)
  | .label _ t | .call _ t => inferInstanceAs (Decidable t.Forward)
  | .ite c e₁ e₂ =>
      @instDecidableAnd _ _ (Expr.instDecidableForward c)
        (@instDecidableAnd _ _ (Expr.instDecidableForward e₁) (Expr.instDecidableForward e₂))

/-- `BMRSᵖ`: every rule body is backward (hereditarily, through calls). -/
def Program.Backward (P : Program α F) : Prop := ∀ f, (P f).Backward

/-- `BMRSˢ`: every rule body is forward. -/
def Program.Forward (P : Program α F) : Prop := ∀ f, (P f).Forward

/-- Backward terms only move left. -/
theorem tden_le_of_backward :
    ∀ {t : Term Unit}, t.Backward → ∀ {v}, tden w i t = some v → v ≤ i
  | .var _, _, v, h => (tden_var_eq_some_iff.mp h).1.le
  | .pred t, ht, v, h => by
    obtain ⟨u, hu, huv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := WordModel.pred?_eq_some_iff.mp huv
    exact Nat.le_of_succ_le (tden_le_of_backward (t := t) ht hu)

/-- Forward terms only move right. -/
theorem le_tden_of_forward :
    ∀ {t : Term Unit}, t.Forward → ∀ {v}, tden w i t = some v → i ≤ v
  | .var _, _, v, h => (tden_var_eq_some_iff.mp h).1.ge
  | .succ t, ht, v, h => by
    obtain ⟨u, hu, huv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := WordModel.succ?_eq_some_iff.mp huv
    exact (le_tden_of_forward (t := t) ht hu).trans (Nat.le_succ u)

/-- Term denotations read only the length, so they transport across equal-length
words. -/
theorem tden_congr (hlen : w.length = w'.length) :
    ∀ t : Term Unit, tden w i t = tden w' i t
  | .var _ => by simp [tden, Term.eval, WordModel.Mem, hlen]
  | .succ t => by rw [tden_succ, tden_succ, tden_congr hlen t, WordModel.succ?_congr hlen]
  | .pred t => by rw [tden_pred, tden_pred, tden_congr hlen t, WordModel.pred?_congr hlen]

/-- **One-sided locality (left)**: a successor-free program evaluated at `i` reads only
positions `≤ i`, so equal-length words agreeing up to `i` evaluate identically. -/
theorem Eval.congr_agreeUpto (hP : P.Backward) (hlen : w.length = w'.length)
    (h : Eval P w i e b) :
    e.Backward → AgreeUpto w w' i → Eval P w' i e b := by
  induction h with
  | tru => exact fun _ _ => .tru
  | fls => exact fun _ _ => .fls
  | initial_true h =>
    exact fun _ _ => Eval.initial_true ((tden_congr hlen _).symm.trans h)
  | initial_false h hv =>
    exact fun _ _ => Eval.initial_false ((tden_congr hlen _).symm.trans h) hv
  | final_true h =>
    exact fun _ _ => Eval.final_true ((tden_congr hlen _).symm.trans (hlen ▸ h))
  | final_false h hv =>
    exact fun _ _ => Eval.final_false ((tden_congr hlen _).symm.trans h) (hlen ▸ hv)
  | label_true h hl has =>
    exact fun he hag => Eval.label_true ((tden_congr hlen _).symm.trans h)
      (hag _ (tden_le_of_backward he h) ▸ hl) has
  | label_false h hl has =>
    exact fun he hag => Eval.label_false ((tden_congr hlen _).symm.trans h)
      (hag _ (tden_le_of_backward he h) ▸ hl) has
  | call h he' ih =>
    exact fun he hag => Eval.call ((tden_congr hlen _).symm.trans h)
      (ih (hP _) fun k hk => hag k (hk.trans (tden_le_of_backward he h)))
  | ite_true hc h₁ ihc ih₁ =>
    exact fun he hag => Eval.ite_true (ihc he.1 hag) (ih₁ he.2.1 hag)
  | ite_false hc h₂ ihc ih₂ =>
    exact fun he hag => Eval.ite_false (ihc he.1 hag) (ih₂ he.2.2 hag)

/-- **One-sided locality (right)**: a predecessor-free program evaluated at `i` reads
only positions `≥ i`, so equal-length words agreeing from `i` on evaluate identically. -/
theorem Eval.congr_agreeFrom (hP : P.Forward) (hlen : w.length = w'.length)
    (h : Eval P w i e b) :
    e.Forward → AgreeFrom w w' i → Eval P w' i e b := by
  induction h with
  | tru => exact fun _ _ => .tru
  | fls => exact fun _ _ => .fls
  | initial_true h =>
    exact fun _ _ => Eval.initial_true ((tden_congr hlen _).symm.trans h)
  | initial_false h hv =>
    exact fun _ _ => Eval.initial_false ((tden_congr hlen _).symm.trans h) hv
  | final_true h =>
    exact fun _ _ => Eval.final_true ((tden_congr hlen _).symm.trans (hlen ▸ h))
  | final_false h hv =>
    exact fun _ _ => Eval.final_false ((tden_congr hlen _).symm.trans h) (hlen ▸ hv)
  | label_true h hl has =>
    exact fun he hag => Eval.label_true ((tden_congr hlen _).symm.trans h)
      (hag _ (le_tden_of_forward he h) ▸ hl) has
  | label_false h hl has =>
    exact fun he hag => Eval.label_false ((tden_congr hlen _).symm.trans h)
      (hag _ (le_tden_of_forward he h) ▸ hl) has
  | call h he' ih =>
    exact fun he hag => Eval.call ((tden_congr hlen _).symm.trans h)
      (ih (hP _) fun k hk => hag k ((le_tden_of_forward he h).trans hk))
  | ite_true hc h₁ ihc ih₁ =>
    exact fun he hag => Eval.ite_true (ihc he.1 hag) (ih₁ he.2.1 hag)
  | ite_false hc h₂ ihc ih₂ =>
    exact fun he hag => Eval.ite_false (ihc he.1 hag) (ih₂ he.2.2 hag)

/-! ### Simultaneous application, at the value level

[yolyan-2025] Def. 4.1 (⊙) and Def. 6.5 (⊘) act per input position on the input value
and the two programs' output values; the program-level operators lift these pointwise.
Stating the algebra ([yolyan-2025] Prop. 4.4) on values keeps it a finite `Bool`
computation and spares the combined-head-space transport. -/

/-- Simultaneous application ⊙ on values ([yolyan-2025] Def. 4.1): a change survives
iff either program makes it. -/
def combine (pin a b : Bool) : Bool := if pin then a && b else a || b

/-- Conjunctive simultaneous application ⊘ on values ([yolyan-2025] Def. 6.5): a change
survives iff both programs make it. -/
def combineC (pin a b : Bool) : Bool := if pin then a || b else a && b

/-- On a true input, ⊙ is conjunction. -/
@[simp] theorem combine_true (a b : Bool) : combine true a b = (a && b) := rfl

/-- On a false input, ⊙ is disjunction — the collapse behind [yolyan-2025] (5.15):
with no underlying stress the ⊙ of the two stress programs is their disjunction. -/
@[simp] theorem combine_false (a b : Bool) : combine false a b = (a || b) := rfl

/-- On a true input, ⊘ is disjunction. -/
@[simp] theorem combineC_true (a b : Bool) : combineC true a b = (a || b) := rfl

/-- On a false input, ⊘ is conjunction — the conjunctive licensing of
[yolyan-2025] §6.3. -/
@[simp] theorem combineC_false (a b : Bool) : combineC false a b = (a && b) := rfl

/-- A ⊙-value differs from the input iff one of the components does
([yolyan-2025] Prop. 4.2): the changes of the simultaneous application are the union
of the changes. -/
theorem combine_ne_iff (pin a b : Bool) :
    combine pin a b ≠ pin ↔ a ≠ pin ∨ b ≠ pin := by decide +revert

theorem combine_comm (pin a b : Bool) : combine pin a b = combine pin b a := by
  decide +revert

theorem combine_assoc (pin a b c : Bool) :
    combine pin (combine pin a b) c = combine pin a (combine pin b c) := by decide +revert

/-- The input itself is a ⊙-identity ([yolyan-2025] Prop. 4.4(iii)). -/
theorem combine_id (pin a : Bool) : combine pin a pin = a := by decide +revert

/-- ⊘ is the De Morgan dual of ⊙: negate the two output values, not the input. -/
theorem combineC_eq_not_combine (pin a b : Bool) :
    combineC pin a b = !combine pin (!a) (!b) := by decide +revert

theorem combineC_comm (pin a b : Bool) : combineC pin a b = combineC pin b a := by
  decide +revert

theorem combineC_assoc (pin a b c : Bool) :
    combineC pin (combineC pin a b) c = combineC pin a (combineC pin b c) := by
  decide +revert

end Subregular.Logic.BMRS
