module

public import Linglib.Semantics.Presupposition.SyntacticEnvironment
public import Mathlib.Tactic.IntervalCases

/-!
# Kalomoiros (2023): Presupposition and Its (A-)Symmetries

This file formalizes System 1 of the dissertation's Limited Symmetry (§3.4), a theory of
presupposition projection that checks Transparency incrementally, at every point of the parse
after a trigger. The language is the propositional fragment of [schlenker-2009]'s L
(Definition 3.4.1), a trigger `p'p` presupposing `p'` and asserting `p`. At a parse point, a
sentence is stably true (false) at a world when every good final of the string up to that point
makes it true (false) there; Definition 3.4.4 (`TranspLS`) requires, at every trigger, every parse
point after it and every assertion, that the worlds of the context where the sentence is stably
true (false) are worlds where it is stably true (false) with the trigger replaced by its assertion.

The check is made world by world (`transpLSAt_iff`), and at a world only the truth functions that
the good finals realize matter (`funs`, `forall_agreeUpTo_iff`), so that each of the
dissertation's facts is a computation. Conjunction is asymmetric: `(p'p and q)` requires the
context to entail `p'` (Fact 3.4.1), `(q and p'p)` only `q → p'` (Fact 3.4.2). Disjunction is
symmetric: `(p'p or q)` requires `¬q → p'` (Fact 3.4.3). A conditional's antecedent behaves like a
first conjunct (Fact 3.4.4) and its consequent like a second (Fact 3.4.5). A negated sentence
respects the constraint iff the sentence does (Proposition 3.4.1), but a negation inside a
coordination changes its polarity: `(if (not p'p). q)` behaves like `(p'p or q)` (Fact 3.4.10).
With several triggers, each trigger's condition is computed separately (Facts 3.4.11–3.4.14), and
material before the highest connective can filter symmetrically (Fact 3.4.15).

Two conditions printed in the dissertation differ from what Definition 3.4.4 gives. For
`(if ((not p'p) and q). r)` the dissertation prints `(q ∧ r) → p'` and omits the derivation; the
constraint gives `(q ∧ ¬r) → p'`, since the antecedent matters only where the consequent is false
(`transpLS_if_not_and`, `not_transpLS_if_not_and_of_printed`). For the second trigger of
`((not p'p) and q'q)` it prints `p'p → q'`; the constraint gives `(not p'p) → q'`, filtering by the
first conjunct as the recipe of Fact 3.4.7 predicts (`transpLSAt_not_and_second`,
`not_transpLSAt_not_and_second_of_printed`).

## Implementation notes

* A trigger `trigger p a` presupposes `p` and asserts `a`; the dissertation writes `p'p` with the
  prime on the presupposition, the reverse of [schlenker-2009]'s convention.
* The parse points after a trigger are the substrings κ of Definition 3.4.4. They are represented
  by `SyntacticEnvironment.AgreeUpTo`, which counts the connective after a first argument and the
  second argument as one item each and ignores closing brackets. At a point inside the second
  argument, the good finals realize at each world either what they realize before the argument or
  what they realize after it, because the argument's value there is either still open or already
  fixed. Since the constraint is checked world by world, these points add no condition.
* A context is a set of worlds, and "for all p" in Definition 3.4.4 ranges over the propositions
  of the assertion.
* Fact 3.4.6 concerns a postposed conditional `(q. if p'p)`, which is not in the language of
  Definition 3.4.1, and is not formalized. Facts 3.4.7 and 3.4.9 are stated for arbitrary
  sentences and are left as `TODO`.

## References

* [kalomoiros-2023]
* [schlenker-2009]
-/

@[expose] public section

namespace Kalomoiros2023

open Presupposition SyntacticEnvironment

variable {Atom W : Type*} (I : Atom → Set W)

/-! ### Definition 3.4.4 -/

/-- The worlds of `C` at which the sentence up to parse point `n` after the gap of `K`, with `X`
in the gap, is true whatever follows. -/
def stablyTrue (C : Set W) (n : ℕ) (K : SyntacticEnvironment Atom) (X : Set W) : Set W :=
  {w ∈ C | ∀ K', AgreeUpTo n K K' → w ∈ K'.truth I X}

/-- The worlds of `C` at which the sentence up to parse point `n` after the gap of `K`, with `X`
in the gap, is false whatever follows. -/
def stablyFalse (C : Set W) (n : ℕ) (K : SyntacticEnvironment Atom) (X : Set W) : Set W :=
  {w ∈ C | ∀ K', AgreeUpTo n K K' → w ∉ K'.truth I X}

/-- Definition 3.4.4 at one trigger, with presupposition `p` at the gap of `K`: at every parse
point after the trigger and for every assertion `D`, the worlds where the sentence is stably true
(false) are worlds where it is stably true (false) with the presupposition deleted. -/
def TranspLSAt (C : Set W) (K : SyntacticEnvironment Atom) (p : Atom) : Prop :=
  ∀ n ≤ K.rightItems, ∀ D : Set W,
    stablyTrue I C n K (I p ∩ D) ⊆ stablyTrue I C n K D ∧
      stablyFalse I C n K (I p ∩ D) ⊆ stablyFalse I C n K D

/-- Definition 3.4.4: a formula is acceptable in `C` when the constraint holds at every trigger. -/
def TranspLS (C : Set W) (F : Formula Atom) : Prop :=
  ∀ o ∈ F.occurrences, TranspLSAt I C o.1 o.2.1

/-- The constraint is checked world by world: at a world where the presupposition fails, whenever
every good final at a parse point makes the sentence true (false) with a false gap, every good
final makes it true (false) with a true gap. -/
theorem transpLSAt_iff (C : Set W) (K : SyntacticEnvironment Atom) (p : Atom) :
    TranspLSAt I C K p ↔ ∀ w ∈ C, w ∉ I p → ∀ n ≤ K.rightItems,
      ((∀ K', AgreeUpTo n K K' → w ∈ K'.truth I ∅) →
          ∀ K', AgreeUpTo n K K' → w ∈ K'.truth I Set.univ) ∧
        ((∀ K', AgreeUpTo n K K' → w ∉ K'.truth I ∅) →
          ∀ K', AgreeUpTo n K K' → w ∉ K'.truth I Set.univ) := by
  have tf (K' : SyntacticEnvironment Atom) := isTruthFunctional_truth I K'
  refine ⟨fun h w hw hp n hn ↦ ⟨fun h₀ ↦ ?_, fun h₀ ↦ ?_⟩, fun h n hn D ↦ ⟨?_, ?_⟩⟩
  · refine ((h n hn Set.univ).1 ⟨hw, fun K' hK ↦ ?_⟩).2
    exact ((tf K').mem_iff_of_notMem (by simp [hp])).2 (h₀ K' hK)
  · refine ((h n hn Set.univ).2 ⟨hw, fun K' hK ↦ ?_⟩).2
    exact mt ((tf K').mem_iff_of_notMem (by simp [hp])).1 (h₀ K' hK)
  · rintro w ⟨hw, hs⟩
    refine ⟨hw, fun K' hK ↦ ?_⟩
    by_cases hp : w ∈ I p
    · exact (tf K' w _ _ (by simp [hp])).1 (hs K' hK)
    · by_cases hd : w ∈ D
      · exact ((tf K').mem_iff_of_mem hd).2 ((h w hw hp n hn).1 (fun K'' hK'' ↦
          ((tf K'').mem_iff_of_notMem (by simp [hp])).1 (hs K'' hK'')) K' hK)
      · exact ((tf K').mem_iff_of_notMem hd).2
          (((tf K').mem_iff_of_notMem (by simp [hp])).1 (hs K' hK))
  · rintro w ⟨hw, hs⟩
    refine ⟨hw, fun K' hK ↦ ?_⟩
    by_cases hp : w ∈ I p
    · exact mt (tf K' w _ _ (by simp [hp])).2 (hs K' hK)
    · by_cases hd : w ∈ D
      · exact mt ((tf K').mem_iff_of_mem hd).1 ((h w hw hp n hn).2 (fun K'' hK'' ↦
          mt ((tf K'').mem_iff_of_notMem (by simp [hp])).2 (hs K'' hK'')) K' hK)
      · exact mt ((tf K').mem_iff_of_notMem hd).1
          (mt ((tf K').mem_iff_of_notMem (by simp [hp])).2 (hs K' hK))

/-! ### The truth functions of the good finals -/

open Classical

/-- A connective's truth function on booleans. -/
def evalB : Connective → Bool → Bool → Bool
  | .conj, a, b => a && b
  | .cond, a, b => !a || b
  | .disj, a, b => a || b

theorem decide_eval (c : Connective) (a b : Prop) :
    decide (c.eval a b) = evalB c (decide a) (decide b) := by
  cases c <;> by_cases ha : a <;> by_cases hb : b <;> simp [Connective.eval, evalB, ha, hb]

/-- The truth value at `w` of a formula. -/
noncomputable def val (w : W) (F : Formula Atom) : Bool := decide (w ∈ F.truth I)

/-- The connectives that may follow a first argument when no item after the gap is fixed. -/
def compat : Connective → List Connective
  | .cond => [.cond]
  | _ => [.conj, .disj]

theorem mem_compat {c c' : Connective} : c' ∈ compat c ↔ (c = .cond ↔ c' = .cond) := by
  cases c <;> cases c' <;> decide

/-- The truth functions at `w` of the good finals of a step up to parse point `n`, as functions of
the gap's truth value. -/
noncomputable def stepFuns (w : W) (n : ℕ) : SyntacticEnvironment.Step Atom → List (Bool → Bool)
  | .not => [not]
  | .right c F => [evalB c (val I w F)]
  | .left c G =>
    if n = 0 then (compat c).flatMap fun c' ↦ [(evalB c' · true), (evalB c' · false)]
    else if n < c.rightItems then [(evalB c · true), (evalB c · false)]
    else [(evalB c · (val I w G))]

/-- The truth functions at `w` of the good finals of an environment up to parse point `n`. -/
noncomputable def funs (w : W) : ℕ → SyntacticEnvironment Atom → List (Bool → Bool)
  | _, [] => [id]
  | n, s :: K => (stepFuns I w n s).flatMap fun f ↦ (funs w (n - s.rightItems) K).map (· ∘ f)

/-- A formula can be true or false at any world. -/
theorem forall_formula_iff [Nonempty Atom] (w : W) (Q : Prop → Prop) :
    (∀ G : Formula Atom, Q (w ∈ G.truth I)) ↔ Q True ∧ Q False := by
  let a := Classical.arbitrary Atom
  let t : Formula Atom := .bin .cond (.atom a) (.atom a)
  have ht : (w ∈ t.truth I) = True := eq_true fun h ↦ h
  have hf : (w ∈ (Formula.not t).truth I) = False := eq_false fun h ↦ h fun h ↦ h
  refine ⟨fun h ↦ ⟨ht ▸ h t, hf ▸ h (.not t)⟩, fun ⟨h₁, h₀⟩ G ↦ ?_⟩
  by_cases hG : w ∈ G.truth I
  · rwa [eq_true hG]
  · rwa [eq_false hG]

theorem forall_stepAgree_iff [Nonempty Atom] (w : W) (n : ℕ) (s : SyntacticEnvironment.Step Atom)
    (X : Set W) (R : Bool → Prop) :
    (∀ s', s.AgreeUpTo n s' → R (decide (w ∈ s'.truth I X))) ↔
      ∀ f ∈ stepFuns I w n s, R (f (decide (w ∈ X))) := by
  cases s with
  | not => simp [SyntacticEnvironment.Step.AgreeUpTo, stepFuns, SyntacticEnvironment.Step.truth]
  | right c F =>
    simp [SyntacticEnvironment.Step.AgreeUpTo, stepFuns, SyntacticEnvironment.Step.truth,
      decide_eval, val]
  | left c G =>
    have key (c' : Connective) : (∀ G' : Formula Atom,
        R (decide (w ∈ (SyntacticEnvironment.Step.left c' G').truth I X))) ↔
          R (evalB c' (decide (w ∈ X)) true) ∧
          R (evalB c' (decide (w ∈ X)) false) := by
      simp only [SyntacticEnvironment.Step.truth, Set.mem_ofPred_eq, decide_eval]
      exact forall_formula_iff I w (fun b ↦ R (evalB c' (decide (w ∈ X)) (decide b))) |>.trans
        (by simp)
    simp only [SyntacticEnvironment.Step.AgreeUpTo, stepFuns]
    split_ifs
    · simp only [forall_exists_index, and_imp, List.forall_mem_flatMap, List.forall_mem_cons,
        List.mem_nil_iff, false_imp_iff, implies_true, and_true, ← mem_compat]
      exact ⟨fun h c' hc ↦ (key c').1 fun G' ↦ h _ c' G' rfl hc,
        fun h _ c' G' he hc ↦ he ▸ (key c').2 (h c' hc) G'⟩
    · simp only [forall_exists_index, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff,
        implies_true, and_true]
      exact ⟨fun h ↦ (key c).1 fun G' ↦ h _ G' rfl, fun h _ G' he ↦ he ▸ (key c).2 h G'⟩
    · simp [SyntacticEnvironment.Step.truth, decide_eval, val]

/-- The good finals at a parse point realize, at each world, the truth functions `funs`. -/
theorem forall_agreeUpTo_iff [Nonempty Atom] (w : W) (n : ℕ) (K : SyntacticEnvironment Atom)
    (X : Set W) (R : Bool → Prop) :
    (∀ K', AgreeUpTo n K K' → R (decide (w ∈ K'.truth I X))) ↔
      ∀ f ∈ funs I w n K, R (f (decide (w ∈ X))) := by
  induction K generalizing n X R with
  | nil => simp [AgreeUpTo, funs, SyntacticEnvironment.truth]
  | cons s K ih =>
    have lhs : (∀ K', AgreeUpTo n (s :: K) K' → R (decide (w ∈ K'.truth I X))) ↔
        ∀ s', s.AgreeUpTo n s' → ∀ K'', AgreeUpTo (n - s.rightItems) K K'' →
          R (decide (w ∈ K''.truth I (s'.truth I X))) :=
      ⟨fun h s' hs K'' hK ↦ h (s' :: K'') ⟨s', K'', rfl, hs, hK⟩,
        fun h K' ⟨s', K'', he, hs, hK⟩ ↦ by subst he; exact h s' hs K'' hK⟩
    rw [lhs]
    simp only [funs, List.forall_mem_flatMap, List.forall_mem_map, Function.comp_apply]
    exact (forall_congr' fun s' ↦ imp_congr_right fun _ ↦ ih _ _ _).trans
      (forall_stepAgree_iff I w n s X fun b ↦ ∀ g ∈ funs I w (n - s.rightItems) K, R (g b))

/-- Definition 3.4.4 world by world, as a condition on the truth functions of the good finals. -/
theorem transpLSAt_iff_funs (C : Set W) (K : SyntacticEnvironment Atom) (p : Atom) :
    TranspLSAt I C K p ↔ ∀ w ∈ C, w ∉ I p → ∀ n ≤ K.rightItems,
      ((∀ f ∈ funs I w n K, f false = true) → ∀ f ∈ funs I w n K, f true = true) ∧
        ((∀ f ∈ funs I w n K, f false = false) → ∀ f ∈ funs I w n K, f true = false) := by
  have : Nonempty Atom := ⟨p⟩
  rw [transpLSAt_iff]
  refine forall₂_congr fun w _ ↦ imp_congr_right fun _ ↦ forall₂_congr fun n _ ↦ ?_
  have e₁ (X : Set W) := forall_agreeUpTo_iff I w n K X (· = true)
  have e₀ (X : Set W) := forall_agreeUpTo_iff I w n K X (· = false)
  simp only [decide_eq_true_iff, decide_eq_false_iff_not] at e₁ e₀
  simp only [e₁, e₀]
  simp

/-! ### Facts -/

variable {C : Set W} {p a q b r : Atom}

theorem transpLS_of_occurrences {F : Formula Atom} {K : SyntacticEnvironment Atom} {p a : Atom}
    (h : F.occurrences = [(K, p, a)]) : TranspLS I C F ↔ TranspLSAt I C K p := by
  simp [TranspLS, h]

/-- Fact 3.4.1 (p. 124): `(p'p and q)` requires the context to entail `p'`. -/
theorem transpLS_and_left : TranspLS I C (.bin .conj (.trigger p a) (.atom q)) ↔ C ⊆ I p := by
  rw [transpLS_of_occurrences I (K := [.left .conj (.atom q)]) (a := a) rfl, transpLSAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ absurd (h hw) hp⟩
  have := h w hw hp 1 (by simp [rightItems, Step.rightItems, Connective.rightItems])
  simp [funs, stepFuns, evalB, Connective.rightItems] at this

/-- Evaluate the constraint at every parse point of a concrete environment. -/
local macro "ls_points" : tactic =>
  `(tactic| (intro n hn
             simp only [rightItems_cons, rightItems_nil, Step.rightItems, Connective.rightItems]
               at hn
             interval_cases n <;>
               simp_all [funs, stepFuns, evalB, val, Formula.truth, Step.rightItems,
                 Connective.rightItems, compat, Connective.eval]))

/-- Evaluate the constraint at one parse point of a concrete environment. -/
local macro "ls_at " h:term : tactic =>
  `(tactic| (simp [funs, stepFuns, evalB, val, Formula.truth, Step.rightItems,
               Connective.rightItems, compat, Connective.eval, *] at $h:term))

/-- Fact 3.4.2 (p. 126): `(q and p'p)` requires the context to entail `q → p'`. -/
theorem transpLS_and_right :
    TranspLS I C (.bin .conj (.atom q) (.trigger p a)) ↔ C ⊆ {w | w ∈ I q → w ∈ I p} := by
  rw [transpLS_of_occurrences I (K := [.right .conj (.atom q)]) (a := a) rfl, transpLSAt_iff_funs]
  refine ⟨fun h w hw hq ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 0 le_rfl
    ls_at this
  · have hq : w ∉ I q := fun hq ↦ hp (h hw hq)
    ls_points

/-- Fact 3.4.3 (p. 127): `(p'p or q)` requires the context to entail `¬q → p'`. -/
theorem transpLS_or_left :
    TranspLS I C (.bin .disj (.trigger p a) (.atom q)) ↔ C ⊆ {w | w ∉ I q → w ∈ I p} := by
  rw [transpLS_of_occurrences I (K := [.left .disj (.atom q)]) (a := a) rfl, transpLSAt_iff_funs]
  refine ⟨fun h w hw hq ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 2 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    ls_at this
  · have hq : w ∈ I q := by_contra fun hq ↦ hp (h hw hq)
    ls_points

/-- Fact 3.4.4 (p. 128): `(if p'p. q)` requires the context to entail `p'`. -/
theorem transpLS_if_left : TranspLS I C (.bin .cond (.trigger p a) (.atom q)) ↔ C ⊆ I p := by
  rw [transpLS_of_occurrences I (K := [.left .cond (.atom q)]) (a := a) rfl, transpLSAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ absurd (h hw) hp⟩
  have := h w hw hp 0 (Nat.zero_le _)
  ls_at this

/-- Fact 3.4.5 (p. 129): `(if q. p'p)` requires the context to entail `q → p'`. -/
theorem transpLS_if_right :
    TranspLS I C (.bin .cond (.atom q) (.trigger p a)) ↔ C ⊆ {w | w ∈ I q → w ∈ I p} := by
  rw [transpLS_of_occurrences I (K := [.right .cond (.atom q)]) (a := a) rfl, transpLSAt_iff_funs]
  refine ⟨fun h w hw hq ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 0 le_rfl
    ls_at this
  · have hq : w ∉ I q := fun hq ↦ hp (h hw hq)
    ls_points

/-- Fact 3.4.10 (p. 136), first half: `(if (not p'p). q)` requires the context to entail `¬q → p'`,
as `(p'p or q)` does. -/
theorem transpLS_if_not_left :
    TranspLS I C (.bin .cond (.not (.trigger p a)) (.atom q)) ↔ C ⊆ {w | w ∉ I q → w ∈ I p} := by
  rw [transpLS_of_occurrences I (K := [.not, .left .cond (.atom q)]) (a := a) rfl,
    transpLSAt_iff_funs]
  refine ⟨fun h w hw hq ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 1 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    ls_at this
  · have hq : w ∈ I q := by_contra fun hq ↦ hp (h hw hq)
    ls_points

/-- Fact 3.4.10 (p. 136): `(if (not p'p). q)` respects the constraint iff `(p'p or q)` does. -/
theorem transpLS_if_not_left_iff_or :
    TranspLS I C (.bin .cond (.not (.trigger p a)) (.atom q)) ↔
      TranspLS I C (.bin .disj (.trigger p a) (.atom q)) := by
  rw [transpLS_if_not_left, transpLS_or_left]

/-- Fact 3.4.8 (p. 134), as the constraint gives it: `(if ((not p'p) and q). r)` requires the
context to entail `(q ∧ ¬r) → p'`. The dissertation prints `(q ∧ r) → p'` and omits the
derivation (`not_transpLS_if_not_and_of_printed`). -/
theorem transpLS_if_not_and :
    TranspLS I C (.bin .cond (.bin .conj (.not (.trigger p a)) (.atom q)) (.atom r)) ↔
      C ⊆ {w | w ∈ I q → w ∉ I r → w ∈ I p} := by
  rw [transpLS_of_occurrences I (K := [.not, .left .conj (.atom q), .left .cond (.atom r)])
    (a := a) rfl, transpLSAt_iff_funs]
  refine ⟨fun h w hw hq hr ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 3 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    ls_at this
  · by_cases hq : w ∈ I q
    · have hr : w ∈ I r := by_contra fun hr ↦ hp (h hw hq hr)
      ls_points
    · ls_points

/-- The condition printed in Fact 3.4.8 is not the constraint's: a context where `q` holds and `r`
and `p'` fail entails `(q ∧ r) → p'` but violates the constraint. -/
theorem not_transpLS_if_not_and_of_printed {w : W} (hq : w ∈ I q) (hr : w ∉ I r) (hp : w ∉ I p) :
    {w} ⊆ {w | w ∈ I q → w ∈ I r → w ∈ I p} ∧
      ¬ TranspLS I {w} (.bin .cond (.bin .conj (.not (.trigger p a)) (.atom q)) (.atom r)) := by
  rw [transpLS_if_not_and]
  refine ⟨fun v hv ↦ ?_, fun h ↦ hp (h rfl hq hr)⟩
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact fun _ hr' ↦ absurd hr' hr

/-- Fact 3.4.11 (p. 137): in `(p'p and q'q)` the first trigger requires the context to entail
`p'`. -/
theorem transpLSAt_and_first :
    TranspLSAt I C [.left .conj (.trigger q b)] p ↔ C ⊆ I p := by
  rw [transpLSAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ absurd (h hw) hp⟩
  have := h w hw hp 1 (by simp [rightItems, Step.rightItems, Connective.rightItems])
  ls_at this

/-- Fact 3.4.12 (p. 137), first trigger: in `((not p'p) and q'q)` it requires the context to entail
`q'q → p'`. -/
theorem transpLSAt_not_and_first :
    TranspLSAt I C [.not, .left .conj (.trigger q b)] p ↔
      C ⊆ {w | w ∈ I q → w ∈ I b → w ∈ I p} := by
  rw [transpLSAt_iff_funs]
  refine ⟨fun h w hw hq hb ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ ?_⟩
  · have := h w hw hp 2 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    ls_at this
  · by_cases hq : w ∈ I q
    · have hb : w ∉ I b := fun hb ↦ hp (h hw hq hb)
      ls_points
    · ls_points

/-- Fact 3.4.12 (p. 137), second trigger, as the constraint gives it: in `((not p'p) and q'q)` it
requires the context to entail `(not p'p) → q'`, filtering by the first conjunct. The
dissertation prints `p'p → q'`. -/
theorem transpLSAt_not_and_second :
    TranspLSAt I C [.right .conj (.not (.trigger p a))] q ↔
      C ⊆ {w | w ∉ I p ∩ I a → w ∈ I q} := by
  rw [transpLSAt_iff_funs]
  refine ⟨fun h w hw hpa ↦ by_contra fun hq ↦ ?_, fun h w hw hq ↦ ?_⟩
  · have := h w hw hq 0 le_rfl
    ls_at this
  · have hpa : w ∈ I p ∩ I a := by_contra fun hpa ↦ hq (h hw hpa)
    obtain ⟨hp, ha⟩ := hpa
    ls_points

/-- Fact 3.4.13 (p. 138), first trigger: in `(p'p or q'q)` it requires the context to entail
`p' or q'q`. -/
theorem transpLSAt_or_first :
    TranspLSAt I C [.left .disj (.trigger q b)] p ↔ C ⊆ {w | w ∈ I p ∨ w ∈ I q ∩ I b} := by
  rw [transpLSAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hn ↦ ?_, fun h w hw hp ↦ ?_⟩
  · simp only [Set.mem_ofPred_eq, not_or, Set.mem_inter_iff, not_and] at hn
    obtain ⟨hp, hqb⟩ := hn
    have := h w hw hp 2 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    by_cases hq : w ∈ I q
    · have hb := hqb hq; ls_at this
    · ls_at this
  · obtain ⟨hq, hb⟩ := (h hw).resolve_left hp
    ls_points

/-- Fact 3.4.13 (p. 138), second trigger: in `(p'p or q'q)` it requires the context to entail
`q' or p'p`. -/
theorem transpLSAt_or_second :
    TranspLSAt I C [.right .disj (.trigger p a)] q ↔ C ⊆ {w | w ∈ I q ∨ w ∈ I p ∩ I a} := by
  rw [transpLSAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hn ↦ ?_, fun h w hw hq ↦ ?_⟩
  · simp only [Set.mem_ofPred_eq, not_or, Set.mem_inter_iff, not_and] at hn
    obtain ⟨hq, hpa⟩ := hn
    have := h w hw hq 0 le_rfl
    by_cases hp : w ∈ I p
    · have ha := hpa hp; ls_at this
    · ls_at this
  · obtain ⟨hp, ha⟩ := (h hw).resolve_left hq
    ls_points

/-- Fact 3.4.14 (p. 138): in `((not p'p) or q'q)` the first trigger requires the context to entail
`p'`. -/
theorem transpLSAt_not_or_first :
    TranspLSAt I C [.not, .left .disj (.trigger q b)] p ↔ C ⊆ I p := by
  rw [transpLSAt_iff_funs]
  refine ⟨fun h w hw ↦ by_contra fun hp ↦ ?_, fun h w hw hp ↦ absurd (h hw) hp⟩
  have := h w hw hp 1 (by simp [rightItems, Step.rightItems, Connective.rightItems])
  ls_at this

/-- Fact 3.4.15 (p. 138): `((p'p and q) or r)` requires the context to entail `q → (p' ∨ r)`:
the second conjunct filters symmetrically, before the highest connective. -/
theorem transpLS_and_or :
    TranspLS I C (.bin .disj (.bin .conj (.trigger p a) (.atom q)) (.atom r)) ↔
      C ⊆ {w | w ∈ I q → w ∈ I p ∨ w ∈ I r} := by
  rw [transpLS_of_occurrences I (K := [.left .conj (.atom q), .left .disj (.atom r)]) (a := a) rfl,
    transpLSAt_iff_funs]
  refine ⟨fun h w hw hq ↦ by_contra fun hn ↦ ?_, fun h w hw hp ↦ ?_⟩
  · simp only [not_or] at hn
    obtain ⟨hp, hr⟩ := hn
    have := h w hw hp 4 (by simp [rightItems, Step.rightItems, Connective.rightItems])
    ls_at this
  · by_cases hq : w ∈ I q
    · have hr : w ∈ I r := ((h hw) hq).resolve_left hp
      ls_points
    · ls_points

/-- The condition printed in Fact 3.4.12 for the second trigger is not the constraint's: a context
where `p'` and `q'` fail entails `p'p → q'` but violates the constraint. -/
theorem not_transpLSAt_not_and_second_of_printed {w : W} (hp : w ∉ I p) (hq : w ∉ I q) :
    {w} ⊆ {w | w ∈ I p ∩ I a → w ∈ I q} ∧
      ¬ TranspLSAt I {w} [.right .conj (.not (.trigger p a))] q := by
  rw [transpLSAt_not_and_second]
  refine ⟨fun v hv hpa ↦ ?_, fun h ↦ hq (h rfl fun hpa ↦ hp hpa.1)⟩
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact absurd hpa.1 hp

/-! ### Proposition 3.4.1: negation -/

theorem forall_agreeUpTo_append_not {n : ℕ} {K : SyntacticEnvironment Atom} {w : W} {X : Set W}
    (P : Prop → Prop) :
    (∀ L, AgreeUpTo n (K ++ [.not]) L → P (w ∈ L.truth I X)) ↔
      ∀ K', AgreeUpTo n K K' → P (w ∉ K'.truth I X) := by
  simp only [agreeUpTo_append_singleton, Step.AgreeUpTo, forall_exists_index, and_imp]
  refine ⟨fun h K' hK ↦ ?_, fun h L K' s' he hK hs ↦ ?_⟩
  · have := h _ K' .not rfl hK rfl
    rwa [truth_append] at this
  · subst he hs
    rw [truth_append]
    exact h K' hK

/-- Proposition 3.4.1 (p. 130): a sentence respects the constraint iff its negation does. -/
theorem transpLS_not (A : Formula Atom) : TranspLS I C (.not A) ↔ TranspLS I C A := by
  simp only [TranspLS, Formula.occurrences, List.forall_mem_map]
  refine forall₂_congr fun o _ ↦ ?_
  rw [transpLSAt_iff, transpLSAt_iff, rightItems_append]
  refine forall₂_congr fun w _ ↦ imp_congr_right fun _ ↦ forall₂_congr fun n _ ↦ ?_
  simp only [forall_agreeUpTo_append_not I (fun x ↦ x), forall_agreeUpTo_append_not I Not,
    not_not]
  exact and_comm

end Kalomoiros2023
