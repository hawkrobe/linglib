/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Set.Finite.List
import Linglib.Core.Computability.TransitionMonoid
import Linglib.Core.Computability.StarFree
import Linglib.Core.Computability.Subregular.Language.StrictlyLocal

/-!
# Strictly local languages are star-free

Over a finite alphabet, every strictly `k`-local language is star-free:
`Language.IsStrictlyLocal.isStarFree`. This places `SL_k ⊆ SF` inside the subregular
hierarchy ([mcnaughton-papert-1971] [heinz-rawal-tanner-2011]) and validates the algebraic
engine `Language.IsStarFree.of_recognizes` on a genuine recognizer.

## Construction

The recognizer is the **local scanner** that remembers only the last `k - 1` augmented
symbols (a reversed window) plus an absorbing dead state `none`, entered when a freshly
completed length-`k` window is not permitted by the grammar. Its **transition monoid**
(`DFA.transitionMonoid`) is finite (`Finite α`) and aperiodic: the scanner is *definite* —
its alive state depends only on the last `k - 1` symbols read — so reading any word `vᵐ`
stabilises for `m ≥ k - 1`, giving the uniform law `x ^ k = x ^ (k-1)`. Recognition folds
the fixed boundary markers `noneᵏ⁻¹` into the start window and the acceptance set, relating
the scanner run to "every `k`-factor of `boundary k w` is permitted".

`[Finite α]` is essential: SL over an infinite alphabet need not even be regular.

## Main results

* `Language.IsStrictlyLocal.isStarFree` — `IsStrictlyLocal L k → IsStarFree L` (finite `α`).
-/

open List

namespace Subregular

variable {α : Type*}

/-- Reversed scanner window: up to `n` augmented symbols, head = most recent. -/
abbrev Win (α : Type*) (n : ℕ) := { w : List (Option α) // w.length ≤ n }

instance [Finite α] (n : ℕ) : Finite (Win α n) :=
  (List.finite_length_le (Option α) n).to_subtype

variable (G : SLGrammar α) (n : ℕ)

open Classical in
/-- Scanner step over window length `n` (locality width `k = n+1`). Dead `none` is
absorbing; otherwise extend the reversed window and flag dead on a forbidden
completed length-`(n+1)` window. -/
private noncomputable def step : Option (Win α n) → Option α → Option (Win α n)
  | none, _ => none
  | some w, a =>
    if (a :: w.val).reverse ∉ G ∧ (a :: w.val).length = n + 1 then none
    else some ⟨(a :: w.val).take n, (List.length_take_le _ _).trans (by simp)⟩

open Classical in
/-- The scanner DFA (start/accept irrelevant: only its transition monoid is used). -/
private noncomputable def scanDFA : DFA (Option α) (Option (Win α n)) where
  step := step G n
  start := none
  accept := ∅

@[simp] private lemma scanDFA_step (s : Option (Win α n)) (a : Option α) :
    (scanDFA G n).step s a = step G n s a := rfl

/-- Dead is absorbing: once `none`, reading anything stays `none`. -/
@[simp] private lemma evalFrom_none (xs : List (Option α)) :
    (scanDFA G n).evalFrom none xs = none := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [DFA.evalFrom_cons]; simpa [step] using ih

/-- Window after an alive run of `xs`: the reversed window is the last `n` symbols of
`xs.reverse ++ w` (most recent first). -/
private lemma evalFrom_alive_window (w : Win α n) (xs : List (Option α)) :
    ∀ w', (scanDFA G n).evalFrom (some w) xs = some w' → w'.val = (xs.reverse ++ w.val).take n := by
  induction xs generalizing w with
  | nil => rintro w' h; simp only [DFA.evalFrom_nil, Option.some.injEq] at h
           subst h; simp [List.take_of_length_le w.2]
  | cons a xs ih =>
    intro w' h
    rw [DFA.evalFrom_cons] at h
    simp only [scanDFA_step, step] at h
    split at h
    · simp only [evalFrom_none] at h; exact absurd h (by simp)
    · rw [ih _ w' h, reverse_cons, append_assoc]
      simpa using take_append_take n xs.reverse (a :: w.val)

/-- A forbidden completed window: some `(n+1)`-factor of `S` is not permitted. -/
private def IsForbiddenWindow (S : List (Option α)) : Prop :=
  ∃ f, f <:+: S ∧ f.length = n + 1 ∧ f ∉ G

variable {β : Type*}

/-- Window-not-full step: the post-step scanned string is unchanged. -/
private lemma scanned_step_lt (w : List β) (a : β) (xs : List β) (h : w.length < n) :
    (take n (a :: w)).reverse ++ xs = w.reverse ++ a :: xs := by
  rw [List.take_of_length_le (by simp; omega)]; simp

/-- For a full window, the `(n+1)`-prefix of the scanned string is the completed window. -/
private lemma take_prefix_full (w : List β) (a : β) (xs : List β) (h : w.length = n) :
    (w.reverse ++ a :: xs).take (n + 1) = (a :: w).reverse := by
  rw [take_append, reverse_cons]
  congr 1
  · rw [List.take_of_length_le (by simp; omega)]
  · simp [h]

/-- Window-full step: the post-step scanned string is the tail of the pre-step one. -/
private lemma scanned_step_eq (w : List β) (a : β) (xs : List β) (h : w.length = n) :
    (take n (a :: w)).reverse ++ xs = (w.reverse ++ a :: xs).tail := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; obtain rfl : w = [] := List.length_eq_zero_iff.mp h; simp
  · have hwr : w.reverse ≠ [] := by simp; rintro rfl; simp at h; omega
    rw [take_cons (by omega), reverse_cons, List.append_assoc, List.tail_append_of_ne_nil hwr,
        show n - 1 = w.length - 1 by omega, ← List.dropLast_eq_take, ← List.tail_reverse]
    rfl

/-- Dead-status: scanning `xs` from window `w` dies iff some forbidden `(n+1)`-window is
completed — exactly the forbidden `(n+1)`-factors of `w.reverse ++ xs`. -/
private lemma evalFrom_eq_none_iff (w : Win α n) (xs : List (Option α)) :
    (scanDFA G n).evalFrom (some w) xs = none ↔ IsForbiddenWindow G n (w.val.reverse ++ xs) := by
  induction xs generalizing w with
  | nil =>
    simp only [DFA.evalFrom_nil, append_nil]
    refine ⟨fun h => absurd h (by simp), ?_⟩
    rintro ⟨f, hf, hlen, _⟩
    exact absurd (hf.length_le.trans (by simpa using w.2)) (by omega)
  | cons a xs ih =>
    rw [DFA.evalFrom_cons]
    simp only [scanDFA_step, step]
    split
    · rename_i hdie
      obtain ⟨hbad, hlen⟩ := hdie
      simp only [evalFrom_none, true_iff]
      refine ⟨(a :: w.val).reverse, ?_, by simpa using hlen, hbad⟩
      rw [reverse_cons]
      refine List.IsPrefix.isInfix ?_
      rw [show a :: xs = [a] ++ xs from rfl, ← List.append_assoc]
      exact List.prefix_append _ _
    · rename_i halive
      rw [ih]
      show IsForbiddenWindow G n ((take n (a :: w.val)).reverse ++ xs)
        ↔ IsForbiddenWindow G n (w.val.reverse ++ a :: xs)
      rcases lt_or_eq_of_le w.2 with hlt | heq
      · rw [scanned_step_lt n w.val a xs hlt]
      · rw [scanned_step_eq n w.val a xs heq]
        have hgood : (a :: w.val).reverse ∈ G := by
          by_contra hc; exact halive ⟨hc, by simpa using heq⟩
        refine ⟨fun ⟨f, hf, hlen, hbad⟩ => ⟨f, hf.trans (List.tail_suffix _).isInfix, hlen, hbad⟩,
          fun ⟨f, hf, hlen, hbad⟩ => ?_⟩
        have hsplit : f <+: (w.val.reverse ++ a :: xs)
            ∨ f <:+: (w.val.reverse ++ a :: xs).tail := by
          match w.val.reverse ++ a :: xs, hf with
          | [], hf => simp [List.eq_nil_of_infix_nil hf] at hlen
          | _ :: _, hf => simpa using List.infix_cons_iff.mp hf
        rcases hsplit with hpre | hinf
        · refine absurd ?_ hbad
          rw [List.prefix_iff_eq_take.mp hpre, hlen, take_prefix_full n w.val a xs heq]
          exact hgood
        · exact ⟨f, hinf, hlen, hbad⟩

/-! ### Aperiodicity of the transition monoid

The scanner is a *definite* automaton: its alive state depends only on the last `n`
symbols read (plus the monotone dead flag). Hence reading `vt` `n+1` or `n+2` times lands
in the same state — the transition monoid satisfies `x ^ (n+2) = x ^ (n+1)`. -/

/-- The list `vt` concatenated `m` times. -/
private abbrev rep (vt : List (Option α)) (m : ℕ) : List (Option α) := (List.replicate m vt).flatten

private lemma rep_succ (vt : List (Option α)) (m : ℕ) : rep vt (m + 1) = rep vt m ++ vt := by
  rw [rep, replicate_succ', flatten_append]; simp [rep]

private lemma length_rep (vt : List (Option α)) (m : ℕ) : (rep vt m).length = m * vt.length := by
  simp [rep, List.length_flatten]

/-- Window stabilisation: after `≥ n` copies of `vt`, one more copy leaves the window
unchanged (the last `n` symbols are already `vt`-periodic). -/
private lemma take_rep_reverse_stable (vt sw : List (Option α)) {m : ℕ} (hm : n ≤ m * vt.length) :
    ((rep vt (m + 1)).reverse ++ sw).take n = ((rep vt m).reverse ++ sw).take n := by
  have hrev : ∀ j, (rep vt j).reverse = rep vt.reverse j := fun j => by
    rw [rep, rep, List.reverse_flatten]; congr 1; simp [List.map_replicate]
  rw [hrev, hrev, rep_succ, List.append_assoc,
    List.take_append_of_le_length (by rw [length_rep]; simpa using hm),
    List.take_append_of_le_length (by rw [length_rep]; simpa using hm)]

/-- Reading `vt` from `evalFrom s (rep vt (n+1))` is a fixed point: the window is already
`vt`-saturated and the dead flag is monotone. -/
private lemma evalFrom_rep_fixed (s : Option (Win α n)) (vt : List (Option α)) :
    (scanDFA G n).evalFrom ((scanDFA G n).evalFrom s (rep vt (n + 1))) vt
      = (scanDFA G n).evalFrom s (rep vt (n + 1)) := by
  rcases eq_or_ne vt [] with hvt | hvt
  · subst hvt
    rw [show rep ([] : List (Option α)) (n + 1) = [] from List.flatten_replicate_nil]; simp
  have hpos : 1 ≤ vt.length := List.length_pos_iff.mpr hvt
  rcases hs : s with _ | sw
  · simp [evalFrom_none]
  set A := (scanDFA G n).evalFrom (some sw) (rep vt n) with hA
  have hBrec : (scanDFA G n).evalFrom (some sw) (rep vt (n + 1)) = (scanDFA G n).evalFrom A vt := by
    rw [hA, ← DFA.evalFrom_of_append, ← rep_succ]
  rw [hBrec]
  rcases hAcase : A with _ | wA
  · simp [evalFrom_none]
  rcases hB : (scanDFA G n).evalFrom (some wA) vt with _ | wB
  · simp [evalFrom_none]
  have hwA : wA.val = ((rep vt n).reverse ++ sw.val).take n :=
    evalFrom_alive_window G n sw (rep vt n) wA (by rw [← hA, hAcase])
  have hwB : wB.val = (vt.reverse ++ wA.val).take n := evalFrom_alive_window G n wA vt wB hB
  have hwAB : wB.val = wA.val := by
    rw [hwB, hwA, take_append_take, ← List.append_assoc,
      show vt.reverse ++ (rep vt n).reverse = (rep vt (n + 1)).reverse by
        rw [rep_succ, List.reverse_append],
      take_rep_reverse_stable n vt sw.val (Nat.le_mul_of_pos_right n hpos)]
  have hwBA : some wB = some wA := by rw [Subtype.ext hwAB]
  rw [hwBA, hB, hwBA]

private lemma toList_pow (v : FreeMonoid (Option α)) (m : ℕ) : (v ^ m).toList = rep v.toList m := by
  induction m with
  | zero => simp [rep]
  | succ k ih => rw [pow_succ, FreeMonoid.toList_mul, ih, rep_succ]

/-- The scanner transition action stabilises at exponent `n + 1`: reading `vt` `n+2` times
equals reading it `n+1` times, as a state transformation. -/
private lemma transitionHom_pow_stabilizes (v : FreeMonoid (Option α)) :
    (scanDFA G n).transitionHom v ^ (n + 2) = (scanDFA G n).transitionHom v ^ (n + 1) := by
  rw [← map_pow, ← map_pow, DFA.transitionHom_eq_iff]
  intro s
  rw [toList_pow, toList_pow, rep_succ, DFA.evalFrom_of_append]
  exact evalFrom_rep_fixed G n s v.toList

/-- The scanner's transition monoid is aperiodic (uniform exponent `n + 1`). -/
private theorem isAperiodic_transitionMonoid :
    Monoid.IsAperiodic (scanDFA G n).transitionMonoid := by
  refine ⟨n + 1, fun x => ?_⟩
  obtain ⟨v, hv⟩ := x.2
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← hv]
  exact transitionHom_pow_stabilizes G n v

/-! ### Recognition and the main theorem -/

/-- The internal-letter transition action `FreeMonoid α →* transitionMonoid`: read each
letter `a` as the augmented symbol `some a`. -/
private noncomputable def scanHom : FreeMonoid α →* (scanDFA G n).transitionMonoid :=
  ((scanDFA G n).transitionHom.comp (FreeMonoid.map Option.some)).codRestrict _
    (fun v => ⟨FreeMonoid.map Option.some v, rfl⟩)

/-- The full left boundary as a start window. -/
private def startWin : Win α n := ⟨List.replicate n none, by simp⟩

@[simp] private lemma scanHom_unop_apply (w : List α) (s : Option (Win α n)) :
    ((scanHom G n (FreeMonoid.ofList w)).val.unop) s
      = (scanDFA G n).evalFrom s (w.map Option.some) := by
  simp only [scanHom, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    DFA.unop_transitionHom_apply]
  congr 1

/-- The scanner run over `w` (with both boundaries folded in) is alive iff `w` lies in the
language generated by `G` at width `n+1` — every `(n+1)`-factor of `boundary (n+1) w` is
permitted. -/
private lemma alive_iff_mem_language (w : List α) :
    (scanDFA G n).evalFrom (some (startWin n)) (w.map Option.some ++ List.replicate n none) ≠ none
      ↔ w ∈ G.language (n + 1) := by
  rw [Ne, evalFrom_eq_none_iff]
  simp only [startWin, List.reverse_replicate, SLGrammar.mem_language, IsForbiddenWindow,
    not_exists, not_and, not_not]
  rw [show List.replicate n none ++ (w.map Option.some ++ List.replicate n none)
        = boundary (n + 1) w by simp [boundary]]
  refine ⟨fun h f hf => ?_, fun h f hinf hlen => h f (List.mem_kFactors.mpr ⟨hinf, hlen⟩)⟩
  rcases Classical.em (f ∈ G) with hg | hg
  · exact hg
  · obtain ⟨hinf, hlen⟩ := List.mem_kFactors.mp hf
    exact absurd (h f hinf hlen) hg

/-- A strictly-`(n+1)`-local language is star-free: the scanner's transition monoid is a
finite aperiodic recognizer ([mcnaughton-papert-1971] [heinz-rawal-tanner-2011]). -/
private theorem isStarFree_of_language_succ (L : Language α) [Finite α]
    (hL : G.language (n + 1) = L) : L.IsStarFree := by
  classical
  refine Language.IsStarFree.of_recognizes (isAperiodic_transitionMonoid G n) (scanHom G n)
    {g | (scanDFA G n).evalFrom (g.val.unop (some (startWin n))) (List.replicate n none) ≠ none}
    (fun w => ?_)
  rw [← hL, Set.mem_setOf_eq, scanHom_unop_apply, ← DFA.evalFrom_of_append, alive_iff_mem_language]

end Subregular

namespace Language

variable {α : Type*} [Finite α]

open Subregular

/-- **Strictly local languages are star-free** ([mcnaughton-papert-1971]). Over a finite
alphabet, the local scanner remembering the last `k - 1` symbols is a finite aperiodic
recognizer, so `SL_k ⊆ SF`. (`[Finite α]` is essential: SL over an infinite alphabet need
not even be regular.) -/
theorem IsStrictlyLocal.isStarFree {L : Language α} {k : ℕ} (h : L.IsStrictlyLocal k) :
    L.IsStarFree := by
  classical
  obtain ⟨G, hG⟩ := h
  rcases k with _ | n
  · -- `k = 0`: membership is the constant `[] ∈ G`, recognized by the trivial monoid.
    refine Language.IsStarFree.of_recognizes (M := PUnit.{1}) Monoid.IsAperiodic.of_subsingleton 1
      (if ([] : Augmented α) ∈ G then Set.univ else ∅) (fun w => ?_)
    rw [← hG]
    simp only [SLGrammar.mem_language, List.mem_kFactors, List.length_eq_zero_iff, and_imp]
    by_cases hg : ([] : Augmented α) ∈ G
    · simpa [hg] using fun f _ (hf : f = []) => hf ▸ hg
    · simp only [hg, if_false, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨[], List.nil_infix, rfl, hg⟩
  · exact isStarFree_of_language_succ G n L hG

end Language
