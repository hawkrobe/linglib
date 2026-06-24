/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.List
import Linglib.Core.Computability.TransitionMonoid
import Linglib.Core.Computability.StarFree
import Linglib.Core.Computability.Subregular.Language.StrictlyPiecewise

/-!
# Strictly piecewise languages are star-free

Over a finite alphabet, every strictly `k`-piecewise language is star-free:
`Language.IsStrictlyPiecewise.isStarFree`. This places `SP_k ⊆ SF` inside the subregular
hierarchy ([heinz-rogers-2010] [mcnaughton-papert-1971]) and — like the sibling
`SL_k ⊆ SF` (`Language.IsStrictlyLocal.isStarFree`) — validates the algebraic engine
`Language.IsStarFree.of_recognizes` on a genuine recognizer.

## Construction

The recognizer is the **subsequence scanner** that remembers only the *profile* of
length-`≤ k-1` subsequences (`<+`, `List.Sublist`) seen so far, plus an absorbing dead state
`none`, entered when a freshly completed length-`k` subsequence is not permitted by the
grammar. Unlike the SL scanner, no boundary augmentation is needed — subsequences are blind
to position. Its **transition monoid** (`DFA.transitionMonoid`) is finite (`Finite α`) and
aperiodic: any subsequence of length `≤ k` selects `≤ k` symbols, so reading any word `vᵐ`
yields a profile that stabilises for `m ≥ k - 1` (a new short subsequence needs a fresh
`v`-symbol, bounding the copies). Recognition relates "alive after reading `w`" to "every
length-`k` subsequence of `w` is permitted".

`[Finite α]` is essential: SP over an infinite alphabet need not even be regular.

## Main results

* `Language.IsStrictlyPiecewise.isStarFree` — `IsStrictlyPiecewise L k → IsStarFree L`
  (finite `α`).
-/

open List

namespace Subregular

variable {α : Type*}

/-- A bounded subsequence: a list of length `≤ n`, the unit a scanner profile is built from. -/
abbrev Sub (α : Type*) (n : ℕ) := { s : List α // s.length ≤ n }

instance [Finite α] (n : ℕ) : Finite (Sub α n) :=
  (List.finite_length_le α n).to_subtype

/-- A **subsequence profile**: the set of bounded subsequences seen so far. -/
abbrev Profile (α : Type*) (n : ℕ) := Set (Sub α n)

variable (G : SPGrammar α) (n : ℕ)

open Classical in
/-- Scanner step over profiles of subsequences up to length `n` (width `k = n+1`). Dead
`none` is absorbing; otherwise a forbidden length-`(n+1)` subsequence completes — some
length-`n` member extended by `a` is not in `G` — and we die, else we record every new
bounded subsequence ending in `a`. -/
private noncomputable def step : Option (Profile α n) → α → Option (Profile α n)
  | none, _ => none
  | some P, a =>
    if ∃ s ∈ P, s.val.length = n ∧ s.val ++ [a] ∉ G then none
    else some (P ∪ {t | ∃ s ∈ P, t.val = s.val ++ [a]})

open Classical in
/-- The scanner DFA (start/accept irrelevant: only its transition monoid is used). -/
private noncomputable def scanDFA : DFA α (Option (Profile α n)) where
  step := step G n
  start := none
  accept := ∅

@[simp] private lemma scanDFA_step (s : Option (Profile α n)) (a : α) :
    (scanDFA G n).step s a = step G n s a := rfl

/-- Dead is absorbing: once `none`, reading anything stays `none`. -/
@[simp] private lemma evalFrom_none (xs : List α) :
    (scanDFA G n).evalFrom none xs = none := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [DFA.evalFrom_cons]; simpa [step] using ih

/-- The canonical profile of a scanned word: all its bounded subsequences. -/
private def profOf (xs : List α) : Profile α n := {s | s.val <+ xs}

/-- One step of `profOf`: the bounded subsequences of `xs ++ [a]` are those of `xs` plus the
ones obtained by appending `a` to a (necessarily short enough) subsequence of `xs`. -/
private lemma profOf_step (xs : List α) (a : α) :
    profOf n (xs ++ [a]) = profOf n xs ∪ {t | ∃ s ∈ profOf n xs, t.val = s.val ++ [a]} := by
  ext t
  simp only [profOf, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro h
    obtain ⟨l₁, l₂, heq, h₁, h₂⟩ := List.sublist_append_iff.mp h
    rcases List.sublist_singleton.mp h₂ with hl₂ | hl₂
    · exact Or.inl (heq ▸ hl₂ ▸ by simpa using h₁)
    · exact Or.inr ⟨⟨l₁, by have := t.2; simp_all; omega⟩, h₁, by simp [heq, hl₂]⟩
  · rintro (h | ⟨s, hs, ht⟩)
    · exact h.trans (List.sublist_append_left _ _)
    · exact ht ▸ hs.append (List.Sublist.refl _)

/-- The **generalised profile** reached from a base profile `P` after reading `ys`: every base
subsequence extended by a subsequence of `ys`. With `P = profOf []` this is `profOf ys`; the
extra generality is what the transition monoid acts on. -/
private def genProf (P : Profile α n) (ys : List α) : Profile α n :=
  {t | ∃ p ∈ P, ∃ q, q <+ ys ∧ t.val = p.val ++ q}

@[simp] private lemma genProf_nil (P : Profile α n) : genProf n P [] = P := by
  ext t; simp only [genProf, Set.mem_setOf_eq]
  refine ⟨fun ⟨p, hp, q, hq, ht⟩ => ?_, fun h => ⟨t, h, [], List.nil_sublist _, by simp⟩⟩
  rw [List.sublist_nil.mp hq, List.append_nil] at ht
  rwa [show t = p from Subtype.ext ht]

/-- The base-profile step matches the scanner's `step` (alive case): reading `a` from `P`
records every `P`-element extended by `a`. -/
private lemma genProf_singleton (P : Profile α n) (a : α) :
    genProf n P [a] = P ∪ {t | ∃ s ∈ P, t.val = s.val ++ [a]} := by
  ext t
  simp only [genProf, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨p, hp, q, hq, ht⟩
    rcases List.sublist_singleton.mp hq with hq | hq
    · exact Or.inl (Subtype.ext (by simpa [hq] using ht) ▸ hp)
    · exact Or.inr ⟨p, hp, by simp [ht, hq]⟩
  · rintro (h | ⟨s, hs, ht⟩)
    · exact ⟨t, h, [], List.nil_sublist _, by simp⟩
    · exact ⟨s, hs, [a], List.Sublist.refl _, ht⟩

/-- `genProf` composes: extending by `xs` then `ys` equals extending by `xs ++ ys`. -/
private lemma genProf_append (P : Profile α n) (xs ys : List α) :
    genProf n (genProf n P xs) ys = genProf n P (xs ++ ys) := by
  ext t
  simp only [genProf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, ⟨p, hp, q, hq, hs⟩, r, hr, ht⟩
    exact ⟨p, hp, q ++ r, hq.append hr, by rw [ht, hs, List.append_assoc]⟩
  · rintro ⟨p, hp, q, hq, ht⟩
    obtain ⟨q₁, q₂, rfl, hq₁, hq₂⟩ := List.sublist_append_iff.mp hq
    exact ⟨⟨p.val ++ q₁, by have := t.2; simp_all; omega⟩, ⟨p, hp, q₁, hq₁, rfl⟩, q₂, hq₂,
      by simp [ht, List.append_assoc]⟩

/-- An alive run from any base profile lands in `genProf`: from `some P`, scanning `ys` either
dies or reaches `some (genProf P ys)`. -/
private lemma evalFrom_alive_genProf (P : Profile α n) (ys : List α) :
    ∀ Q, (scanDFA G n).evalFrom (some P) ys = some Q → Q = genProf n P ys := by
  induction ys generalizing P with
  | nil => rintro Q h; simpa using h.symm
  | cons a ys ih =>
    intro Q h
    rw [DFA.evalFrom_cons] at h
    simp only [scanDFA_step, step] at h
    split at h
    · simp only [evalFrom_none] at h; exact absurd h (by simp)
    · rw [← genProf_singleton] at h
      rw [ih _ _ h, genProf_append, List.singleton_append]

/-- A forbidden completed subsequence of `S`: some length-`(n+1)` subsequence is not in `G`. -/
private def Bad (S : List α) : Prop := ∃ f, f <+ S ∧ f.length = n + 1 ∧ f ∉ G

/-- A forbidden length-`(n+1)` subsequence of `xs ++ [a]` not already in `xs` must end in
`a`: it splits as `f₀ ++ [a]` with `f₀ <+ xs` of length `n`. -/
private lemma bad_snoc (xs : List α) (a : α) {f : List α} (hsub : f <+ xs ++ [a])
    (hnot : ¬ f <+ xs) (hlen : f.length = n + 1) :
    ∃ f₀ : Sub α n, f₀.val <+ xs ∧ f₀.val.length = n ∧ f₀.val ++ [a] = f := by
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp hsub
  rcases List.sublist_singleton.mp h₂ with hl₂ | hl₂
  · exact absurd (hl₂ ▸ by simpa using h₁) hnot
  · subst hl₂
    have : l₁.length = n := by simpa using hlen
    exact ⟨⟨l₁, this.le⟩, h₁, this, rfl⟩

/-- Dead-status (`xs` already clean): scanning `ys` from `profOf xs` dies iff some forbidden
length-`(n+1)` subsequence of `xs ++ ys` completes during `ys` — i.e. iff one exists at all,
since `¬ Bad xs` rules out the prefix-only case. -/
private lemma evalFrom_eq_none_iff (xs ys : List α) (hxs : ¬ Bad G n xs) :
    (scanDFA G n).evalFrom (some (profOf n xs)) ys = none ↔ Bad G n (xs ++ ys) := by
  induction ys generalizing xs with
  | nil => simpa using hxs
  | cons a ys ih =>
    rw [DFA.evalFrom_cons]
    simp only [scanDFA_step, step]
    split
    · rename_i hdie
      obtain ⟨s, hs, hlen, hbad⟩ := hdie
      simp only [evalFrom_none, true_iff]
      refine ⟨s.val ++ [a], ?_, by simp [hlen], hbad⟩
      exact hs.append (List.singleton_sublist.mpr (List.mem_cons_self ..))
    · rename_i halive
      have hxsa : ¬ Bad G n (xs ++ [a]) := by
        rintro ⟨f, hf, hlen, hg⟩
        obtain ⟨f₀, hf₀sub, hf₀, rfl⟩ := bad_snoc n xs a hf (fun hc => hxs ⟨f, hc, hlen, hg⟩) hlen
        exact halive ⟨f₀, by simpa [profOf] using hf₀sub, hf₀, hg⟩
      rw [← profOf_step, ih (xs ++ [a]) hxsa, List.append_assoc, List.singleton_append]

/-! ### Aperiodicity of the transition monoid

Any subsequence of length `≤ n` selects `≤ n` symbols, so reading `v` more than `n` times
beyond an already-`v`-saturated profile adds nothing new and never completes a fresh forbidden
subsequence: the transition monoid satisfies `x ^ (n+1) = x ^ n`. -/

/-- The list `v` concatenated `m` times. -/
private abbrev rep (v : List α) (m : ℕ) : List α := (List.replicate m v).flatten

private lemma rep_succ (v : List α) (m : ℕ) : rep v (m + 1) = rep v m ++ v := by
  rw [rep, replicate_succ', flatten_append]; simp [rep]

private lemma rep_succ_left (v : List α) (m : ℕ) : rep v (m + 1) = v ++ rep v m := by
  rw [rep, replicate_succ, flatten_cons]

private lemma toList_pow (v : FreeMonoid α) (m : ℕ) : (v ^ m).toList = rep v.toList m := by
  induction m with
  | zero => simp [rep]
  | succ k ih => rw [pow_succ, FreeMonoid.toList_mul, ih, rep_succ]

/-- **Block-pigeonhole keystone.** A subsequence of `rep v (m+1)` no longer than `m` is already
a subsequence of `rep v m`: spread over `m+1` identical copies it cannot touch them all, so one
copy can be dropped. Induction on `m`, peeling a leading copy. -/
private lemma sublist_rep_of_length_le (v : List α) :
    ∀ (m : ℕ) (f : List α), f.length ≤ m → f <+ rep v (m + 1) → f <+ rep v m := by
  intro m
  induction m with
  | zero => intro f hf _; rw [Nat.le_zero, List.length_eq_zero_iff] at hf; simp [hf]
  | succ m ih =>
    intro f hf h
    rw [rep_succ_left] at h
    obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := List.sublist_append_iff.mp h
    rcases eq_or_ne g₁ [] with hg | hg
    · simpa [hg] using hg₂
    · have : g₂.length ≤ m := by
        have : 1 ≤ g₁.length := List.length_pos_iff.mpr hg
        simp only [List.length_append] at hf; omega
      rw [rep_succ_left]
      exact hg₁.append (ih g₂ this hg₂)

/-- **Profile stabilisation.** Once `n ≤ m`, the generalised profile after `rep v (m+1)` equals
that after `rep v m`: each profile element selects `≤ n ≤ m` of the available copies, so one
copy is redundant. -/
private lemma genProf_rep_stable (P : Profile α n) (v : List α) {m : ℕ} (hm : n ≤ m) :
    genProf n P (rep v (m + 1)) = genProf n P (rep v m) := by
  ext t
  simp only [genProf, Set.mem_setOf_eq]
  refine ⟨fun ⟨p, hp, q, hq, ht⟩ => ⟨p, hp, q, ?_, ht⟩,
    fun ⟨p, hp, q, hq, ht⟩ => ⟨p, hp, q, hq.trans (rep_succ v m ▸ sublist_append_left _ _), ht⟩⟩
  exact sublist_rep_of_length_le v m q (by have := t.2; simp_all; omega) hq

/-- Reading `v` from `evalFrom s (rep v (n+1))` is a fixed point: the profile is already
`v`-saturated (stabilisation at exponent `n`) and the dead flag is monotone. Mirrors the SL
window-fixed-point argument. -/
private lemma evalFrom_rep_fixed (s : Option (Profile α n)) (v : List α) :
    (scanDFA G n).evalFrom ((scanDFA G n).evalFrom s (rep v (n + 1))) v
      = (scanDFA G n).evalFrom s (rep v (n + 1)) := by
  rcases s with _ | P
  · simp [evalFrom_none]
  have hrec : (scanDFA G n).evalFrom (some P) (rep v (n + 1))
      = (scanDFA G n).evalFrom ((scanDFA G n).evalFrom (some P) (rep v n)) v := by
    rw [← DFA.evalFrom_of_append, ← rep_succ]
  rw [hrec]
  rcases hA : (scanDFA G n).evalFrom (some P) (rep v n) with _ | wA
  · simp [evalFrom_none]
  rcases hB : (scanDFA G n).evalFrom (some wA) v with _ | wB
  · simp [evalFrom_none]
  have hwA : wA = genProf n P (rep v n) := evalFrom_alive_genProf G n P (rep v n) wA hA
  have hwB : wB = genProf n P (rep v (n + 1)) :=
    evalFrom_alive_genProf G n P (rep v (n + 1)) wB (by rw [hrec, hA, hB])
  have hBA : some wB = some wA := by
    rw [hwA, hwB, genProf_rep_stable n P v (le_refl n)]
  rw [hBA, hB, hBA]

/-- The scanner transition action stabilises at exponent `n + 1`. -/
private lemma transitionHom_pow_stabilizes (v : FreeMonoid α) :
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

/-- The transition action corestricted to the transition monoid. -/
private noncomputable def scanHom : FreeMonoid α →* (scanDFA G n).transitionMonoid :=
  (scanDFA G n).transitionHom.codRestrict _ (fun _ => ⟨_, rfl⟩)

@[simp] private lemma scanHom_unop_apply (w : List α) (s : Option (Profile α n)) :
    ((scanHom G n (FreeMonoid.ofList w)).val.unop) s = (scanDFA G n).evalFrom s w := by
  simp only [scanHom, MonoidHom.codRestrict_apply, DFA.unop_transitionHom_apply,
    FreeMonoid.toList_ofList]

/-- The empty word has no length-`(n+1)` subsequence, so the start profile is clean. -/
private lemma not_bad_nil : ¬ Bad G n [] := by
  rintro ⟨f, hf, hlen, _⟩; simp_all

/-- The scanner run over `w` from the start profile is alive iff `w` lies in the language
generated by `G` at width `n+1` — every length-`(n+1)` subsequence of `w` is permitted. -/
private lemma alive_iff_mem_language (w : List α) :
    (scanDFA G n).evalFrom (some (profOf n [])) w ≠ none ↔ w ∈ G.language (n + 1) := by
  rw [Ne, evalFrom_eq_none_iff G n [] w (not_bad_nil G n), List.nil_append, SPGrammar.mem_language]
  simp only [Bad, not_exists, not_and, not_not]
  exact ⟨fun h f hlen hf => h f hf hlen, fun h f hf hlen => h f hlen hf⟩

/-- A strictly-`(n+1)`-piecewise language is star-free: the scanner's transition monoid is a
finite aperiodic recognizer ([heinz-rogers-2010] [mcnaughton-papert-1971]). -/
private theorem isStarFree_of_language_succ (L : Language α) [Finite α]
    (hL : G.language (n + 1) = L) : L.IsStarFree := by
  classical
  refine Language.IsStarFree.of_recognizes (isAperiodic_transitionMonoid G n) (scanHom G n)
    {g | (g.val.unop (some (profOf n []))) ≠ none} (fun w => ?_)
  rw [← hL, Set.mem_setOf_eq, scanHom_unop_apply, alive_iff_mem_language]

end Subregular

namespace Language

variable {α : Type*} [Finite α]

open Subregular

/-- **Strictly piecewise languages are star-free** ([heinz-rogers-2010]
[mcnaughton-papert-1971]). Over a finite alphabet, the subsequence scanner remembering the
length-`≤ k-1` subsequences seen so far is a finite aperiodic recognizer, so `SP_k ⊆ SF`.
(`[Finite α]` is essential: SP over an infinite alphabet need not even be regular.) -/
theorem IsStrictlyPiecewise.isStarFree {L : Language α} {k : ℕ} (h : L.IsStrictlyPiecewise k) :
    L.IsStarFree := by
  classical
  obtain ⟨G, hG⟩ := h
  rcases k with _ | n
  · -- `k = 0`: membership is the constant `[] ∈ G`, recognized by the trivial monoid.
    refine Language.IsStarFree.of_recognizes (M := PUnit.{1}) Monoid.IsAperiodic.of_subsingleton 1
      (if ([] : List α) ∈ G then Set.univ else ∅) (fun w => ?_)
    rw [← hG, SPGrammar.mem_language]
    by_cases hg : ([] : List α) ∈ G
    · simp only [hg, if_pos, Set.mem_univ, iff_true]
      exact fun s (hs : s.length = 0) _ => List.length_eq_zero_iff.mp hs ▸ hg
    · simp only [hg, if_neg, not_false_iff, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨[], rfl, List.nil_sublist _, hg⟩
  · exact isStarFree_of_language_succ G n L hG

end Language
