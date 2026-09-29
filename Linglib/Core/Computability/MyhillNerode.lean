/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Linglib.Core.Computability.Mealy
public import Linglib.Core.Computability.Bimachine

/-!
# Myhill–Nerode theorems for transducers

This file characterizes the Mealy-computable (sequential) and bimachine-computable
functions by their residuals, in the style of `Mathlib.Computability.MyhillNerode`
(which treats the language case).

Given `f : List α → List β` and a word `u`, the *residual* of `f` by `u` is the
function `v ↦ (f (u ++ v)).drop (f u).length` — what `f` appends after reading `u`, the
`f(u)⁻¹f(uv)` of sequential functions — and the *coresidual* of `f` by a suffix `y` is
`u ↦ (f (u ++ y)).take u.length` — what `f` emits before reaching `y`. A function is
Mealy-computable if and only if it is length-preserving, prefix-preserving, and has finitely
many residuals — the Nerode criterion for sequential functions ([eilenberg-1974]
[holcombe-1982]). A function is bimachine-computable if and only if it is length-preserving
with finitely many residuals and finitely many coresiduals: residual classes are the left
states, coresidual classes the right states, and the two-step exchange through
representatives makes the cell output well-defined — the length-preserving stratum of the
canonical bimachine of [reutenauer-schutzenberger-1991], surveyed in [filiot-reynier-2016].
A function built block by block from a summary of its input has residuals that factor through
the summary, and conversely; the strictly local function classes are the instances with a
bounded window as the summary.

## Main definitions

* `residual f u`: the residual of `f` by the word `u`
* `coresidual f y`: the coresidual of `f` by the suffix `y`

## Main theorems

* `factorsThrough_residual_of_append_singleton`,
  `exists_append_singleton_of_factorsThrough_residual`: residuals factor through a summary `W`
  exactly when `f` extends by blocks read off `W`
* `isMealyComputable_of_stateSummary`: a finite left-congruent state summary
  determining the output yields a machine
* `isMealyComputable_iff_residual`: `f` is Mealy-computable if and only if it is
  length-preserving, prefix-preserving, and `Set.range (residual f)` is finite
* `isLengthPreservingBimachineComputable_iff_residual`: `f` is bimachine-computable if and
  only if it is length-preserving and both `Set.range (residual f)` and
  `Set.range (coresidual f)` are finite

[UPSTREAM] candidate: `Mathlib.Computability.MyhillNerode` (as transducer sections of
the existing file, with `residual` beside `Language.leftQuotient`).
-/

@[expose] public section

variable {α β : Type*} (f : List α → List β)

/-- The *residual* of `f` by `u` is what `f` appends after reading `u` — the analogue
for string functions of `Language.leftQuotient`. -/
def residual (u : List α) : List α → List β :=
  fun v => (f (u ++ v)).drop (f u).length

variable {f}

theorem residual_nil (h : f [] = []) : residual f [] = f := by
  funext v; simp [residual, h]

/-- A prefix-preserving `f` extends its output on `u` by the residual. -/
theorem append_residual {u v : List α} (h : f u <+: f (u ++ v)) :
    f u ++ residual f u v = f (u ++ v) := by
  obtain ⟨t, ht⟩ := h
  simp [residual, ← ht]

theorem residual_append_singleton (hlen : ∀ xs, (f xs).length = xs.length) (u : List α)
    (x : α) : residual f (u ++ [x]) = fun v => (residual f u (x :: v)).drop 1 := by
  funext v; simp [residual, hlen]

/-! ### Residuals through a state summary

A function that extends its output by one block per letter, the block read off a summary `W`
of the input whose update is determined, has residuals that factor through `W`; conversely a
prefix-preserving function whose residuals factor through `W` extends by blocks read off `W`.
The strictly local function classes are the instances with `W` a bounded window. -/

section StateSummary

variable {γ : Type*} {W : List α → γ}

/-- A function extending its output at every letter is prefix-preserving. -/
theorem isPrefix_append_of_append_singleton (hf : ∀ u x, f u <+: f (u ++ [x])) (u v : List α) :
    f u <+: f (u ++ v) := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v x ih => exact ih.trans (List.append_assoc u v [x] ▸ hf (u ++ v) x)

/-- Residuals of a function built block by block from a state summary factor through it. -/
theorem factorsThrough_residual_of_append_singleton (δ : γ → α → γ) (g : γ → α → List β)
    (hW : ∀ u x, W (u ++ [x]) = δ (W u) x) (hf : ∀ u x, f (u ++ [x]) = f u ++ g (W u) x) :
    (residual f).FactorsThrough W := by
  have hpre := isPrefix_append_of_append_singleton fun u x => ⟨_, (hf u x).symm⟩
  intro u₁ u₂ h
  funext v
  induction v using List.reverseRecOn with
  | nil => simp [residual]
  | append_singleton v x ih =>
    have hWv : W (u₁ ++ v) = W (u₂ ++ v) := by
      clear ih
      induction v using List.reverseRecOn with
      | nil => simpa using h
      | append_singleton v y ihv => rw [← List.append_assoc, hW, ihv, ← hW, List.append_assoc]
    simp only [residual] at ih ⊢
    rw [← List.append_assoc, hf, List.drop_append_of_le_length (hpre u₁ v).length_le, ih,
      ← List.append_assoc, hf, List.drop_append_of_le_length (hpre u₂ v).length_le, hWv]

/-- A prefix-preserving function whose residuals factor through `W` extends by blocks read
off `W`. -/
theorem exists_append_singleton_of_factorsThrough_residual
    (hpre : ∀ u v, f u <+: f (u ++ v)) (hW : (residual f).FactorsThrough W) :
    ∃ g : γ → α → List β, ∀ u x, f (u ++ [x]) = f u ++ g (W u) x :=
  ⟨fun c x => Function.extend W (residual f) (fun _ _ => []) c [x], fun u x => by
    dsimp only
    rw [hW.extend_apply, append_residual (hpre u [x])]⟩

end StateSummary

variable (f)

/-- Residuals of a machine's run factor through its states. -/
theorem Mealy.residual_run {σ : Type*} (T : Mealy σ α β) (u : List α) :
    residual T.run u = T.runFrom (T.stateAfter T.start u) := by
  funext v
  simp only [residual, Mealy.run, Mealy.runFrom_append, List.drop_left]

/-! ### Necessity -/

theorem IsMealyComputable.length_eq {f : List α → List β} (hf : IsMealyComputable f)
    (xs : List α) : (f xs).length = xs.length := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.length_run xs

theorem IsMealyComputable.isPrefix {f : List α → List β} (hf : IsMealyComputable f)
    (u v : List α) : f u <+: f (u ++ v) := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact ⟨_, (T.runFrom_append T.start u v).symm⟩

theorem IsMealyComputable.finite_range_residual {f : List α → List β}
    (hf : IsMealyComputable f) : (Set.range (residual f)).Finite := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact Set.Finite.subset (Set.finite_range T.runFrom)
    (Set.range_subset_iff.mpr fun u => ⟨_, (T.residual_run u).symm⟩)

/-! ### Sufficiency -/

/-- A length-preserving `f` with a finite `state : List α → σ` that is left-congruent
(`hδ`) and determines `f`'s output at each position (`hout`) is Mealy-computable. -/
theorem isMealyComputable_of_stateSummary
    {f : List α → List β} {σ : Type*} [Fintype σ]
    (state : List α → σ) (δ : σ → α → σ) (out : σ → α → β)
    (hδ : ∀ u x, state (u ++ [x]) = δ (state u) x)
    (hout : ∀ u x w, (f (u ++ x :: w))[u.length]? = some (out (state u) x))
    (hlen : ∀ xs, (f xs).length = xs.length) :
    IsMealyComputable f := by
  refine isMealyComputable_iff.mpr ⟨σ, inferInstance, ⟨state [], δ, out⟩, ?_⟩
  set T : Mealy σ α β := ⟨state [], δ, out⟩
  have hstate : ∀ ps : List α, T.stateAfter T.start ps = state ps := by
    intro ps
    induction ps using List.reverseRecOn with
    | nil => rfl
    | append_singleton ps x ih => rw [T.stateAfter_append, ih, hδ]; rfl
  funext xs
  apply List.ext_getElem?
  intro i
  rw [T.getElem?_run xs i, hstate]
  rcases lt_or_ge i xs.length with hi | hi
  · have key := hout (xs.take i) xs[i] (xs.drop (i + 1))
    rw [List.length_take_of_le hi.le, ← List.drop_eq_getElem_cons hi,
      List.take_append_drop] at key
    rw [List.getElem?_eq_getElem hi, Option.map_some, key]
  · rw [List.getElem?_eq_none hi, List.getElem?_eq_none ((hlen xs).le.trans hi),
      Option.map_none]

/-- A length-preserving, prefix-preserving function with finitely many residuals is
Mealy-computable, with the residuals themselves as the states. -/
theorem isMealyComputable_of_residual {f : List α → List β}
    (hlen : ∀ xs, (f xs).length = xs.length)
    (hpre : ∀ u v, f u <+: f (u ++ v))
    (hfin : (Set.range (residual f)).Finite) :
    IsMealyComputable f := by
  have := Set.Finite.fintype hfin
  have hne : ∀ (r : Set.range (residual f)) (x : α), r.val [x] ≠ [] := by
    rintro ⟨_, u, rfl⟩ x
    exact List.ne_nil_of_length_pos (by simp [residual, hlen])
  refine isMealyComputable_of_stateSummary
    (fun u => ⟨residual f u, Set.mem_range_self u⟩)
    (fun r x => ⟨fun v => (r.val (x :: v)).drop 1, by
      obtain ⟨u, hu⟩ := r.prop
      exact ⟨u ++ [x], by rw [residual_append_singleton hlen, hu]⟩⟩)
    (fun r x => (r.val [x]).head (hne r x))
    (fun u x => Subtype.ext (residual_append_singleton hlen u x))
    (fun u x w => ?_) hlen
  obtain ⟨t, ht⟩ := hpre (u ++ [x]) w
  rw [List.append_assoc, List.singleton_append] at ht
  rw [← ht, List.getElem?_append_left (by rw [hlen]; simp), ← List.head?_drop, ← hlen u,
    show (f (u ++ [x])).drop (f u).length = residual f u [x] from rfl,
    List.head?_eq_some_head]

/-- **Myhill–Nerode for Mealy machines.** A function is Mealy-computable if and only
if it is length-preserving, prefix-preserving, and has finitely many residuals. -/
theorem isMealyComputable_iff_residual {f : List α → List β} :
    IsMealyComputable f
      ↔ (∀ xs, (f xs).length = xs.length) ∧ (∀ u v, f u <+: f (u ++ v))
        ∧ (Set.range (residual f)).Finite :=
  ⟨fun hf => ⟨hf.length_eq, hf.isPrefix, hf.finite_range_residual⟩,
   fun h => isMealyComputable_of_residual h.1 h.2.1 h.2.2⟩

/-! ### Coresiduals -/

/-- The *coresidual* of `f` by the suffix `y` is what `f` emits before reaching `y` —
the right-context dual of `residual`. -/
def coresidual (y : List α) : List α → List β :=
  fun u => (f (u ++ y)).take u.length

/-- Coresiduals step by prepending a letter — the right-to-left congruence. -/
theorem coresidual_cons (x : α) (y : List α) :
    coresidual f (x :: y) = fun u => (coresidual f y (u ++ [x])).take u.length := by
  funext u
  simp only [coresidual, List.take_take, List.length_append, List.length_cons,
    List.length_nil, List.append_assoc, List.singleton_append]
  rw [Nat.min_eq_left (Nat.le_succ _)]

/-- The cell at the seam, read through the residual. -/
theorem getElem?_residual_cons (u : List α) (x : α) (w : List α) :
    (residual f u (x :: w))[0]? = (f (u ++ x :: w))[(f u).length]? := by
  simp [residual, List.getElem?_drop]

/-- The cell at the seam, read through the coresidual. -/
theorem getElem?_coresidual_append (u : List α) (x : α) (w : List α) :
    (coresidual f w (u ++ [x]))[u.length]? = (f (u ++ x :: w))[u.length]? := by
  simp only [coresidual, List.length_append, List.length_cons, List.length_nil,
    List.append_assoc, List.singleton_append]
  exact List.getElem?_take_of_lt (Nat.lt_succ_self _)

/-! ### Myhill–Nerode for bimachines -/

section Bimachine

variable {L R : Type*} (B : Bimachine L R α β)

/-- Scanning past a prefix reseeds the left state. -/
theorem Bimachine.lState_append (u v : List α) :
    B.lState (u ++ v) = B.lStateAfter (B.lState u) v := by
  simp [Bimachine.lState, Bimachine.lStateAfter, List.foldl_append]

/-- A pending suffix reseeds the right state. -/
theorem Bimachine.rState_append (u y : List α) :
    B.rState (u ++ y) = Bimachine.rState {B with rInit := B.rState y} u := by
  simp [Bimachine.rState, List.foldr_append]

/-- Dropping a scanned prefix of a letter-to-letter bimachine run reseeds the left
state. -/
theorem Bimachine.drop_runFrom_append (w : B.LetterToLetter) (l : L) (x v : List α) :
    (B.runFrom l (x ++ v)).drop x.length = B.runFrom (B.lStateAfter l x) v := by
  induction x generalizing l with
  | nil => rfl
  | cons a x ih => simpa [w.output_eq] using ih (B.lStep l a)

/-- Taking the unscanned prefix of a bimachine run reseeds the right state. -/
theorem Bimachine.take_runFrom_append (w : B.LetterToLetter) (l : L) (u y : List α) :
    (B.runFrom l (u ++ y)).take u.length
      = Bimachine.runFrom {B with rInit := B.rState y} l u := by
  induction u generalizing l with
  | nil => rfl
  | cons a u ih =>
    rw [List.cons_append, B.runFrom_cons, w.output_eq, List.singleton_append,
      List.length_cons, List.take_succ_cons, ih (B.lStep l a), B.rState_append u y]
    simp [w.output_eq]

/-- Residuals of a bimachine's run reseed the left automaton. -/
theorem Bimachine.residual_run (w : B.LetterToLetter) (x : List α) :
    residual B.run x = B.runFrom (B.lState x) :=
  funext fun v => by
    simp only [residual, w.length_run]
    exact B.drop_runFrom_append w B.lInit x v

/-- Coresiduals of a bimachine's run reseed the right automaton. -/
theorem Bimachine.coresidual_run (w : B.LetterToLetter) (y : List α) :
    coresidual B.run y = Bimachine.run {B with rInit := B.rState y} :=
  funext fun u => B.take_runFrom_append w B.lInit u y

/-! ### Necessity -/

theorem IsLengthPreservingBimachineComputable.finite_range_residual {f : List α → List β}
    (hf : IsLengthPreservingBimachineComputable f) : (Set.range (residual f)).Finite := by
  obtain ⟨L, _, R, _, B, ⟨w⟩, rfl⟩ := hf
  exact Set.Finite.subset (Set.finite_range B.runFrom)
    (Set.range_subset_iff.mpr fun x => ⟨_, (B.residual_run w x).symm⟩)

theorem IsLengthPreservingBimachineComputable.finite_range_coresidual {f : List α → List β}
    (hf : IsLengthPreservingBimachineComputable f) : (Set.range (coresidual f)).Finite := by
  obtain ⟨L, _, R, _, B, ⟨w⟩, rfl⟩ := hf
  exact Set.Finite.subset (Set.finite_range fun r : R => Bimachine.run {B with rInit := r})
    (Set.range_subset_iff.mpr fun y => ⟨B.rState y, (B.coresidual_run w y).symm⟩)

/-! ### Sufficiency -/

/-- A length-preserving `f` with finite left and right summaries, congruent in their
respective scan directions and jointly determining each output cell, is
bimachine-computable. -/
theorem isLengthPreservingBimachineComputable_of_stateSummaries
    {f : List α → List β} {L R : Type*} [Fintype L] [Fintype R]
    (stateL : List α → L) (δL : L → α → L) (stateR : List α → R) (δR : R → α → R)
    (out : L → α → R → β)
    (hδL : ∀ u x, stateL (u ++ [x]) = δL (stateL u) x)
    (hδR : ∀ x w, stateR (x :: w) = δR (stateR w) x)
    (hout : ∀ u x w, (f (u ++ x :: w))[u.length]? = some (out (stateL u) x (stateR w)))
    (hlen : ∀ xs, (f xs).length = xs.length) :
    IsLengthPreservingBimachineComputable f := by
  refine isLengthPreservingBimachineComputable_iff.mpr ⟨L, inferInstance, R, inferInstance,
    ⟨stateL [], δL, stateR [], δR, fun l a r => [out l a r]⟩, ⟨⟨out, fun _ _ _ => rfl⟩⟩, ?_⟩
  set B : Bimachine L R α β := ⟨stateL [], δL, stateR [], δR, fun l a r => [out l a r]⟩
  have hL : ∀ ps : List α, B.lState ps = stateL ps := by
    intro ps
    induction ps using List.reverseRecOn with
    | nil => rfl
    | append_singleton ps x ih =>
      rw [B.lState_append, hδL, ← ih]
      rfl
  have hR : ∀ ss : List α, B.rState ss = stateR ss := by
    intro ss
    induction ss with
    | nil => rfl
    | cons x ss ih => rw [B.rState_cons, ih, hδR]
  funext xs
  apply List.ext_getElem?
  intro i
  rw [(⟨out, fun _ _ _ => rfl⟩ : B.LetterToLetter).getElem?_run xs i]
  simp only [hL, hR]
  rcases lt_or_ge i xs.length with hi | hi
  · have key := hout (xs.take i) xs[i] (xs.drop (i + 1))
    rw [List.length_take_of_le hi.le, ← List.drop_eq_getElem_cons hi,
      List.take_append_drop] at key
    rw [List.getElem?_eq_getElem hi, Option.map_some, key]
  · rw [List.getElem?_eq_none hi, List.getElem?_eq_none ((hlen xs).le.trans hi),
      Option.map_none]

/-- A length-preserving function with finitely many residuals and coresiduals is
bimachine-computable, with residual classes as the left states and coresidual classes as the
right states, and with the cell output read off representatives, which is well-defined by
exchanging one context at a time. -/
theorem isLengthPreservingBimachineComputable_of_residual {f : List α → List β}
    (hlen : ∀ xs, (f xs).length = xs.length)
    (hfinL : (Set.range (residual f)).Finite)
    (hfinR : (Set.range (coresidual f)).Finite) :
    IsLengthPreservingBimachineComputable f := by
  have := hfinL.fintype
  have := hfinR.fintype
  choose repL hrepL using fun r : Set.range (residual f) => r.prop
  choose repR hrepR using fun s : Set.range (coresidual f) => s.prop
  refine isLengthPreservingBimachineComputable_of_stateSummaries
    (fun u => ⟨residual f u, Set.mem_range_self u⟩)
    (fun r x => ⟨fun v => (r.val (x :: v)).drop 1, by
      obtain ⟨u, hu⟩ := r.prop
      exact ⟨u ++ [x], by rw [residual_append_singleton hlen, hu]⟩⟩)
    (fun w => ⟨coresidual f w, Set.mem_range_self w⟩)
    (fun s x => ⟨fun u => (s.val (u ++ [x])).take u.length, by
      obtain ⟨w, hw⟩ := s.prop
      exact ⟨x :: w, by rw [coresidual_cons, hw]⟩⟩)
    (fun r x s => (f (repL r ++ x :: repR s))[(repL r).length]'(by
      rw [hlen]
      simp))
    (fun u x => Subtype.ext (residual_append_singleton hlen u x))
    (fun x w => Subtype.ext (coresidual_cons f x w))
    (fun u x w => ?_) hlen
  set r : Set.range (residual f) := ⟨residual f u, Set.mem_range_self u⟩
  set s : Set.range (coresidual f) := ⟨coresidual f w, Set.mem_range_self w⟩
  have hres : residual f (repL r) = residual f u := hrepL r
  have hcores : coresidual f (repR s) = coresidual f w := hrepR s
  calc (f (u ++ x :: w))[u.length]?
      = (residual f u (x :: w))[0]? := by rw [getElem?_residual_cons, hlen]
    _ = (residual f (repL r) (x :: w))[0]? := by rw [hres]
    _ = (f (repL r ++ x :: w))[(repL r).length]? := by rw [getElem?_residual_cons, hlen]
    _ = (coresidual f w (repL r ++ [x]))[(repL r).length]? :=
        (getElem?_coresidual_append f _ x w).symm
    _ = (coresidual f (repR s) (repL r ++ [x]))[(repL r).length]? := by rw [hcores]
    _ = (f (repL r ++ x :: repR s))[(repL r).length]? := getElem?_coresidual_append f _ x _
    _ = some ((f (repL r ++ x :: repR s))[(repL r).length]'(by rw [hlen]; simp)) :=
        List.getElem?_eq_getElem _

end Bimachine

/-- **Myhill–Nerode for bimachines.** A function is bimachine-computable if and only
if it is length-preserving with finitely many residuals and finitely many
coresiduals. -/
theorem isLengthPreservingBimachineComputable_iff_residual {f : List α → List β} :
    IsLengthPreservingBimachineComputable f
      ↔ (∀ xs, (f xs).length = xs.length) ∧ (Set.range (residual f)).Finite
        ∧ (Set.range (coresidual f)).Finite :=
  ⟨fun hf => ⟨hf.length_eq, hf.finite_range_residual, hf.finite_range_coresidual⟩,
   fun h => isLengthPreservingBimachineComputable_of_residual h.1 h.2.1 h.2.2⟩

