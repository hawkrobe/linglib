/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Linglib.Core.Computability.Mealy
import Linglib.Core.Computability.Bimachine

/-!
# Myhill–Nerode theorems for transducers

This file characterizes the Mealy-computable (sequential) and bimachine-computable
functions by their residuals, in the style of `Mathlib.Computability.MyhillNerode`
(which treats the language case).

Given `f : List α → List β` and a word `u`, the *residual* of `f` by `u` is the
function `v ↦ (f (u ++ v)).drop u.length` — what `f` appends after reading `u` — and
the *coresidual* of `f` by a suffix `y` is `u ↦ (f (u ++ y)).take u.length` — what `f`
emits before reaching `y`. A function is Mealy-computable if and only if it is
length-preserving, prefix-preserving, and has finitely many residuals — the
Myhill–Nerode argument for the minimal sequential machine of [holcombe-1982]. A
function is bimachine-computable if and only if it is length-preserving with finitely
many residuals and finitely many coresiduals: residual classes are the left states,
coresidual classes the right states, and the two-step exchange through representatives
makes the cell output well-defined — the canonical bimachine of [eilenberg-1974].

## Main definitions

* `residual f u`: the residual of `f` by the word `u`
* `coresidual f y`: the coresidual of `f` by the suffix `y`

## Main theorems

* `isMealyComputable_of_stateSummary`: a finite left-congruent state summary
  determining the output yields a machine
* `isMealyComputable_iff_residual`: `f` is Mealy-computable if and only if it is
  length-preserving, prefix-preserving, and `Set.range (residual f)` is finite
* `isBimachineComputable_iff_residual`: `f` is bimachine-computable if and only if it
  is length-preserving and both `Set.range (residual f)` and
  `Set.range (coresidual f)` are finite

[UPSTREAM] candidate: `Mathlib.Computability.MyhillNerode` (as transducer sections of
the existing file, with `residual` beside `Language.leftQuotient`).
-/

namespace Subregular

variable {α β : Type*} (f : List α → List β)

/-- The *residual* of `f` by `u` is what `f` appends after reading `u` — the analogue
for string functions of `Language.leftQuotient`. -/
def residual (u : List α) : List α → List β :=
  fun v => (f (u ++ v)).drop u.length

@[simp] theorem residual_nil : residual f [] = f := by
  funext v; simp [residual]

theorem residual_append (u v : List α) :
    residual f (u ++ v) = residual (residual f u) v := by
  funext w; simp [residual]

theorem residual_append_singleton (u : List α) (x : α) :
    residual f (u ++ [x]) = fun v => (residual f u (x :: v)).drop 1 := by
  funext v; simp [residual]

/-- Residuals of a machine's run factor through its states. -/
theorem Mealy.residual_run {σ : Type*} (T : Mealy σ α β) (u : List α) :
    residual T.run u = T.runFrom (T.stateAfter T.initial u) := by
  funext v
  simp only [residual, Mealy.run, Mealy.runFrom_append]
  rw [show u.length = (T.runFrom T.initial u).length from (T.length_runFrom _ _).symm,
    List.drop_left]

/-! ### Necessity -/

theorem IsMealyComputable.length_eq {f : List α → List β} (hf : IsMealyComputable f)
    (xs : List α) : (f xs).length = xs.length := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.length_run xs

theorem IsMealyComputable.isPrefix {f : List α → List β} (hf : IsMealyComputable f)
    (u v : List α) : f u <+: f (u ++ v) := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact ⟨_, (T.runFrom_append T.initial u v).symm⟩

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
  have hstate : ∀ ps : List α, T.stateAfter T.initial ps = state ps := by
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

/-- The identity is Mealy-computable, via a one-state summary. -/
theorem isMealyComputable_id : IsMealyComputable (id : List α → List α) :=
  isMealyComputable_of_stateSummary
    (fun _ => ()) (fun _ _ => ()) (fun _ x => x)
    (fun _ _ => rfl) (fun _ _ _ => by simp) (fun _ => rfl)

/-- A length-preserving, prefix-preserving function with finitely many residuals is
Mealy-computable: the residuals themselves are the states. -/
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
      exact ⟨u ++ [x], by rw [residual_append_singleton, hu]⟩⟩)
    (fun r x => (r.val [x]).head (hne r x))
    (fun u x => Subtype.ext (residual_append_singleton f u x))
    (fun u x w => ?_) hlen
  obtain ⟨t, ht⟩ := hpre (u ++ [x]) w
  rw [List.append_assoc, List.singleton_append] at ht
  rw [← ht, List.getElem?_append_left (by rw [hlen]; simp), ← List.head?_drop,
    show (f (u ++ [x])).drop u.length = residual f u [x] from rfl,
    List.head?_eq_some_head]

/-- **Myhill–Nerode for Mealy machines**: a function is Mealy-computable if and only
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
    (residual f u (x :: w))[0]? = (f (u ++ x :: w))[u.length]? := by
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

/-- Dropping a scanned prefix of a bimachine run reseeds the left state. -/
theorem Bimachine.drop_runFrom_append (l : L) (x v : List α) :
    (B.runFrom l (x ++ v)).drop x.length = B.runFrom (B.lStateAfter l x) v := by
  induction x generalizing l with
  | nil => rfl
  | cons a x ih => simpa using ih (B.lStep l a)

/-- Taking the unscanned prefix of a bimachine run reseeds the right state. -/
theorem Bimachine.take_runFrom_append (l : L) (u y : List α) :
    (B.runFrom l (u ++ y)).take u.length
      = Bimachine.runFrom {B with rInit := B.rState y} l u := by
  induction u generalizing l with
  | nil => rfl
  | cons a u ih =>
    show B.output l a (B.rState (u ++ y))
        :: (B.runFrom (B.lStep l a) (u ++ y)).take u.length = _
    rw [ih (B.lStep l a), B.rState_append u y]
    rfl

/-- Residuals of a bimachine's run reseed the left automaton. -/
theorem Bimachine.residual_run (x : List α) :
    residual B.run x = B.runFrom (B.lState x) :=
  funext fun v => B.drop_runFrom_append B.lInit x v

/-- Coresiduals of a bimachine's run reseed the right automaton. -/
theorem Bimachine.coresidual_run (y : List α) :
    coresidual B.run y = Bimachine.run {B with rInit := B.rState y} :=
  funext fun u => B.take_runFrom_append B.lInit u y

/-! ### Necessity -/

theorem IsBimachineComputable.finite_range_residual {f : List α → List β}
    (hf : IsBimachineComputable f) : (Set.range (residual f)).Finite := by
  obtain ⟨L, _, R, _, B, rfl⟩ := hf
  exact Set.Finite.subset (Set.finite_range B.runFrom)
    (Set.range_subset_iff.mpr fun x => ⟨_, (B.residual_run x).symm⟩)

theorem IsBimachineComputable.finite_range_coresidual {f : List α → List β}
    (hf : IsBimachineComputable f) : (Set.range (coresidual f)).Finite := by
  obtain ⟨L, _, R, _, B, rfl⟩ := hf
  exact Set.Finite.subset (Set.finite_range fun r : R => Bimachine.run {B with rInit := r})
    (Set.range_subset_iff.mpr fun y => ⟨B.rState y, (B.coresidual_run y).symm⟩)

/-! ### Sufficiency -/

/-- A length-preserving `f` with finite left and right summaries, congruent in their
respective scan directions and jointly determining each output cell, is
bimachine-computable. -/
theorem isBimachineComputable_of_stateSummaries
    {f : List α → List β} {L R : Type*} [Fintype L] [Fintype R]
    (stateL : List α → L) (δL : L → α → L) (stateR : List α → R) (δR : R → α → R)
    (out : L → α → R → β)
    (hδL : ∀ u x, stateL (u ++ [x]) = δL (stateL u) x)
    (hδR : ∀ x w, stateR (x :: w) = δR (stateR w) x)
    (hout : ∀ u x w, (f (u ++ x :: w))[u.length]? = some (out (stateL u) x (stateR w)))
    (hlen : ∀ xs, (f xs).length = xs.length) :
    IsBimachineComputable f := by
  refine isBimachineComputable_iff.mpr ⟨L, inferInstance, R, inferInstance,
    ⟨stateL [], δL, stateR [], δR, out⟩, ?_⟩
  set B : Bimachine L R α β := ⟨stateL [], δL, stateR [], δR, out⟩
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
  rw [B.getElem?_run xs i]
  simp only [hL, hR]
  rcases lt_or_ge i xs.length with hi | hi
  · have key := hout (xs.take i) xs[i] (xs.drop (i + 1))
    rw [List.length_take_of_le hi.le, ← List.drop_eq_getElem_cons hi,
      List.take_append_drop] at key
    rw [List.getElem?_eq_getElem hi, Option.map_some, key]
  · rw [List.getElem?_eq_none hi, List.getElem?_eq_none ((hlen xs).le.trans hi),
      Option.map_none]

/-- A length-preserving function with finitely many residuals and coresiduals is
bimachine-computable: residual classes are the left states, coresidual classes the
right states, and the cell output is read off representatives — well-defined by
exchanging one context at a time. -/
theorem isBimachineComputable_of_residual {f : List α → List β}
    (hlen : ∀ xs, (f xs).length = xs.length)
    (hfinL : (Set.range (residual f)).Finite)
    (hfinR : (Set.range (coresidual f)).Finite) :
    IsBimachineComputable f := by
  have := hfinL.fintype
  have := hfinR.fintype
  choose repL hrepL using fun r : Set.range (residual f) => r.prop
  choose repR hrepR using fun s : Set.range (coresidual f) => s.prop
  refine isBimachineComputable_of_stateSummaries
    (fun u => ⟨residual f u, Set.mem_range_self u⟩)
    (fun r x => ⟨fun v => (r.val (x :: v)).drop 1, by
      obtain ⟨u, hu⟩ := r.prop
      exact ⟨u ++ [x], by rw [residual_append_singleton, hu]⟩⟩)
    (fun w => ⟨coresidual f w, Set.mem_range_self w⟩)
    (fun s x => ⟨fun u => (s.val (u ++ [x])).take u.length, by
      obtain ⟨w, hw⟩ := s.prop
      exact ⟨x :: w, by rw [coresidual_cons, hw]⟩⟩)
    (fun r x s => (f (repL r ++ x :: repR s))[(repL r).length]'(by
      rw [hlen]
      simp))
    (fun u x => Subtype.ext (residual_append_singleton f u x))
    (fun x w => Subtype.ext (coresidual_cons f x w))
    (fun u x w => ?_) hlen
  set r : Set.range (residual f) := ⟨residual f u, Set.mem_range_self u⟩
  set s : Set.range (coresidual f) := ⟨coresidual f w, Set.mem_range_self w⟩
  have hres : residual f (repL r) = residual f u := hrepL r
  have hcores : coresidual f (repR s) = coresidual f w := hrepR s
  calc (f (u ++ x :: w))[u.length]?
      = (residual f u (x :: w))[0]? := (getElem?_residual_cons f u x w).symm
    _ = (residual f (repL r) (x :: w))[0]? := by rw [hres]
    _ = (f (repL r ++ x :: w))[(repL r).length]? := getElem?_residual_cons f _ x w
    _ = (coresidual f w (repL r ++ [x]))[(repL r).length]? :=
        (getElem?_coresidual_append f _ x w).symm
    _ = (coresidual f (repR s) (repL r ++ [x]))[(repL r).length]? := by rw [hcores]
    _ = (f (repL r ++ x :: repR s))[(repL r).length]? := getElem?_coresidual_append f _ x _
    _ = some ((f (repL r ++ x :: repR s))[(repL r).length]'(by rw [hlen]; simp)) :=
        List.getElem?_eq_getElem _

end Bimachine

/-- **Myhill–Nerode for bimachines**: a function is bimachine-computable if and only
if it is length-preserving with finitely many residuals and finitely many
coresiduals. -/
theorem isBimachineComputable_iff_residual {f : List α → List β} :
    IsBimachineComputable f
      ↔ (∀ xs, (f xs).length = xs.length) ∧ (Set.range (residual f)).Finite
        ∧ (Set.range (coresidual f)).Finite :=
  ⟨fun hf => ⟨hf.length_eq, hf.finite_range_residual, hf.finite_range_coresidual⟩,
   fun h => isBimachineComputable_of_residual h.1 h.2.1 h.2.2⟩

end Subregular
