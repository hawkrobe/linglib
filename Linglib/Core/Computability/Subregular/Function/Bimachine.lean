/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.EquivFin
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy
import Linglib.Core.Data.List.Fold

/-!
# Bimachines and weak determinism

A `Bimachine` (Schützenberger; [mohri-1997]) computes a letter-to-letter string function
using **both** directions of context: a left automaton scans `→` and assigns a left state
to each position, a right automaton scans `←` and assigns a right state, and the output at
position `i` is `out (leftState before i) (input i) (rightState after i)`.

A bimachine over a single alphabet is **non-interacting** when its output is a *union of
one-sided change-rules over the identity*: each side may add its own change, but neither
can suppress the other's. `IsBimachineWeaklyDeterministic` is computability by such a
bimachine — the weakly-deterministic functions.

## Main results

* `Bimachine.run_getElem?` — output `i` is `out (lState (x.take i)) (x i) (rState (x.drop (i+1)))`.
* `not_isBimachineWeaklyDeterministic_of_requiresBothSides` — a map with an unbounded
  *interaction* (`RequiresBothSides`: the target is changed, yet perturbing either far side
  reverts it) is **not** weakly deterministic. The far perturbations force both one-sided
  rules inert at the witness cell while the base needs one to fire — no union of one-sided
  rules can produce the change. A conjunctive change satisfies it; a two-sided union does
  not.
* `weaklyDeterministic_strict_subset_regular` — the inclusion is proper, witnessed by the
  conjunctive flag bimachine `conjBM`.
-/

namespace Subregular

variable {L R α β : Type*}

/-- A bimachine: a left automaton (`lInit`/`lStep`, scanning `→`), a right automaton
(`rInit`/`rStep`, scanning `←` over the suffix), and a cell output `out` reading both
context states and the current symbol. -/
structure Bimachine (L R α β : Type*) where
  lInit : L
  lStep : L → α → L
  rInit : R
  rStep : R → α → R
  out : L → α → R → β

namespace Bimachine

variable (B : Bimachine L R α β)

/-- Left state after scanning a prefix left-to-right. -/
def lState (pre : List α) : L := pre.foldl B.lStep B.lInit
/-- Right state after scanning a suffix right-to-left. -/
def rState (suf : List α) : R := suf.foldr (fun a r => B.rStep r a) B.rInit

theorem lState_nil : B.lState [] = B.lInit := rfl
theorem rState_nil : B.rState [] = B.rInit := rfl

/-- Run threading the left state; each tail's right state is read on the spot. -/
def runAux (B : Bimachine L R α β) : L → List α → List β
  | _, [] => []
  | l, x :: xs => B.out l x (B.rState xs) :: B.runAux (B.lStep l x) xs

/-- The computed function. -/
def run (x : List α) : List β := B.runAux B.lInit x

@[simp] theorem runAux_nil (l : L) : B.runAux l [] = [] := rfl
@[simp] theorem runAux_cons (l : L) (x : α) (xs : List α) :
    B.runAux l (x :: xs) = B.out l x (B.rState xs) :: B.runAux (B.lStep l x) xs := rfl

theorem runAux_length (l : L) (xs : List α) :
    (B.runAux l xs).length = xs.length := by
  induction xs generalizing l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem run_length (x : List α) : (B.run x).length = x.length :=
  B.runAux_length B.lInit x

/-- **Coordinate characterization** (threaded form). -/
theorem runAux_getElem? (l : L) (xs : List α) (i : ℕ) :
    (B.runAux l xs)[i]?
      = (xs[i]?).map (fun a => B.out ((xs.take i).foldl B.lStep l) a (B.rState (xs.drop (i + 1)))) := by
  induction xs generalizing l i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ j => simp [ih, List.take_succ_cons]

/-- **Coordinate characterization**: output `i` is `out (lState (x.take i)) (x i)
(rState (x.drop (i+1)))`. -/
theorem run_getElem? (x : List α) (i : ℕ) :
    (B.run x)[i]?
      = (x[i]?).map (fun a => B.out (B.lState (x.take i)) a (B.rState (x.drop (i + 1)))) := by
  rw [run, runAux_getElem?]; rfl

variable {L' R' : Type*}

/-- Lifts equivalences on the two state spaces to an equivalence on bimachines. -/
@[simps apply_lInit apply_lStep apply_rInit apply_rStep apply_out]
def reindex (eL : L ≃ L') (eR : R ≃ R') : Bimachine L R α β ≃ Bimachine L' R' α β where
  toFun B := {
    lInit := eL B.lInit
    lStep := fun l a => eL (B.lStep (eL.symm l) a)
    rInit := eR B.rInit
    rStep := fun r a => eR (B.rStep (eR.symm r) a)
    out := fun l a r => B.out (eL.symm l) a (eR.symm r)
  }
  invFun B := {
    lInit := eL.symm B.lInit
    lStep := fun l a => eL.symm (B.lStep (eL l) a)
    rInit := eR.symm B.rInit
    rStep := fun r a => eR.symm (B.rStep (eR r) a)
    out := fun l a r => B.out (eL l) a (eR r)
  }
  left_inv B := by simp
  right_inv B := by simp

@[simp] theorem lState_reindex (eL : L ≃ L') (eR : R ≃ R') (pre : List α) :
    (reindex eL eR B).lState pre = eL (B.lState pre) :=
  List.foldl_hom eL fun y x => by simp

@[simp] theorem rState_reindex (eL : L ≃ L') (eR : R ≃ R') (suf : List α) :
    (reindex eL eR B).rState suf = eR (B.rState suf) :=
  List.foldr_hom eR fun x y => by simp

@[simp] theorem runAux_reindex (eL : L ≃ L') (eR : R ≃ R')
    (l : L) (xs : List α) :
    (reindex eL eR B).runAux (eL l) xs = B.runAux l xs := by
  induction xs generalizing l <;> simp [*]

/-- The reindexed bimachine computes the same string function. -/
@[simp] theorem run_reindex (eL : L ≃ L') (eR : R ≃ R') :
    (reindex eL eR B).run = B.run := by
  funext xs; simp [run]

/-! ### Flag bimachines

The recurring two-sided-trigger shape: each side's automaton is the one-bit "some symbol
on my side satisfies `p`" flag, so `lState`/`rState` compute `List.any` and the cell sees
exactly the two flags. The conjunctive witness `conjBM` below is an instance. -/

variable (pL pR : α → Bool) (out : Bool → α → Bool → β)

/-- The bimachine whose side states are "a symbol satisfying `pL`/`pR` occurred on my
side" flags. -/
def ofFlags : Bimachine Bool Bool α β where
  lInit := false
  lStep l a := l || pL a
  rInit := false
  rStep r a := r || pR a
  out := out

@[simp] theorem ofFlags_lState (xs : List α) : (ofFlags pL pR out).lState xs = xs.any pL := by
  simp [lState, ofFlags, List.foldl_or]

@[simp] theorem ofFlags_rState (xs : List α) : (ofFlags pL pR out).rState xs = xs.any pR := by
  show xs.foldr (fun a r => r || pR a) false = _
  induction xs <;> simp_all [Bool.or_comm]

/-- Coordinate characterization of a flag bimachine: output `i` sees the input symbol and
the two window-`any` flags. -/
theorem ofFlags_run_getElem?
    (x : List α) (i : ℕ) :
    ((ofFlags pL pR out).run x)[i]?
      = (x[i]?).map fun a => out ((x.take i).any pL) a ((x.drop (i + 1)).any pR) := by
  simp only [run_getElem?, ofFlags_lState, ofFlags_rState]
  rfl

end Bimachine

/-! ### Weak determinism -/

/-- Computability by a finite bimachine (the length-preserving regular functions). -/
def IsBimachineComputable (f : List α → List β) : Prop :=
  ∃ (L R : Type) (_ : Fintype L) (_ : Fintype R) (B : Bimachine L R α β), B.run = f

/-- **Constructor lemma**: every finite-state bimachine witnesses `IsBimachineComputable`
for its `run`. States are accepted at arbitrary `Type*` and brought down to
`Fin (Fintype.card ·) : Type 0` via `reindex` + `Fintype.equivFin`, so consumers stop
spelling the `∃ (L R : Type)` quadruple. Mirrors `SFST.isLeftSubsequential`. -/
theorem isBimachineComputable {L R : Type*} [Fintype L] [Fintype R] {α β : Type*}
    (B : Bimachine L R α β) : IsBimachineComputable B.run :=
  ⟨Fin (Fintype.card L), Fin (Fintype.card R), inferInstance, inferInstance,
    Bimachine.reindex (Fintype.equivFin L) (Fintype.equivFin R) B, B.run_reindex _ _⟩

section TwoSidedWitness

variable {α : Type*} {x fill y a : α} {n k : ℕ} {p : α → Bool}

/-! ### The flank-witness template

The recurring witness family for two-sided unboundedness: a target buried in a filler
run, with independently editable flanks. `RequiresBothSides.of_flanks` packages the
whole assembly — a map is excluded by exhibiting only the images of the base and the
two single-flank perturbations at the target. This is the three-map method of
[yolyan-2025] §5.3, as an object. -/

/-- A flank-controlled word: `x`, then `n` copies of `fill`, then `y`. -/
def flankWord (x fill y : α) (n : ℕ) : List α := x :: (List.replicate n fill ++ [y])

@[simp] theorem flankWord_length :
    (flankWord x fill y n).length = n + 2 := by
  simp [flankWord]

theorem flankWord_getElem? :
    (flankWord x fill y n)[k]? = if k = 0 then some x else if k = n + 1 then some y
      else if k < n + 2 then some fill else none := by
  simp only [flankWord, List.getElem?_cons, List.getElem?_append, List.getElem?_replicate,
    List.length_replicate, List.getElem?_nil]
  split_ifs <;> first | rfl | omega

@[simp] theorem flankWord_getElem?_zero :
    (flankWord x fill y n)[0]? = some x := rfl

@[simp] theorem flankWord_getElem?_last :
    (flankWord x fill y n)[n + 1]? = some y := by
  rw [flankWord_getElem?]
  split_ifs <;> first | rfl | exact ‹False›.elim | omega

theorem flankWord_getElem?_mid (h₁ : 0 < k) (h₂ : k ≤ n) :
    (flankWord x fill y n)[k]? = some fill := by
  rw [flankWord_getElem?]
  split_ifs <;> first | rfl | exact ‹False›.elim | omega

/-- A non-filler value sits only on a flank. -/
theorem flankWord_getElem?_eq_some_iff {j : ℕ} (hfill : fill ≠ a) :
    (flankWord x fill y n)[j]? = some a ↔ j = 0 ∧ x = a ∨ j = n + 1 ∧ y = a := by
  rw [flankWord_getElem?]
  split_ifs <;> simp_all

/-- A window reaching at most the filler run hits `a` iff the left flank is `a`. -/
theorem exists_le_flankWord_eq_some_iff (hfill : fill ≠ a) (hk : k ≤ n) :
    (∃ j ≤ k, (flankWord x fill y n)[j]? = some a) ↔ x = a := by
  simp [flankWord_getElem?_eq_some_iff hfill, and_or_left, exists_or,
    eq_false (by omega : ¬ (n + 1 ≤ k))]

/-- A window past the left flank hits `a` iff the right flank is `a`. -/
theorem exists_ge_flankWord_eq_some_iff (hfill : fill ≠ a) (h0 : 0 < k)
    (hk : k ≤ n + 1) : (∃ j ≥ k, (flankWord x fill y n)[j]? = some a) ↔ y = a := by
  simp only [flankWord_getElem?_eq_some_iff hfill]
  constructor
  · rintro ⟨j, hj, ⟨rfl, hx⟩ | ⟨rfl, hy⟩⟩
    exacts [absurd hj (by omega), hy]
  · exact fun h => ⟨n + 1, hk, .inr ⟨rfl, h⟩⟩

/-- A flag over a window reaching at most the filler run reads the left flank — the
`ofFlags` counterpart of `exists_le_flankWord_eq_some_iff`. -/
theorem any_take_flankWord (hfill : p fill = false) (h0 : 0 < k) (hk : k ≤ n + 1) :
    ((flankWord x fill y n).take k).any p = p x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [flankWord, List.take_succ_cons, List.take_append_of_le_length (by simp; omega),
    List.take_replicate]
  simp [hfill]

/-- A flag over a window past the left flank reads the right flank. -/
theorem any_drop_flankWord (hfill : p fill = false) (h0 : 0 < k) (hk : k ≤ n + 1) :
    ((flankWord x fill y n).drop k).any p = p y := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [flankWord, List.drop_succ_cons, List.drop_append_of_le_length (by simp; omega),
    List.drop_replicate]
  simp [hfill]

/-- Flank words differing only on the left agree off position `0`. -/
theorem flankWord_congr_left {x' : α} (h : k ≠ 0) :
    (flankWord x fill y n)[k]? = (flankWord x' fill y n)[k]? := by
  rw [flankWord_getElem?, flankWord_getElem?]
  split_ifs <;> first | rfl | exact ‹False›.elim | omega

/-- Flank words differing only on the right agree off the last position. -/
theorem flankWord_congr_right {y' : α} (h : k ≠ n + 1) :
    (flankWord x fill y n)[k]? = (flankWord x fill y' n)[k]? := by
  rw [flankWord_getElem?, flankWord_getElem?]
  split_ifs <;> rfl

/-- `f` requires both sides: some target changes under `f`, yet perturbing either far
side reverts it to the identity. Unlike `IsUnboundedSemiambient`, a two-sided union
never satisfies this — removing one trigger leaves the other, so the output stays
changed. -/
def RequiresBothSides (f : List α → List α) : Prop :=
  ∀ d, ∃ (base : List α) (i : ℕ), i < base.length ∧ (f base)[i]? ≠ base[i]? ∧
    ∀ s, ∃ u, IsFarPerturbation base u i d s ∧ u[i]? = base[i]? ∧ (f u)[i]? = u[i]?

/-- **The three-map template**: a `d`-indexed family of flank words whose target sits
`d`-far from both flanks, changed to `on` in the base and reverted by flipping either
flank alone, requires both sides. -/
theorem RequiresBothSides.of_flanks {f : List α → List α}
    {fill on xOn yOn xOff yOff : α} {n t : ℕ → ℕ} (hne : on ≠ fill)
    (hmargin : ∀ d, d < t d ∧ t d + d < n d + 1)
    (hchange : ∀ d, (f (flankWord xOn fill yOn (n d)))[t d]? = some on)
    (hrevL : ∀ d, (f (flankWord xOff fill yOn (n d)))[t d]? = some fill)
    (hrevR : ∀ d, (f (flankWord xOn fill yOff (n d)))[t d]? = some fill) :
    RequiresBothSides f := by
  intro d
  obtain ⟨hm₁, hm₂⟩ := hmargin d
  have hmid : ∀ x y : α, (flankWord x fill y (n d))[t d]? = some fill := fun x y =>
    flankWord_getElem?_mid (by omega) (by omega)
  refine ⟨flankWord xOn fill yOn (n d), t d, by rw [flankWord_length]; omega,
    by rw [hchange, hmid]; simpa using hne, fun s => ?_⟩
  match s with
  | .left =>
    exact ⟨flankWord xOff fill yOn (n d),
      ⟨by simp, fun k hk => flankWord_congr_left (by omega)⟩, by rw [hmid, hmid],
      by rw [hrevL, hmid]⟩
  | .right =>
    exact ⟨flankWord xOn fill yOff (n d),
      ⟨by simp, fun k hk => flankWord_congr_right (by omega)⟩, by rw [hmid, hmid],
      by rw [hrevR, hmid]⟩

/-- Requiring both sides strengthens unbounded semiambience: a reverted target is in
particular a flipped one. The converse fails (a two-sided union is semiambient but
reverts under neither side alone). -/
theorem RequiresBothSides.isUnboundedSemiambient {f : List α → List α}
    (hf : RequiresBothSides f) : IsUnboundedSemiambient f := fun d =>
  have ⟨base, i, hi, hchange, hw⟩ := hf d
  ⟨base, i, hi, fun s =>
    have ⟨u, hp, hsym, hrev⟩ := hw s
    ⟨u, hp, fun h => hchange (h.trans (hrev.trans hsym))⟩⟩

end TwoSidedWitness

section NonInteraction

variable {L R α : Type*} [DecidableEq α]

/-- Combine two one-sided change proposals over the identity default `a`: take the left
rule's change if it fires (`≠ a`), else the right rule's, else leave the symbol. -/
def unite (cL cR a : α) : α := if cL = a then (if cR = a then a else cR) else cL

/-- With the right proposal inert, the union is whatever the left one proposes. -/
@[simp] theorem unite_right_self (cL a : α) : unite cL a a = cL := by
  unfold unite; split_ifs <;> simp_all

/-- A combined value equal to the default forces *both* one-sided proposals to be inert. -/
theorem unite_eq_default {cL cR a : α} (h : unite cL cR a = a) : cL = a ∧ cR = a := by
  unfold unite at h; split_ifs at h with h1 h2 <;> simp_all

/-- **Non-interaction**: the cell output is a *union of one-sided change-rules over the
identity default* — `ωL`/`ωR` each propose a change for their side, and the output takes
whichever fires, else leaves the symbol unchanged. Neither side can *suppress* the other's
change; that asymmetry is exactly what interaction would require. -/
def Bimachine.IsNonInteracting (B : Bimachine L R α α) : Prop :=
  ∃ (ωL : L → α → α) (ωR : R → α → α), ∀ l a r, B.out l a r = unite (ωL l a) (ωR r a) a

/-- **Weak determinism**: computability by a non-interacting finite bimachine. -/
def IsBimachineWeaklyDeterministic (f : List α → List α) : Prop :=
  ∃ (L R : Type) (_ : Fintype L) (_ : Fintype R) (B : Bimachine L R α α),
    B.run = f ∧ B.IsNonInteracting

/-- **Constructor lemma**: a non-interacting finite-state bimachine witnesses
`IsBimachineWeaklyDeterministic` for its `run`. The one-sided rules survive the
state-space transfer by composing with `e.symm`. -/
theorem isBimachineWeaklyDeterministic {L R : Type*} [Fintype L] [Fintype R]
    (B : Bimachine L R α α) (h : B.IsNonInteracting) :
    IsBimachineWeaklyDeterministic B.run := by
  obtain ⟨ωL, ωR, hω⟩ := h
  refine ⟨Fin (Fintype.card L), Fin (Fintype.card R), inferInstance, inferInstance,
    Bimachine.reindex (Fintype.equivFin L) (Fintype.equivFin R) B, B.run_reindex _ _,
    fun l a => ωL ((Fintype.equivFin L).symm l) a,
    fun r a => ωR ((Fintype.equivFin R).symm r) a, ?_⟩
  intro l a r
  show B.out _ a _ = _
  rw [hω]

/-- Under a non-interacting cell decomposition, a word whose run leaves target `i`
unchanged has both of its change-proposals inert there. -/
theorem inert_of_reverting {B : Bimachine L R α α} {ωL : L → α → α} {ωR : R → α → α}
    (hω : ∀ l a r, B.out l a r = unite (ωL l a) (ωR r a) a) {u : List α} {i : ℕ} {a : α}
    (hsym : u[i]? = some a) (hrev : (B.run u)[i]? = u[i]?) :
    ωL (B.lState (u.take i)) a = a ∧ ωR (B.rState (u.drop (i + 1))) a = a := by
  refine unite_eq_default (Option.some_injective _ (Eq.symm ?_))
  rw [← hsym, ← hrev, B.run_getElem?, hsym, Option.map_some, hω]

/-- **Unbounded interaction ⟹ not weakly deterministic.** At the witness, the base changes
but each far perturbation reverts: the right perturbation keeps the left state, forcing `ωL`
inert at this cell; the left perturbation keeps the right state, forcing `ωR` inert; yet the
base needs one of them to fire — no union of one-sided rules can produce the change. -/
theorem not_isBimachineWeaklyDeterministic_of_requiresBothSides {f : List α → List α}
    (hf : RequiresBothSides f) : ¬ IsBimachineWeaklyDeterministic f := by
  rintro ⟨L, R, _, _, B, rfl, ωL, ωR, hω⟩
  obtain ⟨base, i, hi, hspread, hw⟩ := hf 0
  obtain ⟨uL, ⟨-, hLag⟩, hLsym, hLrev⟩ := hw .left
  obtain ⟨uR, ⟨-, hRag⟩, hRsym, hRrev⟩ := hw .right
  simp only [Nat.sub_zero, Nat.add_zero] at hLag hRag
  -- decompose the base's cell, retarget each side's state to the perturbation that
  -- shares it, and silence both rules by `inert_of_reverting`
  apply hspread
  rw [B.run_getElem?, List.getElem?_eq_getElem hi, Option.map_some, hω,
    hRag.take_eq (by omega), hLag.drop_eq (by omega),
    (inert_of_reverting hω (hRsym.trans (List.getElem?_eq_getElem hi)) hRrev).1,
    (inert_of_reverting hω (hLsym.trans (List.getElem?_eq_getElem hi)) hLrev).2,
    unite_right_self]

end NonInteraction

/-! ### Strictness: weakly deterministic ⊊ bimachine-computable

A *conjunctive* change — a symbol flipped iff a mark occurs on **both** sides — is
bimachine-computable but `RequiresBothSides`, so no non-interacting bimachine computes
it. -/

/-- Toy alphabet for the conjunctive witness: a `mark`, a `neutral` symbol, and the
`flipped` form the neutral symbol takes when both sides are marked. -/
inductive ConjSym | mark | neutral | flipped
  deriving DecidableEq, Repr

instance : Fintype ConjSym := ⟨{.mark, .neutral, .flipped}, fun x => by cases x <;> simp⟩

/-- A neutral symbol flips iff a `mark` occurs on **both** sides — a flag bimachine
(`ofFlags`) tracking a mark on each side, whose cell genuinely needs both flags
(`l && r`). -/
def conjBM : Bimachine Bool Bool ConjSym ConjSym :=
  .ofFlags (· == .mark) (· == .mark) fun l s r =>
    if (l && r) && s == .neutral then .flipped else s

/-- Inside the filler run of a flank word, `conjBM` flips the neutral symbol exactly when
both flanks are marks. -/
private theorem conjBM_flankWord {x y : ConjSym} {n k : ℕ} (h0 : 0 < k) (hk : k ≤ n) :
    (conjBM.run (flankWord x .neutral y n))[k]?
      = some (if x == .mark && y == .mark then .flipped else .neutral) := by
  rw [conjBM, Bimachine.ofFlags_run_getElem?, flankWord_getElem?_mid h0 hk,
    any_take_flankWord (by decide) h0 (by omega),
    any_drop_flankWord (by decide) (by omega) (by omega)]
  simp

/-- The conjunctive change requires both sides: with a mark on each flank the medial
symbol flips, and demoting either mark alone reverts it — the three-map template
(`RequiresBothSides.of_flanks`) applied to a `d`-margined flank word. -/
theorem conjBM_requiresBothSides : RequiresBothSides conjBM.run :=
  .of_flanks (fill := .neutral) (on := .flipped) (xOn := .mark) (yOn := .mark)
    (xOff := .neutral) (yOff := .neutral) (n := fun d => 2 * d + 1) (t := fun d => d + 1)
    (by decide) (fun d => ⟨by omega, by omega⟩)
    (fun d => by rw [conjBM_flankWord (by omega) (by omega)]; rfl)
    (fun d => by rw [conjBM_flankWord (by omega) (by omega)]; rfl)
    (fun d => by rw [conjBM_flankWord (by omega) (by omega)]; rfl)

/-- **The weakly deterministic functions are a proper subclass**: `conjBM` is computed by
a bimachine, but by no non-interacting one. -/
theorem weaklyDeterministic_strict_subset_regular :
    ∃ f : List ConjSym → List ConjSym,
      IsBimachineComputable f ∧ ¬ IsBimachineWeaklyDeterministic f :=
  ⟨conjBM.run, isBimachineComputable conjBM,
   not_isBimachineWeaklyDeterministic_of_requiresBothSides conjBM_requiresBothSides⟩

end Subregular
