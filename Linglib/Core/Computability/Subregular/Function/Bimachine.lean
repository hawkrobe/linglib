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

/-- Transfer a bimachine along state-space equivalences `L ≃ L'` and `R ≃ R'`,
preserving `run`. Mirrors `SFST.transferEquiv`/`Mealy.transferEquiv`; the use case is
bringing `Type*` finite states down to `Fin (Fintype.card ·) : Type 0` so a
universe-polymorphic machine can witness the `Type 0`-state existentials of
`IsBimachineComputable`/`IsBimachineWeaklyDeterministic`. -/
def transferEquiv (eL : L ≃ L') (eR : R ≃ R') :
    Bimachine L' R' α β where
  lInit := eL B.lInit
  lStep l a := eL (B.lStep (eL.symm l) a)
  rInit := eR B.rInit
  rStep r a := eR (B.rStep (eR.symm r) a)
  out l a r := B.out (eL.symm l) a (eR.symm r)

theorem transferEquiv_lState_from (eL : L ≃ L') (eR : R ≃ R')
    (l : L) (pre : List α) :
    pre.foldl (B.transferEquiv eL eR).lStep (eL l) = eL (pre.foldl B.lStep l) :=
  List.foldl_hom eL fun y x => by simp [transferEquiv]

theorem transferEquiv_rState_from (eL : L ≃ L') (eR : R ≃ R')
    (r : R) (suf : List α) :
    suf.foldr (fun a r => (B.transferEquiv eL eR).rStep r a) (eR r)
      = eR (suf.foldr (fun a r => B.rStep r a) r) :=
  List.foldr_hom eR fun x y => by simp [transferEquiv]

theorem transferEquiv_lState (eL : L ≃ L') (eR : R ≃ R')
    (pre : List α) : (B.transferEquiv eL eR).lState pre = eL (B.lState pre) :=
  transferEquiv_lState_from B eL eR B.lInit pre

theorem transferEquiv_rState (eL : L ≃ L') (eR : R ≃ R')
    (suf : List α) : (B.transferEquiv eL eR).rState suf = eR (B.rState suf) :=
  transferEquiv_rState_from B eL eR B.rInit suf

theorem transferEquiv_runAux (eL : L ≃ L') (eR : R ≃ R')
    (l : L) (xs : List α) :
    (B.transferEquiv eL eR).runAux (eL l) xs = B.runAux l xs := by
  induction xs generalizing l with
  | nil => rfl
  | cons x xs ih =>
    rw [runAux_cons, runAux_cons]
    show B.out (eL.symm (eL l)) x (eR.symm ((B.transferEquiv eL eR).rState xs)) ::
        (B.transferEquiv eL eR).runAux (eL (B.lStep (eL.symm (eL l)) x)) xs = _
    rw [eL.symm_apply_apply, transferEquiv_rState, eR.symm_apply_apply, ih]

/-- The transferred bimachine computes the same string function. -/
@[simp] theorem transferEquiv_run (eL : L ≃ L') (eR : R ≃ R') :
    (B.transferEquiv eL eR).run = B.run := by
  funext xs; exact transferEquiv_runAux B eL eR B.lInit xs

/-! ### Flag bimachines

The recurring two-sided-trigger shape: each side's automaton is the one-bit "some symbol
on my side satisfies `p`" flag, so `lState`/`rState` compute `List.any` and the cell sees
exactly the two flags. Conjunctive spreads (`conjBM` in `Hierarchy.lean`) and unbounded
tonal plateauing ([jardine-2016]) are instances. -/

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
`Fin (Fintype.card ·) : Type 0` via `transferEquiv` + `Fintype.equivFin`, so consumers stop
spelling the `∃ (L R : Type)` quadruple. Mirrors `SFST.isLeftSubsequential`. -/
theorem isBimachineComputable {L R : Type*} [Fintype L] [Fintype R] {α β : Type*}
    (B : Bimachine L R α β) : IsBimachineComputable B.run :=
  ⟨Fin (Fintype.card L), Fin (Fintype.card R), inferInstance, inferInstance,
    B.transferEquiv (Fintype.equivFin L) (Fintype.equivFin R), B.transferEquiv_run _ _⟩

section TwoSidedWitness

variable {α : Type*} {x fill y a : α} {n k : ℕ}

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
side reverts it to the identity. Unlike `IsUnboundedCircumambient`, a two-sided union
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

/-- Requiring both sides strengthens unbounded circumambience: a reverted target is in
particular a flipped one. The converse fails (a two-sided union is circumambient but
reverts under neither side alone). -/
theorem RequiresBothSides.isUnboundedCircumambient {f : List α → List α}
    (hf : RequiresBothSides f) : IsUnboundedCircumambient f := fun d =>
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

@[simp] theorem unite_self (a : α) : unite a a a = a := by simp [unite]

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
    B.transferEquiv (Fintype.equivFin L) (Fintype.equivFin R), B.transferEquiv_run _ _,
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
    ← (take_eq_of_agree fun k hk => (hRag k (by omega)).symm : uR.take i = base.take i),
    ← (drop_eq_of_agree fun k _ => (hLag k (by omega)).symm :
        uL.drop (i + 1) = base.drop (i + 1)),
    (inert_of_reverting hω (hRsym.trans (List.getElem?_eq_getElem hi)) hRrev).1,
    (inert_of_reverting hω (hLsym.trans (List.getElem?_eq_getElem hi)) hLrev).2,
    unite_self]

end NonInteraction

end Subregular
