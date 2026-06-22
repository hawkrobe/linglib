/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Basic
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy

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

/-- Left state after scanning a prefix left-to-right. -/
def lState (B : Bimachine L R α β) (pre : List α) : L := pre.foldl B.lStep B.lInit
/-- Right state after scanning a suffix right-to-left. -/
def rState (B : Bimachine L R α β) (suf : List α) : R := suf.foldr (fun a r => B.rStep r a) B.rInit

@[simp] theorem lState_nil (B : Bimachine L R α β) : B.lState [] = B.lInit := rfl
@[simp] theorem rState_nil (B : Bimachine L R α β) : B.rState [] = B.rInit := rfl

/-- Run threading the left state; each tail's right state is read on the spot. -/
def runAux (B : Bimachine L R α β) : L → List α → List β
  | _, [] => []
  | l, x :: xs => B.out l x (B.rState xs) :: B.runAux (B.lStep l x) xs

/-- The computed function. -/
def run (B : Bimachine L R α β) (x : List α) : List β := B.runAux B.lInit x

@[simp] theorem runAux_nil (B : Bimachine L R α β) (l : L) : B.runAux l [] = [] := rfl
@[simp] theorem runAux_cons (B : Bimachine L R α β) (l : L) (x : α) (xs : List α) :
    B.runAux l (x :: xs) = B.out l x (B.rState xs) :: B.runAux (B.lStep l x) xs := rfl

theorem runAux_length (B : Bimachine L R α β) (l : L) (xs : List α) :
    (B.runAux l xs).length = xs.length := by
  induction xs generalizing l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem run_length (B : Bimachine L R α β) (x : List α) : (B.run x).length = x.length :=
  B.runAux_length B.lInit x

/-- **Coordinate characterization** (threaded form). -/
theorem runAux_getElem? (B : Bimachine L R α β) (l : L) (xs : List α) (i : ℕ) :
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
theorem run_getElem? (B : Bimachine L R α β) (x : List α) (i : ℕ) :
    (B.run x)[i]?
      = (x[i]?).map (fun a => B.out (B.lState (x.take i)) a (B.rState (x.drop (i + 1)))) := by
  rw [run, runAux_getElem?]; rfl

end Bimachine

/-! ### Weak determinism -/

/-- Computability by a finite bimachine (the length-preserving regular functions). -/
def IsBimachineComputable (f : List α → List β) : Prop :=
  ∃ (L R : Type) (_ : Fintype L) (_ : Fintype R) (B : Bimachine L R α β), B.run = f

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

/-- A target that **requires both sides**: `f` changes `base[i]` from its input, but
perturbing either far side reverts it to identity. The suppression/conjunction structure of
unbounded interaction. Unlike `IsUnboundedCircumambient`, a two-sided union does *not*
satisfy it: removing one trigger leaves the other, so the output stays changed. -/
def RequiresBothSides (f : List α → List α) : Prop :=
  ∀ d, ∃ (base : List α) (i : ℕ), i < base.length ∧ (f base)[i]? ≠ base[i]? ∧
    (∃ uL : List α, uL.length = base.length ∧ AgreeFrom base uL (i - d) ∧
      uL[i]? = base[i]? ∧ (f uL)[i]? = uL[i]?) ∧
    (∃ uR : List α, uR.length = base.length ∧ AgreeUpto base uR (i + d) ∧
      uR[i]? = base[i]? ∧ (f uR)[i]? = uR[i]?)

/-- **Unbounded interaction ⟹ not weakly deterministic.** At the witness, the base changes
but each far perturbation reverts: the right perturbation keeps the left state, forcing `ωL`
inert at this cell; the left perturbation keeps the right state, forcing `ωR` inert; yet the
base needs one of them to fire — no union of one-sided rules can produce the change. -/
theorem not_isBimachineWeaklyDeterministic_of_requiresBothSides {f : List α → List α}
    (hf : RequiresBothSides f) : ¬ IsBimachineWeaklyDeterministic f := by
  rintro ⟨L, R, _, _, B, rfl, ωL, ωR, hω⟩
  obtain ⟨base, i, hi, hspread, ⟨uL, hLlen, hLag, hLsym, hLrev⟩,
    ⟨uR, hRlen, hRag, hRsym, hRrev⟩⟩ := hf 0
  simp only [Nat.sub_zero, Nat.add_zero] at hLag hRag
  have hbi : base[i]? = some base[i] := List.getElem?_eq_getElem hi
  -- right perturbation keeps the left state; its reverting output makes `ωL` inert here
  have hRtake : uR.take i = base.take i := take_eq_of_agree fun k hk => (hRag k (by omega)).symm
  have hRsym' : uR[i]? = some base[i] := hRsym.trans hbi
  have hRout : (B.run uR)[i]? =
      some (unite (ωL (B.lState (base.take i)) base[i])
        (ωR (B.rState (uR.drop (i + 1))) base[i]) base[i]) := by
    rw [B.run_getElem?, hRsym', Option.map_some, hRtake, hω]
  have hωL : ωL (B.lState (base.take i)) base[i] = base[i] :=
    (unite_eq_default (Option.some_injective _ (hRout.symm.trans (by rw [hRrev, hRsym'])))).1
  -- left perturbation keeps the right state; its reverting output makes `ωR` inert here
  have hLdrop : uL.drop (i + 1) = base.drop (i + 1) := drop_eq_of_agree fun k _ => (hLag k (by omega)).symm
  have hLsym' : uL[i]? = some base[i] := hLsym.trans hbi
  have hLout : (B.run uL)[i]? =
      some (unite (ωL (B.lState (uL.take i)) base[i])
        (ωR (B.rState (base.drop (i + 1))) base[i]) base[i]) := by
    rw [B.run_getElem?, hLsym', Option.map_some, hLdrop, hω]
  have hωR : ωR (B.rState (base.drop (i + 1))) base[i] = base[i] :=
    (unite_eq_default (Option.some_injective _ (hLout.symm.trans (by rw [hLrev, hLsym'])))).2
  -- the base needs a change, but both rules are inert
  apply hspread
  rw [B.run_getElem?, hbi, Option.map_some, hω, hωL, hωR, unite_self]

/-- Non-vacuity: any bimachine whose cell output is literally a `unite` of independent
one-sided rules is non-interacting — the class genuinely admits two-sided union changes,
which a naive per-cell notion would wrongly exclude. -/
example (ωL : L → α → α) (ωR : R → α → α) (lInit : L) (lStep : L → α → L)
    (rInit : R) (rStep : R → α → R) :
    (Bimachine.mk lInit lStep rInit rStep
      (fun l a r => unite (ωL l a) (ωR r a) a)).IsNonInteracting :=
  ⟨ωL, ωR, fun _ _ _ => rfl⟩

end NonInteraction

end Subregular
