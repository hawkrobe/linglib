/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Basic
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy

/-!
# Bimachines and weak determinism

A `Bimachine` (Schützenberger; Mohri) computes a letter-to-letter string function using
**both** directions of context: a left automaton scans `→` and assigns a left state to
each position, a right automaton scans `←` and assigns a right state, and the output at
position `i` is `out (leftState before i) (input i) (rightState after i)`.

A bimachine is **non-interacting** ([heinz-lai-2013], [meinhardt-mai-mccollum-2024]) when
every cell's output is fixed by the left state alone *or* the right state alone — the
two directions never *both* matter at one cell. `IsBimachineWeaklyDeterministic` is
computability by a non-interacting bimachine.

## Main results

* `Bimachine.run_getElem?` — output `i` is `out (lState (x.take i)) (x i) (rState (x.drop (i+1)))`.
* `not_isBimachineWeaklyDeterministic_of_circumambient` — an unbounded-circumambient map
  is **not** weakly deterministic: at a circumambient witness, perturbing one side keeps
  that side's state fixed yet flips the output, so the cell is neither left- nor
  right-determined — contradicting non-interaction. This is the McCollum et al. teeth.
-/

namespace Core.Computability.Subregular.Function

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

/-! ### Locality of the context states -/

/-- Prefixes agreeing below `i` have equal `i`-truncations. -/
theorem take_eq_of_agree {u v : List α} {i : ℕ} (h : ∀ k, k < i → u[k]? = v[k]?) :
    u.take i = v.take i := by
  apply List.ext_getElem?
  intro k
  rcases lt_or_ge k i with hk | hk
  · simpa only [List.getElem?_take_of_lt hk] using h k hk
  · simp [List.getElem?_take_eq_none hk]

/-- Lists agreeing from `i` upward have equal `i`-suffixes. -/
theorem drop_eq_of_agree {u v : List α} {i : ℕ} (h : ∀ k, i ≤ k → u[k]? = v[k]?) :
    u.drop i = v.drop i := by
  apply List.ext_getElem?
  intro k
  simpa only [List.getElem?_drop] using h (i + k) (Nat.le_add_right i k)

/-! ### Weak determinism -/

/-- A bimachine is **non-interacting**: every cell's output is fixed by the left state
alone or by the right state alone. -/
def Bimachine.IsNonInteracting (B : Bimachine L R α β) : Prop :=
  ∀ l a r, (∀ r', B.out l a r' = B.out l a r) ∨ (∀ l', B.out l' a r = B.out l a r)

/-- Computability by a finite bimachine (the length-preserving regular functions). -/
def IsBimachineComputable (f : List α → List β) : Prop :=
  ∃ (L R : Type) (_ : Fintype L) (_ : Fintype R) (B : Bimachine L R α β), B.run = f

/-- **Weak determinism**: computability by a *non-interacting* finite bimachine. -/
def IsBimachineWeaklyDeterministic (f : List α → List β) : Prop :=
  ∃ (L R : Type) (_ : Fintype L) (_ : Fintype R) (B : Bimachine L R α β),
    B.run = f ∧ B.IsNonInteracting

/-- **Circumambient ⟹ not weakly deterministic** — the McCollum et al. teeth. At a
distance-0 circumambient witness `(base, i)`: the right-perturbation `uR` agrees with
`base` up to `i` (same left state, same symbol) yet flips the output, so the cell is not
left-determined; the left-perturbation `uL` agrees from `i` (same right state, same
symbol) yet flips the output, so it is not right-determined. Both fail at the *one* cell
`(lState (base.take i), base[i], rState (base.drop (i+1)))` — contradicting
non-interaction. -/
theorem not_isBimachineWeaklyDeterministic_of_circumambient {f : List α → List β}
    (hf : IsUnboundedCircumambient f) : ¬ IsBimachineWeaklyDeterministic f := by
  rintro ⟨L, R, _, _, B, rfl, hni⟩
  obtain ⟨base, i, hi, ⟨uL, hLlen, hLag, hLne⟩, ⟨uR, hRlen, hRag, hRne⟩⟩ := hf 0
  simp only [Nat.sub_zero, Nat.add_zero] at hLag hRag
  have hbi : base[i]? = some base[i] := List.getElem?_eq_getElem hi
  have hbase : (B.run base)[i]? =
      some (B.out (B.lState (base.take i)) base[i] (B.rState (base.drop (i + 1)))) := by
    rw [B.run_getElem?, hbi]; rfl
  -- `uL` agrees from `i`: same suffix (⇒ right state) and symbol; output differs.
  have hLdrop : uL.drop (i + 1) = base.drop (i + 1) :=
    drop_eq_of_agree fun k _ => (hLag k (by omega)).symm
  have hLsym : uL[i]? = some base[i] := (hLag i le_rfl).symm.trans hbi
  have hLout : (B.run uL)[i]? =
      some (B.out (B.lState (uL.take i)) base[i] (B.rState (base.drop (i + 1)))) := by
    rw [B.run_getElem?, hLsym, hLdrop]; rfl
  have hLneq : B.out (B.lState (uL.take i)) base[i] (B.rState (base.drop (i + 1)))
      ≠ B.out (B.lState (base.take i)) base[i] (B.rState (base.drop (i + 1))) :=
    fun h => hLne (by rw [hbase, hLout, h])
  -- `uR` agrees up to `i`: same prefix (⇒ left state) and symbol; output differs.
  have hRtake : uR.take i = base.take i :=
    take_eq_of_agree fun k hk => (hRag k (by omega)).symm
  have hRsym : uR[i]? = some base[i] := (hRag i le_rfl).symm.trans hbi
  have hRout : (B.run uR)[i]? =
      some (B.out (B.lState (base.take i)) base[i] (B.rState (uR.drop (i + 1)))) := by
    rw [B.run_getElem?, hRsym, hRtake]; rfl
  have hRneq : B.out (B.lState (base.take i)) base[i] (B.rState (uR.drop (i + 1)))
      ≠ B.out (B.lState (base.take i)) base[i] (B.rState (base.drop (i + 1))) :=
    fun h => hRne (by rw [hbase, hRout, h])
  rcases hni (B.lState (base.take i)) base[i] (B.rState (base.drop (i + 1))) with hLdet | hRdet
  · exact hRneq (hLdet (B.rState (uR.drop (i + 1))))
  · exact hLneq (hRdet (B.lState (uL.take i)))

end Core.Computability.Subregular.Function
