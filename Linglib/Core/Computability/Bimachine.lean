/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.EquivFin
import Linglib.Core.Computability.Mealy
import Linglib.Core.Data.Fintype.Transfer
import Linglib.Core.Data.List.Fold

/-!
# Bimachines

A `Bimachine` ([schutzenberger-1961]; [eilenberg-1974]) reads its input in both
directions: a left automaton scans `→`, a right automaton scans `←`, and output `i` is
`output (lState (x.take i)) (x i) (rState (x.drop (i+1)))`. Word-output bimachines
compute exactly the rational functions ([elgot-mezei-1965]; they are the transducers of
[schutzenberger-1976]'s semi-monomial representations, see [sakarovitch-2009]); the
letter-to-letter machines here compute the total length-preserving ones.

## Main definitions

* `Bimachine L R α β`: machine with left states `L`, right states `R`, alphabets `α`, `β`
* `Bimachine.run`: the computed function
* `IsBimachineComputable f`: `f` is computed by some finite bimachine

## Main theorems

* `Bimachine.getElem?_run`: output `i` is
  `output (lState (x.take i)) (x i) (rState (x.drop (i+1)))`

## Implementation notes

Only the left state is threaded through the run (`Bimachine.runFrom`); the recursion
reads each tail's right state on the spot. The class existentials pin state types at
`Type 0`; the universe-polymorphic `isBimachineComputable_iff` recovers generality.
The identification of
`IsBimachineComputable` with the total rational functions preserving the empty word is
classical and not formalized here; `ElgotMezei.lean` proves the composition half.

[UPSTREAM] candidate: `Mathlib.Computability.Bimachine`.
-/

variable {L R α β : Type*}

/-- A bimachine is a left automaton scanning left to right, a right automaton scanning
right to left, and a cell output reading both context states and the current symbol. -/
structure Bimachine (L R α β : Type*) where
  /-- Starting state of the left automaton. -/
  lInit : L
  /-- Transition of the left automaton, scanning left to right. -/
  lStep : L → α → L
  /-- Starting state of the right automaton. -/
  rInit : R
  /-- Transition of the right automaton, scanning right to left. -/
  rStep : R → α → R
  /-- The word emitted from the two context states and the current input symbol. -/
  output : L → α → R → List β

instance [Inhabited L] [Inhabited R] : Inhabited (Bimachine L R α β) :=
  ⟨⟨default, fun _ _ => default, default, fun _ _ => default, fun _ _ _ => []⟩⟩

namespace Bimachine

variable (B : Bimachine L R α β)

/-- `B.lStateAfter l pre` is the left state reached from `l` after scanning `pre`. -/
def lStateAfter (l : L) : List α → L := List.foldl B.lStep l

/-- Left state after scanning a prefix left-to-right from the start state. -/
def lState : List α → L := B.lStateAfter B.lInit

/-- Right state after scanning a suffix right-to-left. -/
def rState (suf : List α) : R := suf.foldr (fun a r => B.rStep r a) B.rInit

/-- `B.runFrom l x` runs `B` on `x` threading the left state from `l`; each tail's
right state is read on the spot. -/
def runFrom : L → List α → List β
  | _, [] => []
  | l, x :: xs => B.output l x (B.rState xs) ++ runFrom (B.lStep l x) xs

/-- The computed function. -/
def run : List α → List β := B.runFrom B.lInit

section
variable (l : L) (x : α) (xs : List α)

@[simp] theorem lStateAfter_nil : B.lStateAfter l [] = l := rfl
@[simp] theorem lStateAfter_cons : B.lStateAfter l (x :: xs) = B.lStateAfter (B.lStep l x) xs :=
  rfl
@[simp] theorem lState_nil : B.lState [] = B.lInit := rfl
@[simp] theorem rState_nil : B.rState [] = B.rInit := rfl
@[simp] theorem rState_cons : B.rState (x :: xs) = B.rStep (B.rState xs) x := rfl

@[simp] theorem runFrom_nil : B.runFrom l [] = [] := rfl
@[simp] theorem runFrom_cons :
    B.runFrom l (x :: xs) = B.output l x (B.rState xs) ++ B.runFrom (B.lStep l x) xs := rfl

end

/-! ### Letter-to-letter bimachines

A cell of a general bimachine emits a word, so the run is a concatenation and output
positions need not track input positions. A **letter-to-letter** bimachine emits exactly
one symbol per cell ([sakarovitch-2009] §IV.6); the function it computes is then
*length-preserving*, and the positional description below holds. -/

/-- A witness that `B` is *letter-to-letter*: every cell emits exactly one symbol, named
by `cell`. -/
structure LetterToLetter (B : Bimachine L R α β) where
  /-- The single symbol emitted at a cell. -/
  cell : L → α → R → β
  /-- Every cell emits exactly that one symbol. -/
  output_eq : ∀ l a r, B.output l a r = [cell l a r]

/-- `B` is letter-to-letter when it admits a `LetterToLetter` witness. -/
def IsLetterToLetter (B : Bimachine L R α β) : Prop := Nonempty B.LetterToLetter

namespace LetterToLetter

variable {B}

/-- The run of a letter-to-letter bimachine has the length of its input. -/
@[simp] theorem length_runFrom (w : B.LetterToLetter) (l : L) (xs : List α) :
    (B.runFrom l xs).length = xs.length := by
  induction xs generalizing l <;> simp [w.output_eq, *]

@[simp] theorem length_run (w : B.LetterToLetter) (xs : List α) :
    (B.run xs).length = xs.length :=
  w.length_runFrom B.lInit xs

/-- Output coordinate `i` reads the left state after the length-`i` prefix and the
right state of the strict suffix. -/
theorem getElem?_runFrom (w : B.LetterToLetter) (l : L) (xs : List α) (i : ℕ) :
    (B.runFrom l xs)[i]? = xs[i]?.map fun a =>
      w.cell (B.lStateAfter l (xs.take i)) a (B.rState (xs.drop (i + 1))) := by
  induction xs generalizing l i <;> cases i <;> simp [w.output_eq, *]

/-- Output `i` is `cell (lState (x.take i)) (x i) (rState (x.drop (i+1)))`. -/
theorem getElem?_run (w : B.LetterToLetter) (x : List α) (i : ℕ) :
    (B.run x)[i]? = x[i]?.map fun a =>
      w.cell (B.lState (x.take i)) a (B.rState (x.drop (i + 1))) :=
  w.getElem?_runFrom B.lInit x i

end LetterToLetter

/-! ### Transport along state equivalences -/

variable {L' R' : Type*}

/-- Transport a bimachine along equivalences on the two state spaces. -/
@[simps]
def map (eL : L ≃ L') (eR : R ≃ R') (B : Bimachine L R α β) : Bimachine L' R' α β where
  lInit := eL B.lInit
  lStep l a := eL (B.lStep (eL.symm l) a)
  rInit := eR B.rInit
  rStep r a := eR (B.rStep (eR.symm r) a)
  output l a r := B.output (eL.symm l) a (eR.symm r)

@[simp] theorem map_refl : map (Equiv.refl L) (Equiv.refl R) B = B := rfl

@[simp] theorem map_map {L'' R'' : Type*} (eL : L ≃ L') (eR : R ≃ R') (eL' : L' ≃ L'')
    (eR' : R' ≃ R'') : map eL' eR' (map eL eR B) = map (eL.trans eL') (eR.trans eR') B := rfl

@[simp] theorem lStateAfter_map (eL : L ≃ L') (eR : R ≃ R') (l' : L') (pre : List α) :
    (map eL eR B).lStateAfter l' pre = eL (B.lStateAfter (eL.symm l') pre) := by
  induction pre generalizing l' <;> simp [*]

@[simp] theorem lState_map (eL : L ≃ L') (eR : R ≃ R') (pre : List α) :
    (map eL eR B).lState pre = eL (B.lState pre) := by
  simp [lState]

@[simp] theorem rState_map (eL : L ≃ L') (eR : R ≃ R') (suf : List α) :
    (map eL eR B).rState suf = eR (B.rState suf) :=
  List.foldr_hom eR fun x y => by simp

@[simp] theorem runFrom_map (eL : L ≃ L') (eR : R ≃ R') (l' : L') (xs : List α) :
    (map eL eR B).runFrom l' xs = B.runFrom (eL.symm l') xs := by
  induction xs generalizing l' <;> simp [*]

@[simp] theorem run_map (eL : L ≃ L') (eR : R ≃ R') :
    (map eL eR B).run = B.run := by
  funext xs; simp [run]

/-- `map` as an equivalence of bimachines. -/
def reindex (eL : L ≃ L') (eR : R ≃ R') : Bimachine L R α β ≃ Bimachine L' R' α β where
  toFun := map eL eR
  invFun := map eL.symm eR.symm
  left_inv B := by simp
  right_inv B := by simp

@[simp] theorem coe_reindex (eL : L ≃ L') (eR : R ≃ R') :
    ⇑(reindex (α := α) (β := β) eL eR) = map eL eR := rfl

@[simp] theorem symm_reindex (eL : L ≃ L') (eR : R ≃ R') :
    (reindex (α := α) (β := β) eL eR).symm = reindex eL.symm eR.symm := rfl

/-- Cells agree exactly when the underlying word-valued outputs do. -/
theorem LetterToLetter.cell_inj {B : Bimachine L R α β} (w : B.LetterToLetter)
    {l l' : L} {a a' : α} {r r' : R} :
    w.cell l a r = w.cell l' a' r' ↔ B.output l a r = B.output l' a' r' := by
  rw [w.output_eq, w.output_eq]; simp

/-- Letter-to-letter-ness transports along state reindexing. -/
def LetterToLetter.map {L' R' : Type*} {B : Bimachine L R α β} (w : B.LetterToLetter)
    (eL : L ≃ L') (eR : R ≃ R') : (Bimachine.map eL eR B).LetterToLetter :=
  ⟨fun l a r => w.cell (eL.symm l) a (eR.symm r), fun _ _ _ => w.output_eq _ _ _⟩

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
  output l a r := [out l a r]

@[simp] theorem ofFlags_lInit : (ofFlags pL pR out).lInit = false := rfl
@[simp] theorem ofFlags_lStep (l : Bool) (a : α) :
    (ofFlags pL pR out).lStep l a = (l || pL a) := rfl
@[simp] theorem ofFlags_rInit : (ofFlags pL pR out).rInit = false := rfl
@[simp] theorem ofFlags_rStep (r : Bool) (a : α) :
    (ofFlags pL pR out).rStep r a = (r || pR a) := rfl
@[simp] theorem ofFlags_output (l : Bool) (a : α) (r : Bool) :
    (ofFlags pL pR out).output l a r = [out l a r] := rfl

/-- A flag bimachine is letter-to-letter, with `out` as its cell. -/
def ofFlags_letterToLetter : (ofFlags pL pR out).LetterToLetter := ⟨out, fun _ _ _ => rfl⟩

@[simp] theorem ofFlags_lState (xs : List α) : (ofFlags pL pR out).lState xs = xs.any pL :=
  List.foldl_or pL false xs

@[simp] theorem ofFlags_rState (xs : List α) : (ofFlags pL pR out).rState xs = xs.any pR :=
  List.foldr_or pR false xs

/-- Output `i` of a flag bimachine sees the input symbol and the two window-`any`
flags. -/
theorem getElem?_ofFlags_run (x : List α) (i : ℕ) :
    ((ofFlags pL pR out).run x)[i]?
      = x[i]?.map fun a => out ((x.take i).any pL) a ((x.drop (i + 1)).any pR) := by
  simp [(ofFlags_letterToLetter pL pR out).getElem?_run, ofFlags_letterToLetter]

end Bimachine

/-! ### Sequential machines as bimachines -/

section ToBimachine

variable {σ : Type*} (T : Mealy σ α β)

/-- A sequential machine as the bimachine whose left automaton does all the work and
whose right automaton is trivial. -/
@[simps]
def Mealy.toBimachine : Bimachine σ Unit α β where
  lInit := T.initial
  lStep := T.step
  rInit := ()
  rStep _ _ := ()
  output l a _ := [T.output l a]

@[simp] theorem Mealy.toBimachine_runFrom (s : σ) (xs : List α) :
    T.toBimachine.runFrom s xs = T.runFrom s xs := by
  induction xs generalizing s <;> simp [*]

/-- The bimachine view computes the same string function. -/
@[simp] theorem Mealy.toBimachine_run : T.toBimachine.run = T.run :=
  funext fun xs => T.toBimachine_runFrom T.initial xs

end ToBimachine

/-! ### The bimachine-computable class -/

/-- Computability by a finite bimachine — classically, the total rational functions
preserving the empty word. -/
def IsBimachineComputable (f : List α → List β) : Prop :=
  ∃ (L : Type) (_ : Fintype L) (R : Type) (_ : Fintype R) (B : Bimachine L R α β),
    B.run = f

/-- `f` is bimachine-computable if and only if it is computed by a finite bimachine
with state types in any universes. -/
theorem isBimachineComputable_iff.{v, w} {f : List α → List β} :
    IsBimachineComputable f
      ↔ ∃ (L : Type v) (_ : Fintype L) (R : Type w) (_ : Fintype R)
          (B : Bimachine L R α β), B.run = f :=
  exists_fintype₂_congr
    (fun eL eR ⟨B, hB⟩ => ⟨.map eL eR B, (B.run_map eL eR).trans hB⟩)
    (fun eL eR ⟨B, hB⟩ => ⟨.map eL eR B, (B.run_map eL eR).trans hB⟩)

/-- Every finite-state bimachine computes a bimachine-computable function, whatever
the universes of its state types. -/
theorem Bimachine.isBimachineComputable {L R : Type*} [Fintype L] [Fintype R]
    (B : Bimachine L R α β) : IsBimachineComputable B.run :=
  isBimachineComputable_iff.mpr ⟨L, inferInstance, R, inferInstance, B, rfl⟩

/-- Computability by a finite **letter-to-letter** bimachine: the total
length-preserving rational functions. -/
def IsLengthPreservingBimachineComputable (f : List α → List β) : Prop :=
  ∃ (L : Type) (_ : Fintype L) (R : Type) (_ : Fintype R) (B : Bimachine L R α β),
    B.IsLetterToLetter ∧ B.run = f

/-- `f` is computed by a finite letter-to-letter bimachine iff it is computed by one with
state types in any universes. -/
theorem isLengthPreservingBimachineComputable_iff.{v, w} {f : List α → List β} :
    IsLengthPreservingBimachineComputable f
      ↔ ∃ (L : Type v) (_ : Fintype L) (R : Type w) (_ : Fintype R)
          (B : Bimachine L R α β), B.IsLetterToLetter ∧ B.run = f :=
  exists_fintype₂_congr
    (fun eL eR ⟨B, ⟨w⟩, hB⟩ =>
      ⟨.map eL eR B, ⟨w.map eL eR⟩, (B.run_map eL eR).trans hB⟩)
    (fun eL eR ⟨B, ⟨w⟩, hB⟩ =>
      ⟨.map eL eR B, ⟨w.map eL eR⟩, (B.run_map eL eR).trans hB⟩)

/-- A length-preserving bimachine-computable function is bimachine-computable. -/
theorem IsBimachineComputable.of_lengthPreserving {f : List α → List β}
    (h : IsLengthPreservingBimachineComputable f) : IsBimachineComputable f :=
  have ⟨L, _, R, _, B, _, hB⟩ := h
  ⟨L, ‹_›, R, ‹_›, B, hB⟩

/-- Functions computed by letter-to-letter bimachines are length-preserving. -/
theorem IsLengthPreservingBimachineComputable.length_eq {f : List α → List β}
    (h : IsLengthPreservingBimachineComputable f) (x : List α) : (f x).length = x.length :=
  have ⟨_, _, _, _, _, ⟨w⟩, hB⟩ := h
  hB ▸ w.length_run x

/-- A Mealy-computable function is bimachine-computable (`Mealy.toBimachine`). -/
theorem IsBimachineComputable.of_mealyComputable {f : List α → List β}
    (h : IsMealyComputable f) : IsBimachineComputable f :=
  have ⟨_, _, T, hT⟩ := h
  hT ▸ T.toBimachine_run ▸ T.toBimachine.isBimachineComputable
