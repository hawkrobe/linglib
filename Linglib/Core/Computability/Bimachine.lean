/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Computability.Mealy
import Linglib.Core.Computability.Subregular.Function.Dependence
import Linglib.Core.Data.List.Fold

/-!
# Bimachines and non-interaction

A `Bimachine` ([schutzenberger-1961]; [eilenberg-1974]) reads its input in both
directions: a left automaton scans `→`, a right automaton scans `←`, and output `i` is
`output (lState (x.take i)) (x i) (rState (x.drop (i+1)))`. Word-output bimachines
compute exactly the rational functions ([elgot-mezei-1965]; they are the transducers of
[schutzenberger-1976]'s semi-monomial representations, see [sakarovitch-2009]); the
letter-to-letter machines here compute the total length-preserving ones.

A bimachine over a single alphabet is **non-interacting** when its output is a union of
conflict-free one-sided change-rules over the identity: each side may add its own
change, the sides agree wherever both fire, and neither can suppress the other's.
`IsNonInteractingBimachineComputable` is computability by such a bimachine — an extra
restriction on the Elgot–Mezei factorization, not a consequence of it.

## Main definitions

* `Bimachine L R α β`: machine with left states `L`, right states `R`, alphabets `α`, `β`
* `Bimachine.run`: the computed function
* `IsBimachineComputable f`: `f` is computed by some finite bimachine
* `Bimachine.IsNonInteracting`: the cell output is a conflict-free union of one-sided
  change-rules over the identity
* `IsNonInteractingBimachineComputable f`: `f` is computed by some non-interacting
  finite bimachine

## Main theorems

* `Bimachine.getElem?_run`: output `i` is
  `output (lState (x.take i)) (x i) (rState (x.drop (i+1)))`
* `RequiresBothSides.not_isNonInteractingBimachineComputable`: a map whose target needs
  both sides at once is computed by no non-interacting bimachine
* `setOf_isNonInteractingBimachineComputable_ssubset`: the non-interacting class is
  proper inside the bimachine-computable functions

## Implementation notes

Only the left state is threaded through the run (`Bimachine.runFrom`); the recursion
reads each tail's right state on the spot. The class existentials pin state types at
`Type 0`; the universe-polymorphic `isBimachineComputable_iff` and
`isNonInteractingBimachineComputable_iff` recover generality. The identification of
`IsBimachineComputable` with the total length-preserving regular functions is classical
and not formalized here.

[UPSTREAM] candidate: `Mathlib.Computability.Bimachine`.
-/

namespace Subregular

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
  /-- The symbol emitted from the two context states and the current input symbol. -/
  output : L → α → R → β

instance [Inhabited L] [Inhabited R] [Inhabited β] : Inhabited (Bimachine L R α β) :=
  ⟨⟨default, fun _ _ => default, default, fun _ _ => default, fun _ _ _ => default⟩⟩

namespace Bimachine

variable (B : Bimachine L R α β)

/-- `B.lStateAfter l pre` is the left state reached from `l` after scanning `pre`. -/
def lStateAfter (l : L) : List α → L := List.foldl B.lStep l

/-- Left state after scanning a prefix left-to-right from the start state. -/
def lState : List α → L := B.lStateAfter B.lInit

/-- Right state after scanning a suffix right-to-left. -/
def rState (suf : List α) : R := suf.foldr (fun a r => B.rStep r a) B.rInit

@[simp] theorem lStateAfter_nil (l : L) : B.lStateAfter l [] = l := rfl
@[simp] theorem lStateAfter_cons (l : L) (x : α) (xs : List α) :
    B.lStateAfter l (x :: xs) = B.lStateAfter (B.lStep l x) xs := rfl
@[simp] theorem lState_nil : B.lState [] = B.lInit := rfl
@[simp] theorem rState_nil : B.rState [] = B.rInit := rfl
@[simp] theorem rState_cons (x : α) (xs : List α) :
    B.rState (x :: xs) = B.rStep (B.rState xs) x := rfl

/-- `B.runFrom l x` runs `B` on `x` threading the left state from `l`; each tail's
right state is read on the spot. -/
def runFrom : L → List α → List β
  | _, [] => []
  | l, x :: xs => B.output l x (B.rState xs) :: runFrom (B.lStep l x) xs

/-- The computed function. -/
def run : List α → List β := B.runFrom B.lInit

@[simp] theorem runFrom_nil (l : L) : B.runFrom l [] = [] := rfl
@[simp] theorem runFrom_cons (l : L) (x : α) (xs : List α) :
    B.runFrom l (x :: xs) = B.output l x (B.rState xs) :: B.runFrom (B.lStep l x) xs := rfl

/-- The run is length-preserving (one output symbol per input symbol). -/
@[simp] theorem length_runFrom (l : L) (xs : List α) :
    (B.runFrom l xs).length = xs.length := by
  induction xs generalizing l <;> simp [*]

@[simp] theorem length_run (xs : List α) : (B.run xs).length = xs.length :=
  B.length_runFrom B.lInit xs

/-- Output coordinate `i` reads the left state after the length-`i` prefix and the
right state of the strict suffix. -/
theorem getElem?_runFrom (l : L) (xs : List α) (i : ℕ) :
    (B.runFrom l xs)[i]? = xs[i]?.map fun a =>
      B.output (B.lStateAfter l (xs.take i)) a (B.rState (xs.drop (i + 1))) := by
  induction xs generalizing l i <;> cases i <;> simp [*]

/-- Output `i` is `output (lState (x.take i)) (x i) (rState (x.drop (i+1)))`. -/
theorem getElem?_run (x : List α) (i : ℕ) :
    (B.run x)[i]? = x[i]?.map fun a =>
      B.output (B.lState (x.take i)) a (B.rState (x.drop (i + 1))) :=
  B.getElem?_runFrom B.lInit x i

/-! ### Reindexing states -/

variable {L' R' : Type*}

/-- Lifts equivalences on the two state spaces to an equivalence on bimachines. -/
@[simps apply_lInit apply_lStep apply_rInit apply_rStep apply_output]
def reindex (eL : L ≃ L') (eR : R ≃ R') : Bimachine L R α β ≃ Bimachine L' R' α β where
  toFun B := {
    lInit := eL B.lInit
    lStep := fun l a => eL (B.lStep (eL.symm l) a)
    rInit := eR B.rInit
    rStep := fun r a => eR (B.rStep (eR.symm r) a)
    output := fun l a r => B.output (eL.symm l) a (eR.symm r)
  }
  invFun B := {
    lInit := eL.symm B.lInit
    lStep := fun l a => eL.symm (B.lStep (eL l) a)
    rInit := eR.symm B.rInit
    rStep := fun r a => eR.symm (B.rStep (eR r) a)
    output := fun l a r => B.output (eL l) a (eR r)
  }
  left_inv B := by simp
  right_inv B := by simp

@[simp] theorem reindex_refl : reindex (Equiv.refl L) (Equiv.refl R) B = B := rfl

@[simp] theorem symm_reindex (eL : L ≃ L') (eR : R ≃ R') :
    (reindex (α := α) (β := β) eL eR).symm = reindex eL.symm eR.symm := rfl

@[simp] theorem lStateAfter_reindex (eL : L ≃ L') (eR : R ≃ R') (l' : L') (pre : List α) :
    (reindex eL eR B).lStateAfter l' pre = eL (B.lStateAfter (eL.symm l') pre) := by
  induction pre generalizing l' <;> simp [*]

@[simp] theorem lState_reindex (eL : L ≃ L') (eR : R ≃ R') (pre : List α) :
    (reindex eL eR B).lState pre = eL (B.lState pre) := by
  simp [lState]

@[simp] theorem rState_reindex (eL : L ≃ L') (eR : R ≃ R') (suf : List α) :
    (reindex eL eR B).rState suf = eR (B.rState suf) :=
  List.foldr_hom eR fun x y => by simp

@[simp] theorem runFrom_reindex (eL : L ≃ L') (eR : R ≃ R') (l' : L') (xs : List α) :
    (reindex eL eR B).runFrom l' xs = B.runFrom (eL.symm l') xs := by
  induction xs generalizing l' <;> simp [*]

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
  output := out

@[simp] theorem ofFlags_lInit : (ofFlags pL pR out).lInit = false := rfl
@[simp] theorem ofFlags_lStep (l : Bool) (a : α) :
    (ofFlags pL pR out).lStep l a = (l || pL a) := rfl
@[simp] theorem ofFlags_rInit : (ofFlags pL pR out).rInit = false := rfl
@[simp] theorem ofFlags_rStep (r : Bool) (a : α) :
    (ofFlags pL pR out).rStep r a = (r || pR a) := rfl
@[simp] theorem ofFlags_output : (ofFlags pL pR out).output = out := rfl

@[simp] theorem ofFlags_lState (xs : List α) : (ofFlags pL pR out).lState xs = xs.any pL :=
  List.foldl_or pL false xs

@[simp] theorem ofFlags_rState (xs : List α) : (ofFlags pL pR out).rState xs = xs.any pR :=
  List.foldr_or pR false xs

/-- Output `i` of a flag bimachine sees the input symbol and the two window-`any`
flags. -/
theorem getElem?_ofFlags_run (x : List α) (i : ℕ) :
    ((ofFlags pL pR out).run x)[i]?
      = x[i]?.map fun a => out ((x.take i).any pL) a ((x.drop (i + 1)).any pR) := by
  simp [getElem?_run]

end Bimachine

/-! ### Sequential machines as bimachines -/

section ToBimachine

variable {σ : Type*}

/-- A sequential machine as the bimachine whose left automaton does all the work and
whose right automaton is trivial. -/
@[simps]
def Mealy.toBimachine (T : Mealy σ α β) : Bimachine σ Unit α β where
  lInit := T.initial
  lStep := T.step
  rInit := ()
  rStep _ _ := ()
  output l a _ := T.output l a

@[simp] theorem Mealy.toBimachine_runFrom (T : Mealy σ α β) (s : σ) (xs : List α) :
    T.toBimachine.runFrom s xs = T.runFrom s xs := by
  induction xs generalizing s <;> simp [*]

/-- The bimachine view computes the same string function. -/
@[simp] theorem Mealy.toBimachine_run (T : Mealy σ α β) : T.toBimachine.run = T.run :=
  funext fun xs => T.toBimachine_runFrom T.initial xs

end ToBimachine

/-! ### The bimachine-computable class -/

/-- Computability by a finite bimachine — the total length-preserving regular
functions (the identification is classical; see the module docstring). -/
def IsBimachineComputable (f : List α → List β) : Prop :=
  ∃ (L R : Type) (_ : Fintype L) (_ : Fintype R) (B : Bimachine L R α β), B.run = f

/-- Every finite-state bimachine computes a bimachine-computable function, whatever
the universes of its state types. -/
theorem Bimachine.isBimachineComputable {L R : Type*} [Fintype L] [Fintype R]
    (B : Bimachine L R α β) : IsBimachineComputable B.run :=
  ⟨Fin (Fintype.card L), Fin (Fintype.card R), inferInstance, inferInstance,
    Bimachine.reindex (Fintype.equivFin L) (Fintype.equivFin R) B, B.run_reindex _ _⟩

/-- `f` is bimachine-computable if and only if it is computed by a finite bimachine
with state types in any universes. -/
theorem isBimachineComputable_iff.{v, w} {f : List α → List β} :
    IsBimachineComputable f
      ↔ ∃ (L : Type v) (R : Type w) (_ : Fintype L) (_ : Fintype R)
          (B : Bimachine L R α β), B.run = f :=
  ⟨fun ⟨L, R, _, _, B, h⟩ => ⟨ULift L, ULift R, inferInstance, inferInstance,
      Bimachine.reindex Equiv.ulift.symm Equiv.ulift.symm B, h ▸ B.run_reindex _ _⟩,
   fun ⟨_, _, _, _, B, h⟩ => h ▸ B.isBimachineComputable⟩

/-- Bimachine-computable functions are length-preserving. -/
theorem IsBimachineComputable.length_eq {f : List α → List β}
    (h : IsBimachineComputable f) (x : List α) : (f x).length = x.length := by
  obtain ⟨L, R, _, _, B, rfl⟩ := h
  exact B.length_run x

/-- A Mealy-computable function is bimachine-computable (`Mealy.toBimachine`). -/
theorem IsBimachineComputable.of_mealyComputable {f : List α → List β}
    (h : IsMealyComputable f) : IsBimachineComputable f := by
  obtain ⟨σ, _, T, rfl⟩ := h
  exact T.toBimachine_run ▸ T.toBimachine.isBimachineComputable

/-! ### Non-interacting bimachines -/

section NonInteraction

variable [DecidableEq α]

namespace Bimachine

/-- `unite cL cR a` takes the left proposal if it fires (`≠ a`), else the right one —
the union of two change proposals over the identity default `a`. The tie-break is
asymmetric (when both fire the left wins) but inert under the conflict-freedom
`IsNonInteracting` requires. -/
def unite (cL cR a : α) : α := if cL = a then cR else cL

/-- With the right proposal inert, the union is whatever the left one proposes. -/
@[simp] theorem unite_right_self (cL a : α) : unite cL a a = cL := by
  unfold unite; split_ifs with h <;> simp [h]

/-- With the left proposal inert, the union is whatever the right one proposes. -/
@[simp] theorem unite_left_self (cR a : α) : unite a cR a = cR := by
  simp [unite]

/-- A firing left proposal wins. -/
theorem unite_of_left_ne {cL a : α} (h : cL ≠ a) (cR : α) : unite cL cR a = cL := if_neg h

/-- The combined value is the default exactly when *both* one-sided proposals are
inert. -/
@[simp] theorem unite_eq_self_iff {cL cR a : α} : unite cL cR a = a ↔ cL = a ∧ cR = a := by
  unfold unite; split_ifs <;> simp_all

/-- A bimachine over a single alphabet is non-interacting when its cell output is a
union of conflict-free one-sided change-rules over the identity default — `ωL` and `ωR`
each propose a change for their side, the two agree wherever both fire, and the output
takes whichever fires, else leaves the symbol unchanged. Neither side can *suppress*
the other's change; that suppression is exactly what interaction would require. -/
def IsNonInteracting (B : Bimachine L R α α) : Prop :=
  ∃ (ωL : L → α → α) (ωR : R → α → α),
    (∀ l r a, ωL l a ≠ a → ωR r a ≠ a → ωL l a = ωR r a) ∧
    ∀ l a r, B.output l a r = unite (ωL l a) (ωR r a) a

/-- The output at a cell is determined by one side alone: fixing the input symbol and
one context state already fixes it. -/
def OneSidedAt (B : Bimachine L R α β) (l : L) (a : α) (r : R) : Prop :=
  (∀ r', B.output l a r' = B.output l a r) ∨ (∀ l', B.output l' a r = B.output l a r)

/-- At every cell whose output differs from the input symbol, a non-interacting
bimachine is one-sided: the change is the left rule's alone or the right rule's alone.
Conflict-freedom is what makes the firing side's value independent of the other side's
state. -/
theorem IsNonInteracting.oneSidedAt_of_change {B : Bimachine L R α α}
    (h : B.IsNonInteracting) {l : L} {a : α} {r : R} (hne : B.output l a r ≠ a) :
    B.OneSidedAt l a r := by
  obtain ⟨ωL, ωR, hcf, hω⟩ := h
  by_cases hL : ωL l a = a
  · have hR : ωR r a ≠ a := fun hR => hne (by simp only [hω, hL, hR, unite_left_self])
    refine .inr fun l' => ?_
    by_cases hL' : ωL l' a = a
    · simp only [hω, hL, hL', unite_left_self]
    · simp only [hω, hL, unite_left_self, unite_of_left_ne hL']
      exact hcf l' r a hL' hR
  · exact .inl fun r' => by simp only [hω, unite_of_left_ne hL]

/-- Under a non-interacting cell decomposition, a word whose run leaves target `i`
unchanged has both of its change-proposals inert there. -/
theorem inert_of_reverting {B : Bimachine L R α α} {ωL : L → α → α} {ωR : R → α → α}
    (hω : ∀ l a r, B.output l a r = unite (ωL l a) (ωR r a) a) {u : List α} {i : ℕ} {a : α}
    (hsym : u[i]? = some a) (hrev : (B.run u)[i]? = u[i]?) :
    ωL (B.lState (u.take i)) a = a ∧ ωR (B.rState (u.drop (i + 1))) a = a := by
  refine unite_eq_self_iff.mp (Option.some_injective _ (Eq.symm ?_))
  rw [← hsym, ← hrev, B.getElem?_run, hsym, Option.map_some, hω]

end Bimachine

/-- Computability by a non-interacting finite bimachine. -/
def IsNonInteractingBimachineComputable (f : List α → List α) : Prop :=
  ∃ (L R : Type) (_ : Fintype L) (_ : Fintype R) (B : Bimachine L R α α),
    B.run = f ∧ B.IsNonInteracting

/-- A function computed by a non-interacting bimachine is in particular
bimachine-computable. -/
theorem IsBimachineComputable.of_nonInteracting {f : List α → List α}
    (h : IsNonInteractingBimachineComputable f) : IsBimachineComputable f := by
  obtain ⟨L, R, _, _, B, rfl, _⟩ := h
  exact B.isBimachineComputable

/-- A non-interacting finite-state bimachine witnesses
`IsNonInteractingBimachineComputable` for its `run`, whatever the universes of its
state types: the one-sided rules survive the state-space transfer by composing with
`e.symm`. -/
theorem Bimachine.isNonInteractingBimachineComputable {L R : Type*} [Fintype L]
    [Fintype R] (B : Bimachine L R α α) (h : B.IsNonInteracting) :
    IsNonInteractingBimachineComputable B.run := by
  obtain ⟨ωL, ωR, hcf, hω⟩ := h
  exact ⟨Fin (Fintype.card L), Fin (Fintype.card R), inferInstance, inferInstance,
    Bimachine.reindex (Fintype.equivFin L) (Fintype.equivFin R) B, B.run_reindex _ _,
    fun l a => ωL ((Fintype.equivFin L).symm l) a,
    fun r a => ωR ((Fintype.equivFin R).symm r) a,
    fun l r a hL hR => hcf _ _ a hL hR, fun l a r => hω _ a _⟩

/-- `f` is computed by a non-interacting finite bimachine if and only if it is computed
by one with state types in any universes. -/
theorem isNonInteractingBimachineComputable_iff.{v, w} {f : List α → List α} :
    IsNonInteractingBimachineComputable f
      ↔ ∃ (L : Type v) (R : Type w) (_ : Fintype L) (_ : Fintype R)
          (B : Bimachine L R α α), B.run = f ∧ B.IsNonInteracting := by
  constructor
  · rintro ⟨L, R, _, _, B, rfl, ωL, ωR, hcf, hω⟩
    exact ⟨ULift L, ULift R, inferInstance, inferInstance,
      Bimachine.reindex Equiv.ulift.symm Equiv.ulift.symm B, B.run_reindex _ _,
      fun l a => ωL (Equiv.ulift.symm.symm l) a, fun r a => ωR (Equiv.ulift.symm.symm r) a,
      fun l r a hL hR => hcf _ _ a hL hR, fun l a r => hω _ a _⟩
  · rintro ⟨L, R, _, _, B, rfl, h⟩
    exact B.isNonInteractingBimachineComputable h

/-- Functions computed by non-interacting bimachines are length-preserving. -/
theorem IsNonInteractingBimachineComputable.length_eq {f : List α → List α}
    (h : IsNonInteractingBimachineComputable f) (x : List α) : (f x).length = x.length :=
  (IsBimachineComputable.of_nonInteracting h).length_eq x

/-- A Mealy-computable function is computed by a non-interacting bimachine: the
bimachine view (`Mealy.toBimachine`) has a trivial right automaton, so the cell output
is a one-sided rule with `ωR` the identity. -/
theorem IsNonInteractingBimachineComputable.of_mealyComputable {f : List α → List α}
    (h : IsMealyComputable f) : IsNonInteractingBimachineComputable f := by
  obtain ⟨σ, _, T, rfl⟩ := h
  exact T.toBimachine_run ▸ T.toBimachine.isNonInteractingBimachineComputable
    ⟨T.output, fun _ a => a, fun _ _ a _ h => absurd rfl h,
     fun l a r => (Bimachine.unite_right_self _ _).symm⟩

/-- A map that requires both sides is computed by no non-interacting bimachine. At the
witness the base changes but each far perturbation reverts: the right perturbation
keeps the left state, forcing `ωL` inert at this cell; the left perturbation keeps the
right state, forcing `ωR` inert; yet the base needs one of them to fire. -/
theorem RequiresBothSides.not_isNonInteractingBimachineComputable {f : List α → List α}
    (hf : RequiresBothSides f) : ¬ IsNonInteractingBimachineComputable f := by
  rintro ⟨L, R, _, _, B, rfl, ωL, ωR, -, hω⟩
  obtain ⟨base, i, hi, hchange, hw⟩ := hf 0
  obtain ⟨uL, ⟨-, hLag⟩, hLsym, hLrev⟩ := hw .left
  obtain ⟨uR, ⟨-, hRag⟩, hRsym, hRrev⟩ := hw .right
  simp only [Nat.sub_zero, Nat.add_zero] at hLag hRag
  -- decompose the base's cell, retarget each side's state to the perturbation that
  -- shares it, and silence both rules by `inert_of_reverting`
  apply hchange
  rw [B.getElem?_run, List.getElem?_eq_getElem hi, Option.map_some, hω,
    hRag.take_eq (by omega), hLag.drop_eq (by omega),
    (Bimachine.inert_of_reverting hω (hRsym.trans (List.getElem?_eq_getElem hi)) hRrev).1,
    (Bimachine.inert_of_reverting hω (hLsym.trans (List.getElem?_eq_getElem hi)) hLrev).2,
    Bimachine.unite_right_self]

end NonInteraction

/-! ### Strictness: non-interacting ⊊ bimachine-computable

A *conjunctive* change — a symbol flipped iff a mark occurs on **both** sides — is
bimachine-computable but `RequiresBothSides`, so no non-interacting bimachine computes
it. -/

/-- The three-symbol alphabet for the conjunctive witness — a `mark`, a `neutral`
symbol, and the `flipped` form the neutral symbol takes when both sides are marked. -/
inductive ConjSym | mark | neutral | flipped
  deriving DecidableEq, Repr, Fintype

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
  rw [conjBM, Bimachine.getElem?_ofFlags_run, getElem?_flankWord_mid h0 hk,
    any_take_flankWord (by decide) h0 (by omega),
    any_drop_flankWord (by decide) (by omega) (by omega)]
  simp

/-- The conjunctive change requires both sides: with a mark on each flank the medial
symbol flips, and demoting either mark alone reverts it — the three-map template
(`RequiresBothSides.of_flanks`) applied to a `d`-margined flank word. -/
theorem conjBM.requiresBothSides : RequiresBothSides conjBM.run :=
  .of_flanks (fill := .neutral) (on := .flipped) (xOn := .mark) (yOn := .mark)
    (xOff := .neutral) (yOff := .neutral) (n := fun d => 2 * d + 1) (t := fun d => d + 1)
    (by decide) (fun d => ⟨by omega, by omega⟩)
    (fun d => by rw [conjBM_flankWord (by omega) (by omega)]; rfl)
    (fun d => by rw [conjBM_flankWord (by omega) (by omega)]; rfl)
    (fun d => by rw [conjBM_flankWord (by omega) (by omega)]; rfl)

/-- The non-interacting class is proper inside the bimachine-computable functions —
`conjBM` is computed by a bimachine, but by no non-interacting one. -/
theorem setOf_isNonInteractingBimachineComputable_ssubset :
    {f : List ConjSym → List ConjSym | IsNonInteractingBimachineComputable f} ⊂
      {f | IsBimachineComputable f} :=
  ⟨fun _ h => IsBimachineComputable.of_nonInteracting h,
   fun h => conjBM.requiresBothSides.not_isNonInteractingBimachineComputable
     (h conjBM.isBimachineComputable)⟩

end Subregular
