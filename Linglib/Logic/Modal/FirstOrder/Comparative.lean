import Linglib.Core.ModelTheory.FiniteModel
import Linglib.Core.Order.TotalPreorder
import Linglib.Core.Order.ComparativeProbability.Systems

/-!
# Comparative possibility over a first-order base

This file defines `CompFormula`, Lewis's comparative-possibility language
over an embedded classical first-order layer, and its truth relation
`Realize` at an index of an ordered family of structures: `A ≻ B` holds
when some (A ∧ ¬B)-index in the cone strictly dominates every
(B ∧ ¬A)-index. `realize_comp_iff_strict_dominationLift` identifies ≻
with the strict domination lift of the ordering — Lewis's lift, which is
also the lift of Kratzer's ordering semantics.

## References

* [lewis-1973] — comparative possibility
* [holliday-icard-2013] — the lift taxonomy; ≻ as the strict l-lifting
* [kratzer-1991] — ordering semantics; [kratzer-2012] — difference sets
* [halpern-2003] — the complete logic WJR
* [rudolph-kocurek-2024] — interpretations as indices
-/

namespace FirstOrder.Language

variable {L : Language} {I W E : Type*}

/-- The extension of a unary relation symbol in a structure carried as a
term. -/
def Structure.ext₁ (S : L.Structure E) (R : L.Relations 1) : Set E :=
  {e | S.RelMap R ![e]}

@[simp] theorem Structure.mem_ext₁ {S : L.Structure E} {R : L.Relations 1}
    {e : E} : e ∈ S.ext₁ R ↔ S.RelMap R ![e] :=
  Iff.rfl

instance (S : L.Structure E) (R : L.Relations 1) (e : E)
    [h : Decidable (S.RelMap R ![e])] : Decidable (e ∈ S.ext₁ R) :=
  h

/-- Pointwise decidability of atoms across a doubly-indexed structure family —
the hook that makes `decide` available on finite models; the semantics itself
is decidability-free. -/
abbrev DecidableAtoms (interp : I → W → L.Structure E) :=
  ∀ (i : I) (w : W) (n : ℕ) (r : L.Relations n) (x : Fin n → E),
    Decidable ((interp i w).RelMap r x)

/-- Comparative-possibility formulas: an embedded classical formula (free
variables valued by domain elements), booleans, and the comparative ≻
(`.comp`). Booleans exist at both layers because negation and the derived
`equi` must scope over ≻. -/
inductive CompFormula (L : Language) (E : Type*) where
  | ofFormula : L.Formula E → CompFormula L E
  | not : CompFormula L E → CompFormula L E
  | inf : CompFormula L E → CompFormula L E → CompFormula L E
  | sup : CompFormula L E → CompFormula L E → CompFormula L E
  | comp : CompFormula L E → CompFormula L E → CompFormula L E

namespace CompFormula

open Core.Order (TotalPreorder)
open ComparativeProbability

/-- Ground unary predication `R(e)`, as an embedded formula. -/
abbrev matom (R : L.Relations 1) (e : E) : CompFormula L E :=
  .ofFormula (R.formula ![Term.var e])

/-- Equipossibility: `A ≈ B := ¬(A ≻ B) ∧ ¬(B ≻ A)`. -/
def equi (A B : CompFormula L E) : CompFormula L E :=
  .inf (.not (.comp A B)) (.not (.comp B A))

/-- Formulas free of the comparative: the fragment whose truth does not
consult the ordering (`CompFree.realize_congr`). -/
def CompFree : CompFormula L E → Prop
  | .ofFormula _ => True
  | .not A => A.CompFree
  | .inf A B => A.CompFree ∧ B.CompFree
  | .sup A B => A.CompFree ∧ B.CompFree
  | .comp _ _ => False

variable (interp : I → W → L.Structure E)

/-- Truth at an index of an ordered structure family, relative to a raw
ordering relation `le` (restricted orderings need not be total). The
comparative: some (A∧¬B)-index in the ≤-cone strictly dominates every
(B∧¬A)-index. -/
def Realize (φ : CompFormula L E) (le : I → I → Prop) (i : I) (w : W) : Prop :=
  match φ with
  | .ofFormula ψ => letI := interp i w; ψ.Realize id
  | .not A => ¬ Realize A le i w
  | .inf A B => Realize A le i w ∧ Realize B le i w
  | .sup A B => Realize A le i w ∨ Realize B le i w
  | .comp A B =>
      coneStrictLift le (fun b a => le b a ∧ ¬ le a b)
        (fun j => Realize A le j w) (fun j => Realize B le j w) i

instance instDec [Fintype I] [Fintype E] [DecidableEq E]
    [hA : DecidableAtoms interp]
    (φ : CompFormula L E) (le : I → I → Prop) [DecidableRel le] (i : I) (w : W) :
    Decidable (Realize interp φ le i w) :=
  match φ with
  | .ofFormula ψ =>
      @Formula.decRealize L E (interp i w) _ _ (fun n r x => hA i w n r x) E ψ id
  | .not A =>
      haveI := instDec A le i w
      inferInstanceAs (Decidable (¬ Realize interp A le i w))
  | .inf A B =>
      haveI := instDec A le i w
      haveI := instDec B le i w
      inferInstanceAs (Decidable (Realize interp A le i w ∧ Realize interp B le i w))
  | .sup A B =>
      haveI := instDec A le i w
      haveI := instDec B le i w
      inferInstanceAs (Decidable (Realize interp A le i w ∨ Realize interp B le i w))
  | .comp A B =>
      haveI : DecidablePred (fun j => Realize interp A le j w) :=
        fun j => instDec A le j w
      haveI : DecidablePred (fun j => Realize interp B le j w) :=
        fun j => instDec B le j w
      inferInstanceAs (Decidable (coneStrictLift
        le (fun b a => le b a ∧ ¬ le a b)
        (fun j => Realize interp A le j w) (fun j => Realize interp B le j w) i))

variable {interp} {A B : CompFormula L E} {le : I → I → Prop}
  {ord : TotalPreorder I} {i : I} {w : W}

/-- The comparative clause over a total preorder — definitional; the rewriting
interface, with the domination conjunction packaged as `ord.lt`. -/
theorem realize_comp_iff :
    Realize interp (.comp A B) ord.le i w ↔
    ∃ i', ord.le i' i ∧ Realize interp A ord.le i' w ∧
      ¬ Realize interp B ord.le i' w ∧
      ∀ i'', ord.le i'' i → Realize interp B ord.le i'' w →
        ¬ Realize interp A ord.le i'' w → ord.lt i'' i' :=
  Iff.rfl

/-- Realization of a ground unary atom. -/
@[simp] theorem realize_matom (R : L.Relations 1) (e : E) :
    Realize interp (.matom R e) le i w ↔ (interp i w).RelMap R ![e] := by
  let _S : L.Structure E := interp i w
  show @Formula.Realize L E (interp i w) E (R.formula ![Term.var e]) id ↔ _
  have hv : (fun j => ((![Term.var e] : Fin 1 → L.Term E) j).realize (M := E) id)
      = ![e] := funext fun j => by rw [Subsingleton.elim j 0]; simp
  rw [Formula.realize_rel, hv]

/-- Comparative-free formulas are ordering-invariant. -/
theorem CompFree.realize_congr :
    ∀ {φ : CompFormula L E}, φ.CompFree →
      ∀ {le le' : I → I → Prop} {i : I} {w : W},
      Realize interp φ le i w ↔ Realize interp φ le' i w
  | .ofFormula _, _ => Iff.rfl
  | .not A, h => not_congr (CompFree.realize_congr (show A.CompFree from h))
  | .inf _ _, h => and_congr (CompFree.realize_congr h.1) (CompFree.realize_congr h.2)
  | .sup _ _, h => or_congr (CompFree.realize_congr h.1) (CompFree.realize_congr h.2)
  | .comp _ _, h => h.elim

/-- ≻ is the *strict l-lifting* of the ordering ([holliday-icard-2013];
Lewis's lifting) applied to the cone at the evaluation index: comparative
possibility, with the ∃∀ clause as the strict Smyth order via
`strict_dominationLift_iff`. -/
theorem realize_comp_iff_strict_dominationLift :
    Realize interp (.comp A B) ord.le i w ↔
    Strict
      (dominationLift (fun a b => ord.le b a))
      {x | ord.le x i ∧ Realize interp A ord.le x w ∧
        ¬ Realize interp B ord.le x w}
      {x | ord.le x i ∧ Realize interp B ord.le x w ∧
        ¬ Realize interp A ord.le x w} :=
  coneStrictLift_iff_strict_dominationLift
    (fun a b => ord.le_total b a) (fun _ _ => Iff.rfl) _ _ _

/-- ≻ is irreflexive — a witness would make A both true and false. -/
theorem not_realize_comp_self : ¬ Realize interp (.comp A A) le i w :=
  fun ⟨_, _, hA, hnA, _⟩ => hnA hA

/-- ≈ is reflexive. -/
theorem realize_equi_self : Realize interp (A.equi A) le i w :=
  ⟨not_realize_comp_self, not_realize_comp_self⟩

/-- ≈ is symmetric. -/
theorem realize_equi_comm :
    Realize interp (A.equi B) le i w ↔ Realize interp (B.equi A) le i w :=
  and_comm

end CompFormula

end FirstOrder.Language
