import Linglib.Core.Logic.FirstOrder.FiniteModel
import Linglib.Core.Order.TotalPreorder
import Linglib.Core.Order.ComparativeProbability.Systems

/-!
# Comparative possibility over a first-order base

[lewis-1973]'s comparative possibility as a formula language: classical
first-order formulas embedded wholesale (the `ModalFormula.ofFormula`
pattern), boolean connectives, and a binary comparative `A ≻ B` (`.comp`)
evaluated at an index of an ordered family of structures — some
(A∧¬B)-index in the cone strictly dominates every (B∧¬A)-index.
`realize_comp_iff_strict_dominationLift` identifies ≻ with the strict
l-lifting of [holliday-icard-2013] §5 — Lewis's lift, which is also the lift
of [kratzer-1991]'s ordering semantics, with complete logic WJR
([halpern-2003]); comparing *difference sets* follows [kratzer-2012]'s revised
lifting. [rudolph-kocurek-2024] instantiates the language with
interpretations as indices.
-/

namespace FirstOrder.Language

/-- The extension of a unary relation symbol in a structure carried as a
term. -/
def Structure.ext₁ {L : Language} {E : Type*} (S : L.Structure E)
    (R : L.Relations 1) : Set E :=
  {e | @Structure.RelMap L E S 1 R ![e]}

@[simp] theorem Structure.mem_ext₁ {L : Language} {E : Type*}
    {S : L.Structure E} {R : L.Relations 1} {e : E} :
    e ∈ S.ext₁ R ↔ @Structure.RelMap L E S 1 R ![e] :=
  Iff.rfl

instance {L : Language} {E : Type*} (S : L.Structure E) (R : L.Relations 1)
    (e : E) [h : Decidable (@Structure.RelMap L E S 1 R ![e])] :
    Decidable (e ∈ S.ext₁ R) :=
  h

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

variable {L : Language} {E : Type*}

/-- Ground unary predication `R(e)`, as an embedded formula. -/
abbrev matom (R : L.Relations 1) (e : E) : CompFormula L E :=
  .ofFormula (R.formula ![Term.var e])

/-- Equipossibility: `A ≈ B := ¬(A ≻ B) ∧ ¬(B ≻ A)`. -/
def equi (A B : CompFormula L E) : CompFormula L E :=
  .inf (.not (.comp A B)) (.not (.comp B A))

/-- Formulas free of the comparative: the fragment whose truth does not
consult the ordering (`realize_congr_of_compFree`). -/
def CompFree : CompFormula L E → Prop
  | .ofFormula _ => True
  | .not A => A.CompFree
  | .inf A B => A.CompFree ∧ B.CompFree
  | .sup A B => A.CompFree ∧ B.CompFree
  | .comp _ _ => False

end CompFormula

/-- Pointwise decidability of atoms across a doubly-indexed structure family —
the hook that makes `decide` available on finite models; the semantics itself
is decidability-free. -/
abbrev DecidableAtoms {L : Language} {I W E : Type*}
    (interp : I → W → L.Structure E) :=
  ∀ (i : I) (w : W) (n : ℕ) (r : L.Relations n) (x : Fin n → E),
    Decidable (@Structure.RelMap L E (interp i w) n r x)

namespace CompFormula

open Core.Order (TotalPreorder)
open ComparativeProbability

variable {L : Language} {I W E : Type*} (interp : I → W → L.Structure E)

/-- Truth at an index of an ordered structure family, relative to a raw
ordering relation `le` (restricted orderings need not be total). The
comparative: some (A∧¬B)-index in the ≤-cone strictly dominates every
(B∧¬A)-index. -/
def Realize (φ : CompFormula L E) (le : I → I → Prop) (i : I) (w : W) : Prop :=
  match φ with
  | .ofFormula ψ => @Formula.Realize _ _ (interp i w) _ ψ id
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

variable (A B : CompFormula L E) (le : I → I → Prop) (ord : TotalPreorder I)
  (i : I) (w : W)

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
    Realize interp (.matom R e) le i w ↔
      @Structure.RelMap L E (interp i w) 1 R ![e] := by
  letI := interp i w
  show @Formula.Realize L E (interp i w) E (R.formula ![Term.var e]) id ↔ _
  have hv : (fun j => ((![Term.var e] : Fin 1 → L.Term E) j).realize (M := E) id)
      = ![e] := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp
  rw [Formula.realize_rel, hv]

/-- Comparative-free formulas are ordering-invariant. -/
theorem realize_congr_of_compFree :
    ∀ (φ : CompFormula L E), φ.CompFree →
      ∀ (le le' : I → I → Prop) (i : I) (w : W),
      (Realize interp φ le i w ↔ Realize interp φ le' i w)
  | .ofFormula _, _, _, _, _, _ => Iff.rfl
  | .not A, h, le, le', i, w =>
      not_congr (realize_congr_of_compFree A h le le' i w)
  | .inf A B, h, le, le', i, w =>
      and_congr (realize_congr_of_compFree A h.1 le le' i w)
        (realize_congr_of_compFree B h.2 le le' i w)
  | .sup A B, h, le, le', i, w =>
      or_congr (realize_congr_of_compFree A h.1 le le' i w)
        (realize_congr_of_compFree B h.2 le le' i w)
  | .comp _ _, h, _, _, _, _ => h.elim

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
    (fun a b => ord.le_total b a) (fun _ _ => Iff.rfl) _ _ i

/-- ≻ is irreflexive — a witness would make A both true and false. -/
theorem not_realize_comp_self : ¬ Realize interp (.comp A A) le i w := by
  rintro ⟨_, _, hA, hnA, _⟩
  exact hnA hA

/-- ≈ is reflexive. -/
theorem realize_equi_self : Realize interp (A.equi A) le i w :=
  ⟨not_realize_comp_self interp A le i w, not_realize_comp_self interp A le i w⟩

/-- ≈ is symmetric. -/
theorem realize_equi_comm :
    Realize interp (A.equi B) le i w ↔ Realize interp (B.equi A) le i w :=
  and_comm

end CompFormula

end FirstOrder.Language
