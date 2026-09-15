import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Core.ModelTheory.FiniteModel
import Linglib.Core.Order.TotalPreorder
import Linglib.Logic.ComparativeProbability.WorldOrdering
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Degree.Delineation

/-!
# Rudolph and Kocurek (2024): Metalinguistic Gradability

This file formalizes the paper's semantic expressivism for metalinguistic comparatives,
equatives, degree modifiers and conditionals. Truth is relative to a semantic ordering, a total
preorder ranking interpretations by the strength of a speaker's commitment to them, together
with an interpretation and a world. *A more than B* holds when some interpretation ranked no
higher than the index makes A true and B false and outranks every one that makes B true and A
false (`ComparativeFormula.Realize`), and the equative is the failure of both comparatives.
The comparative is irreflexive, asymmetric and transitive, contraposes, and distributes over
disjunction and conjunction (`comp_trans` and its neighbours). That a sentence together with
its negated rival entails the comparative holds not for truth but for acceptance, truth at
every top-ranked interpretation (`accepted_comp_of_accepted`), a nonclassical entailment on
which proof by cases fails. A distance function grounds *much more*, *very*, *sorta* and
*mostly*: *very A* is truth at every reasonably close interpretation (`evalVery_iff`). The
metalinguistic conditional restricts the ordering to the antecedent's interpretations and so
conveys weak comparatives. Under No Reversal the comparative reduces to [klein-1980]'s
delineation comparative, and the supplement's revised semantics and degree theory make
metalinguistic degrees a bounded linear order on which the comparative is the degree
substrate's comparative (`mc_iff_comparativeSem`).

## Implementation notes

An interpretation is a world-indexed family of first-order structures, and the language embeds
classical formulas under the boolean connectives and the comparative. The comparative clause is
the strict domination lift of [holliday-icard-2013] applied, within the cone below the index,
to the two difference sets, which is how the modifier *much more* and the comparative share one
template. Orderings are total, as in the paper. The revised semantics and the degree theory
follow [kocurek-2024-supplement]: metalinguistic degrees are the classes of interpretation sets
under the revised equative, ordered by the revised comparative, and the finite models decide
the paper's non-entailments and the supplement's counterexample to equative transitivity.

## References

* [rudolph-kocurek-2024]
* [kocurek-2024-supplement]
* [holliday-icard-2013]
* [klein-1980]
* [lewis-1973]
* [kratzer-2012]
* [halpern-2003]
* [yalcin-2007]
-/

namespace RudolphKocurek2024

open Core.Order (TotalPreorder)
open FirstOrder FirstOrder.Language
open ComparativeProbability

/-! ### The comparative language -/

section Language

variable {W : Type*} {ge_w : W → W → Prop}

/-- [lewis-1973]'s ∃∀ comparative-possibility clause, localized to the cone below an index and
comparing difference sets, the shape of [kratzer-2012]'s revised lifting, with the dominance
relation a parameter: the comparative at the strict ordering, *much more* at "far below". -/
def coneStrictLift (le below : W → W → Prop) (P Q : W → Prop) (i : W) : Prop :=
  ∃ a, le a i ∧ P a ∧ ¬ Q a ∧ ∀ b, le b i → Q b → ¬ P b → below b a

instance (le below : W → W → Prop) (P Q : W → Prop) (i : W) [Fintype W]
    [DecidableRel le] [DecidableRel below] [DecidablePred P] [DecidablePred Q] :
    Decidable (coneStrictLift le below P Q i) := by
  unfold coneStrictLift; infer_instance

/-- The cone difference set at `i`: members of the cone where `P` holds and `Q` fails. -/
def coneDiff (le : W → W → Prop) (P Q : W → Prop) (i : W) : Set W :=
  {x | le x i ∧ P x ∧ ¬ Q x}

/-- Whenever `below` is the strict form of the total `ge_w`, strict domination lifting is an ∃∀
clause in `below`. -/
theorem strict_dominationLift_iff_below {below : W → W → Prop}
    (hTotal : ∀ a b, ge_w a b ∨ ge_w b a)
    (hBelow : ∀ a b, below a b ↔ ge_w b a ∧ ¬ ge_w a b) (A B : Set W) :
    Strict (dominationLift ge_w) A B ↔ ∃ a ∈ A, ∀ b ∈ B, below b a := by
  rw [strict_dominationLift_iff hTotal]
  exact exists_congr λ a => and_congr_right λ _ => forall₂_congr λ b _ => (hBelow b a).symm

/-- Whenever `below` is the strict form of the total `ge_w`, the cone-localized clause is the
strict domination lift on the cone difference sets. -/
theorem coneStrictLift_iff_strict_dominationLift {le below : W → W → Prop}
    (hTotal : ∀ a b, ge_w a b ∨ ge_w b a)
    (hBelow : ∀ a b, below a b ↔ ge_w b a ∧ ¬ ge_w a b) (P Q : W → Prop) (i : W) :
    coneStrictLift le below P Q i ↔
      Strict (dominationLift ge_w) (coneDiff le P Q i) (coneDiff le Q P i) := by
  rw [strict_dominationLift_iff_below hTotal hBelow]
  unfold coneStrictLift coneDiff
  simp only [Set.mem_ofPred_eq, and_imp, and_assoc]

variable {L : Language} {I E : Type*}

/-- The extension of a unary relation symbol in a structure carried as a term. -/
def ext₁ (S : L.Structure E) (R : L.Relations 1) : Set E := {e | S.RelMap R ![e]}

@[simp] theorem mem_ext₁ {S : L.Structure E} {R : L.Relations 1} {e : E} :
    e ∈ ext₁ S R ↔ S.RelMap R ![e] :=
  Iff.rfl

instance (S : L.Structure E) (R : L.Relations 1) (e : E) [h : Decidable (S.RelMap R ![e])] :
    Decidable (e ∈ ext₁ S R) :=
  h

/-- Pointwise decidability of atoms across an interpretation family, the hook that makes
`decide` available on finite models. -/
abbrev DecidableAtoms (interp : I → W → L.Structure E) :=
  ∀ (i : I) (w : W) (n : ℕ) (r : L.Relations n) (x : Fin n → E), Decidable ((interp i w).RelMap r x)

/-- Formulas: an embedded classical formula with free variables valued by domain elements,
the booleans, and the comparative `A ≻ B` (`comp`). -/
inductive ComparativeFormula (L : Language) (E : Type*) where
  | ofFormula : L.Formula E → ComparativeFormula L E
  | not : ComparativeFormula L E → ComparativeFormula L E
  | inf : ComparativeFormula L E → ComparativeFormula L E → ComparativeFormula L E
  | sup : ComparativeFormula L E → ComparativeFormula L E → ComparativeFormula L E
  | comp : ComparativeFormula L E → ComparativeFormula L E → ComparativeFormula L E

namespace ComparativeFormula

/-- Ground unary predication `R(e)`, as an embedded formula. -/
abbrev matom (R : L.Relations 1) (e : E) : ComparativeFormula L E :=
  .ofFormula (R.formula ![Term.var e])

/-- The equative `A ≈ B := ¬(A ≻ B) ∧ ¬(B ≻ A)`. -/
def equi (A B : ComparativeFormula L E) : ComparativeFormula L E :=
  .inf (.not (.comp A B)) (.not (.comp B A))

/-- The weak comparative `A ≽ B := (A ≻ B) ∨ (A ≈ B)`. -/
def weak (A B : ComparativeFormula L E) : ComparativeFormula L E := .sup (.comp A B) (A.equi B)

/-- Formulas free of the comparative, whose truth does not consult the ordering. -/
def ComparativeFree : ComparativeFormula L E → Prop
  | .ofFormula _ => True
  | .not A => A.ComparativeFree
  | .inf A B => A.ComparativeFree ∧ B.ComparativeFree
  | .sup A B => A.ComparativeFree ∧ B.ComparativeFree
  | .comp _ _ => False

variable (interp : I → W → L.Structure E)

/-- Truth at an index of an ordered interpretation family, relative to a raw ordering relation
(restricted orderings need not be total). The comparative: some interpretation in the cone
making `A` true and `B` false strictly dominates every one making `B` true and `A` false. -/
def Realize : ComparativeFormula L E → (I → I → Prop) → I → W → Prop
  | .ofFormula ψ, _, i, w => letI := interp i w; ψ.Realize id
  | .not A, le, i, w => ¬ Realize A le i w
  | .inf A B, le, i, w => Realize A le i w ∧ Realize B le i w
  | .sup A B, le, i, w => Realize A le i w ∨ Realize B le i w
  | .comp A B, le, i, w =>
      coneStrictLift le (Strict le) (Realize A le · w) (Realize B le · w) i

instance instDec [Fintype I] [Fintype E] [DecidableEq E]
    [hA : DecidableAtoms interp] (le : I → I → Prop) [DecidableRel le] :
    ∀ (φ : ComparativeFormula L E) (i : I) (w : W), Decidable (Realize interp φ le i w)
  | .ofFormula ψ, i, w =>
      @Formula.decidableRealize L E (interp i w) _ _ (λ n r x => hA i w n r x) E ψ id
  | .not A, i, w => @instDecidableNot _ (instDec le A i w)
  | .inf A B, i, w => @instDecidableAnd _ _ (instDec le A i w) (instDec le B i w)
  | .sup A B, i, w => @instDecidableOr _ _ (instDec le A i w) (instDec le B i w)
  | .comp A B, i, w =>
      haveI : DecidablePred (Realize interp A le · w) := λ j => instDec le A j w
      haveI : DecidablePred (Realize interp B le · w) := λ j => instDec le B j w
      inferInstanceAs (Decidable (coneStrictLift le (Strict le)
        (Realize interp A le · w) (Realize interp B le · w) i))

variable {interp} {A B : ComparativeFormula L E} {le : I → I → Prop}
  {ord : TotalPreorder I} {i : I} {w : W}

/-- The comparative clause over a total preorder, with the domination conjunction packaged
as `ord.lt`. -/
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
  have hv : (λ j => ((![Term.var e] : Fin 1 → L.Term E) j).realize (M := E) id)
      = ![e] := funext λ j => by rw [Subsingleton.elim j 0]; simp
  rw [Formula.realize_rel, hv]

/-- Comparative-free formulas are ordering-invariant. -/
theorem ComparativeFree.realize_congr :
    ∀ {φ : ComparativeFormula L E}, φ.ComparativeFree →
      ∀ {le le' : I → I → Prop} {i : I} {w : W},
      Realize interp φ le i w ↔ Realize interp φ le' i w
  | .ofFormula _, _ => Iff.rfl
  | .not A, h => not_congr (ComparativeFree.realize_congr (show A.ComparativeFree from h))
  | .inf _ _, h => and_congr (ComparativeFree.realize_congr h.1) (ComparativeFree.realize_congr h.2)
  | .sup _ _, h => or_congr (ComparativeFree.realize_congr h.1) (ComparativeFree.realize_congr h.2)
  | .comp _ _, h => h.elim

/-- The comparative is the strict domination lift of [holliday-icard-2013], Lewis's lifting,
applied to the cone at the evaluation index. -/
theorem realize_comp_iff_strict_dominationLift :
    Realize interp (.comp A B) ord.le i w ↔
    Strict (dominationLift (flip ord.le))
      (coneDiff ord.le (Realize interp A ord.le · w) (Realize interp B ord.le · w) i)
      (coneDiff ord.le (Realize interp B ord.le · w) (Realize interp A ord.le · w) i) :=
  coneStrictLift_iff_strict_dominationLift (λ a b => ord.le_total b a) (λ _ _ => Iff.rfl) _ _ _

/-- The comparative is irreflexive: a witness would make `A` both true and false. -/
theorem not_realize_comp_self : ¬ Realize interp (.comp A A) le i w :=
  λ ⟨_, _, hA, hnA, _⟩ => hnA hA

/-- The equative is reflexive. -/
theorem realize_equi_self : Realize interp (A.equi A) le i w :=
  ⟨not_realize_comp_self, not_realize_comp_self⟩

/-- The equative is symmetric. -/
theorem realize_equi_comm :
    Realize interp (A.equi B) le i w ↔ Realize interp (B.equi A) le i w :=
  and_comm

end ComparativeFormula

end Language

/-! ### Semantic orderings, truth and acceptance -/

/-- The paper's ranking of interpretations by strength of interpretive commitment. -/
abbrev SemanticOrdering (I : Type*) := TotalPreorder I

section Framework

variable {L : Language} {I W E : Type*} (interp : I → W → L.Structure E)

/-- Truth at an index `⟨≤, i, w⟩`. -/
abbrev Eval (φ : ComparativeFormula L E) (ord : SemanticOrdering I) (i : I) (w : W) : Prop :=
  ComparativeFormula.Realize interp φ ord.le i w

/-- Assertoric content: truth at every top-ranked interpretation, the substrate's
`TotalPreorder.AcceptedAt`. -/
def AssertoricContent [Fintype I] (φ : ComparativeFormula L E) (ord : SemanticOrdering I)
    (w : W) : Prop :=
  ord.AcceptedAt (λ i => Eval interp φ ord i w)

instance [Fintype I] [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    (φ : ComparativeFormula L E) (ord : SemanticOrdering I) [DecidableRel ord.le] (w : W) :
    Decidable (AssertoricContent interp φ ord w) := by
  unfold AssertoricContent; infer_instance

/-! ### Entailment -/

section Entailment

variable {ord : SemanticOrdering I} {i : I} {w : W} {A B C : ComparativeFormula L E}

/-- The comparative with its right constituent entails the left: an interpretation making `B`
true and `A` false would have to lie strictly below one ranked no higher than itself. -/
theorem eval_of_comp (h : Eval interp (.comp A B) ord i w) (hB : Eval interp B ord i w) :
    Eval interp A ord i w :=
  of_not_not λ hA => let ⟨_, hle, _, _, hdom⟩ := h; (hdom i (ord.le_refl i) hB hA).2 hle

/-- The comparative is asymmetric. -/
theorem comp_asymm (h : Eval interp (.comp A B) ord i w) : ¬ Eval interp (.comp B A) ord i w :=
  λ ⟨j, hj, hB, hA, domB⟩ =>
    let ⟨i', hi', hA', hB', domA⟩ := h
    (domA j hj hB hA).2 (domB i' hi' hA' hB').1

/-- The comparative is transitive: whichever of the two witnesses is ranked higher witnesses
the composite, and the two domination clauses cover the composite's rivals. -/
theorem comp_trans (h₁ : Eval interp (.comp A B) ord i w)
    (h₂ : Eval interp (.comp B C) ord i w) : Eval interp (.comp A C) ord i w := by
  obtain ⟨i₁, hi₁, hA₁, hB₁, dom₁⟩ := h₁
  obtain ⟨i₂, hi₂, hB₂, hC₂, dom₂⟩ := h₂
  rcases ord.le_total i₂ i₁ with hle | hle
  · refine ⟨i₁, hi₁, hA₁, λ hC₁ => (dom₂ i₁ hi₁ hC₁ hB₁).2 hle, λ j hj hC hA => ?_⟩
    by_cases hB : Eval interp B ord j w
    · exact dom₁ j hj hB hA
    · exact ord.lt_of_lt_of_le (dom₂ j hj hC hB) hle
  · refine ⟨i₂, hi₂, of_not_not λ hA₂ => (dom₁ i₂ hi₂ hB₂ hA₂).2 hle, hC₂, λ j hj hC hA => ?_⟩
    by_cases hB : Eval interp B ord j w
    · exact ord.lt_of_lt_of_le (dom₁ j hj hB hA) hle
    · exact dom₂ j hj hC hB

/-- The comparative contraposes. -/
theorem comp_not_not_iff :
    Eval interp (.comp (.not B) (.not A)) ord i w ↔ Eval interp (.comp A B) ord i w :=
  exists_congr λ _ =>
    ⟨λ ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, not_not.1 h₃, h₂, λ j hj hB hA => h₄ j hj hA (not_not.2 hB)⟩,
      λ ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₃, not_not.2 h₂, λ j hj hA hB => h₄ j hj (not_not.1 hB) hA⟩⟩

/-- The comparative distributes over a disjunction on the right. -/
theorem comp_sup (h : Eval interp (.comp A (.sup B C)) ord i w) :
    Eval interp (.comp A B) ord i w ∧ Eval interp (.comp A C) ord i w :=
  let ⟨i', hi', hA, hBC, dom⟩ := h
  ⟨⟨i', hi', hA, λ hB => hBC (Or.inl hB), λ j hj hB hA' => dom j hj (Or.inl hB) hA'⟩,
    ⟨i', hi', hA, λ hC => hBC (Or.inr hC), λ j hj hC hA' => dom j hj (Or.inr hC) hA'⟩⟩

/-- The comparative distributes over a conjunction on the left. -/
theorem inf_comp (h : Eval interp (.comp (.inf A B) C) ord i w) :
    Eval interp (.comp A C) ord i w ∧ Eval interp (.comp B C) ord i w :=
  let ⟨i', hi', ⟨hA, hB⟩, hC, dom⟩ := h
  ⟨⟨i', hi', hA, hC, λ j hj hC' hnA => dom j hj hC' λ h => hnA h.1⟩,
    ⟨i', hi', hB, hC, λ j hj hC' hnB => dom j hj hC' λ h => hnB h.2⟩⟩

/-- The equative is preserved by negating both sides. -/
theorem equi_not_not (h : Eval interp (A.equi B) ord i w) :
    Eval interp ((ComparativeFormula.not A).equi (.not B)) ord i w :=
  ⟨λ h' => h.2 ((comp_not_not_iff interp).1 h'), λ h' => h.1 ((comp_not_not_iff interp).1 h')⟩

/-- The weak comparative is the negation of the converse comparative. -/
theorem eval_weak_iff : Eval interp (A.weak B) ord i w ↔ ¬ Eval interp (.comp B A) ord i w :=
  ⟨λ h => h.elim (comp_asymm interp) And.right,
    λ h => (em _).elim Or.inl λ h' => Or.inr ⟨h', h⟩⟩

/-- Any two sentences are comparable: one is more than the other, or they are equal. -/
theorem eval_comp_or_equi :
    Eval interp (.sup (.sup (.comp A B) (.comp B A)) (A.equi B)) ord i w :=
  (em _).elim (Or.inl ∘ Or.inl) λ h₁ => (em _).elim (Or.inl ∘ Or.inr) λ h₂ => Or.inr ⟨h₁, h₂⟩

variable [Fintype I]

/-- Truth preservation implies acceptance preservation. -/
theorem accepted_mono (h : ∀ i, Eval interp A ord i w → Eval interp B ord i w)
    (hA : AssertoricContent interp A ord w) : AssertoricContent interp B ord w :=
  λ x hx => h x (hA x hx)

/-- Accepting `A` and `¬B` means accepting `A ≻ B`: every top-ranked interpretation makes `A`
true and `B` false, so an interpretation making `B` true and `A` false is not top-ranked and
lies strictly below each of them. -/
theorem accepted_comp_of_accepted (hA : AssertoricContent interp A ord w)
    (hB : AssertoricContent interp (.not B) ord w) :
    AssertoricContent interp (.comp A B) ord w :=
  λ x hx => ⟨x, ord.le_refl x, hA x hx, hB x hx, λ j hj _ hAj =>
    ⟨hj, λ hxj => hAj (hA j λ y hy => hx y (ord.lt_of_le_of_lt hxj hy))⟩⟩

/-- Accepting `A ≈ B` and `A` means accepting `B`. -/
theorem accepted_of_accepted_equi (h : AssertoricContent interp (A.equi B) ord w)
    (hA : AssertoricContent interp A ord w) : AssertoricContent interp B ord w :=
  λ x hx => of_not_not λ hB => (h x hx).1 ⟨x, ord.le_refl x, hA x hx, hB, λ j hj _ hAj =>
    ⟨hj, λ hxj => hAj (hA j λ y hy => hx y (ord.lt_of_le_of_lt hxj hy))⟩⟩

end Entailment

/-! ### Distance functions and degree modifiers -/

/-- A distance function: which interpretations count as reasonably
close to each — the parameter behind *very*, *sorta*, *mostly*. -/
structure DistanceFunction (I : Type*) (ord : SemanticOrdering I) where
  /-- `close i i'` means i' is reasonably close to i. -/
  close : I → I → Prop
  /-- Centered: i ∈ d(i) -/
  centered : ∀ i, close i i
  /-- Top-bounded: if i' ∈ d(i), then i' ≤ i -/
  topBounded : ∀ i i', close i i' → ord.le i' i
  /-- Convex: if i' ∈ d(i) and i' ≤ i'' ≤ i, then i'' ∈ d(i) -/
  convex : ∀ i i' i'', close i i' → ord.le i' i'' → ord.le i'' i → close i i''
  /-- Noncontractive: if i' ∈ d(i) and i' ≤ j ≤ i, then i' ∈ d(j) -/
  noncontractive : ∀ i i' j, close i i' → ord.le i' j → ord.le j i → close j i'

/-- `i ≪ j`: i is below j and not even reasonably close to it. -/
def FarBelow {I : Type*} (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    (i j : I) : Prop :=
  ord.le i j ∧ ¬ d.close j i

instance {I : Type*} (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    [DecidableRel ord.le] [DecidableRel d.close] :
    DecidableRel (FarBelow ord d) := λ _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- ≪ is asymmetric: centeredness plus noncontractivity force mutually-≤
points to be close. -/
theorem FarBelow.asymm {I : Type*} {ord : SemanticOrdering I}
    (d : DistanceFunction I ord) {a b : I} (h : FarBelow ord d a b) :
    ¬ FarBelow ord d b a :=
  λ h' => h'.2 (d.noncontractive b b a (d.centered b) h'.1 h.1)

/-- "Not far below" is total — what lets the strict l-lifting characterize ≫. -/
theorem not_farBelow_total {I : Type*} {ord : SemanticOrdering I}
    (d : DistanceFunction I ord) (a b : I) :
    ¬ FarBelow ord d a b ∨ ¬ FarBelow ord d b a :=
  imp_iff_not_or.mp (FarBelow.asymm d)

section Modifiers

variable [Fintype I] (φ ψ : ComparativeFormula L E) (ord : SemanticOrdering I)
  (below : I → I → Prop) (d : DistanceFunction I ord) (i : I) (w : W)

/-- The paper's comparative template — the substrate's `coneStrictLift` at the
formulas' truth sets: ≻'s clause with an arbitrary dominance relation in
place of < (`eval_comp_iff_compWith`); ≫ is the instance at ≪. -/
abbrev EvalCompWith : Prop :=
  coneStrictLift ord.le below
    (λ j => Eval interp φ ord j w) (λ j => Eval interp ψ ord j w) i

omit [Fintype I] in
/-- ≻ is the template at <. -/
theorem eval_comp_iff_compWith :
    Eval interp (.comp φ ψ) ord i w ↔ EvalCompWith interp φ ψ ord ord.lt i w :=
  Iff.rfl

/-- Much more (A ≫ B): the template at ≪. -/
abbrev EvalMuchMore : Prop :=
  EvalCompWith interp φ ψ ord (FarBelow ord d) i w

/-- very A := A ≫ ¬A — every reasonably close interpretation makes A true. -/
abbrev EvalVery : Prop :=
  EvalMuchMore interp φ (.not φ) ord d i w

/-- sorta A := ¬ very ¬A — some reasonably close interpretation makes A true. -/
abbrev EvalSorta : Prop :=
  ¬ EvalVery interp (.not φ) ord d i w

/-- mostly A : some reasonably high level
strictly below the top makes A uniformly true, and every A-false level below
the current interpretation sits below it. Compatible with A and with ¬A
(unlike `very`); entails `sorta A`; `mostly A ∧ mostly ¬A` is contradictory. -/
def EvalMostly : Prop :=
  ∃ i', ord.lt i' i ∧ d.close i i' ∧
    (∀ j, ord.equiv j i' → Eval interp φ ord j w) ∧
    ∀ i'', ord.lt i'' i → (∀ j, ord.equiv j i'' → ¬ Eval interp φ ord j w) →
      ord.lt i'' i'

instance [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    [DecidableRel ord.le] [DecidableRel d.close] :
    Decidable (EvalMostly interp φ ord d i w) := by
  unfold EvalMostly
  haveI h1 : DecidableRel ord.lt := inferInstance
  haveI h2 : DecidableRel ord.equiv := inferInstance
  haveI h3 : ∀ j, Decidable (Eval interp φ ord j w) := λ j => inferInstance
  infer_instance

end Modifiers

section ModifierGroundings

variable (φ ψ : ComparativeFormula L E) (ord : SemanticOrdering I)
  (d : DistanceFunction I ord) (i : I) (w : W)

/-- **Grounding**: ≫ is the strict l-lifting under the *coarser* total
preorder "not far below" — the distance-function axioms are exactly what
make that relation total, so [holliday-icard-2013]'s lift machinery applies
with ≪ in the role of <. -/
theorem evalMuchMore_iff_strict_dominationLift :
    EvalMuchMore interp φ ψ ord d i w ↔
    Strict
      (dominationLift (λ a b => ¬ FarBelow ord d a b))
      (coneDiff ord.le (Eval interp φ ord · w) (Eval interp ψ ord · w) i)
      (coneDiff ord.le (Eval interp ψ ord · w) (Eval interp φ ord · w) i) :=
  coneStrictLift_iff_strict_dominationLift
    (λ a b => not_farBelow_total d a b)
    (λ _ _ => ⟨λ h => ⟨FarBelow.asymm d h, not_not_intro h⟩,
      λ h => not_not.mp h.2⟩) _ _ i

/-- **Grounding**: *mostly* is the strict l-lifting comparing φ-uniform
*levels* (`ord.equiv`-classes, mathlib's `AntisymmRel.setoid`): some
reasonably-high all-φ level strictly below the index dominates every
all-¬φ level below it. -/
theorem evalMostly_iff_strict_dominationLift :
    EvalMostly interp φ ord d i w ↔
    Strict
      (dominationLift (λ a b => ord.le b a))
      {x | ord.lt x i ∧ d.close i x ∧ ∀ j, ord.equiv j x → Eval interp φ ord j w}
      {x | ord.lt x i ∧ ∀ j, ord.equiv j x → ¬ Eval interp φ ord j w} := by
  rw [strict_dominationLift_iff_below
    (λ a b => ord.le_total b a) (λ _ _ => Iff.rfl)]
  simp only [Set.mem_ofPred_eq, and_imp, and_assoc]
  rfl

end ModifierGroundings

section ModifierConsequences

variable {ord : SemanticOrdering I} (d : DistanceFunction I ord) {i : I} {w : W}
  {φ : ComparativeFormula L E}

/-- *very A* is truth at every reasonably close interpretation: a witness strictly above a
close falsifier would, by noncontractivity, have it close too. -/
theorem evalVery_iff :
    EvalVery interp φ ord d i w ↔ ∀ i', d.close i i' → Eval interp φ ord i' w := by
  constructor
  · rintro ⟨a, ha, hφa, -, hdom⟩ i' hi'
    by_contra hφ
    obtain ⟨hia, hclose⟩ := hdom i' (d.topBounded i i' hi') hφ hφ
    exact hclose (d.noncontractive i i' a hi' hia ha)
  · intro h
    exact ⟨i, ord.le_refl i, h i (d.centered i), not_not.2 (h i (d.centered i)),
      λ b hb hφ _ => ⟨hb, λ hc => hφ (h b hc)⟩⟩

/-- *very A* entails `A`, since every interpretation is close to itself. -/
theorem eval_of_very (h : EvalVery interp φ ord d i w) : Eval interp φ ord i w :=
  (evalVery_iff interp d).1 h i (d.centered i)

/-- *sorta A* is truth at some reasonably close interpretation. -/
theorem evalSorta_iff :
    EvalSorta interp φ ord d i w ↔ ∃ i', d.close i i' ∧ Eval interp φ ord i' w :=
  ⟨λ h => Classical.byContradiction λ h' =>
      h ((evalVery_iff interp d).2 λ i' hi' hφ => h' ⟨i', hi', hφ⟩),
    λ ⟨i', hi', hφ⟩ h => (evalVery_iff interp d).1 h i' hi' hφ⟩

/-- `A` entails *sorta A*. -/
theorem sorta_of_eval (h : Eval interp φ ord i w) : EvalSorta interp φ ord d i w :=
  (evalSorta_iff interp d).2 ⟨i, d.centered i, h⟩

/-- *mostly A* entails *sorta A*. -/
theorem sorta_of_mostly (h : EvalMostly interp φ ord d i w) : EvalSorta interp φ ord d i w :=
  let ⟨i', _, hc, hφ, _⟩ := h
  (evalSorta_iff interp d).2 ⟨i', hc, hφ i' (AntisymmRel.refl _ _)⟩

/-- *mostly A* and *mostly ¬A* are contradictory: each witness level would lie strictly below
the other. -/
theorem not_mostly_not_of_mostly (h : EvalMostly interp φ ord d i w) :
    ¬ EvalMostly interp (.not φ) ord d i w :=
  λ ⟨i₂, lt₂, _, all₂, dom₂⟩ =>
    let ⟨i₁, lt₁, _, all₁, dom₁⟩ := h
    (dom₁ i₂ lt₂ all₂).2 (dom₂ i₁ lt₁ λ j hj => not_not.2 (all₁ j hj)).1

end ModifierConsequences

/-! ### No Reversal and the delineation bridge -/

/-- No Reversal: below any
interpretation separating `a` from `b`, every extension admitting `b` admits
`a` — the order-restricted analogue of Klein's monotone delineation. -/
def NoReversal (ord : SemanticOrdering I) (R : L.Relations 1) (w : W)
    (a b : E) : Prop :=
  ∀ i i', ord.le i' i →
    a ∈ ext₁ (interp i w) R → b ∉ ext₁ (interp i w) R →
    b ∈ ext₁ (interp i' w) R → a ∈ ext₁ (interp i' w) R

instance [Fintype I] [DecidableAtoms interp]
    (ord : SemanticOrdering I) [DecidableRel ord.le]
    (R : L.Relations 1) (w : W) (a b : E) :
    Decidable (NoReversal interp ord R w a b) := by
  unfold NoReversal; simp only [mem_ext₁]; infer_instance

section Delineation

variable (ord : SemanticOrdering I) (R : L.Relations 1) (w : W)

/-- The delineation induced by a ranked interpretation family: admissible
comparison classes are the extensions of `R` in the ≤-cone; `x` is R-in-C iff
`x ∈ C`. Instantiates [klein-1980]'s comparison-class parameter. -/
def interpretationDelineation (i : I) :
    Degree.Delineation.ComparisonClass E → E → Prop :=
  λ C x =>
    (∃ i', ord.le i' i ∧ C = ext₁ (interp i' w) R) ∧ x ∈ C

/-- The delineation comparative over the induced delineation is the ∃-witness
clause of the MC: some cone extension separates `a` from `b`. -/
theorem delineation_comparativeSem_iff (i : I) (a b : E) :
    Degree.Delineation.comparativeSem
      (interpretationDelineation interp ord R w i) a b ↔
    ∃ i', ord.le i' i ∧ a ∈ ext₁ (interp i' w) R ∧ b ∉ ext₁ (interp i' w) R := by
  constructor
  · rintro ⟨C, ⟨⟨i', h_le, rfl⟩, h_aC⟩, h_nb⟩
    exact ⟨i', h_le, h_aC, λ hb => h_nb ⟨⟨i', h_le, rfl⟩, hb⟩⟩
  · rintro ⟨i', h_le, h_a, h_b⟩
    exact ⟨ext₁ (interp i' w) R, ⟨⟨i', h_le, rfl⟩, h_a⟩,
      λ h => h_b h.2⟩

/-- Under No Reversal, the
metalinguistic comparative for a gradable predicate IS [klein-1980]'s
delineation comparative (`Delineation.comparativeSem`) over the
interpretation-induced delineation — the paper's the paper: NR makes the
domination clause of the MC semantics redundant. -/
theorem eval_mc_iff_delineation_of_noReversal (i : I) (a b : E)
    (hnr : NoReversal interp ord R w b a) :
    Eval interp (.comp (.matom R a) (.matom R b)) ord i w ↔
    Degree.Delineation.comparativeSem
      (interpretationDelineation interp ord R w i) a b := by
  rw [Eval, ComparativeFormula.realize_comp_iff, delineation_comparativeSem_iff]
  simp only [ComparativeFormula.realize_matom, ← mem_ext₁]
  constructor
  · rintro ⟨i', h_le, h_A, h_B, -⟩
    exact ⟨i', h_le, h_A, h_B⟩
  · rintro ⟨i', h_le, h_a, h_b⟩
    refine ⟨i', h_le, h_a, h_b, λ i'' h'' hB'' hA'' => ?_⟩
    have h_not : ¬ ord.le i' i'' :=
      λ hle' => h_b (hnr i'' i' hle' hB'' hA'' h_a)
    rcases ord.le_total i'' i' with h1 | h2
    · exact ⟨h1, h_not⟩
    · exact absurd h2 h_not

end Delineation
/-! ### The revised semantics -/

section Revised

/-- Truth under the revised MC semantics ([kocurek-2024-supplement]). The
basic semantics fails ME transitivity; the revision strengthens the MC: the
(A∧¬B)-witness must dominate either all B-interpretations or all
¬A-interpretations, blocking vacuous comparatives.

The supplement shows that the basic entailment patterns are preserved, that equative
transitivity is validated, and that the two semantics are interdefinable. -/
def EvalRevised : ComparativeFormula L E → SemanticOrdering I → I → W → Prop
  | .ofFormula ψ, _, i, w => letI := interp i w; ψ.Realize id
  | .not A, ord, i, w => ¬ EvalRevised A ord i w
  | .inf A B, ord, i, w => EvalRevised A ord i w ∧ EvalRevised B ord i w
  | .sup A B, ord, i, w => EvalRevised A ord i w ∨ EvalRevised B ord i w
  | .comp A B, ord, i, w =>
      ∃ i', ord.le i' i ∧ EvalRevised A ord i' w ∧
        ¬ EvalRevised B ord i' w ∧
        ((∀ i'', ord.le i'' i → EvalRevised B ord i'' w → ord.lt i'' i') ∨
         (∀ i'', ord.le i'' i → ¬ EvalRevised A ord i'' w → ord.lt i'' i'))

instance EvalRevised.instDec [Fintype I] [Fintype E] [DecidableEq E]
    [hA : DecidableAtoms interp] (ord : SemanticOrdering I) [DecidableRel ord.le] :
    ∀ (φ : ComparativeFormula L E) (i : I) (w : W),
      Decidable (EvalRevised interp φ ord i w)
  | .ofFormula ψ, i, w =>
      @Formula.decidableRealize L E (interp i w) _ _ (λ n r x => hA i w n r x) E ψ id
  | .not A, i, w => @instDecidableNot _ (EvalRevised.instDec ord A i w)
  | .inf A B, i, w =>
      @instDecidableAnd _ _ (EvalRevised.instDec ord A i w) (EvalRevised.instDec ord B i w)
  | .sup A B, i, w =>
      @instDecidableOr _ _ (EvalRevised.instDec ord A i w) (EvalRevised.instDec ord B i w)
  | .comp A B, i, w =>
      haveI : ∀ j, Decidable (EvalRevised interp A ord j w) :=
        (EvalRevised.instDec ord A · w)
      haveI : ∀ j, Decidable (EvalRevised interp B ord j w) :=
        (EvalRevised.instDec ord B · w)
      inferInstanceAs (Decidable (∃ i', ord.le i' i ∧
        EvalRevised interp A ord i' w ∧ ¬ EvalRevised interp B ord i' w ∧
        ((∀ i'', ord.le i'' i → EvalRevised interp B ord i'' w → ord.lt i'' i') ∨
         (∀ i'', ord.le i'' i → ¬ EvalRevised interp A ord i'' w → ord.lt i'' i'))))

variable (A B : ComparativeFormula L E) (ord : SemanticOrdering I) (i : I) (w : W)

/-- Characterization of the revised MC case — definitional. -/
theorem evalRevised_mc_iff :
    EvalRevised interp (.comp A B) ord i w ↔
    ∃ i', ord.le i' i ∧ EvalRevised interp A ord i' w ∧
      ¬ EvalRevised interp B ord i' w ∧
      ((∀ i'', ord.le i'' i → EvalRevised interp B ord i'' w → ord.lt i'' i') ∨
       (∀ i'', ord.le i'' i → ¬ EvalRevised interp A ord i'' w → ord.lt i'' i')) :=
  Iff.rfl

end Revised
/-! ### The metalinguistic conditional -/

section MCond

variable [Fintype I] (A B : ComparativeFormula L E)

/-- Restrict an ordering relation to A-interpretations : drops non-A
interpretations, so the result satisfies reflexivity (at A-interpretations)
and transitivity but not totality — hence the consequent of a conditional is
evaluated via `EvalGen` rather than `Eval`. -/
def restrictLE (le : I → I → Prop) (w : W) : I → I → Prop :=
  λ i j => le i j ∧ ComparativeFormula.Realize interp A le i w ∧
    ComparativeFormula.Realize interp A le j w

instance [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    (le : I → I → Prop) [DecidableRel le] (w : W) :
    DecidableRel (restrictLE interp A le w) := λ _ _ => by
  unfold restrictLE; infer_instance

variable (ord : SemanticOrdering I) (i : I) (w : W)

/-- Metalinguistic conditional : the
antecedent is evaluated with the full ordering, the consequent with the
A-restricted ordering ≤_A. For non-metagradable A and B this reduces to
interpretation-strict implication.

Key properties: C1 (conditionals entail weak comparatives), M1
(⊨ A → (A ≻ ¬A), see `mcond_m1`), failure of modus tollens for acceptance. -/
def EvalMCond : Prop :=
  ∀ i', ord.le i' i → ComparativeFormula.Realize interp A ord.le i' w →
    ComparativeFormula.Realize interp B (restrictLE interp A ord.le w) i' w

instance [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    [DecidableRel ord.le] :
    Decidable (EvalMCond interp A B ord i w) := by
  unfold EvalMCond; infer_instance

omit [Fintype I] in
/-- **Grounding in the common-ground substrate**: for an MC-free consequent —
strictly weaker than the paper's reduction, which also assumes the antecedent
MC-free — the metalinguistic conditional is Stalnakerian entailment (`⊆`)
of the consequent by the ranked antecedent-cone. The
antecedent may contain ≻ freely: it is always evaluated at the full ordering,
and an MC-free consequent never consults the restricted one. -/
theorem evalMCond_iff_entails (hB : B.ComparativeFree) :
    EvalMCond interp A B ord i w ↔
    {x | ord.le x i ∧ ComparativeFormula.Realize interp A ord.le x w} ⊆
      {x | ComparativeFormula.Realize interp B ord.le x w} := by
  constructor
  · rintro h x ⟨hx1, hx2⟩
    exact hB.realize_congr.mp (h x hx1 hx2)
  · intro h x hx hAx
    exact hB.realize_congr.mpr (h ⟨hx, hAx⟩)

omit [Fintype I] in
/-- A conditional with comparative-free consequent conveys the weak comparative: every ranked
antecedent interpretation makes the consequent true, so none witnesses `A ≻ B`. -/
theorem weak_of_mcond (hB : B.ComparativeFree) (h : EvalMCond interp A B ord i w) :
    Eval interp (B.weak A) ord i w :=
  (eval_weak_iff interp).2 λ ⟨i', hi', hA, hnB, _⟩ => hnB (hB.realize_congr.1 (h i' hi' hA))

omit [Fintype I] in
/-- *If A or B, then A*, but not *if A or B, then B*, conveys the strict comparative `A ≻ B`
for comparative-free constituents: the second conditional's failure is a ranked witness for `A`
and against `B`, and the first leaves it no rival. -/
theorem comp_of_mcond_sup (hA : A.ComparativeFree) (hB : B.ComparativeFree)
    (h₁ : EvalMCond interp (.sup A B) A ord i w) (h₂ : ¬ EvalMCond interp (.sup A B) B ord i w) :
    Eval interp (.comp A B) ord i w := by
  rw [evalMCond_iff_entails interp _ _ ord i w hA] at h₁
  rw [evalMCond_iff_entails interp _ _ ord i w hB, Set.not_subset] at h₂
  obtain ⟨x, ⟨hx, hAB⟩, hnB⟩ := h₂
  exact ⟨x, hx, hAB.resolve_right hnB, hnB, λ j hj hB' hnA => absurd (h₁ ⟨hj, Or.inr hB'⟩) hnA⟩

omit [Fintype I] in
/-- *If A, then more A than not* is valid for comparative-free `A`: under the restricted
ordering every ranked interpretation makes `A` true, so the consequent's rival set is empty. -/
theorem mcond_comp_not (hA : A.ComparativeFree) : EvalMCond interp A (.comp A (.not A)) ord i w :=
  λ i' _ hA' => ⟨i', ⟨ord.le_refl i', hA', hA'⟩, hA.realize_congr.1 hA',
    not_not.2 (hA.realize_congr.1 hA'),
    λ _ ⟨_, hAb, _⟩ hnA _ => absurd (hA.realize_congr.1 hAb) hnA⟩

end MCond

end Framework

/-! ### The common ground -/

section CommonGround

variable {L : Language} {I W E : Type*} [Fintype I] (interp : I → W → L.Structure E)

/-- The proposition a sentence expresses over the enriched index: the ordering–world pairs at
which its assertoric content holds. The common ground is a set of such pairs, and an assertion
removes the pairs outside this proposition. -/
def assertoricProp (φ : ComparativeFormula L E) : Set (SemanticOrdering I × W) :=
  {p | AssertoricContent interp φ p.1 p.2}

end CommonGround

noncomputable section DegreeTheory

variable {L : Language} {I W E : Type*} [Fintype I] [DecidableEq I]
  (interp : I → W → L.Structure E) (ord : SemanticOrdering I) (i : I)

open Classical

/-! ### Fields and denotations -/

/-- The field I_i: the set of interpretations ranked at or below i.
Classical: the degree theory proves structure, it never computes. -/
def field : Finset I :=
  Finset.univ.filter (λ j => ord.le j i)

/-- The denotation of a formula: the set of interpretations in I_i
where the formula is true (under the revised semantics). -/
def denotation (φ : ComparativeFormula L E) (w : W) : Finset I :=
  (field ord i).filter (λ j => EvalRevised interp φ ord j w)

omit [DecidableEq I] in
theorem denotation_subset_field (φ : ComparativeFormula L E) (w : W) :
    denotation interp ord i φ w ⊆ field ord i :=
  Finset.filter_subset _ _

/-! ### Degree equivalence -/

/-- ∼ condition (i): each element of `X \ Y` is matched by one of `Y \ X` at
least as high, and vice versa. -/
def equivCond1 (X Y : Finset I) : Prop :=
  (∀ i' ∈ X \ Y, ∃ i'' ∈ Y \ X, ord.le i' i'') ∧
  (∀ i' ∈ Y \ X, ∃ i'' ∈ X \ Y, ord.le i' i'')

/-- ∼ condition (ii): each element of the symmetric difference is dominated
both by an element of `X ∩ Y` and by one of the field outside `X ∪ Y`. -/
def equivCond2 (X Y : Finset I) : Prop :=
  ∀ i' ∈ (X ∪ Y) \ (X ∩ Y),
    (∃ i'' ∈ X ∩ Y, ord.le i' i'') ∧
    (∃ i'' ∈ field ord i \ (X ∪ Y), ord.le i' i'')

/-- Metalinguistic degree equivalence `X ∼_i Y`: the revised ME truth
conditions applied to interpretation sets. -/
def degreeEquiv (X Y : Finset I) : Prop :=
  equivCond1 ord X Y ∨ equivCond2 ord i X Y

/-! ### Reflexivity and symmetry -/

/-- ∼ is reflexive. -/
theorem degreeEquiv_refl (X : Finset I) :
    degreeEquiv ord i X X := by
  left
  constructor <;> intro i' h <;> simp at h

/-- ∼ is symmetric. -/
theorem degreeEquiv_symm (X Y : Finset I) :
    degreeEquiv ord i X Y → degreeEquiv ord i Y X := by
  intro h
  rcases h with h1 | h2
  · left; exact ⟨h1.2, h1.1⟩
  · right
    intro i' hi'
    have hi'swap : i' ∈ (X ∪ Y) \ (X ∩ Y) := by
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hi' ⊢
      exact ⟨Or.symm hi'.1, λ ⟨h1, h2⟩ => hi'.2 ⟨h2, h1⟩⟩
    obtain ⟨h2a, h2b⟩ := h2 i' hi'swap
    constructor
    · obtain ⟨i'', hi''mem, hi''le⟩ := h2a
      exact ⟨i'', by rwa [Finset.inter_comm] at hi''mem, hi''le⟩
    · obtain ⟨i'', hi''mem, hi''le⟩ := h2b
      exact ⟨i'', by rwa [Finset.union_comm] at hi''mem, hi''le⟩

/-! ### The ordering on interpretation sets -/

/-- `X ⊐ Y`: some witness in `X \ Y` inside the field dominates all of
`Y \ X` and, moreover, all of `X ∩ Y` or all of the field outside `X ∪ Y` —
the revised MC truth conditions applied to interpretation sets. -/
def strictlyBetter (X Y : Finset I) : Prop :=
  ∃ i' ∈ X \ Y,
    i' ∈ field ord i ∧
    (∀ i'' ∈ Y \ X, ord.lt i'' i') ∧
    ((∀ i'' ∈ X ∩ Y, ord.lt i'' i') ∨
     (∀ i'' ∈ field ord i \ (X ∪ Y), ord.lt i'' i'))

omit [Fintype I] in
/-- If m dominates X ∩ Y and Y \ X, it dominates all of Y. -/
private lemma dom_all_of_inter_sdiff (m : I) (X Y : Finset I)
    (h_cap : ∀ c ∈ X ∩ Y, ord.lt c m)
    (h_sdiff : ∀ y ∈ Y \ X, ord.lt y m) :
    ∀ y ∈ Y, ord.lt y m := by
  intro y hy
  by_cases hyx : y ∈ X
  · exact h_cap y (Finset.mem_inter.mpr ⟨hyx, hy⟩)
  · exact h_sdiff y (Finset.mem_sdiff.mpr ⟨hy, hyx⟩)

/-- If m dominates Y \ X and field ord i \ (X ∪ Y), it dominates field ord i \ X. -/
private lemma dom_fX_of_sdiff_comp (m : I) (X Y : Finset I)
    (h_yx : ∀ y ∈ Y \ X, ord.lt y m)
    (h_comp : ∀ c ∈ field ord i \ (X ∪ Y), ord.lt c m) :
    ∀ c ∈ field ord i \ X, ord.lt c m := by
  intro c hc
  by_cases hc_y : c ∈ Y
  · exact h_yx c (Finset.mem_sdiff.mpr ⟨hc_y, (Finset.mem_sdiff.mp hc).2⟩)
  · exact h_comp c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,
      λ h => Finset.mem_union.mp h |>.elim (Finset.mem_sdiff.mp hc).2 hc_y⟩)

omit [Fintype I] in
/-- (X ∪ Y) \ (X ∩ Y) = (X \ Y) ∪ (Y \ X). -/
private lemma mem_symdiff_iff (X Y : Finset I) (s : I) :
    s ∈ (X ∪ Y) \ (X ∩ Y) ↔ s ∈ (X \ Y) ∪ (Y \ X) := by
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨hx | hy, hni⟩
    · exact Or.inl ⟨hx, λ hy => hni ⟨hx, hy⟩⟩
    · exact Or.inr ⟨hy, λ hx => hni ⟨hx, hy⟩⟩
  · rintro (⟨hx, hny⟩ | ⟨hy, hnx⟩)
    · exact ⟨Or.inl hx, λ ⟨_, hy⟩ => hny hy⟩
    · exact ⟨Or.inr hy, λ ⟨hx, _⟩ => hnx hx⟩

omit [Fintype I] in
/-- X ≠ Y → (X \ Y) ∪ (Y \ X) is nonempty. -/
private lemma symdiff_nonempty (X Y : Finset I) (h : X ≠ Y) : ((X \ Y) ∪ (Y \ X)).Nonempty := by
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  apply h; ext x
  constructor
  · intro hx
    by_contra hy
    have : x ∈ (X \ Y) ∪ (Y \ X) :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hx, hy⟩))
    rw [h_empty] at this; simp at this
  · intro hy
    by_contra hx
    have : x ∈ (X \ Y) ∪ (Y \ X) :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hy, hx⟩))
    rw [h_empty] at this; simp at this

/-! ### The ordering respects equivalence -/

/-- ⊐ is irreflexive. -/
theorem strictlyBetter_irrefl (X : Finset I) :
    ¬ strictlyBetter ord i X X := by
  intro ⟨i', hi', _, _, _⟩
  simp at hi'

/-- ∼ refutes ⊐: equivalent sets are incomparable. -/
theorem degreeEquiv_not_strictlyBetter (X Y : Finset I) :
    degreeEquiv ord i X Y → ¬ strictlyBetter ord i X Y := by
  intro h_eq ⟨i', h_sdiff, _, h_ymx, h_inner⟩
  rcases h_eq with ⟨h_match, _⟩ | h2
  · -- equivCond1: i' ∈ X\Y is matched by i'' ∈ Y\X with i' ≤ i''
    obtain ⟨i'', h_i''_sdiff, h_le⟩ := h_match i' h_sdiff
    exact (h_ymx i'' h_i''_sdiff).2 h_le
  · -- equivCond2: i' ∈ (X ∪ Y) \ (X ∩ Y), dominated by X∩Y and field\(X∪Y)
    have h_symdiff : i' ∈ (X ∪ Y) \ (X ∩ Y) :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp h_sdiff).1),
         λ h => (Finset.mem_sdiff.mp h_sdiff).2 (Finset.mem_inter.mp h).2⟩
    obtain ⟨⟨i₁, h_i₁_mem, h_le₁⟩, ⟨i₂, h_i₂_mem, h_le₂⟩⟩ := h2 i' h_symdiff
    rcases h_inner with h_cap | h_comp
    · exact (h_cap i₁ h_i₁_mem).2 h_le₁
    · exact (h_comp i₂ h_i₂_mem).2 h_le₂

/-- ⊐ respects ∼ on the right — `X ⊐ Y` and `Y ∼ Z` give `X ⊐ Z`. -/
theorem strictlyBetter_respects_right (X Y Z : Finset I)
    (_hXf : X ⊆ field ord i) (hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    strictlyBetter ord i X Y → degreeEquiv ord i Y Z →
    strictlyBetter ord i X Z := by
  rintro ⟨m, hm_sd, hm_f, hm_yx, hm_inner⟩ hyz
  have hm_x := (Finset.mem_sdiff.mp hm_sd).1
  have hm_ny := (Finset.mem_sdiff.mp hm_sd).2
  rcases hm_inner with h_left | h_right
  · -- LEFT INNER: m dominates all of Y
    have m_dom_Y := dom_all_of_inter_sdiff ord m X Y h_left hm_yx
    -- z ∈ Z, z ∉ Y → lt z m (via Y∼Z matching + m_dom_Y)
    have z_ny_lt : ∀ z, z ∈ Z → z ∉ Y → ord.lt z m := by
      intro z hz hny
      rcases hyz with ⟨_, hyz_b⟩ | hyz2
      · obtain ⟨y', hy', hle⟩ := hyz_b z (Finset.mem_sdiff.mpr ⟨hz, hny⟩)
        exact ord.lt_of_le_of_lt hle (m_dom_Y y' (Finset.mem_sdiff.mp hy').1)
      · obtain ⟨⟨c, hc, hle⟩, _⟩ := hyz2 z
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hz),
            λ h => hny (Finset.mem_inter.mp h).1⟩)
        exact ord.lt_of_le_of_lt hle (m_dom_Y c (Finset.mem_inter.mp hc).1)
    -- m ∉ Z forced
    have hm_nz : m ∉ Z :=
      λ hm_z => absurd (z_ny_lt m hm_z hm_ny) (ord.lt_irrefl m)
    refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_x, hm_nz⟩, hm_f, ?_, Or.inl ?_⟩
    · intro z hz
      by_cases hz_y : z ∈ Y
      · exact hm_yx z (Finset.mem_sdiff.mpr ⟨hz_y, (Finset.mem_sdiff.mp hz).2⟩)
      · exact z_ny_lt z (Finset.mem_sdiff.mp hz).1 hz_y
    · intro c hc
      by_cases hc_y : c ∈ Y
      · exact m_dom_Y c hc_y
      · exact z_ny_lt c (Finset.mem_inter.mp hc).2 hc_y
  · -- RIGHT INNER: m dominates field ord i \ X
    have m_dom_fX := dom_fX_of_sdiff_comp ord i m X Y hm_yx h_right
    -- Helper: w ∈ X forced when m_dom_fX w gives lt w m, contradicting le m w
    have forced_in_X (w : I) (hw_f : w ∈ field ord i) (hle : ord.le m w) :
        w ∈ X := by
      by_contra h
      exact (m_dom_fX w (Finset.mem_sdiff.mpr ⟨hw_f, h⟩)).2 hle
    by_cases hm_z : m ∈ Z
    · -- m ∈ Z ∩ X: find alternative witness via Y∼Z
      -- Helper: once we have witness w ∈ X\Z with le m w, build the ⊐ proof
      suffices ∃ w, w ∈ X \ Z ∧ w ∈ field ord i ∧ ord.le m w from by
        obtain ⟨w, hw_sd, hw_f, hle⟩ := this
        refine ⟨w, hw_sd, hw_f, ?_, Or.inr ?_⟩
        · intro z hz; exact ord.lt_of_lt_of_le
            (m_dom_fX z (Finset.mem_sdiff.mpr ⟨hZf (Finset.mem_sdiff.mp hz).1,
              (Finset.mem_sdiff.mp hz).2⟩)) hle
        · intro c hc; exact ord.lt_of_lt_of_le
            (m_dom_fX c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,
              λ h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h))⟩)) hle
      rcases hyz with ⟨_, hyz_b⟩ | hyz2
      · -- cond1: m ∈ Z\Y → ∃ y₀ ∈ Y\Z, le m y₀; y₀ ∈ X forced
        obtain ⟨y₀, hy₀, hle⟩ := hyz_b m (Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩)
        exact ⟨y₀, Finset.mem_sdiff.mpr ⟨forced_in_X y₀ (hYf (Finset.mem_sdiff.mp hy₀).1) hle,
          (Finset.mem_sdiff.mp hy₀).2⟩, hYf (Finset.mem_sdiff.mp hy₀).1, hle⟩
      · -- cond2: ∃ c₂ ∈ field ord i\(Y∪Z), le m c₂; c₂ ∈ X forced
        obtain ⟨_, ⟨c₂, hc₂, hle⟩⟩ := hyz2 m
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hm_z),
            λ h => hm_ny (Finset.mem_inter.mp h).1⟩)
        exact ⟨c₂, Finset.mem_sdiff.mpr ⟨forced_in_X c₂ (Finset.mem_sdiff.mp hc₂).1 hle,
          λ h => (Finset.mem_sdiff.mp hc₂).2 (Finset.mem_union.mpr (Or.inr h))⟩,
          (Finset.mem_sdiff.mp hc₂).1, hle⟩
    · -- m ∉ Z: witness = m ∈ X\Z
      refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_x, hm_z⟩, hm_f, ?_, Or.inr ?_⟩
      · intro z hz; exact m_dom_fX z (Finset.mem_sdiff.mpr
          ⟨hZf (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩)
      · intro c hc; exact m_dom_fX c (Finset.mem_sdiff.mpr
          ⟨(Finset.mem_sdiff.mp hc).1,
           λ h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h))⟩)

/-- ⊐ respects ∼ on the left — `X ⊐ Y` and `X ∼ Z` give `Z ⊐ Y`. -/
theorem strictlyBetter_respects_left (X Y Z : Finset I)
    (hXf : X ⊆ field ord i) (_hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    strictlyBetter ord i X Y → degreeEquiv ord i X Z →
    strictlyBetter ord i Z Y := by
  rintro ⟨m, hm_sd, hm_f, hm_yx, hm_inner⟩ hxz
  have hm_x := (Finset.mem_sdiff.mp hm_sd).1
  have hm_ny := (Finset.mem_sdiff.mp hm_sd).2
  rcases hm_inner with h_left | h_right
  · -- LEFT INNER: m dominates all of Y
    have m_dom_Y := dom_all_of_inter_sdiff ord m X Y h_left hm_yx
    by_cases hm_z : m ∈ Z
    · -- m ∈ Z: witness m ∈ Z\Y
      refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩, hm_f, ?_, Or.inl ?_⟩
      · intro y hy; exact m_dom_Y y (Finset.mem_sdiff.mp hy).1
      · intro c hc; exact m_dom_Y c (Finset.mem_inter.mp hc).2
    · -- m ∉ Z: use X∼Z to find w ∈ Z with le m w, w ∉ Y forced
      -- Once we have w, the proof is uniform
      suffices ∃ w, w ∈ Z \ Y ∧ w ∈ field ord i ∧ ord.le m w from by
        obtain ⟨w, hw_sd, hw_f, hle⟩ := this
        refine ⟨w, hw_sd, hw_f, ?_, Or.inl ?_⟩
        · intro y hy; exact ord.lt_of_lt_of_le
            (m_dom_Y y (Finset.mem_sdiff.mp hy).1) hle
        · intro c hc; exact ord.lt_of_lt_of_le
            (m_dom_Y c (Finset.mem_inter.mp hc).2) hle
      -- Helper: w ∉ Y when m_dom_Y w and le m w (lt w m contradicts le m w)
      have not_in_Y (w : I) (hle : ord.le m w) : w ∉ Y :=
        λ h => (m_dom_Y w h).2 hle
      rcases hxz with ⟨hxz_a, _⟩ | hxz2
      · obtain ⟨z₀, hz₀, hle⟩ := hxz_a m (Finset.mem_sdiff.mpr ⟨hm_x, hm_z⟩)
        exact ⟨z₀, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz₀).1, not_in_Y z₀ hle⟩,
          hZf (Finset.mem_sdiff.mp hz₀).1, hle⟩
      · obtain ⟨⟨z₁, hz₁, hle⟩, _⟩ := hxz2 m
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl hm_x),
            λ h => hm_z (Finset.mem_inter.mp h).2⟩)
        exact ⟨z₁, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hz₁).2, not_in_Y z₁ hle⟩,
          hXf (Finset.mem_inter.mp hz₁).1, hle⟩
  · -- RIGHT INNER: m dominates field ord i \ X
    have m_dom_fX := dom_fX_of_sdiff_comp ord i m X Y hm_yx h_right
    -- c ∈ X\Z → lt c m (via X∼Z matching to field\X, then m_dom_fX)
    have lt_via_xz : ∀ c, c ∈ X → c ∉ Z → ord.lt c m := by
      intro c hc_x hc_nz
      rcases hxz with ⟨hxz_a, _⟩ | hxz2
      · obtain ⟨z', hz', hle⟩ := hxz_a c (Finset.mem_sdiff.mpr ⟨hc_x, hc_nz⟩)
        exact ord.lt_of_le_of_lt hle (m_dom_fX z'
          (Finset.mem_sdiff.mpr ⟨hZf (Finset.mem_sdiff.mp hz').1,
            (Finset.mem_sdiff.mp hz').2⟩))
      · obtain ⟨_, ⟨c', hc', hle⟩⟩ := hxz2 c
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl hc_x),
            λ h => hc_nz (Finset.mem_inter.mp h).2⟩)
        exact ord.lt_of_le_of_lt hle (m_dom_fX c'
          (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc').1,
            λ h => (Finset.mem_sdiff.mp hc').2 (Finset.mem_union.mpr (Or.inl h))⟩))
    -- m ∈ Z forced
    have hm_z : m ∈ Z := by
      by_contra hm_nz; exact absurd (lt_via_xz m hm_x hm_nz) (ord.lt_irrefl m)
    -- Witness m ∈ Z\Y
    refine ⟨m, Finset.mem_sdiff.mpr ⟨hm_z, hm_ny⟩, hm_f, ?_, Or.inr ?_⟩
    · intro y hy
      by_cases hy_x : y ∈ X
      · exact lt_via_xz y hy_x (Finset.mem_sdiff.mp hy).2
      · exact hm_yx y (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1, hy_x⟩)
    · intro c hc
      by_cases hc_x : c ∈ X
      · exact lt_via_xz c hc_x
          (λ h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_union.mpr (Or.inl h)))
      · exact m_dom_fX c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1, hc_x⟩)

/-- ⊐ is transitive. -/
theorem strictlyBetter_trans (X Y Z : Finset I) :
    strictlyBetter ord i X Y → strictlyBetter ord i Y Z →
    strictlyBetter ord i X Z := by
  rintro ⟨m₁, hm₁_sd, hm₁_f, hm₁_yx, hm₁_inner⟩
         ⟨m₂, hm₂_sd, hm₂_f, hm₂_zy, hm₂_inner⟩
  have hm₁_x := (Finset.mem_sdiff.mp hm₁_sd).1
  have hm₁_ny := (Finset.mem_sdiff.mp hm₁_sd).2
  have hm₂_y := (Finset.mem_sdiff.mp hm₂_sd).1
  have hm₂_nz := (Finset.mem_sdiff.mp hm₂_sd).2
  -- Key helper: z ∈ Z\X → lt z m₁ (when m₂ ≤ m₁)
  have zx_lt_m1 (hle : ord.le m₂ m₁) (z : I) (hz : z ∈ Z \ X) : ord.lt z m₁ := by
    have hz_z := (Finset.mem_sdiff.mp hz).1
    have hz_nx := (Finset.mem_sdiff.mp hz).2
    by_cases hz_y : z ∈ Y
    · exact hm₁_yx z (Finset.mem_sdiff.mpr ⟨hz_y, hz_nx⟩)
    · exact ord.lt_of_lt_of_le (hm₂_zy z (Finset.mem_sdiff.mpr ⟨hz_z, hz_y⟩)) hle
  -- Key helper: z ∈ Z\X → lt z m₂ (when m₁ ≤ m₂)
  have zx_lt_m2 (hle : ord.le m₁ m₂) (z : I) (hz : z ∈ Z \ X) : ord.lt z m₂ := by
    have hz_z := (Finset.mem_sdiff.mp hz).1
    have hz_nx := (Finset.mem_sdiff.mp hz).2
    by_cases hz_y : z ∈ Y
    · exact ord.lt_of_lt_of_le
        (hm₁_yx z (Finset.mem_sdiff.mpr ⟨hz_y, hz_nx⟩)) hle
    · exact hm₂_zy z (Finset.mem_sdiff.mpr ⟨hz_z, hz_y⟩)
  rcases ord.le_total m₂ m₁ with hle | hle
  · -- Case: m₂ ≤ m₁. Witness = m₁.
    -- m₁ ∉ Z: lt m₁ m₂ ∧ le m₂ m₁ → lt m₁ m₁
    have hm₁_nz : m₁ ∉ Z := λ h =>
      absurd (ord.lt_of_lt_of_le
        (hm₂_zy m₁ (Finset.mem_sdiff.mpr ⟨h, hm₁_ny⟩)) hle) (ord.lt_irrefl m₁)
    refine ⟨m₁, Finset.mem_sdiff.mpr ⟨hm₁_x, hm₁_nz⟩, hm₁_f, zx_lt_m1 hle, ?_⟩
    -- Inner disjunct: follows from X⊐Y's inner
    rcases hm₁_inner with h_cap | h_comp
    · -- Left: ∀ X∩Y < m₁ → ∀ X∩Z < m₁
      left; intro c hc
      have hc_x := (Finset.mem_inter.mp hc).1
      have hc_z := (Finset.mem_inter.mp hc).2
      by_cases hc_y : c ∈ Y
      · exact h_cap c (Finset.mem_inter.mpr ⟨hc_x, hc_y⟩)
      · exact ord.lt_of_lt_of_le
          (hm₂_zy c (Finset.mem_sdiff.mpr ⟨hc_z, hc_y⟩)) hle
    · -- Right: ∀ field\(X∪Y) < m₁ → ∀ field\(X∪Z) < m₁
      right; intro c hc
      have hc_f := (Finset.mem_sdiff.mp hc).1
      have hc_nxz := (Finset.mem_sdiff.mp hc).2
      have hc_nx : c ∉ X := λ h => hc_nxz (Finset.mem_union.mpr (Or.inl h))
      have hc_nz : c ∉ Z := λ h => hc_nxz (Finset.mem_union.mpr (Or.inr h))
      by_cases hc_y : c ∈ Y
      · exact hm₁_yx c (Finset.mem_sdiff.mpr ⟨hc_y, hc_nx⟩)
      · exact h_comp c (Finset.mem_sdiff.mpr
          ⟨hc_f, λ h => Finset.mem_union.mp h |>.elim hc_nx hc_y⟩)
  · -- Case: m₁ ≤ m₂. Witness = m₂.
    -- m₂ ∈ X: lt m₂ m₁ ∧ le m₁ m₂ → lt m₂ m₂
    have hm₂_x : m₂ ∈ X := by
      by_contra h; exact absurd (ord.lt_of_lt_of_le
        (hm₁_yx m₂ (Finset.mem_sdiff.mpr ⟨hm₂_y, h⟩)) hle) (ord.lt_irrefl m₂)
    refine ⟨m₂, Finset.mem_sdiff.mpr ⟨hm₂_x, hm₂_nz⟩, hm₂_f, zx_lt_m2 hle, ?_⟩
    -- Inner disjunct: follows from Y⊐Z's inner
    rcases hm₂_inner with h_cap | h_comp
    · -- Left: ∀ Y∩Z < m₂ → ∀ X∩Z < m₂
      left; intro c hc
      have hc_x := (Finset.mem_inter.mp hc).1
      have hc_z := (Finset.mem_inter.mp hc).2
      by_cases hc_y : c ∈ Y
      · exact h_cap c (Finset.mem_inter.mpr ⟨hc_y, hc_z⟩)
      · exact hm₂_zy c (Finset.mem_sdiff.mpr ⟨hc_z, hc_y⟩)
    · -- Right: ∀ field\(Y∪Z) < m₂ → ∀ field\(X∪Z) < m₂
      right; intro c hc
      have hc_f := (Finset.mem_sdiff.mp hc).1
      have hc_nxz := (Finset.mem_sdiff.mp hc).2
      have hc_nx : c ∉ X := λ h => hc_nxz (Finset.mem_union.mpr (Or.inl h))
      have hc_nz : c ∉ Z := λ h => hc_nxz (Finset.mem_union.mpr (Or.inr h))
      by_cases hc_y : c ∈ Y
      · exact ord.lt_of_lt_of_le
          (hm₁_yx c (Finset.mem_sdiff.mpr ⟨hc_y, hc_nx⟩)) hle
      · exact h_comp c (Finset.mem_sdiff.mpr
          ⟨hc_f, λ h => Finset.mem_union.mp h |>.elim hc_y hc_nz⟩)

/-- trichotomy — `X ∼ Y`, `X ⊐ Y`, or `Y ⊐ X`. -/
theorem strictlyBetter_total (X Y : Finset I)
    (hX : X ⊆ field ord i) (hY : Y ⊆ field ord i) :
    degreeEquiv ord i X Y ∨ strictlyBetter ord i X Y ∨
    strictlyBetter ord i Y X := by
  by_cases h_eq : X = Y
  · exact Or.inl (h_eq ▸ degreeEquiv_refl ord i X)
  · obtain ⟨m, hm, hm_max⟩ := ord.exists_le_max _ (symdiff_nonempty X Y h_eq)
    -- Helper: any element of the symdiff ≤ m
    have hm_max' : ∀ s ∈ (X \ Y) ∪ (Y \ X), ord.le s m := hm_max
    rcases Finset.mem_union.mp hm with hm_xy | hm_yx
    · -- m ∈ X\Y: either equivCond1, or strictlyBetter X Y
      have hm_field : m ∈ field ord i := hX (Finset.mem_sdiff.mp hm_xy).1
      by_cases h_all_yx : ∀ y ∈ Y \ X, ord.lt y m
      · -- All Y\X < m: check inner disjunct
        by_cases h_cap : ∀ c ∈ X ∩ Y, ord.lt c m
        · exact Or.inr (Or.inl ⟨m, hm_xy, hm_field, h_all_yx, Or.inl h_cap⟩)
        · by_cases h_comp : ∀ c ∈ field ord i \ (X ∪ Y), ord.lt c m
          · exact Or.inr (Or.inl ⟨m, hm_xy, hm_field, h_all_yx, Or.inr h_comp⟩)
          · -- Neither inner holds: equivCond2
            push Not at h_cap h_comp
            obtain ⟨c₁, hc₁_mem, hc₁_nlt⟩ := h_cap
            obtain ⟨c₂, hc₂_mem, hc₂_nlt⟩ := h_comp
            have hc₁_ge := ord.le_of_not_lt hc₁_nlt
            have hc₂_ge := ord.le_of_not_lt hc₂_nlt
            exact Or.inl (Or.inr (λ s hs => by
              have h_le_sm := hm_max' s ((mem_symdiff_iff X Y s).mp hs)
              exact ⟨⟨c₁, hc₁_mem, ord.le_trans s m c₁ h_le_sm hc₁_ge⟩,
                     ⟨c₂, hc₂_mem, ord.le_trans s m c₂ h_le_sm hc₂_ge⟩⟩))
      · -- ∃ y₀ ∈ Y\X with ¬(lt y₀ m): equivCond1
        push Not at h_all_yx
        obtain ⟨y₀, hy₀_mem, hy₀_nlt⟩ := h_all_yx
        have hy₀_ge := ord.le_of_not_lt hy₀_nlt
        exact Or.inl (Or.inl
          ⟨λ x hx => ⟨y₀, hy₀_mem,
              ord.le_trans x m y₀
                (hm_max' x (Finset.mem_union.mpr (Or.inl hx))) hy₀_ge⟩,
           λ y hy => ⟨m, hm_xy,
              hm_max' y (Finset.mem_union.mpr (Or.inr hy))⟩⟩)
    · -- m ∈ Y\X: symmetric case — either equivCond1, or strictlyBetter Y X
      have hm_field : m ∈ field ord i := hY (Finset.mem_sdiff.mp hm_yx).1
      by_cases h_all_xy : ∀ x ∈ X \ Y, ord.lt x m
      · -- All X\Y < m: check inner disjunct
        by_cases h_cap : ∀ c ∈ Y ∩ X, ord.lt c m
        · exact Or.inr (Or.inr ⟨m, hm_yx, hm_field, h_all_xy, Or.inl h_cap⟩)
        · by_cases h_comp : ∀ c ∈ field ord i \ (Y ∪ X), ord.lt c m
          · exact Or.inr (Or.inr ⟨m, hm_yx, hm_field, h_all_xy, Or.inr h_comp⟩)
          · -- Neither inner holds: equivCond2
            push Not at h_cap h_comp
            obtain ⟨c₁, hc₁_mem, hc₁_nlt⟩ := h_cap
            obtain ⟨c₂, hc₂_mem, hc₂_nlt⟩ := h_comp
            have hc₁_ge := ord.le_of_not_lt hc₁_nlt
            have hc₂_ge := ord.le_of_not_lt hc₂_nlt
            exact Or.inl (Or.inr (λ s hs => by
              have h_le_sm := hm_max' s ((mem_symdiff_iff X Y s).mp hs)
              exact ⟨⟨c₁, by rw [Finset.inter_comm]; exact hc₁_mem,
                      ord.le_trans s m c₁ h_le_sm hc₁_ge⟩,
                     ⟨c₂, by rw [Finset.union_comm]; exact hc₂_mem,
                      ord.le_trans s m c₂ h_le_sm hc₂_ge⟩⟩))
      · -- ∃ x₀ ∈ X\Y with ¬(lt x₀ m): equivCond1
        push Not at h_all_xy
        obtain ⟨x₀, hx₀_mem, hx₀_nlt⟩ := h_all_xy
        have hx₀_ge := ord.le_of_not_lt hx₀_nlt
        exact Or.inl (Or.inl
          ⟨λ x hx => ⟨m, hm_yx,
              hm_max' x (Finset.mem_union.mpr (Or.inl hx))⟩,
           λ y hy => ⟨x₀, hx₀_mem,
              ord.le_trans y m x₀
                (hm_max' y (Finset.mem_union.mpr (Or.inr hy))) hx₀_ge⟩⟩)

/-! ### Transitivity -/

/-- ∼ is transitive on field-subsets, via trichotomy and respect for equivalence. -/
theorem degreeEquiv_trans (X Y Z : Finset I)
    (hXf : X ⊆ field ord i) (hYf : Y ⊆ field ord i) (hZf : Z ⊆ field ord i) :
    degreeEquiv ord i X Y → degreeEquiv ord i Y Z →
    degreeEquiv ord i X Z := by
  intro hxy hyz
  by_contra h_neq
  rcases strictlyBetter_total ord i X Z hXf hZf with h | h | h
  · exact h_neq h
  · -- X ⊐ Z, Z ∼ Y → X ⊐ Y, contradicts X ∼ Y
    exact degreeEquiv_not_strictlyBetter ord i X Y hxy
      (strictlyBetter_respects_right ord i X Z Y hXf hZf hYf h
        (degreeEquiv_symm ord i Y Z hyz))
  · -- Z ⊐ X, X ∼ Y → Z ⊐ Y, contradicts Y ∼ Z
    exact degreeEquiv_not_strictlyBetter ord i Z Y
      (degreeEquiv_symm ord i Y Z hyz)
      (strictlyBetter_respects_right ord i Z X Y hZf hXf hYf h hxy)

/-- ∼ as a `Setoid` on field-subsets (transitivity needs the field bound). -/
def metalinguisticSetoid :
    Setoid {X : Finset I // X ⊆ field ord i} where
  r X Y := degreeEquiv ord i X.1 Y.1
  iseqv := {
    refl := λ X => degreeEquiv_refl ord i X.1
    symm := λ {X Y} h => degreeEquiv_symm ord i X.1 Y.1 h
    trans := λ {X Y Z} hxy hyz =>
      degreeEquiv_trans ord i X.1 Y.1 Z.1 X.2 Y.2 Z.2 hxy hyz
  }

end DegreeTheory

/-! ### Metalinguistic degrees -/

/-- Metalinguistic degrees: ∼-classes of interpretation sets. The degree of
a sentence is `deg` of its denotation (`formulaDeg`). -/
def MetaDegree (I : Type*) [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) :=
  Quotient (metalinguisticSetoid ord i)

/-- The metalinguistic degree of an interpretation set. -/
def deg {I : Type*} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X : Finset I) (hX : X ⊆ field ord i) :
    MetaDegree I ord i :=
  Quotient.mk (metalinguisticSetoid ord i) ⟨X, hX⟩
/-! ### The comparative and the equative on degrees -/

/-- Membership in `field`: j ∈ I_i iff j ≤ i. -/
private theorem mem_field_iff {I : Type*} [Fintype I] [DecidableEq I]
    {ord : SemanticOrdering I} {i j : I} :
    j ∈ field ord i ↔ ord.le j i := by
  simp [field]

/-- Membership in `denotation`: j ∈ ⟦φ⟧_i iff j ≤ i and ⟦φ⟧^j = 1. -/
private theorem mem_denotation_iff {L : Language} {I W E : Type*}
    [Fintype I] [DecidableEq I]
    {interp : I → W → L.Structure E}
    {φ : ComparativeFormula L E}
    {ord : SemanticOrdering I} {i j : I} {w : W} :
    j ∈ denotation interp ord i φ w ↔
    ord.le j i ∧ EvalRevised interp φ ord j w := by
  simp [denotation, field]

noncomputable section DegreeBridges

variable {L : Language} {I W E : Type*} [Fintype I] [DecidableEq I]
  (interp : I → W → L.Structure E) (ord : SemanticOrdering I) (i : I)

/-- The metalinguistic degree of a formula's denotation. -/
def formulaDeg (φ : ComparativeFormula L E) (w : W) : MetaDegree I ord i :=
  deg ord i (denotation interp ord i φ w) (denotation_subset_field interp ord i φ w)

variable (A B : ComparativeFormula L E) (w : W)

/-- revised MC holds iff denotation of A ⊐ denotation of B. -/
theorem mc_iff_degree_gt :
    EvalRevised interp (.comp A B) ord i w ↔
    strictlyBetter ord i (denotation interp ord i A w)
      (denotation interp ord i B w) := by
  rw [evalRevised_mc_iff]
  constructor
  · rintro ⟨i', h_le, h_A, h_B, h_dom⟩
    refine ⟨i', Finset.mem_sdiff.mpr
        ⟨mem_denotation_iff.mpr ⟨h_le, h_A⟩,
         λ h => h_B (mem_denotation_iff.mp h).2⟩,
      mem_field_iff.mpr h_le, ?_, ?_⟩
    · intro i'' h_mem
      obtain ⟨h_inY, h_ninX⟩ := Finset.mem_sdiff.mp h_mem
      obtain ⟨h_le'', h_B''⟩ := mem_denotation_iff.mp h_inY
      rcases h_dom with h1 | h2
      · exact h1 i'' h_le'' h_B''
      · exact h2 i'' h_le'' λ h_A'' => h_ninX (mem_denotation_iff.mpr ⟨h_le'', h_A''⟩)
    · rcases h_dom with h1 | h2
      · exact Or.inl λ i'' h_mem =>
          h1 i'' (mem_denotation_iff.mp (Finset.mem_inter.mp h_mem).2).1
            (mem_denotation_iff.mp (Finset.mem_inter.mp h_mem).2).2
      · refine Or.inr λ i'' h_mem => ?_
        have h_sd := Finset.mem_sdiff.mp h_mem
        exact h2 i'' (mem_field_iff.mp h_sd.1) λ h_A'' =>
          h_sd.2 (Finset.mem_union.mpr
            (Or.inl (mem_denotation_iff.mpr ⟨mem_field_iff.mp h_sd.1, h_A''⟩)))
  · rintro ⟨i', h_sdiff, h_field, h_ymx, h_inner⟩
    obtain ⟨h_inX, h_ninY⟩ := Finset.mem_sdiff.mp h_sdiff
    obtain ⟨h_le, h_A⟩ := mem_denotation_iff.mp h_inX
    have h_B : ¬ EvalRevised interp B ord i' w :=
      λ h => h_ninY (mem_denotation_iff.mpr ⟨h_le, h⟩)
    refine ⟨i', h_le, h_A, h_B, ?_⟩
    rcases h_inner with h1 | h2
    · left; intro i'' h_le'' h_B''
      by_cases h_A'' : EvalRevised interp A ord i'' w
      · exact h1 i'' (Finset.mem_inter.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_A''⟩,
           mem_denotation_iff.mpr ⟨h_le'', h_B''⟩⟩)
      · exact h_ymx i'' (Finset.mem_sdiff.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_B''⟩,
           λ h => h_A'' (mem_denotation_iff.mp h).2⟩)
    · right; intro i'' h_le'' h_A''
      by_cases h_B'' : EvalRevised interp B ord i'' w
      · exact h_ymx i'' (Finset.mem_sdiff.mpr
          ⟨mem_denotation_iff.mpr ⟨h_le'', h_B''⟩,
           λ h => h_A'' (mem_denotation_iff.mp h).2⟩)
      · exact h2 i'' (Finset.mem_sdiff.mpr
          ⟨mem_field_iff.mpr h_le'',
           λ h => (Finset.mem_union.mp h).elim
             (λ h => h_A'' (mem_denotation_iff.mp h).2)
             (λ h => h_B'' (mem_denotation_iff.mp h).2)⟩)

/-- ME holds iff denotations have the same degree — the Boolean-free
bridge from `EvalRevised` to the algebraic degree structure. Forward direction
uses `strictlyBetter_total`. -/
theorem me_iff_same_degree :
    EvalRevised interp (A.equi B) ord i w ↔
    degreeEquiv ord i (denotation interp ord i A w)
      (denotation interp ord i B w) := by
  have hX := denotation_subset_field interp ord i A w
  have hY := denotation_subset_field interp ord i B w
  constructor
  · intro h
    obtain ⟨h1, h2⟩ : ¬ EvalRevised interp (.comp A B) ord i w ∧
        ¬ EvalRevised interp (.comp B A) ord i w := h
    rcases strictlyBetter_total ord i _ _ hX hY with h | h | h
    · exact h
    · exact absurd ((mc_iff_degree_gt interp ord i A B w).mpr h) h1
    · exact absurd ((mc_iff_degree_gt interp ord i B A w).mpr h) h2
  · intro h_eq
    exact show ¬ EvalRevised interp (.comp A B) ord i w ∧
        ¬ EvalRevised interp (.comp B A) ord i w from
      ⟨λ h => degreeEquiv_not_strictlyBetter ord i _ _ h_eq
          ((mc_iff_degree_gt interp ord i A B w).mp h),
       λ h => degreeEquiv_not_strictlyBetter ord i _ _
          (degreeEquiv_symm ord i _ _ h_eq)
          ((mc_iff_degree_gt interp ord i B A w).mp h)⟩

end DegreeBridges
/-! ### The metalinguistic degree scale

The results above make `MetaDegree` a bounded linear order, a scale in the degree
substrate's sense. The instances below package that, and
`mc_iff_comparativeSem` cashes it out: the revised MC is the degree
substrate's binary comparative over the measure function `formulaDeg`. -/

noncomputable section Scale

variable {L : Language} {I W E : Type*} [Fintype I] [DecidableEq I]
  (interp : I → W → L.Structure E) (ord : SemanticOrdering I) (i : I)

instance [DecidableRel ord.le] (X Y : Finset I) : Decidable (equivCond1 ord X Y) := by
  unfold equivCond1; infer_instance

instance [DecidableRel ord.le] (X Y : Finset I) : Decidable (equivCond2 ord i X Y) := by
  unfold equivCond2; infer_instance

instance [DecidableRel ord.le] (X Y : Finset I) : Decidable (degreeEquiv ord i X Y) := by
  unfold degreeEquiv; infer_instance

instance [DecidableRel ord.le] (X Y : Finset I) : Decidable (strictlyBetter ord i X Y) := by
  unfold strictlyBetter; infer_instance

/-- nothing is strictly better than the full field `I_i`
(packaged as `OrderTop` below). -/
theorem not_strictlyBetter_field (X : Finset I) (hX : X ⊆ field ord i) :
    ¬ strictlyBetter ord i X (field ord i) := by
  rintro ⟨i', hi', -⟩
  exact (Finset.mem_sdiff.mp hi').2 (hX (Finset.mem_sdiff.mp hi').1)

/-- the empty set is strictly better than nothing
(packaged as `OrderBot` below). -/
theorem not_strictlyBetter_empty (X : Finset I) :
    ¬ strictlyBetter ord i (∅ : Finset I) X := by
  rintro ⟨i', hi', -⟩
  simp at hi'

/-- packaged as a congruence: ⊐ is invariant under ∼ on both sides. -/
theorem strictlyBetter_congr {X X' Y Y' : Finset I}
    (hXf : X ⊆ field ord i) (hX'f : X' ⊆ field ord i)
    (hYf : Y ⊆ field ord i) (hY'f : Y' ⊆ field ord i)
    (hX : degreeEquiv ord i X X') (hY : degreeEquiv ord i Y Y') :
    strictlyBetter ord i X Y ↔ strictlyBetter ord i X' Y' :=
  ⟨λ h => strictlyBetter_respects_right ord i X' Y Y' hX'f hYf hY'f
      (strictlyBetter_respects_left ord i X Y X' hXf hYf hX'f h hX) hY,
   λ h => strictlyBetter_respects_right ord i X Y' Y hXf hY'f hYf
      (strictlyBetter_respects_left ord i X' Y' X hX'f hY'f hXf h
        (degreeEquiv_symm ord i X X' hX)) (degreeEquiv_symm ord i Y Y' hY)⟩

instance [DecidableRel ord.le] : DecidableEq (MetaDegree I ord i) := λ d₁ d₂ =>
  Quotient.recOnSubsingleton₂ d₁ d₂ λ X Y =>
    decidable_of_iff (degreeEquiv ord i X.1 Y.1)
      ⟨λ h => Quotient.sound h, λ h => Quotient.exact h⟩

/-- The scale order: `deg X ≤ deg Y` iff X is not strictly better than Y
(well-defined on ∼-classes by `strictlyBetter_congr`). -/
protected def MetaDegree.le (d₁ d₂ : MetaDegree I ord i) : Prop :=
  Quotient.lift₂ (λ X Y => ¬ strictlyBetter ord i X.1 Y.1)
    (λ a₁ b₁ a₂ b₂ h₁ h₂ => propext (not_congr
      (strictlyBetter_congr ord i a₁.2 a₂.2 b₁.2 b₂.2 h₁ h₂))) d₁ d₂

/-- `MetaDegree` is a linear order: , packaged. Irreflexivity,
transitivity, and totality of ⊐ become the order axioms on the quotient. -/
instance : LinearOrder (MetaDegree I ord i) where
  le := MetaDegree.le ord i
  le_refl d := Quotient.inductionOn d λ X => strictlyBetter_irrefl ord i X.1
  le_trans d₁ d₂ d₃ := Quotient.inductionOn₃ d₁ d₂ d₃ λ X Y Z h₁ h₂ hXZ => by
    rcases strictlyBetter_total ord i X.1 Y.1 X.2 Y.2 with heq | hXY | hYX
    · exact h₂ (strictlyBetter_respects_left ord i X.1 Z.1 Y.1 X.2 Z.2 Y.2 hXZ heq)
    · exact h₁ hXY
    · exact h₂ (strictlyBetter_trans ord i Y.1 X.1 Z.1 hYX hXZ)
  le_antisymm d₁ d₂ := Quotient.inductionOn₂ d₁ d₂ λ X Y h₁ h₂ => by
    rcases strictlyBetter_total ord i X.1 Y.1 X.2 Y.2 with heq | hXY | hYX
    · exact Quotient.sound heq
    · exact absurd hXY h₁
    · exact absurd hYX h₂
  le_total d₁ d₂ := Quotient.inductionOn₂ d₁ d₂ λ X Y => by
    by_cases h : strictlyBetter ord i X.1 Y.1
    · exact Or.inr λ hYX => strictlyBetter_irrefl ord i X.1
        (strictlyBetter_trans ord i X.1 Y.1 X.1 h hYX)
    · exact Or.inl h
  toDecidableLE := Classical.decRel _

/-- , packaged: the tautology's degree is ⊤, the contradiction's ⊥. -/
instance : BoundedOrder (MetaDegree I ord i) where
  top := deg ord i (field ord i) (Finset.Subset.refl _)
  le_top d := Quotient.inductionOn d λ X => not_strictlyBetter_field ord i X.1 X.2
  bot := deg ord i ∅ (Finset.empty_subset _)
  bot_le d := Quotient.inductionOn d λ X => not_strictlyBetter_empty ord i X.1

@[simp] theorem deg_le_deg_iff {X Y : Finset I}
    (hX : X ⊆ field ord i) (hY : Y ⊆ field ord i) :
    deg ord i X hX ≤ deg ord i Y hY ↔ ¬ strictlyBetter ord i X Y := Iff.rfl

/-- The strict order on metalinguistic degrees is exactly ⊐ (arguments
flipped): Y's degree lies below X's iff X is strictly better. -/
theorem deg_lt_deg_iff {X Y : Finset I}
    (hX : X ⊆ field ord i) (hY : Y ⊆ field ord i) :
    deg ord i Y hY < deg ord i X hX ↔ strictlyBetter ord i X Y := by
  rw [lt_iff_le_not_ge]
  constructor
  · rintro ⟨-, h⟩
    exact not_not.mp h
  · intro h
    exact ⟨λ hYX => strictlyBetter_irrefl ord i Y
        (strictlyBetter_trans ord i Y X Y hYX h), not_not.mpr h⟩

/-- **The paper's (59), in the substrate's vocabulary**: the revised
metalinguistic comparative IS the degree substrate's binary comparative
(`Degree.comparativeSem`, positive direction) over the metalinguistic measure
function `formulaDeg`. Metagradability thereby instantiates the degree
substrate's central object — a measure `μ : E → D` into a bounded linear
scale — with `E` the formulas and `D` the `MetaDegree` scale. -/
theorem mc_iff_comparativeSem (A B : ComparativeFormula L E) (w : W) :
    EvalRevised interp (.comp A B) ord i w ↔
    Degree.comparativeSem (λ φ => formulaDeg interp ord i φ w) A B .positive := by
  rw [mc_iff_degree_gt]
  simp only [Degree.comparativeSem, gt_iff_lt]
  exact (deg_lt_deg_iff ord i (denotation_subset_field interp ord i A w)
    (denotation_subset_field interp ord i B w)).symm

end Scale

/-! ### Finite models -/

/-- One world. -/
inductive W | w0
  deriving DecidableEq, Repr, Fintype

/-- One entity: Ann. -/
inductive Entity | ann
  deriving DecidableEq, Repr, Fintype

/-- Three interpretations. -/
inductive I3 | i0 | i1 | i2
  deriving DecidableEq, Repr, Fintype

/-- The linear ordering `i0 < i1 < i2`. -/
def ord₃ : SemanticOrdering I3 :=
  .ofBool
    (λ i j => match i, j with
      | .i0, _ => true
      | .i1, .i0 => false
      | .i1, _ => true
      | .i2, .i2 => true
      | .i2, _ => false)
    (by intro i; cases i <;> rfl)
    (by intro i j k hij hjk; cases i <;> cases j <;> cases k <;> simp_all)
    (by intro i j; cases i <;> cases j <;> simp)

instance : DecidableRel ord₃.le := λ _ _ => inferInstanceAs (Decidable (_ = true))

/-- An interpretation family over a monadic language from a truth table. -/
@[instance_reducible] def interpOf {Sym I E : Type*} (f : I → Sym → E → Bool) :
    I → W → (Language.monadic Sym).Structure E :=
  λ i _ => monadic.structure λ P e => f i P e = true

instance {Sym I E : Type*} (f : I → Sym → E → Bool) : DecidableAtoms (interpOf f) :=
  inferInstance

/-- The predicates *linguist* and *philosopher*. -/
inductive Pred | linguist | philosopher
  deriving DecidableEq, Repr, Fintype

/-- *Ann is a linguist*. -/
abbrev La : ComparativeFormula (Language.monadic Pred) Entity := .matom Pred.linguist .ann

/-- *Ann is a philosopher*. -/
abbrev Pa : ComparativeFormula (Language.monadic Pred) Entity := .matom Pred.philosopher .ann

/-- Ann is a philosopher at `i0`, a linguist at `i1`, both at `i2`. -/
@[instance_reducible] def both : I3 → W → (Language.monadic Pred).Structure Entity :=
  interpOf λ i P _ => match i, P with
    | .i0, .philosopher => true
    | .i0, .linguist => false
    | .i1, .linguist => true
    | .i1, .philosopher => false
    | .i2, _ => true

/-- Ann is a philosopher at `i0`, a linguist at `i1`, neither at `i2`. -/
@[instance_reducible] def neither : I3 → W → (Language.monadic Pred).Structure Entity :=
  interpOf λ i P _ => match i, P with
    | .i0, .philosopher => true
    | .i1, .linguist => true
    | _, _ => false

/-- Observation 1: *Ann is more a linguist than a philosopher* is consistent with her being
both, and with her being neither. -/
theorem comp_consistent_with_both_and_neither :
    (Eval both (.comp La Pa) ord₃ .i2 .w0 ∧ Eval both La ord₃ .i2 .w0 ∧
      Eval both Pa ord₃ .i2 .w0) ∧
    (Eval neither (.comp La Pa) ord₃ .i2 .w0 ∧ ¬ Eval neither La ord₃ .i2 .w0 ∧
      ¬ Eval neither Pa ord₃ .i2 .w0) := by
  decide

/-- Two tied interpretations. -/
inductive I2 | j0 | j1
  deriving DecidableEq, Repr, Fintype

/-- The ordering with `j0` and `j1` tied at the top. -/
def tiedOrd : SemanticOrdering I2 :=
  .ofBool (λ _ _ => true) (by intro i; cases i <;> rfl)
    (by intro i j k _ _; cases i <;> cases j <;> cases k <;> rfl)
    (by intro i j; left; cases i <;> cases j <;> rfl)

instance : DecidableRel tiedOrd.le := λ _ _ => inferInstanceAs (Decidable (_ = true))

/-- Ann is a linguist at `j0` and a philosopher at `j1`. -/
@[instance_reducible] def tied : I2 → W → (Language.monadic Pred).Structure Entity :=
  interpOf λ i P _ => match i, P with
    | .j0, .linguist => true
    | .j1, .philosopher => true
    | _, _ => false

/-- Observation 5: *Ann is as much a linguist as not* is consistent, a borderline case. -/
theorem equi_not_consistent : Eval tied (La.equi (.not La)) tiedOrd .j0 .w0 := by decide

/-- Acceptance is nonclassical: the tautology is accepted on the tied model while the
disjunction of the two comparatives it splits into is not, as with [yalcin-2007]'s
informational entailment. -/
theorem accepted_sup_not_accepted_comp :
    AssertoricContent tied (.sup La (.not La)) tiedOrd .w0 ∧
      ¬ AssertoricContent tied (.sup (.comp La (.not La)) (.comp (.not La) La)) tiedOrd .w0 := by
  decide

/-- Modus tollens fails for acceptance: *if A then more A than not* is valid, its consequent's
negation is accepted on the tied model, yet `¬A` is not. -/
theorem modus_tollens_not_accepted :
    AssertoricContent tied (.not (.comp La (.not La))) tiedOrd .w0 ∧
      ¬ AssertoricContent tied (.not La) tiedOrd .w0 := by
  decide

/-- The distance function on `ord₃` whose thresholds reach one level down. -/
def dist₃ : DistanceFunction I3 ord₃ where
  close i i' := (match i, i' with
    | .i0, .i0 => true
    | .i1, .i0 => true
    | .i1, .i1 => true
    | .i2, .i1 => true
    | .i2, .i2 => true
    | _, _ => false : Bool) = true
  centered := by decide
  topBounded := by decide
  convex := by decide
  noncontractive := by decide

instance : DecidableRel dist₃.close := λ _ _ => inferInstanceAs (Decidable (_ = true))

/-- *sorta A* and *mostly A* are consistent with `¬A`: at the top of the model where Ann is
neither, a close lower level makes her a linguist. -/
theorem sorta_mostly_consistent_with_not :
    ¬ Eval neither La ord₃ .i2 .w0 ∧ EvalSorta neither La ord₃ dist₃ .i2 .w0 ∧
      EvalMostly neither La ord₃ dist₃ .i2 .w0 := by
  decide

/-- `A` does not entail *very A*: a close interpretation may falsify it. -/
theorem not_very_of_eval : Eval both La ord₃ .i1 .w0 ∧ ¬ EvalVery both La ord₃ dist₃ .i1 .w0 := by
  decide

/-- The metalinguistic conditional is not the material conditional: *if Ann is a linguist, she
is a philosopher* fails at the top of the model where she is both. -/
theorem mcond_not_material : ¬ EvalMCond both La Pa ord₃ .i2 .w0 := by decide

/-! ### No Reversal -/

/-- Two entities for a gradable predicate. -/
inductive Entity2 | ann | ben
  deriving DecidableEq, Repr, Fintype

/-- The predicate *tall*. -/
inductive Pred1 | tall
  deriving DecidableEq, Repr, Fintype

/-- *Ann is tall*. -/
abbrev Ta : ComparativeFormula (Language.monadic Pred1) Entity2 := .matom Pred1.tall .ann

/-- *Ben is tall*. -/
abbrev Tb : ComparativeFormula (Language.monadic Pred1) Entity2 := .matom Pred1.tall .ben

/-- Nested extensions of *tall*: nobody at `i0`, Ann at `i1`, both at `i2`. -/
@[instance_reducible] def nested : I3 → W → (Language.monadic Pred1).Structure Entity2 :=
  interpOf λ i _ e => match i, e with
    | .i0, _ => false
    | .i1, .ann => true
    | .i1, .ben => false
    | .i2, _ => true

/-- No Reversal holds for the nested extensions, in the direction the bridge consumes. -/
theorem noReversal_nested : NoReversal nested ord₃ Pred1.tall .w0 .ben .ann := by decide

/-- *Ann is taller than Ben* holds from `i1` up and its converse nowhere. -/
theorem ann_taller_nested :
    Eval nested (.comp Ta Tb) ord₃ .i1 .w0 ∧ ∀ i : I3, ¬ Eval nested (.comp Tb Ta) ord₃ i .w0 := by
  decide

/-- Extensions of *tall* that reverse: Ann at `i0`, Ben at `i1`, both at `i2`. -/
@[instance_reducible] def reversing : I3 → W → (Language.monadic Pred1).Structure Entity2 :=
  interpOf λ i _ e => match i, e with
    | .i0, .ann => true
    | .i0, .ben => false
    | .i1, .ann => false
    | .i1, .ben => true
    | .i2, _ => true

/-- Without No Reversal the comparative and the delineation comparative come apart: the
reversing model violates it, the comparative fails at the top, and the delineation
comparative holds there. -/
theorem diverge_without_noReversal :
    ¬ NoReversal reversing ord₃ Pred1.tall .w0 .ben .ann ∧
    ¬ Eval reversing (.comp Ta Tb) ord₃ .i2 .w0 ∧
    Degree.Delineation.comparativeSem
      (interpretationDelineation reversing ord₃ Pred1.tall .w0 .i2) .ann .ben :=
  ⟨by decide, by decide,
    (delineation_comparativeSem_iff reversing ord₃ Pred1.tall .w0 .i2 .ann .ben).mpr
      ⟨.i0, by decide, by decide, by decide⟩⟩

/-! ### Equative transitivity -/

/-- Three predicates. -/
inductive Pred3 | linguist | philosopher | psychologist
  deriving DecidableEq, Repr, Fintype

/-- Four interpretations. -/
inductive I4 | i | j | k | l
  deriving DecidableEq, Repr, Fintype

/-- The ordering `l < j ≡ k < i`; the tie in the middle is what makes both equatives hold. -/
def ord₄ : SemanticOrdering I4 :=
  .ofBool
    (λ x y => match x, y with
      | .l, _ => true
      | .j, .l => false
      | .j, _ => true
      | .k, .l => false
      | .k, _ => true
      | .i, .i => true
      | .i, _ => false)
    (by intro x; cases x <;> rfl)
    (by intro x y z hxy hyz; cases x <;> cases y <;> cases z <;> simp_all)
    (by intro x y; cases x <;> cases y <;> simp)

instance : DecidableRel ord₄.le := λ _ _ => inferInstanceAs (Decidable (_ = true))

/-- The supplement's counterexample: Ann is all three at `i`, a linguist and psychologist at
`j`, a philosopher at `k`, a linguist and philosopher at `l`. -/
@[instance_reducible] def counterexample : I4 → W → (Language.monadic Pred3).Structure Entity :=
  interpOf λ idx P _ => match idx, P with
    | .i, _ => true
    | .j, .philosopher => false
    | .j, _ => true
    | .k, .philosopher => true
    | .k, _ => false
    | .l, .psychologist => false
    | .l, _ => true

/-- *Ann is a linguist*, *a philosopher*, *a psychologist*. -/
abbrev La₄ : ComparativeFormula (Language.monadic Pred3) Entity := .matom Pred3.linguist .ann
abbrev Pa₄ : ComparativeFormula (Language.monadic Pred3) Entity := .matom Pred3.philosopher .ann
abbrev Ca₄ : ComparativeFormula (Language.monadic Pred3) Entity := .matom Pred3.psychologist .ann

/-- The basic equative is not transitive: linguist and philosopher, philosopher and
psychologist, but Ann is more a linguist than a psychologist, vacuously, since no ranked
interpretation makes her a psychologist and not a linguist. -/
theorem equi_not_trans :
    Eval counterexample (La₄.equi Pa₄) ord₄ .i .w0 ∧
      Eval counterexample (Pa₄.equi Ca₄) ord₄ .i .w0 ∧
      Eval counterexample (.comp La₄ Ca₄) ord₄ .i .w0 := by
  decide

/-- The revised semantics blocks the vacuous witness and restores transitivity on the same
model. -/
theorem equiRevised_trans :
    EvalRevised counterexample (La₄.equi Pa₄) ord₄ .i .w0 ∧
      EvalRevised counterexample (Pa₄.equi Ca₄) ord₄ .i .w0 ∧
      EvalRevised counterexample (La₄.equi Ca₄) ord₄ .i .w0 := by
  decide

end RudolphKocurek2024

