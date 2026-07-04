/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Focus.Interpretation
import Linglib.Semantics.Questions.Hamblin

/-!
# Focus antecedents

The anaphoric source of the squiggle's contrast set ([rooth-1992]):
what the preceding discourse supplies — a question, a prior assertion
to correct, explicitly offered alternatives, or a parallel focus
([uhmann-1991]'s focus-control taxonomy, adopted by
[hartmann-zimmermann-2007] §1.2). `Use` classifies the shapes;
felicity (`Antecedent.Admits`) is `fip` on the antecedent's contrast
set, uniformly across uses — and `use_not_factorsThrough_contrastSet`
shows the four-way split is invisible to the semantics.

## Implementation notes

Payloads are flat Hamblin sets (`PropFocusValue`), keeping antecedents
over finite models `decide`-friendly; the inquisitive layer plugs in
via `Antecedent.ofQuestion` and `Question.alt`, with
`alt_which_singleton` identifying the two Hamblin constructions. The
`assertion` payload is a raw prior proposition; the
`Discourse.CommonGround.HasAssertion` hookup (a correction/denial
move) is deferred.
-/

namespace Semantics.Focus

open Semantics.Focus.Interpretation (fip PropFocusValue qaCongruentWeak)

variable {W : Type*}

/-- The four pragmatic uses of one semantic focus ([uhmann-1991]):
the image of `Antecedent.use`. -/
inductive Use where
  | newInfo      -- controlled by a question
  | corrective   -- correction of a prior assertion
  | selective    -- selection from explicitly offered alternatives
  | contrastive  -- parallel contrast across utterances
  deriving DecidableEq, Repr, Inhabited

/-- A focus antecedent: the discourse object that supplies the
squiggle's contrast set. -/
inductive Antecedent (W : Type*) where
  /-- A question with (flat Hamblin) denotation `q`. -/
  | question (q : PropFocusValue W)
  /-- A prior assertion `p`, corrected among alternatives `alts`. -/
  | assertion (p : Set W) (alts : PropFocusValue W)
  /-- Explicitly offered alternatives ('coffee or tea?'). -/
  | offer (alts : PropFocusValue W)
  /-- A parallel focus with focus value `alts`. -/
  | parallel (alts : PropFocusValue W)

/-- The contrast set Γ an antecedent supplies to the squiggle. -/
def Antecedent.contrastSet : Antecedent W → PropFocusValue W
  | .question q        => q
  | .assertion _ alts  => alts
  | .offer alts        => alts
  | .parallel alts     => alts

/-- The pragmatic use an antecedent shape licenses. -/
def Antecedent.use : Antecedent W → Use
  | .question _     => .newInfo
  | .assertion _ _  => .corrective
  | .offer _        => .selective
  | .parallel _     => .contrastive

@[simp] theorem contrastSet_question (q : PropFocusValue W) :
    (Antecedent.question q).contrastSet = q := rfl
@[simp] theorem contrastSet_assertion (p : Set W) (alts : PropFocusValue W) :
    (Antecedent.assertion p alts).contrastSet = alts := rfl
@[simp] theorem contrastSet_offer (alts : PropFocusValue W) :
    (Antecedent.offer alts).contrastSet = alts := rfl
@[simp] theorem contrastSet_parallel (alts : PropFocusValue W) :
    (Antecedent.parallel alts).contrastSet = alts := rfl

@[simp] theorem use_question (q : PropFocusValue W) :
    (Antecedent.question q).use = .newInfo := rfl
@[simp] theorem use_assertion (p : Set W) (alts : PropFocusValue W) :
    (Antecedent.assertion p alts).use = .corrective := rfl
@[simp] theorem use_offer (alts : PropFocusValue W) :
    (Antecedent.offer alts).use = .selective := rfl
@[simp] theorem use_parallel (alts : PropFocusValue W) :
    (Antecedent.parallel alts).use = .contrastive := rfl

/-- The canonical antecedent of each shape (empty payloads): a section
of `Antecedent.use`. -/
def Use.toAntecedent : Use → Antecedent W
  | .newInfo     => .question ∅
  | .corrective  => .assertion ∅ ∅
  | .selective   => .offer ∅
  | .contrastive => .parallel ∅

@[simp] theorem use_toAntecedent (u : Use) :
    (Use.toAntecedent (W := W) u).use = u := by cases u <;> rfl

/-- Every pragmatic use is realised by some antecedent shape. -/
theorem use_surjective : Function.Surjective (Antecedent.use (W := W)) :=
  fun u => ⟨u.toAntecedent, use_toAntecedent u⟩

/-- Roothian felicity of a focus value against an antecedent: `fip` on
the antecedent's contrast set. -/
def Antecedent.Admits (c : Antecedent W) (fv : PropFocusValue W) : Prop :=
  fip c.contrastSet fv

/-- The question case is the substrate's Q-A congruence. -/
theorem question_admits_iff (q fv : PropFocusValue W) :
    (Antecedent.question q).Admits fv ↔ qaCongruentWeak fv q := Iff.rfl

/-- `Admits` is monotone in the focus value. -/
theorem Antecedent.Admits.mono {c : Antecedent W} {fv fv' : PropFocusValue W}
    (hc : c.Admits fv) (h : fv ⊆ fv') : c.Admits fv' := hc.trans h

/-- An intersection of focus values is admitted iff both are. -/
theorem admits_inter_iff {c : Antecedent W} {fv fv' : PropFocusValue W} :
    c.Admits (fv ∩ fv') ↔ c.Admits fv ∧ c.Admits fv' :=
  Set.subset_inter_iff

/-- Felicity factors through the contrast set: the semantics sees Γ,
never the use label. -/
theorem admits_factorsThrough_contrastSet (fv : PropFocusValue W) :
    Function.FactorsThrough (Antecedent.Admits · fv)
      (Antecedent.contrastSet (W := W)) :=
  fun _ _ h => congrArg (fip · fv) h

/-- Distinct uses can supply one and the same Γ (a question and an
explicit offer, say), so the four-way split is invisible to the
Roothian semantics — pragmatic, not semantic. -/
theorem use_not_factorsThrough_contrastSet :
    ¬ Function.FactorsThrough (Antecedent.use (W := W))
        Antecedent.contrastSet :=
  fun h => absurd (h (a := .question ∅) (b := .offer ∅) rfl) (by simp)

/-! ### Hamblin antecedents -/

/-- The flat Hamblin set of complete answers over a domain. -/
def hamblin (D : Type*) : PropFocusValue D := Set.range fun d => ({d} : Set D)

/-- The wh-question antecedent over a whole domain. -/
def whAntecedent (D : Type*) : Antecedent D := .question (hamblin D)

theorem whAntecedent_admits (D : Type*) :
    (whAntecedent D).Admits (hamblin D) := subset_rfl

/-- A `Question` supplies its maximal alternatives as a question
antecedent — the bridge from the inquisitive layer. -/
def Antecedent.ofQuestion (q : Question W) : Antecedent W :=
  .question (Question.alt q)

/-- The maximal alternatives of the inquisitive wh-question over the
singleton predicates are exactly the flat Hamblin set. -/
theorem alt_which_singleton (D : Type*) [Nonempty D] :
    Question.alt (Question.which (Set.univ : Set D) fun d => ({d} : Set D)) =
      hamblin D := by
  have hA : IsAntichain (· ⊆ ·) ((fun d => ({d} : Set D)) '' Set.univ) := by
    rintro p ⟨a, -, rfl⟩ q ⟨b, -, rfl⟩ hne hsub
    exact hne (by rw [Set.singleton_subset_singleton.mp hsub])
  rw [Question.alt_which_of_antichain Set.univ_nonempty
      (fun d _ => Set.singleton_nonempty d) hA, Set.image_univ]
  rfl

/-- The inquisitive wh-question and the flat Hamblin antecedent
coincide. -/
theorem ofQuestion_which_eq_whAntecedent (D : Type*) [Nonempty D] :
    Antecedent.ofQuestion
        (Question.which (Set.univ : Set D) fun d => ({d} : Set D)) =
      whAntecedent D :=
  congrArg Antecedent.question (alt_which_singleton D)

end Semantics.Focus
