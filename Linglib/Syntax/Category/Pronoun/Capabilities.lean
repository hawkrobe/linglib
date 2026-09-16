/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.UD.Basic
import Linglib.Syntax.Agreement.Phi
import Linglib.Syntax.Binding.CoreferenceStatus
import Linglib.Syntax.Binding.Basic
import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Morphology.Word.Agree

/-!
# Pronoun capabilities

Typeclass mixins for pronoun-like carriers. A carrier may be a lexical record
(`Pronoun`, `PersonalPronoun`) or a surface token (`Word`); a consumer requires
exactly the axes it touches.

## Main declarations

* `Proform` — a pro-form takes its antecedents from a fixed form-class, its
  domain ([bloomfield-1933]); `Proform.CandidateAntecedent` is derived — domain
  membership plus φ-agreement (`HasPhi.Agree`, from `Syntax/Agreement/Phi.lean`).
* `Bound` instances for the pronoun carriers.
* `bindingClassOf_toWord` — `Pronoun.toWord` classifies as its `Bound` class.

## Implementation notes

Word-class-neutral capabilities live with their domains: `Indefinite` in
`Semantics/Quantification/Indefinite.lean`, `Bound` in `Syntax/Binding/CoreferenceStatus.lean`.
Three axes are fields, not classes: deficiency (`Pronoun.strength`, per-series
[cardinaletti-starke-1999]), lexical kind (`Pronoun.pronType`, UD morphology),
and register/referential person (`PersonalPronoun` fields, borne by one
carrier).

`Proform.CandidateAntecedent` is token-level: whether an anaphoric site is a
bare pro-form or hosts deleted structure ([hankamer-sag-1976]; [baltin-2012])
is a theory question for study files.
-/

open Morphology (Word)

/-! ### φ instances and the pro-form -/

instance : HasPhi Pronoun := ⟨fun p => p.toWord.phi⟩
instance : HasPhi PersonalPronoun := ⟨fun p => p.toPronoun.toWord.phi⟩

/-- A pronoun agrees exactly as its projected word does. -/
theorem HasPhi.agree_toWord {β : Type*} [HasPhi β] (p : Pronoun) (b : β) :
    HasPhi.Agree p b ↔ HasPhi.Agree p.toWord b := Iff.rfl

/-- A pro-form takes its antecedents from a fixed form-class — its *domain*
(the notion originates with [bloomfield-1933]'s substitutes). -/
class Proform (α : Type*) where
  /-- `w` is in the form-class `a` stands for. -/
  Domain : α → Word → Prop

/-- A candidate antecedent for a pro-form is a domain member that φ-agrees
with it. -/
def Proform.CandidateAntecedent {α : Type*} [Proform α] [HasPhi α]
    (a : α) (w : Word) : Prop :=
  Proform.Domain a w ∧ HasPhi.Agree a w

/-- A candidate antecedent φ-agrees with its pro-form. -/
theorem Proform.CandidateAntecedent.agree {α : Type*} [Proform α] [HasPhi α] {a : α}
    {w : Word} (h : CandidateAntecedent a w) : HasPhi.Agree a w := h.2

/-- A pronoun's domain is the nominal tokens. -/
instance : Proform Pronoun := ⟨fun _ w => Binding.isNominalCat w.cat = true⟩

instance : Proform PersonalPronoun := ⟨fun _ w => Binding.isNominalCat w.cat = true⟩

instance (p : Pronoun) (w : Word) : Decidable (Proform.Domain p w) :=
  inferInstanceAs (Decidable (_ = true))

instance (p : PersonalPronoun) (w : Word) : Decidable (Proform.Domain p w) :=
  inferInstanceAs (Decidable (_ = true))

instance {α : Type*} [Proform α] [HasPhi α] (a : α) (w : Word)
    [Decidable (Proform.Domain a w)] : Decidable (Proform.CandidateAntecedent a w) := by
  unfold Proform.CandidateAntecedent; infer_instance

/-! ### The pronoun carriers' `Bound` instances, and the faithfulness certificate -/

/-- A bare `Pronoun`'s class is its declared `bindingClass`; an undeclared
φ-shell defaults to Principle-B `.pronoun` ([chomsky-1981]'s elsewhere case). -/
instance : Bound Pronoun := ⟨fun p => p.bindingClass.getD .pronoun⟩
instance : Bound PersonalPronoun := ⟨fun p => p.toPronoun.bindingClass.getD .pronoun⟩

/-- A pronoun's projected word classifies (`Binding.bindingClassOf`) exactly as
its `Bound` class. -/
theorem bindingClassOf_toWord (p : Pronoun) (h : p.bindingClass ≠ some .rExpression)
    (hr : p.pronType = some .Rcp → p.bindingClass = some .reciprocal) :
    Binding.bindingClassOf p.toWord = Bound.source p := by
  show Binding.bindingClassOf p.toWord = some (p.bindingClass.getD .pronoun)
  rcases hb : p.bindingClass with _ | (_ | _ | _ | _) <;>
      rcases hp : p.pronType with _ | pt <;> (try cases pt) <;>
    simp_all +decide [Binding.bindingClassOf, Pronoun.toWord]
