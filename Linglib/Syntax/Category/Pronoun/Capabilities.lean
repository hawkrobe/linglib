/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.UD.Basic
import Linglib.Features.Phi
import Linglib.Features.Case.Capabilities
import Linglib.Features.Gender.Capabilities
import Linglib.Features.Number.Capabilities
import Linglib.Features.Person.Capabilities
import Linglib.Features.CoreferenceStatus
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
  membership plus φ-agreement (`HasPhi.Agree`, from `Features/Phi.lean`).
* `Bound`, `HasNumber`, `HasPerson`, `HasCase`, `HasGender` instances for the
  pronoun carriers.
* `bindingClassOf_toWord`, `numberOf_toWord`, `personOf_toWord`, `caseOf_toWord`,
  `genderOf_toWord` — `Pronoun.toWord` commutes with each axis, up to what UD
  realization can express: clusivity, minimal/augmented number, and animacy-based
  gender are lost; case and binding class are preserved.

## Implementation notes

Word-class-neutral capabilities live with their domains: `Indefinite` in
`Features/Indefinite.lean`, `Bound` in `Features/CoreferenceStatus.lean`.
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

/-! ### The number axis: `HasNumber` instances and faithfulness -/

instance : HasNumber Pronoun := ⟨fun p => p.number⟩

instance : HasNumber PersonalPronoun := ⟨fun p => numberOf p.toPronoun⟩

/-- A pronoun's number survives projection to `Word` exactly on UD-expressible
values; the minimal/augmented values are lost, since `Number.toUD` is partial. -/
theorem numberOf_toWord (p : Pronoun) :
    numberOf p.toWord = p.number.bind fun n => n.toUD.bind Number.fromUD := by
  show (p.number.bind Number.toUD).bind Number.fromUD = _
  cases p.number <;> rfl

/-! ### The person axis: `HasPerson` instances and faithfulness -/

instance : HasPerson Pronoun := ⟨fun p => p.person⟩

instance : HasPerson PersonalPronoun := ⟨fun p => personOf p.toPronoun⟩

/-- Projection to `Word` coarsens person, since UD realization has no
clusivity. -/
theorem personOf_toWord (p : Pronoun) :
    personOf p.toWord = (personOf p).map Person.coarsen := by
  show (p.person.map Person.toUD).map Person.fromUD = p.person.map Person.coarsen
  simp [Option.map_map, Function.comp_def, Person.fromUD_toUD]

/-! ### The case axis: `HasCase` instances and faithfulness -/

instance : HasCase Pronoun := ⟨fun p => p.case_⟩

instance : HasCase PersonalPronoun := ⟨fun p => caseOf p.toPronoun⟩

/-- Projection to `Word` preserves case, since `Case.toUD` is a bijection. -/
theorem caseOf_toWord (p : Pronoun) : caseOf p.toWord = caseOf p := by
  show (p.case_.map Case.toUD).map Case.fromUD = p.case_
  simp [Option.map_map, Function.comp_def, Case.fromUD_toUD]

/-! ### The gender axis: `HasGender` instances and faithfulness -/

instance : HasGender Pronoun := ⟨fun p => p.gender⟩

instance : HasGender PersonalPronoun := ⟨fun p => genderOf p.toPronoun⟩

/-- A pronoun's gender survives projection to `Word` exactly on UD-expressible
values; the animacy-based labels are lost, since `Gender.toUD` is partial. -/
theorem genderOf_toWord (p : Pronoun) :
    genderOf p.toWord = p.gender.bind fun g => g.toUD.map Gender.fromUD := by
  show (p.gender.bind Gender.toUD).map Gender.fromUD = _
  cases p.gender <;> rfl
