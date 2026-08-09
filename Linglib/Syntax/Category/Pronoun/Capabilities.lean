/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.UD.Basic
import Linglib.Features.Case.Capabilities
import Linglib.Features.Gender.Capabilities
import Linglib.Features.Number.Capabilities
import Linglib.Features.Person.Capabilities
import Linglib.Features.CoreferenceStatus
import Linglib.Syntax.Binding.Basic
import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Morphology.Word.Agree

/-!
# Pronoun capabilities — a mixin tower over pronoun carriers

Pronoun *entries* (`Pronoun`, `PersonalPronoun`, `IndefinitePronoun`, …) are bundled `structure`
values — many per language, like mathlib's `MonoidHom`. This file gives the *capabilities* a
carrier `α` can have, as typeclass mixins abstracting over the representation — the
`MonoidHomClass`/`ContinuousMul`-over-`MonoidHom`/`Mul` relationship, applied to pronouns. A
consumer (binding engine, agreement module, …) then requires exactly the axes it touches:
`[Proform α]` for form/φ, `[Bound α]` for the Principle A/B/C role, and so on — composed by
instance parameters with no `extends`-diamond. The carrier may be a record (`Pronoun`), a syntactic
object (`Word`), or a future theory representation; each supplies its own instances.

## Main declarations

* `Proform` — the spine: a carrier exposes a surface `form` and agreement `phi`-features.
* `Proform.Agree` — carrier-generic φ-agreement, the compatibility filter referent
  resolution and agreement consumers share; `Word.Agree` is its `Word` specialization.
* `instance Bound Pronoun` / `Bound PersonalPronoun` — the pronoun carriers' binding-axis
  instances. The `Bound` *class* (with `Anaphoric`/`Pronominal`/`Referring` and the
  `Bound.Is*` element predicates) is theory-neutral and lives beside its partial companion
  `Features.BindingSource` in `Features/CoreferenceStatus.lean`.
* `bindingClassOf_toWord` — the faithfulness certificate: the binding engine's canonical
  morphology source (`Binding.bindingClassOf`) agrees with the `Bound` mixin on every
  projected pro-form, so the surface engine and the carrier capability never diverge.
* `HasNumber`/`HasPerson`/`HasCase`/`HasGender` instances for the pronoun carriers, each
  with a faithfulness theorem (`numberOf_toWord`, `personOf_toWord`, `caseOf_toWord`,
  `genderOf_toWord`) locating exactly what `toWord`'s UD realization preserves or loses.

## Implementation notes

Capabilities live near their domain (mathlib-style: `ContinuousMul` is in `Topology`, not
`Algebra`). The word-class-neutral `Indefinite` capability (`[Indefinite α]`, Haspelmath
function-coverage) therefore lives in `Features/Indefinite.lean`, and the binding axis `Bound`
lives in `Features/CoreferenceStatus.lean` — neither is pronoun-specific.

Three further axes are deferred, each for a principled reason. *Deficiency*
([cardinaletti-starke-1999] `Pronoun.Strength`) is *per-series*, not per-element: every carrier's
strength is carrier-uniform (Italian clitics are all `.clitic`; the Mixtec clitic/nonclitic *fields*
have fixed strengths), so an `α → Strength` accessor would be constant on every carrier — a
per-*type* fact, not a per-element capability. It is served by the `Pronoun.strength` field
(series-level, `none` when not homogeneous) and the `Strength` linear order, not by a class.
The finer *lexical-kind* axis (personal vs relative vs interrogative vs
demonstrative) is `Pronoun.pronType` — real UD morphology on the carrier (no invented enum),
threaded onto the projected word by `toWord`. The *deictic* axis (register, referential
person) is borne by one carrier only, which carries it as fields
(`PersonalPronoun.register`/`referentialPerson`); a class over those accessors earns its
keep when a second carrier bears the axis.
-/

open Morphology (Word)

/-! ### The spine: `Proform` -/

/-- A pronoun-like carrier exposes a surface `form` and agreement `phi`-features — everything true
of *every* pronoun, the base every other capability builds over (cf. `Mul`/`Semigroup` as the base
operation class). -/
class Proform (α : Type*) where
  /-- Surface form (romanization or orthographic). -/
  form : α → String
  /-- Agreement φ-features (person/number/gender). -/
  phi : α → UD.MorphFeatures

instance : Proform Word := ⟨Word.form, Word.phi⟩
instance : Proform Pronoun := ⟨Pronoun.form, fun p => p.toWord.phi⟩
instance : Proform PersonalPronoun :=
  ⟨fun p => p.toPronoun.form, fun p => p.toPronoun.toWord.phi⟩

/-! ### φ-agreement over carriers -/

/-- φ-agreement between two pro-form carriers: their `phi`-features unify
(`UD.MorphFeatures.compatible`), an unspecified feature acting as a wildcard —
the carrier-generic form of `Word.Agree`. The compatibility filter referent
resolution and agreement consumers share: a pronoun's φ narrows the candidate
referents to those it agrees with. -/
def Proform.Agree {α β : Type*} [Proform α] [Proform β] (a : α) (b : β) : Prop :=
  (Proform.phi a).compatible (Proform.phi b)

instance {α β : Type*} [Proform α] [Proform β] (a : α) (b : β) :
    Decidable (Proform.Agree a b) := by
  unfold Proform.Agree; infer_instance

/-- On word tokens, carrier-generic agreement is `Word.Agree`. -/
theorem Proform.agree_word (w1 w2 : Word) : Proform.Agree w1 w2 ↔ w1.Agree w2 := Iff.rfl

/-- A pronoun agrees exactly as its projected word does — `Proform.phi` on
`Pronoun` is projection-then-φ by construction. -/
theorem Proform.agree_toWord {β : Type*} [Proform β] (p : Pronoun) (b : β) :
    Proform.Agree p b ↔ Proform.Agree p.toWord b := Iff.rfl

/-! ### The pronoun carriers' `Bound` instances, and the faithfulness certificate -/

/-- A bare `Pronoun`'s declared class, defaulting an undeclared φ-shell to Principle-B `.pronoun`
([chomsky-1981]'s elsewhere case for a pro-form). -/
instance : Bound Pronoun := ⟨fun p => p.bindingClass.getD .pronoun⟩
instance : Bound PersonalPronoun := ⟨fun p => p.toPronoun.bindingClass.getD .pronoun⟩

/-- The canonical morphology source agrees with the mixin: a pro-form's projected word
classifies (`Binding.bindingClassOf`, reading `Reflex`/`PronType`/category) exactly as the
carrier's `Bound` class — `Pronoun.toWord` threads the binding morphology faithfully, so the
surface engine and the capability never diverge. Two coherence premises, both vacuous for
every actual entry: the pronoun is not lexically declared an R-expression (its surface
category `.PRON` would win), and it does not *store* `PronType=Rcp` (reciprocal is derived
by `toWord` from `bindingClass = .reciprocal`, never stored). -/
theorem bindingClassOf_toWord (p : Pronoun) (h : p.bindingClass ≠ some .rExpression)
    (hr : p.pronType = some .Rcp → p.bindingClass = some .reciprocal) :
    Binding.bindingClassOf p.toWord = Bound.source p := by
  show Binding.bindingClassOf p.toWord = some (p.bindingClass.getD .pronoun)
  rcases hb : p.bindingClass with _ | (_ | _ | _ | _) <;>
      rcases hp : p.pronType with _ | pt <;> (try cases pt) <;>
    simp_all +decide [Binding.bindingClassOf, Pronoun.toWord]

/-! ### The number axis: `HasNumber` instances and faithfulness -/

/-- A pronoun bears its analytical number directly — the carrier field is
root-`Number`-typed. -/
instance : HasNumber Pronoun := ⟨fun p => p.number⟩

instance : HasNumber PersonalPronoun := ⟨fun p => numberOf p.toPronoun⟩

/-- Projecting a pronoun to a `Word` realizes its number through UD: the
round-trip is identity exactly on UD-expressible values — the
minimal/augmented values are lost to realization (`Number.toUD` is
partial), the number analogue of `personOf_toWord`'s coarsening. -/
theorem numberOf_toWord (p : Pronoun) :
    numberOf p.toWord = p.number.bind fun n => n.toUD.bind Number.fromUD := by
  show (p.number.bind Number.toUD).bind Number.fromUD = _
  cases p.number <;> rfl

/-! ### The person axis: `HasPerson` instances and faithfulness -/

/-- A pronoun bears its analytical person directly — the carrier field is
root-`Person`-typed, clusivity included (Tagalog *kami* =
`firstExclusive`). -/
instance : HasPerson Pronoun := ⟨fun p => p.person⟩

instance : HasPerson PersonalPronoun := ⟨fun p => personOf p.toPronoun⟩

/-- Projecting a pronoun to a `Word` coarsens its person: `Word` carries
UD realization, which has no clusivity — the mixin makes the loss
explicit rather than silent. -/
theorem personOf_toWord (p : Pronoun) :
    personOf p.toWord = (personOf p).map Person.coarsen := by
  show (p.person.map Person.toUD).map Person.fromUD = p.person.map Person.coarsen
  simp [Option.map_map, Function.comp_def, Person.fromUD_toUD]

/-! ### The case axis: `HasCase` instances and faithfulness -/

/-- A pronoun bears its analytical case directly — the carrier field is
root-`Case`-typed. -/
instance : HasCase Pronoun := ⟨fun p => p.case_⟩

instance : HasCase PersonalPronoun := ⟨fun p => caseOf p.toPronoun⟩

/-- Projecting a pronoun to a `Word` realizes its case through UD
losslessly: `Case.toUD` is currently a bijection, so — unlike person
(clusivity lost) and number (minimal/augmented lost) — the round-trip is
the identity. This is the theorem that degrades when an analytical
refinement splits a UD cell (`Case.fromUD_toUD`). -/
theorem caseOf_toWord (p : Pronoun) : caseOf p.toWord = caseOf p := by
  show (p.case_.map Case.toUD).map Case.fromUD = p.case_
  simp [Option.map_map, Function.comp_def, Case.fromUD_toUD]

/-! ### The gender axis: `HasGender` instances and faithfulness -/

/-- A pronoun bears its analytical gender directly — the carrier field is
root-`Gender`-typed. -/
instance : HasGender Pronoun := ⟨fun p => p.gender⟩

instance : HasGender PersonalPronoun := ⟨fun p => genderOf p.toPronoun⟩

/-- Projecting a pronoun to a `Word` realizes its gender through UD: the
round-trip is identity exactly on UD-expressible values — the animacy-based
labels are lost to realization (`Gender.toUD` is partial), the gender
analogue of `numberOf_toWord`. -/
theorem genderOf_toWord (p : Pronoun) :
    genderOf p.toWord = p.gender.bind fun g => g.toUD.map Gender.fromUD := by
  show (p.gender.bind Gender.toUD).map Gender.fromUD = _
  cases p.gender <;> rfl
