/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.UD.Features

/-!
# Tense forms

This file defines tense forms. A tense form of a verb, in the sense of the traditional
grammars, is a member of the verb's tense paradigm, such as the simple past or the present
perfect. It is described here by its make-up, the tense inflection of its finite verb and the
nonfinite forms stacked under that verb. A synthetic form has a finite lexical verb and nothing
else. A periphrastic form is built from another form by putting its verb, in a nonfinite form,
under an auxiliary that takes over the tense inflection, so that the perfect of the simple
present *builds* is the present perfect *has built*, and the perfect of that is the double
perfect *has had built* of the South German dialects. Two languages whose forms have the same
make-up share the form, and which tense and which aspect it expresses in each is a matter of
analysis left to studies.

## Main declarations

* `Tense.Form.Nonfinite`: the nonfinite verb forms that build periphrastic tense forms.
* `Tense.Form`: a tense form, by the inflection of its finite verb and its nonfinite chain.
* `Tense.Form.under`, `Tense.Form.perfect`, `Tense.Form.progressive`: the periphrastic form
  built on a form.
* `Tense.Form.simplePresent`, `Tense.Form.simplePast` and the forms built on them.
* `Tense.Form.IsPerfect`: the form is the perfect of some form.
-/

namespace Tense

/-- A nonfinite verb form in a periphrastic tense form. -/
inductive Form.Nonfinite where
  /-- The infinitive, as German *bauen* under *werden*. -/
  | infinitive
  /-- The present participle, as English *building* under *be*. -/
  | presentParticiple
  /-- The past participle, as English *built* under *have* and German *gebaut* under *haben*. -/
  | pastParticiple
  deriving DecidableEq, Repr, Inhabited

/-- A tense form of a verb consists of the tense inflection of its finite verb and the nonfinite
forms under the finite verb, outermost first, so that the lexical verb is the last of them, or
the finite verb itself when there are none. -/
@[ext]
structure Form where
  /-- The tense inflection of the finite verb. -/
  finite : UD.Tense
  /-- The nonfinite forms under the finite verb, outermost first. -/
  nonfinite : List Form.Nonfinite := []
  deriving DecidableEq, Repr

namespace Form

/-- The periphrastic form built on `f` puts the verb of `f` in the nonfinite form `n` under an
auxiliary with the tense inflection of `f`. -/
def under (n : Nonfinite) (f : Form) : Form := { f with nonfinite := n :: f.nonfinite }

/-- The perfect of a form puts its verb in the past participle under an auxiliary. -/
def perfect : Form → Form := under .pastParticiple

/-- The progressive of a form puts its verb in the present participle under an auxiliary. -/
def progressive : Form → Form := under .presentParticiple

@[simp] theorem under_finite (n : Nonfinite) (f : Form) : (f.under n).finite = f.finite := rfl

@[simp] theorem under_nonfinite (n : Nonfinite) (f : Form) :
    (f.under n).nonfinite = n :: f.nonfinite := rfl

theorem under_injective (n : Nonfinite) : Function.Injective (under n) := fun f g h ↦ by
  have h₁ := congrArg Form.finite h
  have h₂ := congrArg Form.nonfinite h
  simp only [under_finite, under_nonfinite, List.cons.injEq, true_and] at h₁ h₂
  exact Form.ext h₁ h₂

@[simp] theorem perfect_inj {f g : Form} : f.perfect = g.perfect ↔ f = g :=
  (under_injective _).eq_iff

/-- The simple present is the synthetic present, as *builds*. -/
def simplePresent : Form := { finite := .Pres }

/-- The simple past is the synthetic past, as *built*. -/
def simplePast : Form := { finite := .Past }

/-- The present progressive is the progressive of the simple present, as *is building*. -/
def presentProgressive : Form := simplePresent.progressive

/-- The past progressive is the progressive of the simple past, as *was building*. -/
def pastProgressive : Form := simplePast.progressive

/-- The present perfect is the perfect of the simple present, as *has built*. -/
def presentPerfect : Form := simplePresent.perfect

/-- The past perfect is the perfect of the simple past, as *had built*. -/
def pastPerfect : Form := simplePast.perfect

/-- The double perfect is the perfect of the present perfect. -/
def doublePerfect : Form := presentPerfect.perfect

/-- A form is a perfect when it is the perfect of some form. -/
def IsPerfect (f : Form) : Prop := ∃ g : Form, f = g.perfect

theorem isPerfect_iff {f : Form} : f.IsPerfect ↔ f.nonfinite.head? = some .pastParticiple := by
  refine ⟨fun ⟨g, h⟩ ↦ h ▸ rfl, fun h ↦ ?_⟩
  obtain ⟨t, _ | ⟨n, l⟩⟩ := f
  · simp at h
  · obtain rfl : n = .pastParticiple := by simpa using h
    exact ⟨⟨t, l⟩, rfl⟩

instance : DecidablePred IsPerfect := fun _ ↦ decidable_of_iff _ isPerfect_iff.symm

end Form

end Tense
