/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Word.Basic
import Linglib.Semantics.Modality.ModalTypes
import Linglib.Features.Number.Capabilities
import Linglib.Features.Person.Capabilities

open Morphology (Word)
open Modality (ForceFlavor ModalItem ModalFeature ModalInterpretability)
open Features.Register (Level)

/-!
# Auxiliary

An auxiliary is a closed-class function word of verbal predication: it
carries tense, aspect, modality, or voice while a lexical verb carries the
content (UD `AUX`). Modal auxiliaries additionally have meanings in the
force–flavor space — *must* is necessity over epistemic, deontic or
circumstantial backgrounds — and may sit at a marked register (*shall*).

This file provides the auxiliary as a lexical object: its form, its
agreement and verb-form features, its modality, and its register.
Per-language fragments supply the entries.

## Main declarations

* `Auxiliary` — the lexical object.
* `Auxiliary.toWord` — the `AUX` word it spells out.
* `Auxiliary.toModalItem`, `Auxiliary.modalFeature` — its modality as
  a `ModalItem`, and as the uninterpretable modal feature of [zeijlstra-2007].

## References

* [anderson-2006a], §1.2
* [zeijlstra-2007]
-/

/-- An auxiliary: form, agreement and verb-form features, modality (empty
for non-modal auxiliaries), and register. -/
structure Auxiliary where
  form : String
  features : UD.MorphFeatures := {}
  /-- The modality, as force–flavor pairs; empty for the non-modal
      auxiliaries. -/
  modality : List ForceFlavor := []
  register : Level := .neutral
  deriving DecidableEq, Repr

namespace Auxiliary

/-- The `AUX` word an auxiliary spells out. -/
def toWord (a : Auxiliary) : Word := { form := a.form, cat := .AUX, features := a.features }

@[simp] theorem toWord_cat (a : Auxiliary) : a.toWord.cat = .AUX := rfl

/-- Morphological tense; `none` for base forms such as *can* and *will*. -/
def tense (a : Auxiliary) : Option UD.Tense := a.features.tense

/-- Agreement person. -/
def person (a : Auxiliary) : Option UD.Person := a.features.person

/-- Agreement number. -/
def number (a : Auxiliary) : Option UD.Number := a.features.number

/-- The modal item an auxiliary contributes: form, meanings, register. -/
def toModalItem (a : Auxiliary) : ModalItem := ⟨a.form, a.modality, a.register⟩

/-- The modal feature a modal auxiliary carries ([zeijlstra-2007]): the force
of its primary meaning, **uninterpretable** — semantically vacuous and
checked by a c-commanding interpretable operator. `none` for an auxiliary
with no modality. -/
def modalFeature (a : Auxiliary) : Option ModalFeature :=
  a.modality.head?.map fun ff => ⟨ff.force, .uninterpretable⟩

/-- The interpretability of the auxiliary's modal feature, if it has one. -/
def interpretability (a : Auxiliary) : Option ModalInterpretability :=
  a.modalFeature.map (·.interp)

instance : HasNumber Auxiliary := ⟨fun a => a.features.number.bind Number.fromUD⟩

instance : HasPerson Auxiliary := ⟨fun a => a.features.person.map Person.fromUD⟩

end Auxiliary
