import Linglib.Fragments.Hausa.Determiners
import Linglib.Semantics.Quantification.Basic

/-!
# Zimmermann (2008): Quantification in Hausa

This file formalizes a fragment of [zimmermann-2008]'s survey of the Hausa quantifier system,
the handbook chapter in [matthewson-2008] whose inventory the fragment `Hausa.Determiners` types
after the reference grammars [newman-2000] and [jaggar-2001]. Two of the chapter's observations
are modelled on a three-passenger domain: the *kō*-*wh* universals quantify over the members of
the restrictor one by one, so *kōwānè faasinjèe yā daurà wàndà* 'every passenger buckled their
seatbelt' is false as soon as one passenger did not (`kowWh_daura_false`), and the marked
indefinite *wani* under clausal negation is ambiguous between a wide-scope and a narrow-scope
reading, which the model separates (`wani_wide_scope`, `wani_narrow_scope_false`).

## Implementation notes

* The *kō*-*wh* universal is read as the generalized quantifier `every_sem`; the chapter's own
  choice among generalized-quantifier, indeterminate-pronoun and choice-function analyses is
  not represented.
* The section and example locators of the chapter and of the grammars are not verified
  against the sources.

## TODO

* The collective universal *duk* on plural and mass restrictors, free-choice *kō*-*wh* in modal
  contexts, and the chapter's Chadic typology of universals await access to the chapter.

## References

* [zimmermann-2008]
* [matthewson-2008]
* [newman-2000]
* [jaggar-2001]
-/

namespace Zimmermann2008

open Hausa.Determiners Quantification

/-! ### A three-passenger domain -/

/-- Three passengers, *faasinjojî*: Audù, Bàlki and Càdi. -/
inductive Faasinjee
  | audu | balki | cadi
  deriving DecidableEq, Repr

/-- *yā daurà wàndà* 'buckled their seatbelt': Audù and Bàlki did, Càdi did not. -/
def Daura : Faasinjee → Prop
  | .audu => True
  | .balki => True
  | .cadi => False

instance : DecidablePred Daura := λ x => match x with
  | .audu => isTrue trivial
  | .balki => isTrue trivial
  | .cadi => isFalse id

/-! ### The distributive universal -/

/-- The denotation of a Hausa universal: *kō*-*wh* is the distributive generalized quantifier;
the collective *duk* is left to the chapter's plural analysis. -/
def UniversalQuantifier.denot : UniversalQuantifier → Option (GQ Faasinjee)
  | .kowWh => some every_sem
  | .duk => none

/-- *kōwānè faasinjèe yā daurà wàndà* 'every passenger buckled their seatbelt' is false on the
model: Càdi did not. -/
theorem kowWh_daura_false : ¬ every_sem (λ _ : Faasinjee => True) Daura :=
  λ h => h .cadi trivial

/-! ### The indefinite *wani* under negation -/

/-- The wide-scope reading of *wani faasinjèe bài daurà wàndà ba*, some passenger did not
buckle their seatbelt, holds: Càdi is the witness. -/
theorem wani_wide_scope : some_sem (λ _ : Faasinjee => True) (¬ Daura ·) :=
  ⟨.cadi, trivial, id⟩

/-- The narrow-scope reading, no passenger buckled their seatbelt, fails: Audù did. -/
theorem wani_narrow_scope_false : ¬ ¬ ∃ x : Faasinjee, Daura x :=
  λ h => h ⟨.audu, trivial⟩

/-- The two readings of *wani* under negation come apart on the model. -/
theorem wani_ambiguity_witness :
    some_sem (λ _ : Faasinjee => True) (¬ Daura ·) ∧ ¬ ¬ ∃ x : Faasinjee, Daura x :=
  ⟨wani_wide_scope, wani_narrow_scope_false⟩

end Zimmermann2008
