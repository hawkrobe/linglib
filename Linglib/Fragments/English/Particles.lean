module

public import Linglib.Syntax.Category.Particle.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# English particles

This file defines the English polarity particles and the meta-question adverb *quick*. The
polarity particles *yes* and *no* answer polar questions and respond to assertions, and English
has no polarity-reversing particle ([holmberg-2016]). What each particle marks is a matter of
analysis: a valued polarity feature for [holmberg-2016], features of the response for
[farkas-bruce-2010]. *Quick* or *quickly* before a
question tells the addressee to answer without delay; Dayal groups it with the meta-question
particles, which occur in matrix questions and quotations and are ungrammatical embedded,
*Mary asked Sue quick where she hid the matza*.

## Main definitions

* `English.PolarityParticle`: the polarity particles.
* `English.Particles.quick`: the meta-question adverb.

## References

* [holmberg-2016]
* [farkas-bruce-2010]
* [dayal-2025]
-/

@[expose] public section

namespace English

/-- The English polarity particles. -/
inductive PolarityParticle where
  /-- *yes*. -/
  | yes
  /-- *no*. -/
  | no
  deriving DecidableEq, Repr, Fintype

/-- The spelling of a polarity particle. -/
def PolarityParticle.form : PolarityParticle → String
  | .yes => "yes"
  | .no => "no"

end English

namespace English.Particles

/-! ### Meta-question adverb -/

/-- *quick* or *quickly* before a question, available in matrix questions and quotations and
excluded from embedded questions. -/
def quick : Particle where
  form := "quick"
  position := some .clauseInitial
  distribution := fun c e ↦ match c with
    | .polar | .alternative | .constituent =>
      match e with
      | .matrix => some .optional
      | .subordinated => some .excluded
      | .quasiSubordinated => some .excluded
      | .quotation => some .optional
      | .insubordinated => none
    | _ => none

end English.Particles
