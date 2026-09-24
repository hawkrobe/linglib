module

public import Linglib.Semantics.Polarity.Operator

/-!
# Turkish question particles

Turkish polar questions carry the clitic *=mI*, with the vowel-harmony allomorphs *mı*, *mi*,
*mu* and *mü*. It attaches to the focused constituent, by default rightmost, and contributes no
propositional content beyond marking question force and focus, so its denotation is the
identity `Polarity.affirm`, [atlamaz-2023], [turk-hirsch-2026]. The entry records the lexical
primitives only; the syntactic category and head position the analyses assume live in the
studies that adopt them.

## References

* [atlamaz-2023]
* [turk-hirsch-2026]
-/

@[expose] public section

namespace Turkish.QuestionParticles

open Polarity

/-- A Turkish question particle has a citation form, its vowel-harmony allomorphs, and the
operator on propositions it contributes, polymorphic in the world type. -/
structure TurkishQParticle where
  form : String
  allomorphs : List String
  denotation : ∀ {W : Type}, (W → Prop) → (W → Prop)

/-- *=mI*, the polar question particle, semantically the identity. -/
def mi : TurkishQParticle where
  form := "mI"
  allomorphs := ["mı", "mi", "mu", "mü"]
  denotation := affirm _

end Turkish.QuestionParticles
