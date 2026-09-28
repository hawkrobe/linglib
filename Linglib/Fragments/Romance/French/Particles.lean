module

public import Mathlib.Tactic.DeriveFintype

/-!
# French polarity particles

The polarity particles *oui*, *non* and *si* (`French.PolarityParticle`). *Si*, glossed
yes.REV, is the polarity-reversing affirmative: after a negative question it replaces *oui*,
which cannot confirm the positive alternative, *Tu n'es pas fatigué? — \*Oui / Si*
([holmberg-2016]), and it reverses a negative assertion, *Il ne fait pas beau. — Si (il fait
beau)*. Unlike the Italian *sì che* and Spanish *sí que* constructions, *si* is limited to
answering a preceding opposite turn ([garassino-jacob-2018]). What each particle marks is a
matter of analysis: a valued polarity feature for [holmberg-2016], features of the response for
[farkas-bruce-2010].

## References

* [holmberg-2016]
* [farkas-bruce-2010]
* [garassino-jacob-2018]
-/

@[expose] public section

namespace French

/-- The French polarity particles. -/
inductive PolarityParticle where
  /-- *oui* 'yes': *Tu es fatigué?* 'Are you tired?' — *Oui*. -/
  | oui
  /-- *non* 'no'. -/
  | non
  /-- *si* 'yes.REV', contradicting a negative: *Tu n'es pas fatigué?* 'Are you not tired?' —
  *Si*, I am. -/
  | si
  deriving DecidableEq, Repr, Fintype

/-- The spelling of a polarity particle. -/
def PolarityParticle.form : PolarityParticle → String
  | .oui => "oui"
  | .non => "non"
  | .si => "si"

end French
