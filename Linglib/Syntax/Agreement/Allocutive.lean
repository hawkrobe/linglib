import Linglib.Pragmatics.SocialMeaning.Register
import Linglib.Syntax.Gender.Basic
import Linglib.Syntax.Number.Basic

/-!
# Allocutive markers

An allocutive marker encodes features of the addressee on the clause, whether or not the
addressee is an argument of it: the Souletin Basque verbal suffixes, the Magahi and Tamil
agreement suffixes, the Korean and Japanese addressee-honorific endings and the Galician
solidarity clitics. An `AllocutiveMarker` records the form with the addressee features it
encodes: the honorific level always, and the gender or number where the marker distinguishes
them.

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

/-- An allocutive marker: a form with the features of the addressee it encodes. -/
structure AllocutiveMarker where
  /-- The surface form. -/
  form : String
  /-- The honorific level of the addressee, on the scale of `PersonalPronoun.register`. -/
  register : SocialMeaning.Register.Level
  /-- The gender of the addressee, where the marker distinguishes it. -/
  gender : Option Gender := none
  /-- The number of addressees, where the marker distinguishes it. -/
  number : Option Number := none
  deriving DecidableEq, Repr
