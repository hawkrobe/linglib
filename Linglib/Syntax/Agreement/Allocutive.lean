module

public import Linglib.Pragmatics.SocialMeaning.Honorific
public import Linglib.Pragmatics.SocialMeaning.Register
public import Linglib.Syntax.Gender.Basic
public import Linglib.Syntax.Number.Basic

/-!
# Allocutive markers

An allocutive marker encodes features of the addressee on the clause, whether or not the
addressee is an argument of it: the Souletin Basque verbal suffixes, the Magahi and Tamil
agreement suffixes, the Korean and Japanese addressee-honorific endings and the Galician
solidarity clitics. An `AllocutiveMarker` records the form with the addressee features it
encodes: the honorific level always, and the gender or number where the marker distinguishes
them. The Korean speech-style particles fuse the addressee's level with the formality of the
discourse, which is the marker's register.

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

@[expose] public section

/-- An allocutive marker is a form with the features of the addressee it encodes. -/
structure AllocutiveMarker where
  /-- The surface form. -/
  form : String
  /-- The honorific level of the addressee, on the scale of `PersonalPronoun.honorific`. -/
  honorific : SocialMeaning.HonorificLevel
  /-- The formality of the discourse, where the marker encodes it. -/
  register : SocialMeaning.Register := .neutral
  /-- The gender of the addressee, where the marker distinguishes it. -/
  gender : Option Gender := none
  /-- The number of addressees, where the marker distinguishes it. -/
  number : Option Number := none
  deriving DecidableEq, Repr
