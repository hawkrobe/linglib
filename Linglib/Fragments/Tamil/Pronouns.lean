module

public import Linglib.Syntax.Agreement.Allocutive
public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Tamil pronouns and the allocutive marker

This file defines the personal pronouns of colloquial Tamil and its allocutive marker. The
first person plural distinguishes the inclusive *naam* from the exclusive *naan-ŋgæ*, the
clusivity contrast of the Dravidian languages; the second person sets the familiar *nii* against
*nii-ŋgæ*, which serves as the plural and as the polite singular; the third person singular has
the masculine *avan*, the feminine *avaɭ* and the polite *avar*, and the plural is *avan-ŋgæ*.
The suffix *-ŋgæ* is the plural of nouns and pronouns alike, *maram-ŋgæ* 'trees', underlyingly
*-ŋgæɭ* with a final *-ɭ* that surfaces before a vowel, and on the finite verb it is the
allocutive marker of politeness to the addressee, used, as McFadden puts it, with those one
would address as *nii-ŋgæ*. Levinson's further addressee honorifics, the mid *-ppaa* and *-maa*
and the low *-ɖaa* and *-ɖii*, McFadden keeps apart from *-ŋgæ* in grammatical terms, and they
are not recorded here. The forms are in McFadden's transcription as Alok and Bhalla reproduce
them.

## Main definitions

* `Tamil.Pronouns.pronouns`: the personal pronouns.
* `Tamil.Pronouns.pluralSuffix`, `Tamil.Pronouns.alloc`: the plural suffix and its allocutive
  use.

## References

* [alok-bhalla-2026]
* [mcfadden-2026]
-/

@[expose] public section

namespace Tamil.Pronouns

/-! ### Personal pronouns -/

/-- The first person singular *naan*. -/
def naan : PersonalPronoun := { form := "naan", person := some .first, number := some .singular }

/-- The first person plural inclusive *naam*. -/
def naam : PersonalPronoun :=
  { form := "naam", person := some .firstInclusive, number := some .plural }

/-- The first person plural exclusive *naan-ŋgæ*, the plural of *naan*. -/
def naanŋgæ : PersonalPronoun :=
  { form := "naan-ŋgæ", person := some .firstExclusive, number := some .plural }

/-- The familiar second person singular *nii*. -/
def nii : PersonalPronoun :=
  { form := "nii", person := some .second, number := some .singular,
    honorific := some .nonhonorific }

/-- The second person plural *nii-ŋgæ*, which is also the polite singular. -/
def niiŋgæ : PersonalPronoun :=
  { form := "nii-ŋgæ", person := some .second, number := some .plural,
    honorific := some .honorific, referential := {.addressee, .addresseeOthers} }

/-- The third person singular masculine *avan*. -/
def avan : PersonalPronoun :=
  { form := "avan", person := some .third, number := some .singular, gender := some .masculine,
    honorific := some .nonhonorific }

/-- The third person singular feminine *avaɭ*. -/
def avaL : PersonalPronoun :=
  { form := "avaɭ", person := some .third, number := some .singular, gender := some .feminine,
    honorific := some .nonhonorific }

/-- The polite third person singular *avar*. -/
def avar : PersonalPronoun :=
  { form := "avar", person := some .third, number := some .singular, honorific := some .honorific }

/-- The third person plural *avan-ŋgæ*, the plural of *avan*. -/
def avanŋgæ : PersonalPronoun :=
  { form := "avan-ŋgæ", person := some .third, number := some .plural, gender := some .masculine }

/-- The personal pronouns. -/
def pronouns : Finset PersonalPronoun :=
  {naan, naam, naanŋgæ, nii, niiŋgæ, avan, avaL, avar, avanŋgæ}

/-! ### The plural suffix and the allocutive marker -/

/-- The plural suffix *-ŋgæ* of nouns and pronouns. -/
def pluralSuffix : String := "-ŋgæ"

/-- The allocutive marker, the plural suffix on the finite verb, marking politeness to the
addressee. -/
def alloc : AllocutiveMarker := { form := pluralSuffix, honorific := .honorific }

end Tamil.Pronouns
