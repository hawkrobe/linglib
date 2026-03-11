import Linglib.Core.Lexical.Word
import Linglib.Core.Register
import Linglib.Core.Prominence

/-!
# Shared Pronoun and Allocutive Entry Types
@cite{alok-bhalla-2026}

Cross-linguistic structures for pronoun inventories and allocutive markers,
shared across all Fragment/*/Pronouns.lean files.

## PronounEntry

Covers the union of fields needed by all language fragments:
- Core: form, person, number (all fragments)
- Morphosyntactic: case_ (Galician, English)
- Sociolinguistic: register (all SA-based fragments)
- Orthographic: script (Korean hangul, Japanese kanji)

## AllocutiveEntry

Shared structure for allocutive markers — verbal suffixes (Hindi, Magahi,
Maithili, Punjabi, Tamil, Basque), particles (Korean, Japanese), or
clitics (Galician) that realize speaker-addressee agreement.

-/

namespace Core.Pronouns

open Core.Register (Level)

/-- Cross-linguistic pronoun entry.

Covers personal pronouns across all Fragment languages. Language-specific
extensions (e.g., English PronounType/wh) remain in their respective
Fragment files. -/
structure PronounEntry where
  /-- Surface form (romanization or orthographic) -/
  form : String
  /-- Grammatical person (UD.Person) -/
  person : Option Person := none
  /-- Grammatical number (UD.Number) -/
  number : Option Number := none
  /-- Grammatical case (UD.Case) -/
  case_ : Option Case := none
  /-- Register level (formality/honorifics). Binary T/V systems use
      `.informal`/`.formal`; ternary honorific systems (Hindi, Magahi,
      Maithili, Korean) use all three levels. -/
  register : Level := .informal
  /-- Referential person — who the pronoun refers to in terms of discourse
      role — when it diverges from formal/agreement person. For polite
      pronouns (Italian LEI, Spanish USTED, German SIE), the formal `person`
      field is 3rd (governing agreement, clitic allomorphy, reflexive binding),
      while `referentialPerson` is 2nd (governing the PCC, Fancy Constraint,
      resolved agreement). For ordinary pronouns, leave as `none` —
      referential person coincides with formal person.
      @cite{adamson-zompi-2025} -/
  referentialPerson : Option Core.Prominence.PersonLevel := none
  /-- Native script form (hangul, kanji, Devanagari, etc.) -/
  script : Option String := none
  deriving Repr, BEq

/-- Cross-linguistic allocutive marker entry.

Covers verbal suffixes, particles, and clitics that realize allocutive
agreement across all Fragment languages. -/
structure AllocutiveEntry where
  /-- Surface form of the marker -/
  form : String
  /-- Register level (matching PronounEntry.register scale) -/
  register : Level
  /-- Gloss string (e.g., "IMP.NH", "POL", "2sg.DAT.fam") -/
  gloss : String
  deriving Repr, BEq

end Core.Pronouns
