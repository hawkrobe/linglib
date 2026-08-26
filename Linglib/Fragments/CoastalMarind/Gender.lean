import Mathlib.Tactic.DeriveFintype

/-!
# Coastal Marind gender

The four genders of Coastal Marind (Anim, New Guinea) after Olsson's description as tabulated in
[adamson-2024]: the demonstrative and similative agreement forms, and the nouns whose form
alternates overtly by gender, among them *nanVh* 'face', which takes the gender of its possessor.

## References

* [adamson-2024]
-/

namespace CoastalMarind

/-- The four genders: men; women and animals; and two inanimate classes. -/
inductive Gender where
  | gI
  | gII
  | gIII
  | gIV
  deriving DecidableEq, Repr, Fintype

/-- The distal demonstrative *-pe* by gender in the singular; genders I and II share the plural
form *i-pe* with gender IV. -/
def demonstrative : Gender → String
  | .gI => "e-pe"
  | .gII => "u-pe"
  | .gIII => "e-pe"
  | .gIV => "i-pe"

/-- The similative postposition *hV* for genders I and II. -/
def similative : Gender → Option String
  | .gI => some "hi"
  | .gII => some "hu"
  | _ => none

/-- A noun with overt gender alternation: its gender I, gender II, and plural forms. -/
structure Alternating where
  gloss : String
  gI : String
  gII : String
  pl : String
  deriving DecidableEq, Repr

/-- The alternating nouns. -/
def alternating : List Alternating :=
  [⟨"man/woman/people", "anem", "anum", "anim"⟩, ⟨"cousin", "namek", "namuk", "namik"⟩,
    ⟨"face", "nanih", "nanuh", "nanih"⟩,
    ⟨"boy/girl/children", "wananggib", "wananggub", "wanangga"⟩,
    ⟨"somebody", "eɣal", "eɣul", "eɣal"⟩]

/-- The form of *nanVh* 'face' by gender. -/
def face : Gender → String
  | .gII => "nanuh"
  | _ => "nanih"

end CoastalMarind
