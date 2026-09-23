module

/-!
# English inflectional spelling

The regular inflectional suffixes of English in their spelling: *-s*, which the plural of a
count noun and the third-singular present of a verb share (*cats*, *sits*; *stories*,
*cries*; *boxes*, *fixes*), *-ed* of the past and past participle, and *-ing* of the present
participle. Each rule takes the citation form to the suffixed form and applies the spelling
adjustments at the boundary: *y* after a consonant becomes *ie*, a sibilant takes *-es*, a
final silent *e* drops before a vowel-initial suffix.

## Main definitions

* `suffixS`, `suffixEd`, `suffixIng` — the three suffixes with their spelling adjustments
-/

@[expose] public section

namespace English

def isVowel (c : Char) : Bool :=
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'

/-- Whether the form ends in a consonant followed by *y*. -/
def endsWithConsonantY (s : String) : Bool :=
  match s.toList.reverse with
  | 'y' :: c :: _ => !isVowel c
  | _ => false

/-- Whether the form ends in a sibilant spelled *sh*, *ch*, *ss*, *x* or *z*. -/
def endsWithSibilant (s : String) : Bool :=
  s.endsWith "sh" || s.endsWith "ch" || s.endsWith "ss" || s.endsWith "x" || s.endsWith "z"

/-- The form with *-s*: *-ies* after a consonant and *y*, *-es* after a sibilant. -/
def suffixS (stem : String) : String :=
  if endsWithConsonantY stem then String.ofList (stem.toList.dropLast ++ "ies".toList)
  else if endsWithSibilant stem then stem ++ "es"
  else stem ++ "s"

/-- The form with *-ed*: *-ied* after a consonant and *y*, *-d* after *e*. -/
def suffixEd (stem : String) : String :=
  if endsWithConsonantY stem then String.ofList (stem.toList.dropLast ++ "ied".toList)
  else if stem.endsWith "e" then stem ++ "d"
  else stem ++ "ed"

/-- The form with *-ing*, dropping a final silent *e*. -/
def suffixIng (stem : String) : String :=
  if stem.endsWith "e" && !stem.endsWith "ee" then
    String.ofList (stem.toList.dropLast ++ "ing".toList)
  else stem ++ "ing"

end English
