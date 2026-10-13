module

public import Linglib.Morphology.Nanosyntax.Lexicalization

/-!
# De Clercq et al. (2025): Nanosyntax: State of the art and recent developments

De Clercq, Caha, Starke and Vanden Wyngaerd present the lexicalization algorithm through case
studies, three of which this file runs. In the degrees of comparison the size of the root
decides how many suffixes an adjective takes, and an entry matching a larger phrase overrides
the exponents inside it. In Czech declension a root that lexicalizes the accusative by itself
shrinks in the genitive, the derivation going back to an earlier merger. In the Friulian
present a suffix storing a branching tree appears in the first and third person and makes room
for a second suffix in the second.

## Main results

* `english_degrees`, `armenian_degrees`, `czech_degrees`: the lexicalization table of the
  degrees of comparison.
* `czech_declension`, `genitive_levels`: the genitive is *-a* in both noun classes, with the
  same structure.
* `friulian_present`: the first and third person are alike and the second has a suffix more.

## Implementation notes

The chapter's entries with an unlabelled root, for inverse number marking and for the Friulian
verb *bati*, and its prefixes, built in a workspace of their own, are outside the engine. The
Czech superlative *nej-* is such a prefix, so `czech_degrees` shows only that the movement
steps do not derive the superlative.

## References

* [declercq-et-al-2025]
* [starke-2018]
-/

@[expose] public section

namespace DeClercqEtAl2025

open Morphology.Nanosyntax Morphology.Exponence RoseTree

/-! ### Degrees of comparison -/

/-- The features of the adjectival sequence are the adjective, gradability, the comparative
and the superlative. -/
inductive Deg where
  | a | q | cmpr | sprl
  deriving DecidableEq, Repr

/-- English *tall* stores the gradable adjective, *-er* the comparative alone and *-est* the
superlative over the comparative. -/
def tall : RuleSet (LexicalEntry Deg String) :=
  [⟨phrase .a [.q], "tall"⟩, ⟨leaf .cmpr, "er"⟩, ⟨phrase .cmpr [.sprl], "est"⟩]

/-- English *bad* beside *worse*, a root storing the comparative. -/
def bad : RuleSet (LexicalEntry Deg String) :=
  [⟨phrase .a [.q], "bad"⟩, ⟨phrase .a [.q, .cmpr], "worse"⟩, ⟨leaf .cmpr, "er"⟩]

/-- Armenian *partsrahasag* 'tall' stores the superlative. -/
def partsrahasag : RuleSet (LexicalEntry Deg String) :=
  [⟨phrase .a [.q, .cmpr, .sprl], "partsrahasag"⟩]

/-- Czech *inteligent-* stores the bare adjective, with the adjectivizer *-n* and the
comparative *-ějš* storing one feature each. -/
def inteligent : RuleSet (LexicalEntry Deg String) :=
  [⟨leaf .a, "inteligent"⟩, ⟨leaf .q, "n"⟩, ⟨leaf .cmpr, "ějš"⟩]

/-- Czech *chytr-* 'smart' stores the gradable adjective. -/
def chytr : RuleSet (LexicalEntry Deg String) :=
  [⟨phrase .a [.q], "chytr"⟩, ⟨leaf .cmpr, "ějš"⟩]

/-- The sequences of the positive, the comparative and the superlative. -/
def degrees : List (List Deg) := [[.a, .q], [.a, .q, .cmpr], [.a, .q, .cmpr, .sprl]]

/-- English *tall*, *tall-er*, *tall-est*: the comparative suffix follows the evacuated root
and the superlative suffix overrides it. With *worse* in the lexicon the comparative needs no
evacuation, so it is *worse* and not *badd-er*. -/
theorem english_degrees :
    degrees.map (exponents tall) = [some ["tall"], some ["tall", "er"], some ["tall", "est"]] ∧
      exponents bad [.a, .q, .cmpr] = some ["worse"] := by
  decide

/-- Armenian has the one form in all three degrees, each phrase a subtree of the stored
one. -/
theorem armenian_degrees :
    degrees.map (exponents partsrahasag) =
      [some ["partsrahasag"], some ["partsrahasag"], some ["partsrahasag"]] := by
  decide

/-- Czech *inteligent-n-(í)*, *inteligent-n-ějš-(í)* and *chytř-ejš-(í)*: the smaller root takes
a suffix more. The movement steps do not derive the superlative, no entry storing the
superlative feature with a unary foot, and the algorithm's last resort builds the prefix
*nej-*. -/
theorem czech_degrees :
    degrees.map (exponents inteligent) =
        [some ["inteligent", "n"], some ["inteligent", "n", "ějš"], none] ∧
      exponents chytr [.a, .q, .cmpr] = some ["chytr", "ějš"] := by
  decide

/-! ### Czech declension -/

/-- The features of the nominal sequence are the noun, the singular, and one each for the
nominative, the accusative and the genitive. -/
inductive Case where
  | n | sg | k1 | k2 | k3
  deriving DecidableEq, Repr

/-- The suffix *-a* stores the genitive down to the singular. -/
def suffixA : LexicalEntry Case String := ⟨phrase .sg [.k1, .k2, .k3], "a"⟩

/-- *chleb-* 'bread' stores the bare noun. -/
def chleb : RuleSet (LexicalEntry Case String) := [⟨leaf .n, "chleb"⟩, suffixA]

/-- *jazyk* 'tongue' stores the accusative. -/
def jazyk : RuleSet (LexicalEntry Case String) :=
  [⟨phrase .n [.sg, .k1, .k2], "jazyk"⟩, suffixA]

/-- The sequences of the nominative, the accusative and the genitive. -/
def cases : List (List Case) :=
  [[.n, .sg, .k1], [.n, .sg, .k1, .k2], [.n, .sg, .k1, .k2, .k3]]

/-- *chleb-a* in all three cases, and *jazyk*, *jazyk*, *jazyk-a*. -/
theorem czech_declension :
    cases.map (exponents chleb) =
        [some ["chleb", "a"], some ["chleb", "a"], some ["chleb", "a"]] ∧
      cases.map (exponents jazyk) = [some ["jazyk"], some ["jazyk"], some ["jazyk", "a"]] := by
  decide

/-- In the genitive the root *jazyk* cannot grow, and no entry lexicalizes the genitive feature
alone, so the derivation goes back to the merger of the singular and evacuates the noun there.
Its constituents are then those of *chleb-a*, the two classes levelled. -/
theorem genitive_levels :
    (lexicalize jazyk [.n, .sg, .k1, .k2, .k3]).map (·.map Prod.fst) =
      (lexicalize chleb [.n, .sg, .k1, .k2, .k3]).map (·.map Prod.fst) := by
  decide

/-! ### The Friulian present -/

/-- The features of the verbal sequence are tense, number, person, participant and speaker. -/
inductive Phi where
  | t | num | π | part | spkr
  deriving DecidableEq, Repr

/-- Tualis Friulian *fin-* 'finish' stores number over tense, *-iʃ* the speaker over a person
phrase stranded beside the participant, and *-s* the participant alone. -/
def fin : RuleSet (LexicalEntry Phi String) :=
  [⟨phrase .t [.num], "fin"⟩, ⟨node .spkr [leaf .π, leaf .part], "iʃ"⟩, ⟨leaf .part, "s"⟩]

/-- Third person *fin-iʃ*, second *fin-iʃ-s*, first *fin-iʃ*. In the first person the verb
evacuates alone from under the speaker feature, which strands the person and the participant
phrases in the shape *-iʃ* stores. -/
theorem friulian_present :
    exponents fin [.t, .num, .π] = some ["fin", "iʃ"] ∧
      exponents fin [.t, .num, .π, .part] = some ["fin", "iʃ", "s"] ∧
      exponents fin [.t, .num, .π, .part, .spkr] = some ["fin", "iʃ"] := by
  decide

end DeClercqEtAl2025
