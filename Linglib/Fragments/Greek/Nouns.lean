import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998

/-! # Greek Noun Fragment

Greek nominal parameters. Greek is a [-arg, +pred] language like Romance:
bare nouns are predicative (need D for argumenthood), bare plurals cannot
denote kinds without an overt definite article.

Greek differs from Romance in DP-internal syntax: adjectives are prenominal
(as in Germanic), indicating that N cannot raise past the α constituent
(opaque α). This means proper names cannot satisfy strong D by N-raising
and must instead appear with an overt definite article.
-/

namespace Fragments.Greek.Nouns

open Semantics.Lexical.Noun.Kind.Chierchia1998 (BlockingPrinciple NominalMapping)

/-- Greek is a [-arg, +pred] language: nouns are predicates,
    bare arguments are not licensed for kind reference.
    Same as Romance (@cite{chierchia-1998}). -/
def greekMapping : NominalMapping := .predOnly

/-- Greek has a rich article system that blocks bare arguments. -/
def greekBlocking : BlockingPrinciple :=
  { determiners := ["o", "i", "to", "oi", "ta",   -- definite
                     "enas", "mia", "ena"]          -- indefinite
  , iotaBlocked := true
  , existsBlocked := true
  , downBlocked := true }

/-- Greek bare plurals are not licensed as arguments. -/
def barePluralLicensed : Bool := !greekBlocking.downBlocked

/-- Greek bare singulars are not licensed as arguments. -/
def bareSingularLicensed : Bool := false

example : barePluralLicensed = false := rfl
example : bareSingularLicensed = false := rfl

end Fragments.Greek.Nouns
