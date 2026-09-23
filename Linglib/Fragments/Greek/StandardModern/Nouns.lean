module

public import Linglib.Semantics.Genericity.NominalMappingParameter

/-!
# Greek nominal parameters

Greek is [−arg, +pred] like Romance ([chierchia-1998]): bare nouns are predicates and need D to
be arguments, and bare plurals cannot denote kinds without the definite article. Its articles are
`Greek.StandardModern.Determiners.inventory`. Greek differs from Romance in DP-internal syntax:
adjectives are prenominal, so N cannot raise past them, and a proper name cannot satisfy strong
D by raising and takes the definite article instead (`Studies/Longobardi2001.lean`).

## References

* [chierchia-1998]
-/

@[expose] public section

namespace Greek.StandardModern.Nouns

open Genericity

/-- Greek is [−arg, +pred]: nouns are predicates and need D to be arguments. -/
def nominalMapping : NominalMapping := .predOnly

end Greek.StandardModern.Nouns
