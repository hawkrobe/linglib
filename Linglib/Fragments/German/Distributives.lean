module

public import Linglib.Semantics.Plurality.Distributivity
public import Linglib.Syntax.Category.Determiner.Basic

/-!
# German distributive expressions

This file defines the German universal determiners *jeder* 'each, every' and *alle* 'all' and
the distributive denotations of *jeder* and of the adverb *jeweils* 'each, respectively'. Durrell
describes *jeder* as used only in the singular, as a determiner or a pronoun, and *alle* as
chiefly plural, in the singular with mass nouns and mostly in formal registers. *Jeder*
distributes its predicate over every atom of a plurality, the substrate's maximal distribution,
and *jeweils*, which has no determiner use, over the atoms of a subplurality the context
tolerates. Haslinger and colleagues class the items by obligatory distributivity and exception
intolerance in their study.

## References

* [durrell-2011]
* [haslinger-etal-2025]
-/

@[expose] public section

namespace German.Distributives

open Plurality Plurality.Distributivity

/-- *Jeder* 'each, every' is a determiner of singular nouns. -/
def jeder : Quantifier := { form := "jeder", numberRestriction := some .singular }

/-- *Alle* 'all' is a determiner chiefly of plural nouns, and in the singular of mass nouns. -/
def alle : Quantifier := { form := "alle", selectsMass := true }

variable {Atom W : Type*}

/-- `jederSem P` distributes `P` over every atom of a plurality. -/
abbrev jederSem (P : Atom → W → Prop) : Finset Atom → W → Prop := distMaximal P

/-- `jeweilsSem P tol` distributes `P` over the atoms of some subplurality that the tolerance
`tol` admits. -/
abbrev jeweilsSem (P : Atom → W → Prop) (tol : Tolerance Atom) : Finset Atom → W → Prop :=
  distTolerant P tol

end German.Distributives
