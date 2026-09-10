import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.DeriveFintype

/-!
# Expletive negation

Typological classification of expletive negation (EN), the negative marker without negative
force of *before*-clauses, comparatives, *until*-clauses, and exclamatives, in the tradition of
[espinal-1992]. `ENType` is [rett-2026]'s high/low distinction by attachment site, `ENStrength`
is [greco-2020]'s weak/strong distinction by the polarity-sensitive elements an environment
still licenses (`ENStrength.licensed`), and `ENBlockingReason` records why a trigger class fails
to license EN in a language ([jin-koenig-2021]). Fragments type their per-language EN data
with these.

## References

* [espinal-1992]
* [greco-2020]
* [jin-koenig-2021]
* [rett-2026]
-/

namespace Negation

/-- Why a trigger class fails to license EN in a language ([jin-koenig-2021] section 7). -/
inductive ENBlockingReason where
  /-- The language disprefers modal operators in complement clauses. -/
  | modalRestriction
  /-- Comparative complements admit only noun phrases. -/
  | npOnlyComplement
  /-- The concept is expressed analytically with a necessary negation. -/
  | analyticNegation
  deriving DecidableEq, Repr

/-- [rett-2026]'s two types of EN: high EN, above TP, is obligatory and non-truth-conditional
(exclamatives, surprise negation); low EN, below TP, is optional and truth-conditional in
ambidirectional environments (*before*, *than*, *fear*). -/
inductive ENType where
  | high
  | low
  deriving DecidableEq, Repr

/-- The four classes of polarity-sensitive element [greco-2020] Table 1 tests in each EN
environment: weak NPIs (*alzare un dito* 'lift a finger'), strong NPIs (*affatto* 'at all'),
not-also conjunctions (*e neanche*), and n-words (*nessuno* 'nobody'). -/
inductive PolarityClass where
  | weakNPI
  | strongNPI
  | notAlsoConj
  | nWord
  deriving DecidableEq, Repr, Fintype

/-- [greco-2020]'s two classes of EN environment: weak EN keeps some of the licensing of
standard negation, strong EN keeps none. -/
inductive ENStrength where
  | weak
  | strong
  deriving DecidableEq, Repr

/-- The polarity classes an EN environment of each strength licenses ([greco-2020] Table 1,
whose rows are uniform within each class): weak EN licenses weak NPIs and n-words. -/
def ENStrength.licensed : ENStrength → Finset PolarityClass
  | .weak => {.weakNPI, .nWord}
  | .strong => ∅

end Negation
