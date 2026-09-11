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

/-- The four semantic licensing conditions on expletive-negation triggers of [jin-koenig-2021],
(13): the trigger's meaning entails its argument and the argument's negation in distinct sets of
worlds, at distinct times, contains negation outright, or predicates a degree of distinct
entities. -/
inductive ENLicensing where
  | propositionalAttitude
  | temporal
  | logical
  | comparative
  deriving DecidableEq, Repr, Fintype

/-- The trigger classes of [jin-koenig-2021] Table 5, each named by a representative concept. -/
inductive ENTriggerClass where
  | fear
  | regret
  | deny
  | forget
  | before
  | cannotWait
  | since
  | rarely
  | impossible
  | without
  | unless
  | moreThan
  | differentThan
  | tooTo
  deriving DecidableEq, Repr, Fintype

/-- The licensing condition of a trigger class, [jin-koenig-2021] Section 6. -/
def ENTriggerClass.licensing : ENTriggerClass → ENLicensing
  | .fear | .regret | .deny | .forget => .propositionalAttitude
  | .before | .cannotWait | .since | .rarely => .temporal
  | .impossible | .without | .unless => .logical
  | .moreThan | .differentThan | .tooTo => .comparative

/-- The trigger concepts of [jin-koenig-2021] Table 6, one representative per subclass. -/
inductive ENConcept where
  | fear
  | avoid
  | regret
  | complain
  | adviseAgainst
  | deny
  | hide
  | despair
  | forget
  | delay
  | refuse
  | stop
  | prevent
  | almost
  | barely
  | before
  | cannotWait
  | since
  | rarely
  | impossible
  | difficult
  | without
  | unless
  | onlyDependsOn
  | moreThan
  | lessThan
  | differentThan
  | tooTo
  deriving DecidableEq, Repr, Fintype

/-- The class of a concept. -/
def ENConcept.cls : ENConcept → ENTriggerClass
  | .fear | .avoid => .fear
  | .regret | .complain | .adviseAgainst => .regret
  | .deny | .hide | .despair => .deny
  | .forget | .delay | .refuse | .stop | .prevent | .almost | .barely => .forget
  | .before => .before
  | .cannotWait => .cannotWait
  | .since => .since
  | .rarely => .rarely
  | .impossible | .difficult => .impossible
  | .without => .without
  | .unless | .onlyDependsOn => .unless
  | .moreThan | .lessThan => .moreThan
  | .differentThan => .differentThan
  | .tooTo => .tooTo

end Negation
