module

public import Linglib.Syntax.Category.Coordinator

/-!
# Irish coordinators

Irish coordinates with free words that stand before the second coordinand: *agus* 'and', *nó*
'or' and *ach* 'but'. The emphatic conjunction is *idir … agus* 'both … and', which Haspelmath
lists among the correlatives whose second member is the plain coordinator. Irish has no emphatic
negative pair like *neither … nor*: Haspelmath records the single word *ná* 'nor', used after
the ordinary sentence negation, which is also the particle 'than' of comparatives.

## Main definitions

* `Irish.Coordination.agus`, `Irish.Coordination.no_`, `Irish.Coordination.na_`,
  `Irish.Coordination.ach`: the conjunctive, disjunctive, negative and adversative coordinators.
* `Irish.Coordination.idirAgus`: the emphatic conjunction.

## TODO

*nó* and *ach* are not in Haspelmath's chapter and have not been checked against a grammar of
Irish.

## References

* [haspelmath-2007]
-/

@[expose] public section

namespace Irish.Coordination

/-- *agus* 'and'. -/
def agus : Coordinator :=
  { form := "agus", gloss := "and", role := .conjunctive, kind := .free }

/-- *nó* 'or'. -/
def no_ : Coordinator :=
  { form := "nó", gloss := "or", role := .disjunctive, kind := .free }

/-- *ná* 'nor', also the comparative particle 'than'. -/
def na_ : Coordinator :=
  { form := "ná", gloss := "nor; than", role := .negative, kind := .free }

/-- *ach* 'but'. -/
def ach : Coordinator :=
  { form := "ach", gloss := "but", role := .adversative, kind := .free }

/-- The coordinators. -/
def allEntries : List Coordinator := [agus, no_, na_, ach]

/-- *idir … agus* 'both … and'. -/
def idirAgus : Coordinator.Correlative := ⟨"idir", agus.form, agus⟩

/-- The emphatic constructions. -/
def correlatives : List Coordinator.Correlative := [idirAgus]

end Irish.Coordination
