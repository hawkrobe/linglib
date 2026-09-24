module

public import Linglib.Syntax.Case.Basic

/-!
# Basel German case

This file defines the Basel German definite articles and stressed first person singular pronouns
as case markers, following Suter's grammar, and derives the inventory they realize. The pronouns
keep the nominative, the accusative and the dative apart (§124), while an article never tells the
accusative from the nominative (§§82–83). The genitive has long vanished as a case (§91), and the
dative has taken over its functions (§§193–194).

## Main definitions

* `articles`, `pronouns`: the definite articles and the stressed first person singular pronouns
* `inventory`: the cases they realize

## Implementation notes

The genitive surviving in names for a whole family, *s Waagners* 'the Wagner family', and in
frozen expressions (§§83, 92) is left out of the inventory.

## References

* [suter-1992]
-/

@[expose] public section

namespace German.Basel.Case

/-! ### The definite article -/

/-- *der* is the masculine singular nominative and accusative and the feminine singular dative
(§83). -/
def der : Case.Marker := ⟨"der", {.nom, .acc, .dat}⟩

/-- *die* is the feminine singular and the plural nominative and accusative (§83). -/
def die : Case.Marker := ⟨"die", {.nom, .acc}⟩

/-- *d* is the reduced form of *die* (§83). -/
def d : Case.Marker := ⟨"d", {.nom, .acc}⟩

/-- *s* is the neuter singular nominative and accusative (§83). -/
def s : Case.Marker := ⟨"s", {.nom, .acc}⟩

/-- *em* is the masculine and neuter singular dative (§83). -/
def em : Case.Marker := ⟨"em", {.dat}⟩

/-- *de* is the plural dative (§83). -/
def de : Case.Marker := ⟨"de", {.dat}⟩

/-- `articles` is the set of definite articles. -/
def articles : Finset Case.Marker := {der, die, d, s, em, de}

/-! ### The pronoun -/

/-- *yych* is the stressed nominative 'I' (§125). -/
def yych : Case.Marker := ⟨"yych", {.nom}⟩

/-- *mii* is the stressed accusative 'me' (§125). -/
def mii : Case.Marker := ⟨"mii", {.acc}⟩

/-- *miir* is the stressed dative 'me' (§125). -/
def miir : Case.Marker := ⟨"miir", {.dat}⟩

/-- `pronouns` is the set of stressed first person singular pronouns. -/
def pronouns : Finset Case.Marker := {yych, mii, miir}

/-! ### The inventory -/

/-- `inventory` is the set of cases the articles and the pronouns realize. -/
def inventory : Finset Case := Case.Marker.inventory (articles ∪ pronouns)

theorem inventory_eq : inventory = {.nom, .acc, .dat} := by decide

/-- No article tells the accusative from the nominative (§82). -/
theorem nom_mem_iff_acc_mem_of_mem_articles :
    ∀ m ∈ articles, .nom ∈ m.cases ↔ .acc ∈ m.cases := by decide

/-- The pronoun does (§124). -/
theorem exists_pronoun_acc_not_nom :
    ∃ m ∈ pronouns, .acc ∈ m.cases ∧ .nom ∉ m.cases :=
  ⟨mii, by decide, by decide⟩

end German.Basel.Case
