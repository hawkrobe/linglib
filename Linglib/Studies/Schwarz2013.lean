import Linglib.Semantics.Reference.Definiteness
import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Fragments.German.Determiners
import Linglib.Fragments.Fering.Determiners
import Linglib.Fragments.Akan.Determiners
import Linglib.Fragments.MauritianCreole.Determiners
import Linglib.Fragments.HaitianCreole.Determiners
import Linglib.Fragments.Lakhota.Determiners
import Linglib.Fragments.Hausa.Determiners

/-!
# Schwarz (2013): Two Kinds of Definites Cross-linguistically

This file formalizes the survey's typology of definite articles. Beyond the German and Fering
baseline of [schwarz-2009], where a weak article marks situational uniqueness and a strong one
anaphoricity, the survey finds languages whose only overt definite article is anaphoric, with weak
definites as bare nominals (Akan *nó*, Mauritian Creole *la*), languages with two overt articles
(Lakhota *kiŋ* and *k'uŋ*, Hausa *-n* and *ɗîn*), and Haitian Creole *la*, a single article
covering both use families that fits neither pattern. Each language's cell is derived from its
fragment's `Determiners.inventory` through the substrate's `markingStrategy`, and the bridging
split, part-whole bridging with the weak article and producer bridging with the strong one, is the
substrate's `Bridging.strength`. The Lakhota classification is tentative in the survey itself,
whose footnote 16 concedes [ingham-2003]'s anaphoric *kiŋ*; the project fragment encodes that
anaphoric use, under which the derived cell flips from bipartite to generally marked
(`anaphoric_kin_flips_cell`).

## Implementation notes

The survey's remarks on covarying uses, that both German and Fering articles and the creole *la*
allow them, are recorded in the fragments' `.donkey` uses rather than proved here, since the
survey reports no data on the remaining languages.

## References

* [schwarz-2013]
* [schwarz-2009]
* [ingham-2003]
* [wespel-2008]
-/

namespace Schwarz2013

open Reference

/-! ### The German/Fering baseline (§3.1) -/

/-- German and Fering each split the definite paradigm in two, Fering's A-form against its
D-form and German's contracted against its full preposition-article forms, deriving the
bipartite cell. -/
theorem german_fering_bipartite :
    German.Determiners.inventory.markingStrategy = .bipartite ∧
    Fering.Determiners.inventory.markingStrategy = .bipartite :=
  ⟨German.Determiners.marking, Fering.Determiners.marking⟩

/-- The bridging split (§3.2): part-whole bridging, the fridge and its crisper, takes the
weak article, and producer bridging, the play and its author, the strong one, in German (16)
and Fering (17) alike. -/
theorem bridging_split :
    Bridging.strength .partWhole = .uniqueness ∧
    Bridging.strength .relational = .familiarity :=
  ⟨rfl, rfl⟩

/-! ### Languages with exclusively anaphoric articles (§4.1) -/

/-- Akan *nó* and Mauritian Creole *la* mark only anaphoric definites, weak definites being
bare nominals: the marked-anaphoric cell. -/
theorem exclusively_anaphoric :
    Akan.Determiners.inventory.markingStrategy = .markedAnaphoric ∧
    MauritianCreole.Determiners.inventory.markingStrategy = .markedAnaphoric :=
  ⟨Akan.Determiners.marking, MauritianCreole.Determiners.marking⟩

/-- The §4.1 pattern through the cell's characterization: neither language marks uniqueness
overtly and both mark familiarity. -/
theorem weak_definites_bare :
    (¬ Akan.Determiners.inventory.Marks .uniqueness ∧
      Akan.Determiners.inventory.Marks .familiarity) ∧
    (¬ MauritianCreole.Determiners.inventory.Marks .uniqueness ∧
      MauritianCreole.Determiners.inventory.Marks .familiarity) :=
  ⟨Determiner.Inventory.markingStrategy_eq_markedAnaphoric_iff.mp
      Akan.Determiners.marking,
    Determiner.Inventory.markingStrategy_eq_markedAnaphoric_iff.mp
      MauritianCreole.Determiners.marking⟩

/-! ### Languages with two articles (§4.2) -/

/-- Hausa splits its two overt articles: suffixal *-n* for uniquely identifiable referents,
inferable first mentions included, and *ɗîn* for discourse-old ones (§4.2.2), the bipartite
cell of German and Fering. -/
theorem hausa_bipartite :
    Hausa.Determiners.inventory.markingStrategy = .bipartite :=
  Hausa.Determiners.marking

/-- The tentative construal of Lakhota in §4.2.1: *kiŋ* weak only, for globally and
situationally unique referents ((30), (31)), and *k'uŋ* the anaphoric strong article, 'the
above-mentioned'. -/
def lakhotaWeakStrongConstrual : Determiner.Inventory :=
  [ .article { form := "kiŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := {.immediateSituation, .largerSituation} },
    .article { form := "k'uŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := {.anaphoric} } ]

/-- Under the tentative construal, Lakhota patterns with German and Fering. -/
theorem construal_bipartite :
    lakhotaWeakStrongConstrual.markingStrategy = .bipartite := by decide

/-- The caveat of footnote 16: granting [ingham-2003]'s anaphoric *kiŋ*, as the project
fragment does, makes *kiŋ* syncretic and flips the derived cell to generally marked, so the
weak and strong parallel is indeed less extensive. -/
theorem anaphoric_kin_flips_cell :
    lakhotaWeakStrongConstrual.markingStrategy = .bipartite ∧
    Lakhota.Determiners.inventory.markingStrategy = .generallyMarked ∧
    Lakhota.Determiners.inventory.IsSyncretic :=
  ⟨construal_bipartite, Lakhota.Determiners.marking, by decide⟩

/-! ### Haitian Creole: a different type of contrast (§4.3) -/

/-- Haitian Creole *la* covers uniqueness at every level, anaphora and both bridging types
((39) to (42)): a syncretic sole article, so the derived cell is generally marked, neither the
§4.1 nor the §4.2 pattern. -/
theorem haitian_generallyMarked :
    HaitianCreole.Determiners.inventory.markingStrategy = .generallyMarked ∧
    HaitianCreole.Determiners.inventory.IsSyncretic :=
  ⟨HaitianCreole.Determiners.marking, by decide⟩

end Schwarz2013
