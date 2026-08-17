import Linglib.Semantics.Definiteness.Defs
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

[schwarz-2013] surveys the weak/strong article contrast beyond the German
and Fering baseline of [schwarz-2009]: languages whose only overt definite
article is anaphoric (Akan *nó*, Mauritian Creole *la* — weak definites
are bare nominals, §4.1), languages with two overt articles (Lakhota
*kiŋ* ~ *k'uŋ*, Hausa *-n* ~ *ɗîn*, §4.2), and Haitian Creole *la*, whose
single article covers both use families and fits neither pattern (§4.3).
Each language's cell is derived from its Fragment's
`Determiners.inventory`; the bridging split (§3.2) is the substrate's
`bridgingPresupType`. The Lakhota classification is tentative in the paper
itself: fn. 16 concedes [ingham-2003]'s anaphoric *kiŋ*, under which the
derived cell flips from `.bipartite` to `.generallyMarked` — the project
fragment encodes the flipped cell, and the divergence is proved below.

## References

* [schwarz-2013]
-/

namespace Schwarz2013

open Semantics.Definiteness

/-! ### The German/Fering baseline (§3.1) -/

/-- German and Fering each split the definite paradigm in two — Fering's
    A-form vs D-form, German's contracted vs full preposition-article
    forms (exx. (5)–(7)) — deriving the `.bipartite` cell. -/
theorem german_fering_bipartite :
    German.Determiners.inventory.markingStrategy = .bipartite ∧
    Fering.Determiners.inventory.markingStrategy = .bipartite :=
  ⟨German.Determiners.marking, Fering.Determiners.marking⟩

/-- The bridging split (§3.2): part-whole bridging (the fridge … the
    crisper) takes the weak article, producer/relational bridging (the
    play … the author) the strong, in both German and Fering. -/
theorem bridging_split :
    bridgingPresupType .partWhole = .uniqueness ∧
    bridgingPresupType .relational = .familiarity :=
  ⟨rfl, rfl⟩

/-! ### Languages with exclusively anaphoric articles (§4.1) -/

/-- Akan *nó* and Mauritian Creole *la* mark only anaphoric definites;
    weak definites are bare nominals — the `.markedAnaphoric` cell. -/
theorem exclusively_anaphoric :
    Akan.Determiners.inventory.markingStrategy = .markedAnaphoric ∧
    MauritianCreole.Determiners.inventory.markingStrategy = .markedAnaphoric :=
  ⟨Akan.Determiners.marking, MauritianCreole.Determiners.marking⟩

/-- The §4.1 pattern unpacked via the cell characterization: neither
    language marks uniqueness overtly, both mark familiarity. -/
theorem weak_definites_bare :
    (¬ Akan.Determiners.inventory.MarksPresup .uniqueness ∧
      Akan.Determiners.inventory.MarksPresup .familiarity) ∧
    (¬ MauritianCreole.Determiners.inventory.MarksPresup .uniqueness ∧
      MauritianCreole.Determiners.inventory.MarksPresup .familiarity) :=
  ⟨Determiner.Inventory.markingStrategy_eq_markedAnaphoric_iff.mp
      Akan.Determiners.marking,
    Determiner.Inventory.markingStrategy_eq_markedAnaphoric_iff.mp
      MauritianCreole.Determiners.marking⟩

/-! ### Languages with two articles (§4.2) -/

/-- Hausa splits its two overt articles weak/strong: suffixal *-n* for
    uniquely identifiable referents including inferable first mentions,
    *ɗîn* for discourse-familiar ones (§4.2.2) — `.bipartite`, like German
    and Fering. -/
theorem hausa_bipartite :
    Hausa.Determiners.inventory.markingStrategy = .bipartite :=
  Hausa.Determiners.marking

/-- §4.2.1's tentative construal of Lakhota: *kiŋ* weak-only (globally and
    situationally unique referents, exx. (30)–(31)), *k'uŋ* the anaphoric
    strong article ('the above-mentioned'). -/
def lakhotaWeakStrongConstrual : Determiner.Inventory :=
  [ .article { form := "kiŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.immediateSituation, .largerSituation] },
    .article { form := "k'uŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric] } ]

/-- Under the tentative construal, Lakhota patterns with German and
    Fering. -/
theorem construal_bipartite :
    lakhotaWeakStrongConstrual.markingStrategy = .bipartite := by decide

/-- Fn. 16's caveat, formalized: granting [ingham-2003]'s anaphoric *kiŋ* —
    as the project fragment does — makes *kiŋ* syncretic, and the derived
    cell flips to `.generallyMarked`: the weak/strong parallel "may be even
    less extensive" indeed. -/
theorem anaphoric_kin_flips_cell :
    lakhotaWeakStrongConstrual.markingStrategy = .bipartite ∧
    Lakhota.Determiners.inventory.markingStrategy = .generallyMarked ∧
    Lakhota.Determiners.inventory.IsSyncretic :=
  ⟨construal_bipartite, Lakhota.Determiners.marking, by decide⟩

/-! ### Haitian Creole: a different type of contrast (§4.3) -/

/-- Haitian Creole *la* covers uniqueness at every level, anaphora, and
    both bridging types (exx. (39)–(42)): a syncretic sole article, so the
    derived cell is `.generallyMarked` — neither the §4.1 nor the §4.2
    pattern. -/
theorem haitian_generallyMarked :
    HaitianCreole.Determiners.inventory.markingStrategy = .generallyMarked ∧
    HaitianCreole.Determiners.inventory.IsSyncretic :=
  ⟨HaitianCreole.Determiners.marking, by decide⟩

/-! ### Covarying uses (§5.2) -/

/-- Covarying (donkey) definites are reported for the German and Fering
    strong articles and for creole *la* (fn. 20, via [wespel-2008]), and
    the corresponding fragments carry the `.donkey` use. -/
theorem covarying_reported :
    (∃ e ∈ German.Determiners.inventory, .donkey ∈ e.definiteUses) ∧
    (∃ e ∈ Fering.Determiners.inventory, .donkey ∈ e.definiteUses) ∧
    (∃ e ∈ MauritianCreole.Determiners.inventory, .donkey ∈ e.definiteUses) ∧
    (∃ e ∈ HaitianCreole.Determiners.inventory, .donkey ∈ e.definiteUses) := by
  decide

/-- The survey reports no covarying uses for Akan, Lakhota, or Hausa, and
    the corresponding fragments record none. -/
theorem covarying_unreported :
    (¬ ∃ e ∈ Akan.Determiners.inventory, .donkey ∈ e.definiteUses) ∧
    (¬ ∃ e ∈ Lakhota.Determiners.inventory, .donkey ∈ e.definiteUses) ∧
    (¬ ∃ e ∈ Hausa.Determiners.inventory, .donkey ∈ e.definiteUses) := by
  decide

end Schwarz2013
