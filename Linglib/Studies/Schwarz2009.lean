import Linglib.Semantics.Reference.Description
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.German.Determiners

/-!
# Schwarz (2009): Two Types of Definites in Natural Language

This file formalizes [schwarz-2009]'s thesis that the definite article decomposes into two
articles with distinct presuppositions, the weak article of uniqueness and the strong article of
familiarity, read off the German paradigm of contracted against full preposition-article forms
and masked in English by the syncretic *the*. Both articles are evaluated at a resource
situation; the strong article additionally takes an anaphoric index, so the weak article's
referent is the unique satisfier at the situation and covaries with it
(`weak_article_referent_iff`, `weak_article_covaries`), while the strong article's referent is
the antecedent wherever it is defined and does not (`strong_article_referent_iff`,
`strong_article_rigid`). The German inventory marks the two strengths with distinct forms and
the English one with a single form (`german_two_articles`, `english_syncretic_articles`,
`strategy_split`). The two articles can disagree on a referent in one context: over a restrictor
with two satisfiers the weak article fails uniqueness and the strong article returns its
antecedent (`weak_article_fails_on_multi`, `strong_article_picks_indexed_antecedent`,
`two_articles_can_disagree`).

## References

* [schwarz-2009]
* [schwarz-2013]
* [coppock-beaver-2015]
* [patel-grosz-grosz-2017]
-/

namespace Schwarz2009

open Reference Semantics Semantics.Composition

variable {E W : Type}

/-! ### The two articles take different arguments -/

/-- The weak article denotes `x` at a situation iff `x` is the unique satisfier of the
restrictor there: the situation fixes the referent. -/
theorem weak_article_referent_iff (R : Restrictor E W) (g : Assignment E) (s : W) (x : E) :
    ⟦Description.unique R⟧ g s = some x ↔ R g s x ∧ ∀ y, R g s y → y = x :=
  Description.denote_unique_eq_some_iff R g s

/-- The strong article denotes `x` at a situation iff `x` is its antecedent `g d` and the
restrictor holds of the antecedent there: the index fixes the referent. -/
theorem strong_article_referent_iff (R : Restrictor E W) (d : ℕ) (g : Assignment E) (s : W)
    (x : E) : ⟦Description.anaphoric R d⟧ g s = some x ↔ R g s (g d) ∧ x = g d :=
  Description.denote_anaphoric_eq_some_iff R d g s

/-- The strong article's referent does not covary with the resource situation. -/
theorem strong_article_rigid (R : Restrictor E W) (d : ℕ) (g : Assignment E) {s s' : W}
    {x x' : E} (h : ⟦Description.anaphoric R d⟧ g s = some x)
    (h' : ⟦Description.anaphoric R d⟧ g s' = some x') : x = x' :=
  Description.denote_anaphoric_rigid R d g s h h'

/-! ### The morphological correlate -/

/-- German marks both strengths, with distinct forms. -/
theorem german_two_articles :
    German.Determiners.inventory.Marks .uniqueness ∧
      German.Determiners.inventory.Marks .familiarity ∧
        ¬ German.Determiners.inventory.IsSyncretic := by
  decide

/-- English marks both strengths with the one syncretic form *the*. -/
theorem english_syncretic_articles :
    English.Determiners.inventory.Marks .uniqueness ∧
      English.Determiners.inventory.Marks .familiarity ∧
        English.Determiners.inventory.IsSyncretic := by
  decide

/-- German is bipartite and English generally marked: the same two strengths, distinguished at
the surface in one language and not the other. -/
theorem strategy_split :
    German.Determiners.inventory.markingStrategy = .bipartite ∧
      English.Determiners.inventory.markingStrategy = .generallyMarked :=
  ⟨German.Determiners.marking, English.Determiners.marking⟩

/-! ### The two articles pick different referents -/

/-- Two students. -/
inductive Student where
  | alice
  | bob
  deriving DecidableEq, Repr

/-- Both students count as students at every situation, so the restrictor has two satisfiers
and the weak article fails uniqueness. -/
def studentRestr : Restrictor Student Bool := fun _ _ _ ↦ True

/-- The discourse referent at index `0` is Alice. -/
def gAlice : Assignment Student := fun _ ↦ Student.alice

/-- The weak article fails on a restrictor with two satisfiers. -/
theorem weak_article_fails_on_multi (s : Bool) :
    ⟦Description.unique studentRestr⟧ gAlice s = none := by
  rw [Option.eq_none_iff_forall_ne_some]
  intro x hx
  obtain ⟨-, hu⟩ := (Description.denote_unique_eq_some_iff _ _ _).1 hx
  exact nomatch (hu .alice trivial).trans (hu .bob trivial).symm

/-- The strong article returns its antecedent however many entities satisfy the restrictor. -/
theorem strong_article_picks_indexed_antecedent (s : Bool) :
    ⟦Description.anaphoric studentRestr 0⟧ gAlice s = some .alice :=
  (Description.denote_anaphoric_eq_some_iff _ _ _ _).2 ⟨trivial, rfl⟩

/-- The two articles disagree on a referent in the same context: the semantic counterpart of
the German morphological split. -/
theorem two_articles_can_disagree (s : Bool) :
    ⟦Description.unique studentRestr⟧ gAlice s ≠
      ⟦Description.anaphoric studentRestr 0⟧ gAlice s := by
  rw [weak_article_fails_on_multi, strong_article_picks_indexed_antecedent]
  exact nofun

/-- A restrictor whose unique satisfier differs between two situations, *the mayor* across
towns. -/
def mayorRestr : Restrictor Student Bool := fun _ s x ↦ x = if s then .alice else .bob

/-- The weak article covaries with the resource situation: over `mayorRestr` it picks Alice in
one situation and Bob in the other, the covarying larger-situation uses that the strong article
lacks (`strong_article_rigid`). -/
theorem weak_article_covaries :
    ⟦Description.unique mayorRestr⟧ gAlice true = some .alice ∧
      ⟦Description.unique mayorRestr⟧ gAlice false = some .bob :=
  ⟨(Description.denote_unique_eq_some_iff _ _ _).2 ⟨rfl, fun _ h ↦ h⟩,
    (Description.denote_unique_eq_some_iff _ _ _).2 ⟨rfl, fun _ h ↦ h⟩⟩

end Schwarz2009
