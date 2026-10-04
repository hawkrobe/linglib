module

public import Linglib.Syntax.WordOrder
public import Linglib.Studies.BrueningAlKhalaf2020
public import Linglib.Data.Examples.Schwarzer2026
public import Linglib.Data.Experiments.Schwarzer2026
public import Linglib.Fragments.German.Verbs
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Schwarzer (2026): The law and order of selection-violating coordination

This file formalizes the squib's test of the three analyses of selection-violating coordination,
a clause coordinated with a noun phrase in a position where only the noun phrase is selected. The
bottom-up analyses of [sag-etal-1985] and [munn-1993] give the coordination an asymmetric
structure in which the first conjunct alone is prominent for the selector, so the selected noun
phrase comes first whatever the position of the verb; the linear closeness analysis of
[bruening-alkhalaf-2020] and [bruening-2025] derives left to right and lets the conjunct linearly
adjacent to the selector satisfy selection; and the temporal closeness analysis of [kim-lu-2024]
treats the mismatch as a grammaticality illusion in which the parser checks the conjunct closest in
time to the selector, which is the conjunct the linear analysis checks
(`closestInTime_eq_leftToRight`). In German the two predictions come apart: complements precede
the verb in an embedded finite clause and follow it in a root clause with verb-second
(`embeddedPosition`, `rootPosition`), so the closeness accounts admit only the clause first in the
embedded case, where the two accounts admit opposite orders (`accounts_diverge_embedded`).

Experiment 1 confirms that German allows the construction with verbs that reject a bare
*dass*-clause (`Data/Examples/Schwarzer2026`, (11) and (12)): selection raises the ratings of both
complements, and a coordination loses less than a bare clause where the verb does not select one
(`selection_raises`, `selection_interaction`). Experiment 2's forced choice finds the noun phrase
first in twenty-three of thirty choices in both positions (`Data/Experiments/Schwarzer2026`), so
the preferred order is the noun phrase first in both (`preferred_eq`). A noun-phrase-first
preference in the embedded position refutes the closeness prediction
(`closeness_rejects_dpFirst`), and
the choices supply it (`choices_refute_closeness`), while the structural account admits the noun
phrase first in either position (`structural_admits_iff`) and matches the choices in both positions
(`choices_match_structural`); the squib notes that the latter is thereby supported only
indirectly.

## Implementation notes

* The verb positions are read off the German verb-second profile, with the finite verb in the
  clause-final position of an embedded clause and in second position of a root declarative.
* The eight predicates of Experiment 1 are the entries of `Fragments/German/Verbs`, whose frames
  say whether a predicate takes a *dass*-clause; each row's selection value is read off its
  predicate's entry (`rows_selectsCP`), and so are the judgments of the bare clauses (`dass_rows`).
* The descriptive statistics of Experiment 1 and the choices of Experiment 2 are
  `Data/Experiments/Schwarzer2026`; the mixed model and the logistic regression are not
  formalized, and the preferred order is read off the counts as the order chosen more often.

## References

* [schwarzer-2026]
* [bruening-alkhalaf-2020]
* [kim-lu-2024]
* [sag-etal-1985]
-/

@[expose] public section

namespace Schwarzer2026

open BrueningAlKhalaf2020
open Syntax (Cat)
open Syntax.Cat (NP)

variable {α : Type*}

/-- In a German root declarative the verb in second position precedes its complements, the
configuration of (17). -/
abbrev rootPosition : HeadDirection := .headInitial

/-- In an embedded finite clause the verb is clause-final, so the coordination precedes it, the
configuration of (16). -/
abbrev embeddedPosition : HeadDirection := .headFinal

/-- The phrases of a coordination of the noun phrase and the clause in each order. -/
def Order.phrases : Order → List Cat
  | .dpFirst => [NP, .CP]
  | .cpFirst => [.CP, NP]

/-- The temporal closeness analysis has the parser check the conjunct closest in time to the
selector, the first when the verb precedes and the last, whose features are still in memory, when
it follows. -/
def closestInTime : HeadDirection → List α → Option α
  | .headInitial, cs => cs.head?
  | .headFinal, cs => cs.getLast?

/-- The temporal closeness analysis checks the conjunct the left-to-right derivation does. -/
theorem closestInTime_eq_leftToRight : closestInTime (α := α) = leftToRight := by
  funext d cs; cases d <;> simp [closestInTime]

/-- The bottom-up analyses check the first conjunct whatever the verb's position, and so admit
the selected noun phrase first, (10b), with a verb that does not select a clause. -/
theorem structural_admits_iff (o : Order) :
    Admits (Licensed List.head? {NP}) o.phrases ↔ o = .dpFirst := by
  cases o <;> decide

/-- The closeness accounts admit the clause first in the embedded position, (10a). -/
theorem closeness_embedded_iff (o : Order) :
    Admits (Licensed (leftToRight embeddedPosition) {NP}) o.phrases ↔ o = .cpFirst := by
  cases o <;> decide

/-- The accounts diverge in the embedded position only, which is what makes German the test
case, since in the root position the linear account checks the first conjunct too. -/
theorem accounts_diverge_embedded :
    (∃ o : Order, ¬ (Admits (Licensed List.head? {NP}) o.phrases ↔
        Admits (Licensed (leftToRight embeddedPosition) {NP}) o.phrases)) ∧
      leftToRight (α := Conjunct) rootPosition = List.head? :=
  ⟨⟨.dpFirst, by decide⟩, funext leftToRight_headInitial⟩

/-- A noun phrase first in the embedded position refutes the linear and temporal closeness
accounts, whatever the reason for the preference. -/
theorem closeness_rejects_dpFirst :
    ¬ Admits (Licensed (leftToRight embeddedPosition) {NP}) Order.dpFirst.phrases ∧
      ¬ Admits (Licensed (closestInTime embeddedPosition) {NP}) Order.dpFirst.phrases := by
  rw [closestInTime_eq_leftToRight]
  exact ⟨by decide, by decide⟩

/-! ### The predicates -/

/-- The fragment entry of a predicate named in a row. -/
def entryOf (form : String) : Option German.Verb :=
  German.Verbs.allVerbs.find? (·.form = form)

/-- The four predicates of Experiment 1 that select a *dass*-clause. -/
def selecting : List German.Verb :=
  [German.Verbs.veranlassen, German.Verbs.vergessen, German.Verbs.erwarten,
    German.Verbs.beschliessen]

/-- The four predicates of Experiment 1 that do not. -/
def nonSelecting : List German.Verb :=
  [German.Verbs.beenden, German.Verbs.streichen, German.Verbs.uebereilen, German.Verbs.entwickeln]

/-- All eight predicates take a noun phrase, and only the selecting four a clause. -/
theorem selection_of_entries :
    (∀ v ∈ selecting ++ nonSelecting, v.toVerb.TakesNominal) ∧
      (∀ v ∈ selecting, v.toVerb.TakesClausal) ∧ ∀ v ∈ nonSelecting, ¬ v.toVerb.TakesClausal := by
  decide

/-- Every row names a predicate with a fragment entry. -/
theorem rows_have_entries : ∀ e ∈ Examples.all, ((e.feature? "verb").bind entryOf).isSome := by
  decide

/-- Each row's selection value is that of its predicate's entry. -/
theorem rows_selectsCP :
    ∀ e ∈ Examples.all, ∀ v ∈ (e.feature? "verb").bind entryOf,
      (e.feature? "selectsCP" = some "yes" ↔ v.toVerb.TakesClausal) := by
  decide

/-- A bare *dass*-clause is acceptable exactly after a predicate that takes a clause, (11a) and
(12a). -/
theorem dass_rows :
    ∀ e ∈ Examples.all, e.feature? "complement" = some "dass" →
      ∀ v ∈ (e.feature? "verb").bind entryOf,
        (e.judgment = .acceptable ↔ v.toVerb.TakesClausal) := by
  decide

/-! ### The experiments -/

/-- Selection raises the mean rating of both complements. -/
theorem selection_raises (c : Complement) :
    (ratings c .no).meanZ.toRat < (ratings c .yes).meanZ.toRat := by
  cases c <;> decide +kernel

/-- In the interaction of Experiment 1 a coordination gains less from selection than a bare
*dass*-clause, so that after a verb that does not select a clause it is rated above the bare
clause. -/
theorem selection_interaction :
    (ratings .coord .yes).meanZ.toRat - (ratings .coord .no).meanZ.toRat <
      (ratings .dass .yes).meanZ.toRat - (ratings .dass .no).meanZ.toRat ∧
    (ratings .dass .no).meanZ.toRat < (ratings .coord .no).meanZ.toRat := by
  decide +kernel

/-- The head direction of a position of Experiment 2. -/
def Position.direction : Position → HeadDirection
  | .preverbal => embeddedPosition
  | .postverbal => rootPosition

/-- The order chosen more often in a position of Experiment 2. -/
def preferred (p : Position) : Order :=
  if (choices p .cpFirst).count < (choices p .dpFirst).count then .dpFirst else .cpFirst

/-- The noun phrase first is preferred in both positions. -/
theorem preferred_eq (p : Position) : preferred p = .dpFirst := by
  cases p <;> decide

/-- Experiment 2 refutes the linear and temporal closeness accounts. -/
theorem choices_refute_closeness :
    ¬ Admits (Licensed (leftToRight Position.preverbal.direction) {NP})
        (preferred .preverbal).phrases ∧
      ¬ Admits (Licensed (closestInTime Position.preverbal.direction) {NP})
        (preferred .preverbal).phrases := by
  rw [preferred_eq]
  exact closeness_rejects_dpFirst

/-- The structural account admits exactly the preferred order in both positions. -/
theorem choices_match_structural (p : Position) (o : Order) :
    Admits (Licensed List.head? {NP}) o.phrases ↔ o = preferred p := by
  rw [preferred_eq, structural_admits_iff]

end Schwarzer2026
