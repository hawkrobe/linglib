import Mathlib.Data.Fintype.Powerset
import Linglib.Pragmatics.NeoGricean.Basic
import Linglib.Studies.GoodmanStuhlmuller2013
import Linglib.Data.Examples.BaleEtAl2025

/-!
# Bale, Noguchi, Rolland & Barner 2025: competence by default

A strong scalar implicature needs more than the weak one: from *some* the hearer infers that
the speaker does not know that *all* holds, and only with competence — the speaker knows
whether *all* holds — does this become knowledge that *all* is false. Two hypotheses about
competence are tested. Under competence by default the hearer assumes it and cancels it when
the speaker's contextual knowledge state contradicts it; under contextual licensing it is
adopted only when the context supplies it. Farmer Brown opens two of three boxes, both with
red cubes, looks or does not look into the third, and says that some or all of the boxes have
red cubes; the participant is asked whether the third box has red cubes. Integrating the
speaker's state, the two hypotheses give the same answers — yes after *all*, no after *some*
from a speaker who looked, don't know after *some* from one who did not. They come apart only
when integration fails: a hearer who keeps the default derives the strong implicature from an
ignorant speaker, and participants under cognitive load answered no to the ignorant speaker's
*some* more than twice as often as those without load, while the knowledgeable speaker's
*some* showed only the usual small reduction.

## Main definitions

* `speakerState`: what Farmer Brown knows after looking into `a` boxes, in each world.
* `uttered`: Quality and the weak implicatures of the stronger scalar alternatives.
* `integrated`, `unintegrated`: the hearer's worlds with and without the speaker's contextual
  knowledge state.
* `contextual`, `competenceDefault`, `competenceDefaultLoad`: the two hypotheses, and the
  default with integration blocked.
* `competent_iff_looked`: the speaker is competent about *all* exactly when he looked into
  the third box.
* `rows_expected`: the expected response in each trial type is the contextual-licensing
  answer.
* `competenceDefault_eq_contextual`: with integration the default is cancelled exactly where
  the context contradicts it, so the two hypotheses agree.
* `load_diverges`, `load_agrees_of_knowledgeable`: without integration the default yields the
  strong implicature from the ignorant speaker and nothing new from the knowledgeable one.

## References

* [bale-etal-2025]
* [geurts-2010] — competence by default
* [soames-1982], [horn-1989] — contextual licensing and the stepwise recipe
* [vanrooij-schulz-2004] — competence assumed whenever consistent
* [goodman-stuhlmuller-2013] — the observation states
-/

namespace BaleEtAl2025

open Data.Examples GoodmanStuhlmuller2013 NeoGricean Set

/-! ### Worlds, evidence and knowledge states -/

/-- The proposition a quantified statement about the three boxes expresses. -/
def prop (q : QUtt) : Set WorldState := {w | qMeaning q w}

instance (q : QUtt) : DecidablePred (· ∈ prop q) :=
  λ w => inferInstanceAs (Decidable (qMeaning q w))

/-- *All of the boxes have red cubes* — the alternative, and the question asked. -/
abbrev all : Set WorldState := prop .all

/-- What the participant sees: boxes 1 and 2 have red cubes. -/
def seen : Set WorldState := {w | 2 ≤ w.toNat}

instance : DecidablePred (· ∈ seen) := λ w => inferInstanceAs (Decidable (2 ≤ w.toNat))

/-- What Farmer Brown knows in world `w` after looking into `a` boxes, boxes 1 and 2 among
    them: the worlds compatible with the red cubes he saw. -/
def speakerState (a : Access) (w : WorldState) : Set WorldState :=
  {v | obsCompatible a ⟨min a.val w.toNat, Nat.lt_succ_of_le (Nat.min_le_left ..)⟩ v}

instance (a : Access) (w : WorldState) : DecidablePred (· ∈ speakerState a w) :=
  λ v => inferInstanceAs (Decidable (obsCompatible a _ v))

instance (S T : Set WorldState) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] :
    Decidable (S ⊆ T) :=
  decidable_of_iff (∀ w, w ∈ S → w ∈ T) Iff.rfl

instance (S T : Set WorldState) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] :
    Decidable (S ⊂ T) :=
  decidable_of_iff (S ⊆ T ∧ ¬ T ⊆ S) Iff.rfl

instance (S T : Set WorldState) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] :
    Decidable (S = T) :=
  decidable_of_iff (∀ w, w ∈ S ↔ w ∈ T) Set.ext_iff.symm

instance (S : Finset WorldState) : DecidablePred (· ∈ (↑S : Set WorldState)) :=
  λ w => decidable_of_iff (w ∈ S) Finset.mem_coe.symm

instance (S : Set WorldState) [DecidablePred (· ∈ S)] : Decidable (S ∈ competent all) :=
  decidable_of_iff (S ⊆ all ∨ S ⊆ allᶜ) Iff.rfl

/-- The speaker is competent about *all* exactly when he looked into the third box. -/
theorem competent_iff_looked (a : Access) (w : WorldState) (hw : w ∈ seen) :
    speakerState a w ∈ competent all ↔ a = Access.a3 := by
  revert a w; decide

/-! ### The recipe and its integration with context -/

/-- Quality and the weak implicatures of the stronger scalar alternatives: the speaker knows
    the statement and does not know any stronger one. -/
def uttered (q : QUtt) : Set (Set WorldState) :=
  {S | S ⊆ prop q ∧ ∀ q', prop q' ⊂ prop q → S ∈ primaryImplicature (prop q')}

instance (S : Set WorldState) [DecidablePred (· ∈ S)] (q : QUtt) : Decidable (S ∈ uttered q) :=
  decidable_of_iff (S ⊆ prop q ∧ ∀ q', prop q' ⊂ prop q → ¬ S ⊆ prop q') Iff.rfl

/-- The hearer's worlds with the speaker's contextual knowledge state integrated: the worlds
    in which what the speaker saw satisfies the epistemic constraints. -/
def integrated (a : Access) (E : Set (Set WorldState)) : Set WorldState :=
  {w ∈ seen | speakerState a w ∈ E}

instance (a : Access) (E : Set (Set WorldState)) [∀ w, Decidable (speakerState a w ∈ E)] :
    DecidablePred (· ∈ integrated a E) :=
  λ w => inferInstanceAs (Decidable (w ∈ seen ∧ speakerState a w ∈ E))

/-- The hearer's worlds without that integration: the worlds some knowledge state satisfying
    the constraints contains, knowledge being factive. -/
def unintegrated (E : Set (Set WorldState)) : Set WorldState :=
  {w ∈ seen | ∃ S : Finset WorldState, (↑S : Set WorldState) ∈ E ∧ w ∈ S}

instance (E : Set (Set WorldState))
    [∀ S : Finset WorldState, Decidable ((↑S : Set WorldState) ∈ E)] :
    DecidablePred (· ∈ unintegrated E) :=
  λ w => inferInstanceAs
    (Decidable (w ∈ seen ∧ ∃ S : Finset WorldState, (↑S : Set WorldState) ∈ E ∧ w ∈ S))

/-! ### The two hypotheses -/

/-- Contextual licensing: competence only as the speaker's contextual knowledge state
    supplies it. -/
def contextual (a : Access) (q : QUtt) : Set WorldState := integrated a (uttered q)

instance (a : Access) (q : QUtt) : DecidablePred (· ∈ contextual a q) :=
  λ w => inferInstanceAs (Decidable (w ∈ integrated a (uttered q)))

/-- Competence by default with integration: the default is kept where the speaker's contextual
    state bears it out and cancelled where that state contradicts it everywhere. -/
def competenceDefault (a : Access) (q : QUtt) : Set WorldState :=
  {w | w ∈ integrated a (uttered q ∩ competent all) ∨
    ((∀ w', w' ∉ integrated a (uttered q ∩ competent all)) ∧ w ∈ contextual a q)}

instance (a : Access) (q : QUtt) : DecidablePred (· ∈ competenceDefault a q) :=
  λ w => inferInstanceAs (Decidable (w ∈ integrated a (uttered q ∩ competent all) ∨
    ((∀ w', w' ∉ integrated a (uttered q ∩ competent all)) ∧ w ∈ contextual a q)))

/-- The default with integration blocked, as under cognitive load. -/
def competenceDefaultLoad (q : QUtt) : Set WorldState :=
  unintegrated (uttered q ∩ competent all)

instance (q : QUtt) : DecidablePred (· ∈ competenceDefaultLoad q) :=
  λ w => inferInstanceAs (Decidable (w ∈ unintegrated (uttered q ∩ competent all)))

/-- The participant's response to *Do you think there are red cubes in this box?* -/
inductive Answer
  | yes
  | no
  | dontKnow
  deriving DecidableEq, Repr

/-- The answer the remaining worlds support: yes if the third box has red cubes in all of
    them, no if in none. -/
def answer (worlds : Set WorldState) [DecidablePred (· ∈ worlds)] : Answer :=
  if worlds ⊆ all then .yes else if worlds ⊆ allᶜ then .no else .dontKnow

/-- With integration the default is cancelled exactly where the context contradicts it, so
    the two hypotheses agree. -/
theorem competenceDefault_eq_contextual (a : Access) (q : QUtt) :
    competenceDefault a q = contextual a q := by
  revert a q; decide

/-- Without integration the default yields the strong implicature from the ignorant speaker,
    where contextual licensing leaves the third box open. -/
theorem load_diverges :
    answer (competenceDefaultLoad .some_) = .no ∧
      answer (contextual Access.a2 .some_) = .dontKnow := by
  decide

/-- For the knowledgeable speaker the blocked default changes nothing. -/
theorem load_agrees_of_knowledgeable (q : QUtt) :
    answer (competenceDefaultLoad q) = answer (contextual Access.a3 q) := by
  revert q; decide

/-! ### The trial types -/

/-- How many boxes Farmer Brown looked into. -/
def access? (r : LinguisticExample) : Option Access :=
  match r.feature? "boxesSeen" with
  | some "2" => some Access.a2
  | some "3" => some Access.a3
  | _ => none

/-- The quantifier of his statement. -/
def quantifier? (r : LinguisticExample) : Option QUtt :=
  match r.feature? "quantifier" with
  | some "some" => some .some_
  | some "all" => some .all
  | _ => none

/-- The response the paper expects. -/
def expected? (r : LinguisticExample) : Option Answer :=
  match r.feature? "expectedResponse" with
  | some "yes" => some .yes
  | some "no" => some .no
  | some "dontKnow" => some .dontKnow
  | _ => none

/-- The expected response in each trial type is the contextual-licensing answer. -/
theorem rows_expected :
    ∀ r ∈ Examples.all, ∀ a ∈ access? r, ∀ q ∈ quantifier? r, ∀ e ∈ expected? r,
      answer (contextual a q) = e := by
  decide

end BaleEtAl2025
