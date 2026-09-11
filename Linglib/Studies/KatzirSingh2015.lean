import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Katzir and Singh (2015): Economy of Structure and Information

This file formalizes the two felicity conditions of [katzir-singh-2015] for the oddness of
assertions such as *Some Italians come from a warm country* ([magri-2009]) and *John has one
wife* ([spector-2014]). The question condition (8) asks that an assertion address a good
question, one the participants are known to want settled; the answer condition (15) asks that
it be a true, relevant answer that is not needlessly worse than another true relevant one, an
alternative being better (16) when it is at most as complex, in the structural sense of
[katzir-2007], and at least as strong. `Scenario` collects the meanings and complexities of the
alternatives, the context, and the question, and `Felicitous` is the conjunction of the two
conditions at a world.

Being better is a strict order (`Scenario.better_trans`), a true relevant alternative of no
greater complexity that is strictly stronger makes an answer needlessly weak
(`Scenario.not_goodAnswer_of_stronger`), the mechanism behind the *some*/*all* cases of (17)
and (18) and behind [heim-1991]'s Maximize Presupposition in (21), and disjoining a stronger or
conjoining a weaker constituent makes an answer needlessly complex
(`Scenario.not_goodAnswer_disj`, `Scenario.not_goodAnswer_conj`), the Hurford constraint of (22)
and (23). The paper's scenarios then decide: the one-answer question of (1) makes *some* and
*all* alike odd, the open question of (17) leaves *all* good and *some* odd where all holds, the
downward-entailing (18) reverses the verdict, the common-knowledge context of (19) leaves the
question formed by the alternatives with one live answer while the explicit question of (20)
does not, and (21) and (22) fall to the answer condition.

## Implementation notes

A question is a family of answers, the alternatives of the assertion when no question is
explicit, and it is settled in a context when its live answers there coincide, the use the
paper makes of the good question of (7); an assertion is relevant when it does not split a cell
of the partition the answers induce (the paper's footnote 8). Complexity enters as a rank, the
structural order not being rebuilt on trees. Meanings are sets of worlds, with presupposition
folded into truth for (21). The embedded cases of Section 4, which the paper leaves open, are
not represented.

## References

* [katzir-singh-2015]
* [magri-2009], [spector-2014], [heim-1991], [hurford-1974], [katzir-2007]
-/

namespace KatzirSingh2015

/-- A discourse situation: the meanings of the alternatives and their structural complexity,
the context, and the question, a family of answers. -/
structure Scenario (W U A : Type*) where
  meaning : U → Set W
  complexity : U → ℕ
  context : Set W
  question : A → Set W

namespace Scenario

variable {W U A : Type*} (s : Scenario W U A)

/-- The question is settled in the context: its live answers there coincide. -/
def Settled : Prop :=
  ∀ a b : A, (∃ w ∈ s.context, w ∈ s.question a) → (∃ w ∈ s.context, w ∈ s.question b) →
    ∀ w ∈ s.context, (w ∈ s.question a ↔ w ∈ s.question b)

/-- Relevant to the question: within the context, the assertion does not split a cell of the
partition the answers induce. -/
def Relevant (u : U) : Prop :=
  ∀ w ∈ s.context, ∀ v ∈ s.context,
    (∀ a, w ∈ s.question a ↔ v ∈ s.question a) → (w ∈ s.meaning u ↔ v ∈ s.meaning u)

/-- (16a): at least as good, at most as complex and at least as strong. -/
def AtLeastAsGood (u v : U) : Prop :=
  s.complexity u ≤ s.complexity v ∧ s.meaning u ⊆ s.meaning v

/-- (16b): strictly better. -/
def Better (u v : U) : Prop := s.AtLeastAsGood u v ∧ ¬ s.AtLeastAsGood v u

/-- (15): a good answer at `w` is true, relevant, and not needlessly worse than a true relevant
alternative. -/
def GoodAnswer (u : U) (w : W) : Prop :=
  w ∈ s.meaning u ∧ s.Relevant u ∧ ¬ ∃ v, s.Better v u ∧ w ∈ s.meaning v ∧ s.Relevant v

/-- Felicitous at `w`: the question is not settled, (8), and the assertion is a good answer,
(15). -/
def Felicitous (u : U) (w : W) : Prop := ¬ s.Settled ∧ s.GoodAnswer u w

section Decidable

variable [Fintype W] [Fintype U] [Fintype A] [∀ u, DecidablePred (· ∈ s.meaning u)]
  [DecidablePred (· ∈ s.context)] [∀ a, DecidablePred (· ∈ s.question a)]

instance : Decidable s.Settled := inferInstanceAs (Decidable (∀ _ _, _ → _ → ∀ _ ∈ _, _))

instance (u : U) : Decidable (s.Relevant u) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, ∀ _ ∈ _, _ → _))

instance (u v : U) : Decidable (s.AtLeastAsGood u v) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _ → _))

instance (u v : U) : Decidable (s.Better u v) := inferInstanceAs (Decidable (_ ∧ ¬ _))

instance (u : U) (w : W) : Decidable (s.GoodAnswer u w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ¬ ∃ _, _))

instance (u : U) (w : W) : Decidable (s.Felicitous u w) := inferInstanceAs (Decidable (¬ _ ∧ _))

end Decidable

variable {u v x : U}

theorem atLeastAsGood_refl (u : U) : s.AtLeastAsGood u u := ⟨le_rfl, subset_rfl⟩

theorem atLeastAsGood_trans (h : s.AtLeastAsGood u v) (h' : s.AtLeastAsGood v x) :
    s.AtLeastAsGood u x :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

theorem better_irrefl (u : U) : ¬ s.Better u u := λ h => h.2 (s.atLeastAsGood_refl u)

theorem better_asymm (h : s.Better u v) : ¬ s.Better v u := λ h' => h.2 h'.1

/-- Better-than is a strict order, the irreflexive part of the at-least-as-good preorder. -/
theorem better_trans (h : s.Better u v) (h' : s.Better v x) : s.Better u x :=
  ⟨s.atLeastAsGood_trans h.1 h'.1, λ hx => h.2 (s.atLeastAsGood_trans h'.1 hx)⟩

/-- A needlessly weak answer: a true relevant alternative of no greater complexity that is
strictly stronger is better, so the answer is not good. -/
theorem not_goodAnswer_of_stronger {w : W} (hc : s.complexity v ≤ s.complexity u)
    (hs : s.meaning v ⊂ s.meaning u) (hw : w ∈ s.meaning v) (hr : s.Relevant v) :
    ¬ s.GoodAnswer u w :=
  λ h => h.2.2 ⟨v, ⟨⟨hc, hs.1⟩, λ h' => hs.2 h'.2⟩, hw, hr⟩

/-- A needlessly complex answer, (22): a disjunction whose second disjunct entails the first
says what the first does at greater complexity, so it is not a good answer where the first
disjunct is a true relevant one. -/
theorem not_goodAnswer_disj {d φ ψ : U} {w : W} (hd : s.meaning d = s.meaning φ ∪ s.meaning ψ)
    (hψ : s.meaning ψ ⊆ s.meaning φ) (hc : s.complexity φ < s.complexity d)
    (hw : w ∈ s.meaning φ) (hr : s.Relevant φ) : ¬ s.GoodAnswer d w := by
  have heq : s.meaning d = s.meaning φ := by rw [hd, Set.union_eq_left.mpr hψ]
  exact λ h => h.2.2 ⟨φ, ⟨⟨hc.le, by rw [heq]⟩, λ h' => absurd h'.1 (not_le.mpr hc)⟩, hw, hr⟩

/-- Likewise a conjunction whose second conjunct is entailed by the first, (23). -/
theorem not_goodAnswer_conj {c φ ψ : U} {w : W} (hc' : s.meaning c = s.meaning φ ∩ s.meaning ψ)
    (hψ : s.meaning φ ⊆ s.meaning ψ) (hc : s.complexity φ < s.complexity c)
    (hw : w ∈ s.meaning φ) (hr : s.Relevant φ) : ¬ s.GoodAnswer c w := by
  have heq : s.meaning c = s.meaning φ := by rw [hc', Set.inter_eq_left.mpr hψ]
  exact λ h => h.2.2 ⟨φ, ⟨⟨hc.le, by rw [heq]⟩, λ h' => absurd h'.1 (not_le.mpr hc)⟩, hw, hr⟩

end Scenario

/-! ### Some and all (Sections 1 and 3.2)

The *some* and *all* alternatives over the three ways a set of grades, names or origins can
fall: to all, to some but not all, or to none. -/

/-- Whether the property holds of all, of some but not all, or of none. -/
inductive Share
  | all | someNotAll | none
  deriving DecidableEq, Repr, Fintype

/-- The scalar alternatives. -/
inductive Scalar
  | some_ | all_
  deriving DecidableEq, Repr, Fintype

/-- *Some* is true unless of none, *all* only of all. -/
def scalarDenotes : Scalar → Share → Prop
  | .some_, w => w ≠ .none
  | .all_, w => w = .all

instance : ∀ u w, Decidable (scalarDenotes u w) := λ u w => by
  cases u <;> unfold scalarDenotes <;> infer_instance

/-- The scalar scenario, the alternatives forming the question: a context, and the same
complexity for both. -/
abbrev scalar (context : Set Share) : Scenario Share Scalar Scalar where
  meaning u := {w | scalarDenotes u w}
  complexity _ := 1
  context := context
  question u := {w | scalarDenotes u w}

/-- (1) and (19): where the context makes *some* and *all* equivalent, as common knowledge that
Italy is warm or that every father names all his children alike does, the question they form
has one live answer and both are odd. -/
theorem some_all_odd_of_settled :
    (scalar {w | w ≠ .someNotAll}).Settled ∧
      ∀ u w, ¬ (scalar {w | w ≠ .someNotAll}).Felicitous u w := by
  decide

/-- (17): where the equivalence is the speaker's belief rather than common knowledge, the
question is open, and where the property holds of all *all* is a good answer while *some* is
needlessly weak. -/
theorem all_felicitous_some_odd :
    (scalar Set.univ).Felicitous .all_ .all ∧ ¬ (scalar Set.univ).Felicitous .some_ .all := by
  decide

/-- (20): the explicit question *to how many?* is not settled by the common knowledge of (19),
and *all* becomes a good answer while *some* stays needlessly weak. -/
abbrev explicit : Scenario Share Scalar Share where
  meaning u := {w | scalarDenotes u w}
  complexity _ := 1
  context := {w | w ≠ .someNotAll}
  question a := {a}

theorem explicit_question_rescues_all :
    ¬ explicit.Settled ∧ explicit.Felicitous .all_ .all ∧ ¬ explicit.Felicitous .some_ .all := by
  decide

/-- (18): under a downward-entailing operator the entailment reverses, *some* being the
stronger, and it is *all* that is needlessly weak. -/
def restrictorDenotes : Scalar → Share → Prop
  | .some_, w => w = .all
  | .all_, w => w ≠ .none

instance : ∀ u w, Decidable (restrictorDenotes u w) := λ u w => by
  cases u <;> unfold restrictorDenotes <;> infer_instance

/-- The scenario of (18): every professor who assigned an A to some/all of his students got a
raise, over how many of the A-givers got one. -/
abbrev restrictor : Scenario Share Scalar Scalar where
  meaning u := {w | restrictorDenotes u w}
  complexity _ := 1
  context := Set.univ
  question u := {w | restrictorDenotes u w}

theorem some_felicitous_all_odd :
    restrictor.Felicitous .some_ .all ∧ ¬ restrictor.Felicitous .all_ .all := by
  decide

/-! ### Maximize Presupposition (Section 3.2.3) -/

/-- How many suns there are and whether one shines. -/
inductive Sky
  | oneShining | oneDark | many
  deriving DecidableEq, Repr, Fintype

/-- *A sun is shining* and *the sun is shining*. -/
inductive Article
  | a | the
  deriving DecidableEq, Repr, Fintype

/-- The definite carries the uniqueness presupposition into its truth conditions. -/
def articleDenotes : Article → Sky → Prop
  | .a, w => w ≠ .oneDark
  | .the, w => w = .oneShining

instance : ∀ u w, Decidable (articleDenotes u w) := λ u w => by
  cases u <;> unfold articleDenotes <;> infer_instance

/-- (21) with common knowledge of one sun, the question being whether it shines. -/
abbrev sun : Scenario Sky Article Bool where
  meaning u := {w | articleDenotes u w}
  complexity _ := 1
  context := {w | w ≠ .many}
  question b := {w | decide (w = .oneShining) = b}

/-- Maximize Presupposition as an instance of the answer condition: the definite is the better
answer and the indefinite needlessly weak. -/
theorem the_felicitous_a_odd :
    sun.Felicitous .the .oneShining ∧ ¬ sun.Felicitous .a .oneShining := by
  decide

/-! ### Hurford disjunctions (Section 3.3) -/

/-- Where John went. -/
inductive Trip
  | paris | franceNotParis | elsewhere
  deriving DecidableEq, Repr, Fintype

/-- *John visited France*, and the disjunction (22) with *Paris*. -/
inductive Visit
  | france | franceOrParis
  deriving DecidableEq, Repr, Fintype

def visitDenotes : Visit → Trip → Prop
  | .france, w => w ≠ .elsewhere
  | .franceOrParis, w => w ≠ .elsewhere

instance : ∀ u w, Decidable (visitDenotes u w) := λ u w => by
  cases u <;> unfold visitDenotes <;> infer_instance

/-- (22): the disjunction is more complex than its first disjunct, and the question is where
John went. -/
abbrev hurford : Scenario Trip Visit Trip where
  meaning u := {w | visitDenotes u w}
  complexity | .france => 1 | .franceOrParis => 2
  context := Set.univ
  question a := {a}

/-- *France or Paris* is a needlessly complex answer wherever *France* is true. -/
theorem hurford_odd : ∀ w, ¬ hurford.Felicitous .franceOrParis w := by decide

/-- *France* is a good answer where true. -/
theorem france_felicitous : hurford.Felicitous .france .paris := by decide

end KatzirSingh2015
