import Linglib.Semantics.Attitudes.Desire.QuestionBased
import Linglib.Semantics.Attitudes.Desire.Conditional
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset

/-!
# Phillips-Brown (2025): Some-Things-Considered Desire

This file formalizes the question-based semantics of desire ascriptions of
[phillips-brown-2025]. Conflicting ascriptions, *you want to take a nap* and *you don't want to
take a nap* both true, falsify the belief-based semantics of [heim-1992] and [von-fintel-1999],
which evaluate the agent's preferences over her whole belief set with no context sensitivity
(§2.1) (`vonFintel_no_conflict`, `heim_no_conflict`); a context-sensitive preference relation
predicts them but, valuing whole worlds, predicts *you want to fail the exam* wherever *Nap* is
true (§2.2), an instance of the closure under doxastic equivalence of [villalta-2008] (§4.1)
(`closure_under_doxastic_equivalence`, `cpr_overgenerates`). The proposal evaluates an
ascription against a contextual question (§3): the answers compatible with the beliefs are
ranked by the desires they entail, *S wants p* holds when every best answer entails *p*, and the
ascription is defined only if *p* is considered relative to the question (§3.6), the question
is diverse and does not stack the deck (§3.7), and the beliefs are sensitive to it (§4.2).
*Nap* is true considering whether one naps and whether one feels rested, *Not-nap* considering
whether one naps and whether one passes, and in the former context *Fail* is undefined, the
outcome of the exam being ignored (`act_true`, `not_act_true`, `cost_undefined`); the lobster
case, *Lobster*, *Not-lobster* and *Die*, is the same model. The deck-stacked question of Lu's
case would make *Lu wants it not to rain* true and is excluded by the anti-deckstacking
constraint, which the level playing field satisfies (`not_rain_deckstacked`,
`deckstacked_excluded`); an agent whose beliefs are insensitive to every question that
considers *p*, William III and nuclear war, has *S wants p* undefined in every context
(`undefined_of_insensitive`), which leaves the semantics Strawson upward monotone
(`Desire.QuestionBased.toPartialProp_strawsonEntails`).

## Implementation notes

The act, its benefit and its cost are the three issues of the nap and lobster cases (nap,
feeling rested, failing the exam; eating the lobster, the gustatory experience, dying), the
beliefs tying benefit and cost to the act, and the desires being the benefit and not the cost;
a question is a list of answers, the question raised by a list of issues being the nonempty
cells of their joint partition. The Anti-deckstacking Constraint quantifies over all
propositions; read so, it admits only questions whose answers are singletons
(`antiDeckstacking_univ_singleton`), so the substrate restricts it to a list of salient
propositions, here the issues of each case. Heim's semantics is the conditional one of
`Desire/Conditional`, and the diversity constraint's role, blocking vacuous truth and falsity,
is `Desire.QuestionBased.not_want_of_not_exists` and `want_of_isConsidered_of_not_exists`.
Levinson's expected-value comparison, the sufficient-desirability semantics of §2.4, the Heimian
question-based semantics of footnote 16, and the finest-question simulation of §3.4
(`Desire.QuestionBased.want_finest_iff`) are prose.

## References

* [phillips-brown-2025]
* [heim-1992]
* [von-fintel-1999]
* [villalta-2008]
* [yalcin-2018]
-/

namespace PhillipsBrown2025

open Desire Desire.QuestionBased

/-! ### The nap and lobster cases (§2.1, §2.2) -/

/-- A state: whether the act is done, whether its benefit obtains, whether its cost obtains. -/
structure World where
  act : Bool
  benefit : Bool
  cost : Bool
  deriving DecidableEq

instance : Fintype World :=
  Fintype.ofEquiv (Bool × Bool × Bool)
    ⟨λ p => ⟨p.1, p.2.1, p.2.2⟩, λ w => (w.act, w.benefit, w.cost), λ _ => rfl, λ _ => rfl⟩

/-- The act: napping, eating the lobster. -/
def act : Finset World := Finset.univ.filter (·.act)

/-- Its benefit: feeling rested, the gustatory experience. -/
def benefit : Finset World := Finset.univ.filter (·.benefit)

/-- Its cost: failing the exam, dying of anaphylactic shock. -/
def cost : Finset World := Finset.univ.filter (·.cost)

/-- The beliefs: the benefit and the cost each come exactly with the act. -/
def bel : Set World := {w | w.benefit = w.act ∧ w.cost = w.act}

instance : DecidablePred (· ∈ bel) :=
  λ w => inferInstanceAs (Decidable (w.benefit = w.act ∧ w.cost = w.act))

/-- The desires: the benefit, and not the cost. -/
def desires : List (Finset World) := [benefit, costᶜ]

/-- Von Fintel's semantics cannot make *Nap* and *Not-nap* both true, whatever the desires:
some belief-world is best, and it settles the act one way. -/
theorem vonFintel_no_conflict (G : List (Finset World)) :
    ¬ (BestWorlds.Want G bel ↑act ∧ BestWorlds.Want G bel (↑act : Set World)ᶜ) :=
  λ ⟨h, h'⟩ => h.not_compl ⟨⟨true, true, true⟩, by decide⟩ h'

/-- Neither can Heim's, under her definedness amendment and antisymmetric desirability. -/
theorem heim_no_conflict (F : Conditional.Frame World) (w : World) [Std.Antisymm (F.pref w)]
    (hd : Conditional.Defined bel ↑act) :
    ¬ (Conditional.Want F bel w ↑act ∧ Conditional.Want F bel w (↑act : Set World)ᶜ) :=
  λ ⟨h, h'⟩ => h.not_compl hd h'

/-- Closure under doxastic equivalence (§4.1): on a belief-based semantics, the cost being
believed to come exactly with the act, wanting the act is wanting the cost, *Nap* entailing
*Fail*. -/
theorem closure_under_doxastic_equivalence (G : List (Finset World))
    (h : BestWorlds.Want G bel ↑act) : BestWorlds.Want G bel ↑cost :=
  h.mono_on (by decide +kernel)

/-- A context-sensitive preference relation overgenerates (§2.2): the value of feeling rested
makes *Nap* true, and with it *Fail*. -/
theorem cpr_overgenerates :
    BestWorlds.Want [benefit] bel ↑act ∧ BestWorlds.Want [benefit] bel ↑cost :=
  ⟨by decide, closure_under_doxastic_equivalence _ (by decide +kernel)⟩

/-! ### Some-things-considered desire (§3) -/

/-- The question considering whether the act is done and whether its benefit obtains
(Figure 3). -/
def qBenefit : List (Finset World) := ofIssues [act, benefit]

/-- The question considering whether the act is done and whether its cost obtains
(Figure 5). -/
def qCost : List (Finset World) := ofIssues [act, cost]

/-- The salient propositions of the case, the test set of the anti-deckstacking constraint. -/
def issues : List (Finset World) := [act, benefit, cost]

/-- *Nap*, *Lobster*: considering the act and its benefit, the ascription is defined and true. -/
theorem act_true : Defined issues qBenefit bel ↑act ∧ Want desires qBenefit bel ↑act := by
  decide +kernel

/-- *Fail*, *Die*: in that context the cost is ignored, so the ascription is undefined
(§3.6), which blocks the inference from *Nap* to *Fail* (§4.1). -/
theorem cost_undefined : ¬ IsConsidered qBenefit ↑cost := by decide

/-- *Not-nap*, *Not-lobster*: considering the act and its cost, not doing the act is wanted,
and so is avoiding the cost, *Not-die*. -/
theorem not_act_true :
    Defined issues qCost bel (↑act : Set World)ᶜ ∧ Want desires qCost bel (↑act : Set World)ᶜ ∧
      Want desires qCost bel (↑cost : Set World)ᶜ := by
  decide +kernel

/-! ### Deck-stacking (§3.7) -/

/-- A state of Lu's case: whether it rains, whether Lu is happy. -/
structure LuWorld where
  rain : Bool
  happy : Bool
  deriving DecidableEq

instance : Fintype LuWorld :=
  Fintype.ofEquiv (Bool × Bool)
    ⟨λ p => ⟨p.1, p.2⟩, λ w => (w.rain, w.happy), λ _ => rfl, λ _ => rfl⟩

/-- It rains tomorrow. -/
def rain : Finset LuWorld := Finset.univ.filter (·.rain)

/-- Lu is happy tomorrow. -/
def happy : Finset LuWorld := Finset.univ.filter (·.happy)

/-- Lu's beliefs: happy whatever the weather. -/
def belLu : Set LuWorld := {w | w.happy = true}

instance : DecidablePred (· ∈ belLu) := λ w => inferInstanceAs (Decidable (w.happy = true))

/-- The deck-stacked question (Figure 7): whether it rains, and if not, whether Lu is happy. -/
def qStacked : List (Finset LuWorld) := [rain, rainᶜ ∩ happy, rainᶜ \ happy]

/-- The level playing field (Figure 9). -/
def qFair : List (Finset LuWorld) := ofIssues [rain, happy]

/-- Without the constraint the deck-stacked question makes *Lu wants it not to rain* true,
though Lu is indifferent to the weather; the level playing field makes it false. -/
theorem not_rain_deckstacked :
    Want [happy] qStacked belLu (↑rain : Set LuWorld)ᶜ ∧
      ¬ Want [happy] qFair belLu (↑rain : Set LuWorld)ᶜ := by
  decide +kernel

/-- The deck-stacked question violates the constraint at *happy*, which one answer entails and
another leaves open, while the level playing field satisfies it for every proposition. -/
theorem deckstacked_excluded :
    ¬ IsAntiDeckstacking [happy] qStacked ∧
      ∀ q : Finset LuWorld, (∃ a ∈ qFair, a ⊆ q) → IsConsidered qFair ↑q := by
  decide +kernel

/-- Read with `q` ranging over all propositions, the Anti-deckstacking Constraint admits, among
questions with two disjoint answers, only those whose answers are singletons: with two states
in an answer, the union of another answer with one of them is entailed by an answer and settled
by none. -/
theorem antiDeckstacking_univ_singleton {W : Type*} [DecidableEq W] {Q : List (Finset W)}
    (h : ∀ q : Finset W, (∃ a ∈ Q, a ⊆ q) → IsConsidered Q (↑q : Set W)) {a a' : Finset W}
    (ha : a ∈ Q) (ha' : a' ∈ Q) (hd : Disjoint a a') {w₁ w₂ : W} (h₁ : w₁ ∈ a) (h₂ : w₂ ∈ a) :
    w₁ = w₂ := by
  by_contra hne
  rcases h (a' ∪ a.erase w₂) ⟨a', ha', Finset.subset_union_left⟩ a ha with hall | hnone
  · rcases Finset.mem_union.1 (hall w₂ h₂) with h | h
    · exact Finset.disjoint_left.1 hd h₂ h
    · exact (Finset.mem_erase.1 h).1 rfl
  · exact hnone w₁ h₁ (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hne, h₁⟩))

/-! ### Belief-sensitivity (§4.2) -/

/-- An agent whose beliefs are insensitive to every question relative to which `p` is
considered, William III and England avoiding nuclear war with France, has *S wants p* undefined
in every context: where `p` is considered the beliefs are insensitive, and where they are
sensitive `p` is not considered. -/
theorem undefined_of_insensitive {W : Type*} {bel p : Set W}
    (h : ∀ Q : List (Finset W), IsConsidered Q p → ¬ IsBelSensitive Q bel)
    (N Q : List (Finset W)) : ¬ Defined N Q bel p :=
  λ hd => h Q hd.1 hd.2.2.2

end PhillipsBrown2025
