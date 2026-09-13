import Linglib.Semantics.Questions.Partition.Basic
import Linglib.Semantics.Attitudes.Desire.BestWorlds
import Linglib.Semantics.Attitudes.Desire.Conditional
import Linglib.Semantics.Presupposition.Basic
import Linglib.Core.Order.OfCriteria
import Mathlib.Order.Preorder.Finite
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
ascription against a contextual question (§3), a partition of the worlds: the answers
compatible with the beliefs are ranked by the desires they entail, *S wants p* holds when every
best answer entails *p* (`Want`), and the ascription is defined only if the question decides *p*
(§3.6), is diverse and does not stack the deck (§3.7), and the beliefs are sensitive to it
(§4.2) (`Defined`). *Nap* is true considering whether one naps and whether one feels rested,
*Not-nap* considering whether one naps and whether one passes, and in the former context *Fail*
is undefined, the outcome of the exam being ignored (`act_true`, `not_act_true`,
`cost_undefined`); the lobster case, *Lobster*, *Not-lobster* and *Die*, is the same model. The
deck-stacked question of Lu's case would make *Lu wants it not to rain* true and is excluded by
the anti-deckstacking constraint, which the level playing field satisfies
(`not_rain_deckstacked`, `deckstacked_excluded`); an agent whose beliefs are insensitive to
every question that decides *p*, William III and nuclear war, has *S wants p* undefined in every
context (`undefined_of_insensitive`), which leaves the semantics Strawson upward monotone
(`toPartialProp_strawsonEntails`). On the finest question the semantics is the best-worlds one
(`want_bot_iff`).

## Implementation notes

* A question is a `Setoid`, its answers the cells; the question raised by a list of issues is
  their `Setoid.ofProps`, and *p* is considered relative to a question when the question
  decides it. Answers are ordered by the desires they entail, [kratzer-1981]'s ordering with
  entailment as satisfaction (`entailed`), and the best answers are the `MaximalFor` elements
  of that valuation.
* The act, its benefit and its cost are the three issues of the nap and lobster cases (nap,
  feeling rested, failing the exam; eating the lobster, the gustatory experience, dying), the
  beliefs tying benefit and cost to the act, and the desires being the benefit and not the
  cost. The Anti-deckstacking Constraint quantifies over all propositions; read so, it admits
  only the finest partition (`antiDeckstacking_univ_singleton`), so it is restricted here to a
  list of salient propositions, the issues of each case.
* Heim's semantics is the conditional one of `Desire/Conditional`. Levinson's expected-value
  comparison, the sufficient-desirability semantics of §2.4, and the Heimian question-based
  semantics of footnote 16 are prose.

## References

* [phillips-brown-2025]
* [heim-1992]
* [von-fintel-1999]
* [villalta-2008]
* [yalcin-2018]
* [kratzer-1981]
-/

namespace PhillipsBrown2025

open Desire Presupposition

section Semantics

variable {W : Type*} (G N : List (Finset W)) (s : Setoid W) (bel p : Set W)

/-! ### Question-based desire (§3) -/

/-- An answer, the cell of `w`, compatible with the beliefs. -/
def Live (w : W) : Prop := ∃ v ∈ s.cell w, v ∈ bel

/-- The desires an answer entails: answers are ordered by inclusion of these. -/
abbrev entailed : W → Set (Finset W) := Preorder.satisfied (λ w g => s.cell w ⊆ ↑g) {g | g ∈ G}

/-- `S wants p`: every best live answer entails `p`. -/
def Want : Prop := ∀ w, MaximalFor (Live s bel) (entailed G s) w → s.cell w ⊆ p

/-- Some answer entails `p` and some entails `¬p`. -/
def IsDiverse : Prop := (∃ w, s.cell w ⊆ p) ∧ ∃ w, s.cell w ⊆ pᶜ

/-- Every salient proposition in `N` that some answer entails is itself decided. -/
def IsAntiDeckstacking : Prop := ∀ q ∈ N, (∃ w, s.cell w ⊆ ↑q) → s.Decides ↑q

/-- The beliefs discriminate among the answers: some answer is live and some is not. -/
def IsBelSensitive : Prop := (∃ w, Live s bel w) ∧ ∃ w, ¬ Live s bel w

/-- The four metasemantic constraints jointly. -/
def Defined : Prop :=
  s.Decides p ∧ IsDiverse s p ∧ IsAntiDeckstacking N s ∧ IsBelSensitive s bel

/-- Question-based *want* with its definedness conditions as presupposition. -/
def toPartialProp : PartialProp W := ⟨λ _ => Defined N s bel p, λ _ => Want G s bel p⟩

section Decidable

variable [Fintype W] [DecidableEq W] [DecidableRel s] [DecidablePred (· ∈ bel)]
  [DecidablePred (· ∈ p)]

instance (w : W) : Decidable (Live s bel w) := inferInstanceAs (Decidable (∃ v ∈ s.cell w, _))

instance (w : W) : Decidable (MaximalFor (Live s bel) (entailed G s) w) :=
  inferInstanceAs (Decidable (Live s bel w ∧ ∀ z, Live s bel z → _ → _))

instance : Decidable (Want G s bel p) := inferInstanceAs (Decidable (∀ _, _ → _))

instance : Decidable (IsDiverse s p) := inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (IsAntiDeckstacking N s) := inferInstanceAs (Decidable (∀ q ∈ N, _ → _))

instance : Decidable (IsBelSensitive s bel) := inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (Defined N s bel p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end Decidable

variable {G N s bel p} {q : Set W}

theorem Want.mono (hpq : p ⊆ q) (h : Want G s bel p) : Want G s bel q :=
  λ w hw => (h w hw).trans hpq

/-- A best live answer exists whenever some answer is live. -/
theorem exists_best [Finite W] (h : ∃ w, Live s bel w) :
    ∃ w, MaximalFor (Live s bel) (entailed G s) w :=
  Set.Finite.exists_maximalFor _ {w | Live s bel w} (Set.toFinite _) h

/-- Without a `p`-answer the ascription is false as soon as some answer is live: the diversity
constraint against vacuous falsity. -/
theorem not_want_of_not_exists [Finite W] (hlive : ∃ w, Live s bel w)
    (hp : ¬ ∃ w, s.cell w ⊆ p) : ¬ Want G s bel p := λ hw =>
  let ⟨w, hb⟩ := exists_best (G := G) hlive
  hp ⟨w, hw w hb⟩

/-- With the question deciding `p` and no `¬p`-answer the ascription is true: the diversity
constraint against vacuous truth. -/
theorem want_of_decides_of_not_exists (hc : s.Decides p) (hnp : ¬ ∃ w, s.cell w ⊆ pᶜ) :
    Want G s bel p := λ w _ =>
  (Setoid.decides_iff_forall_cell.1 hc w).resolve_right λ h => hnp ⟨w, h⟩

/-- Strawson upward monotonicity: where both ascriptions are defined, `want p` entails
`want q` for `p ⊆ q`. -/
theorem toPartialProp_strawsonEntails (hpq : p ⊆ q) :
    (toPartialProp G N s bel p).strawsonEntails (toPartialProp G N s bel q) :=
  λ _ _ _ h => h.mono hpq

/-- On the finest question, question-based *want* is best-worlds *want* (§3.4). -/
theorem want_bot_iff : Want G ⊥ bel p ↔ BestWorlds.Want G bel p := by
  simp only [Want, BestWorlds.Want, BestWorlds.Undominated, BestWorlds.le_iff, MaximalFor, Live,
    entailed, Preorder.satisfied, Setoid.cell_bot, Set.mem_singleton_iff, exists_eq_left,
    Set.singleton_subset_iff, Set.ofPred_subset_ofPred, Finset.mem_coe, and_imp]
  simp +contextual [Set.mem_ofPred_eq]

end Semantics

/-! ### The nap and lobster cases (§2.1, §2.2) -/

/-- A state: whether the act is done, whether its benefit obtains, whether its cost obtains. -/
structure World where
  act : Bool
  benefit : Bool
  cost : Bool
  deriving DecidableEq

instance : Fintype World :=
  Fintype.ofEquiv (Bool × Bool × Bool)
    ⟨λ t => ⟨t.1, t.2.1, t.2.2⟩, λ w => (w.act, w.benefit, w.cost), λ _ => rfl, λ _ => rfl⟩

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
def qBenefit : Setoid World := Setoid.ofProps {act, benefit}

/-- The question considering whether the act is done and whether its cost obtains
(Figure 5). -/
def qCost : Setoid World := Setoid.ofProps {act, cost}

instance : DecidableRel qBenefit := inferInstanceAs (DecidableRel (Setoid.ofProps _))
instance : DecidableRel qCost := inferInstanceAs (DecidableRel (Setoid.ofProps _))

/-- The salient propositions of the case, the test set of the anti-deckstacking constraint. -/
def issues : List (Finset World) := [act, benefit, cost]

/-- *Nap*, *Lobster*: considering the act and its benefit, the ascription is defined and true. -/
theorem act_true : Defined issues qBenefit bel ↑act ∧ Want desires qBenefit bel ↑act := by
  decide +kernel

/-- *Fail*, *Die*: in that context the cost is ignored, so the ascription is undefined
(§3.6), which blocks the inference from *Nap* to *Fail* (§4.1). -/
theorem cost_undefined : ¬ qBenefit.Decides ↑cost := by decide +kernel

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
    ⟨λ t => ⟨t.1, t.2⟩, λ w => (w.rain, w.happy), λ _ => rfl, λ _ => rfl⟩

/-- It rains tomorrow. -/
def rain : Finset LuWorld := Finset.univ.filter (·.rain)

/-- Lu is happy tomorrow. -/
def happy : Finset LuWorld := Finset.univ.filter (·.happy)

/-- Lu's beliefs: happy whatever the weather. -/
def belLu : Set LuWorld := {w | w.happy = true}

instance : DecidablePred (· ∈ belLu) := λ w => inferInstanceAs (Decidable (w.happy = true))

/-- The deck-stacked question (Figure 7): whether it rains, and if not, whether Lu is happy. -/
def qStacked : Setoid LuWorld := Setoid.ker λ w => if w.rain then none else some w.happy

/-- The level playing field (Figure 9). -/
def qFair : Setoid LuWorld := Setoid.ofProps {rain, happy}

instance : DecidableRel qStacked := inferInstanceAs (DecidableRel (Setoid.ker _))
instance : DecidableRel qFair := inferInstanceAs (DecidableRel (Setoid.ofProps _))

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
      ∀ q : Finset LuWorld, (∃ w, qFair.cell w ⊆ ↑q) → qFair.Decides ↑q := by
  decide +kernel

/-- Read with `q` ranging over all propositions, the Anti-deckstacking Constraint admits only
the finest partition: two worlds in one cell, with a second cell available, are equal, since
the union of the second cell with the first minus one of the worlds is entailed by an answer
and decided by none. -/
theorem antiDeckstacking_univ_singleton {W : Type*} {s : Setoid W}
    (h : ∀ q : Set W, (∃ w, s.cell w ⊆ q) → s.Decides q) {w₁ w₂ w₃ : W} (h₁₂ : s w₁ w₂)
    (h₁₃ : ¬ s w₁ w₃) : w₁ = w₂ := by
  by_contra hne
  have hq := Setoid.decides_iff.1 (h (s.cell w₃ ∪ (s.cell w₁ \ {w₂})) ⟨w₃, Set.subset_union_left⟩)
  rcases (hq w₁ w₂ h₁₂).1 (Or.inr ⟨s.refl' w₁, hne⟩) with h | ⟨_, h⟩
  · exact h₁₃ (s.trans' h₁₂ h)
  · exact h rfl

/-! ### Belief-sensitivity (§4.2) -/

/-- An agent whose beliefs are insensitive to every question that decides `p`, William III and
England avoiding nuclear war with France, has *S wants p* undefined in every context: where `p`
is decided the beliefs are insensitive, and where they are sensitive `p` is not decided. -/
theorem undefined_of_insensitive {W : Type*} {bel p : Set W}
    (h : ∀ s : Setoid W, s.Decides p → ¬ IsBelSensitive s bel) (N : List (Finset W))
    (s : Setoid W) : ¬ Defined N s bel p :=
  λ hd => h s hd.1 hd.2.2.2

end PhillipsBrown2025
