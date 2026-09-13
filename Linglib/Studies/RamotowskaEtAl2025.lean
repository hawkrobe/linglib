import Linglib.Semantics.Conditionals.Counterfactual
import Linglib.Semantics.Plurality.Trivalent

/-!
# Ramotowska, Marty, Romoli, and Santorio (2025): Counterfactuals and Quantificational Force

This file formalizes [ramotowska-marty-romoli-santorio-2025]'s comparison of three theories of
counterfactuals on quantified sentences in mixed scenarios, where some but not all of the
players would have won. The universal theory of [lewis-1973] and [kratzer-2012] quantifies over
the closest antecedent worlds (2); the selectional theory of [stalnaker-1968] evaluates the whole
sentence at a selected world and supervaluates over the candidate selections after composition
(5); the
homogeneity theory of [von-fintel-1997] and [kriz-2015] gives each counterfactual a third
status during composition (6). Unembedded, the last two agree that a single player's
counterfactual has a third status and the first calls it false (Table 1, `unembedded`).
Embedded under a quantifier they part ways: the universal theory makes the sentence turn on its
polarity (`universal_polarity`), the selectional theory on its quantificational force, the
universal sentences false and the existential ones true whatever the question under discussion
(`selectional_force`), and the homogeneity theory leaves every quantified sentence undefined
under either projection algorithm (`homogeneity_undefined`), so that only there is a gap for a
question under discussion to resolve, as it does for the plural definite of the same scenario
(`dissociation`). The implicature variant of [bassi-bar-lev-2018] (§8) mispredicts *some* and
*not all* (`implicature_some`, `implicature_notAll`). The paper's two experiments find the force
effect and no effect of the question under discussion on counterfactuals, alongside a question
effect on plural definites, the pattern of the selectional theory.

## Implementation notes

A scenario is a similarity ordering, an antecedent, and one consequent per player. Mixedness is
stated as the paper's setting has it: every closest antecedent world has a winner and a loser,
and every player wins in one closest world and loses in another. The homogeneity theory's
projection through a quantifier is the Kleene aggregation of the players' trivalent values,
conjunctive or disjunctive over the values or their negations; the paper notes that the choice
makes no difference when every instance is undefined, and its Table 3 row for that theory,
which rests on a pragmatic resolution of undefinedness by the question under discussion, is
not derived. Force is the paper's binary, universal against existential, which differs from the
weak/strong labels of [barwise-cooper-1981] on *no*. The mean ratings and mixed-effects models
of §5 and §6 are not restated.

## References

* [ramotowska-marty-romoli-santorio-2025]
* [lewis-1973]
* [kratzer-2012]
* [stalnaker-1968]
* [von-fintel-1997]
* [kriz-2015]
* [bassi-bar-lev-2018]
* [barwise-cooper-1981]
-/

open Conditionals Conditionals.Counterfactual

namespace RamotowskaEtAl2025

/-! ### Quantified counterfactuals -/

/-- The four quantifiers of the test sentences (15): *all*, *none*, *some*, and *not all* of the
players would have won. -/
inductive Quant
  | all | none | some | notAll
  deriving DecidableEq, Repr, Fintype

/-- Quantificational force, the paper's binary: *all* and *none* are universal, *some* and *not
all* existential. -/
inductive Force
  | universal | existential
  deriving DecidableEq, Repr

/-- The force of a quantifier. -/
def Quant.force : Quant → Force
  | .all | .none => .universal
  | .some | .notAll => .existential

/-- Polarity: *all* and *some* are positive, *none* and *not all* negative. -/
def Quant.IsPositive : Quant → Prop
  | .all | .some => True
  | .none | .notAll => False

/-- The selectional theory's verdict in a mixed scenario is fixed by force alone. -/
def Force.verdict : Force → Trivalent
  | .universal => .false
  | .existential => .true

/-- The quantifier applied to a domain and a predicate. -/
def Quant.eval {ι : Type*} (q : Quant) (D : Finset ι) (P : ι → Prop) : Prop :=
  match q with
  | .all => ∀ d ∈ D, P d
  | .none => ∀ d ∈ D, ¬ P d
  | .some => ∃ d ∈ D, P d
  | .notAll => ∃ d ∈ D, ¬ P d

instance {ι : Type*} (q : Quant) (D : Finset ι) (P : ι → Prop) [DecidablePred P] :
    Decidable (q.eval D P) := by
  cases q <;> dsimp only [Quant.eval] <;> infer_instance

/-- The quantifier's projection through the players' trivalent values: the Kleene meet for the
universal quantifiers and the Kleene join for the existential ones, over the values or their
negations. -/
def Quant.aggregate (q : Quant) (vs : List Trivalent) : Trivalent :=
  match q with
  | .all => Trivalent.aggregate .conjunctive vs
  | .none => Trivalent.aggregate .conjunctive (vs.map Trivalent.neg)
  | .some => Trivalent.aggregate .disjunctive vs
  | .notAll => Trivalent.aggregate .disjunctive (vs.map Trivalent.neg)

variable {W ι : Type*} [DecidableEq W] [Fintype W] (sim : SimilarityOrdering W)
  (A : W → Prop) [DecidablePred A] (w : W) (D : Finset ι) (B : ι → W → Prop)

/-- The closest antecedent worlds to the world of evaluation. -/
abbrev closest : Finset W := sim.closestWorlds w (Finset.univ.filter A)

/-! ### Mixed scenarios -/

/-- A win-some-lose-some scenario: there are players, every closest antecedent world has a
winner and a loser among them, and every player wins in some closest world and loses in
another. -/
structure Mixed : Prop where
  nonempty : D.Nonempty
  worlds : ∀ w' ∈ closest sim A w, (∃ d ∈ D, B d w') ∧ ∃ d ∈ D, ¬ B d w'
  players : ∀ d ∈ D, (∃ w' ∈ closest sim A w, B d w') ∧ ∃ w' ∈ closest sim A w, ¬ B d w'

/-- Some closest antecedent world exists. -/
theorem Mixed.closest_nonempty (h : Mixed sim A w D B) : (closest sim A w).Nonempty :=
  let ⟨d, hd⟩ := h.nonempty
  let ⟨⟨w₁, hw₁, _⟩, _⟩ := h.players d hd
  ⟨w₁, hw₁⟩

/-! ### The theories on a quantified sentence -/

variable [∀ d, DecidablePred (B d)]

/-- The universal theory (2): the quantifier over the players' universal counterfactuals. -/
def universal (q : Quant) : Prop := q.eval D λ d => universalCounterfactual sim A (B d) w

/-- The selectional theory (5): the quantified sentence evaluated at the selected world and
supervaluated over the candidate selections, the closest antecedent worlds. -/
def selectional (q : Quant) : Trivalent :=
  Trivalent.dist (closest sim A w) λ w' => q.eval D λ d => B d w'

/-- The homogeneity theory (6): each player's counterfactual carries its third status into
composition, and the quantifier projects it. -/
noncomputable def homogeneity (q : Quant) : Trivalent :=
  q.aggregate (D.toList.map λ d => selectionalCounterfactual sim A (B d) w)

/-- The implicature theory (§8): the basic existential meaning (23) and its exhaustified
universal strengthening (24), the latter computed in the upward-entailing scope of *some* and
the former in the downward-entailing scope of *not all*. -/
def implicature (q : Quant) : Prop :=
  match q with
  | .all => ∀ d ∈ D, universalCounterfactual sim A (B d) w
  | .none => ∀ d ∈ D, ¬ lewisMight sim A (B d) w
  | .some => ∃ d ∈ D, universalCounterfactual sim A (B d) w
  | .notAll => ∃ d ∈ D, ¬ lewisMight sim A (B d) w

variable {sim A w D B}

/-! ### Predictions in mixed scenarios -/

/-- Table 1, the unembedded case: a player's counterfactual is false on the universal theory,
indeterminate on the selectional theory, and undefined on the homogeneity theory. -/
theorem unembedded (h : Mixed sim A w D B) {d : ι} (hd : d ∈ D) :
    ¬ universalCounterfactual sim A (B d) w ∧
      selectionalCounterfactual sim A (B d) w = .indet ∧
      (homogeneityCounterfactual sim A (B d) w).presupposition = .failed := by
  obtain ⟨⟨w₁, hw₁, hB₁⟩, ⟨w₂, hw₂, hB₂⟩⟩ := h.players d hd
  have hnot : ¬ ∀ w' ∈ closest sim A w, B d w' := λ hall => hB₂ (hall w₂ hw₂)
  have hnot' : ¬ ∀ w' ∈ closest sim A w, ¬ B d w' := λ hnone => hnone w₁ hw₁ hB₁
  refine ⟨hnot, ?_, ?_⟩
  · unfold selectionalCounterfactual
    rw [if_neg hnot, if_neg hnot']
  · unfold homogeneityCounterfactual
    rw [if_neg hnot, if_neg hnot']

/-- The universal theory turns on polarity: since every player's counterfactual is false, the
positive sentences are false and the negative ones true. -/
theorem universal_polarity (h : Mixed sim A w D B) (q : Quant) :
    universal sim A w D B q ↔ ¬ q.IsPositive := by
  have hfalse : ∀ d ∈ D, ¬ universalCounterfactual sim A (B d) w :=
    λ d hd => (unembedded h hd).1
  cases q
  · simp only [universal, Quant.eval, Quant.IsPositive, not_true_eq_false, iff_false]
    exact λ hall => let ⟨d, hd⟩ := h.nonempty; hfalse d hd (hall d hd)
  · simp only [universal, Quant.eval, Quant.IsPositive, not_false_eq_true, iff_true]
    exact hfalse
  · simp only [universal, Quant.eval, Quant.IsPositive, not_true_eq_false, iff_false]
    exact λ ⟨d, hd, hc⟩ => hfalse d hd hc
  · simp only [universal, Quant.eval, Quant.IsPositive, not_false_eq_true, iff_true]
    exact let ⟨d, hd⟩ := h.nonempty; ⟨d, hd, hfalse d hd⟩

/-- Table 3, the selectional row: the quantified sentence is determinately false for the
universal quantifiers and determinately true for the existential ones, whatever the polarity,
because every selected world has a winner and a loser. -/
theorem selectional_force (h : Mixed sim A w D B) (q : Quant) :
    selectional sim A w D B q = q.force.verdict := by
  cases q
  · exact (Trivalent.dist_eq_false_iff _ _).2 ⟨h.closest_nonempty, λ w' hw' hall =>
      let ⟨d, hd, hB⟩ := (h.worlds w' hw').2; hB (hall d hd)⟩
  · exact (Trivalent.dist_eq_false_iff _ _).2 ⟨h.closest_nonempty, λ w' hw' hnone =>
      let ⟨d, hd, hB⟩ := (h.worlds w' hw').1; hnone d hd hB⟩
  · exact (Trivalent.dist_eq_true_iff _ _).2 λ w' hw' => (h.worlds w' hw').1
  · exact (Trivalent.dist_eq_true_iff _ _).2 λ w' hw' => (h.worlds w' hw').2

/-- No selectional value is a gap: there is nothing for a question under discussion to
resolve. -/
theorem selectional_determinate (h : Mixed sim A w D B) (q : Quant) :
    selectional sim A w D B q ≠ .indet := by
  rw [selectional_force h]
  cases q <;> simp [Quant.force, Force.verdict]

/-- Every player's counterfactual is undefined, so the quantified sentence is undefined under
either projection algorithm, for every quantifier: the homogeneity theory leaves the sentences
to pragmatics. -/
theorem homogeneity_undefined (h : Mixed sim A w D B) (q : Quant) :
    homogeneity sim A w D B q = .indet := by
  have hl : D.toList.map (λ d => selectionalCounterfactual sim A (B d) w)
      = List.replicate D.card .indet := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, λ v hv => ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hv
    exact (unembedded h (Finset.mem_toList.1 hd)).2.1
  have hpos : 0 < D.card := Finset.card_pos.2 h.nonempty
  cases q <;> simp only [homogeneity, Quant.aggregate, hl, List.map_replicate, Trivalent.neg] <;>
    exact Trivalent.aggregate_replicate_indet _ _ hpos

/-- (25): with the implicature computed in its scope, *some* says that some player was
guaranteed to win, false in the scenario. -/
theorem implicature_some (h : Mixed sim A w D B) : ¬ implicature sim A w D B .some :=
  λ ⟨_, hd, hc⟩ => (unembedded h hd).1 hc

/-- (26): with the basic existential meaning in its scope, *not all* says that some player
could not have won, false in the scenario. -/
theorem implicature_notAll (h : Mixed sim A w D B) : ¬ implicature sim A w D B .notAll :=
  λ ⟨d, hd, hc⟩ => hc λ hall =>
    let ⟨w₁, hw₁, hB₁⟩ := (h.players d hd).1
    hall w₁ hw₁ hB₁

/-- The dissociation of Experiment 2: at a world where some but not all of the players won, the
plural definite *the players won* has a gap, while the quantified counterfactuals of the same
scenario have none. -/
theorem dissociation (h : Mixed sim A w D B) {v : W}
    (hv : (∃ d ∈ D, B d v) ∧ ∃ d ∈ D, ¬ B d v) (q : Quant) :
    Plurality.Trivalent.pluralTruthValue B D v = .indet ∧ selectional sim A w D B q ≠ .indet :=
  ⟨(Plurality.Trivalent.pluralTruthValue_eq_gap_iff B D v).2 hv, selectional_determinate h q⟩


end RamotowskaEtAl2025
