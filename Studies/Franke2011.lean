module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Linglib.Core.Order.Argmax
public import Linglib.Pragmatics.SignalingGame.Interpretation
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Data.Examples.Franke2011

/-!
# Franke (2011): Quantity Implicatures, Exhaustive Interpretation, and Rational Conversation

An interpretation game has as states the distinctions that the alternatives to a sentence can
draw and as messages the alternatives themselves, and its receiver tries to guess the state.
Franke explains quantity implicatures by iterated best response in such a game: a level-0
receiver reads a message as its denotation, a level-0 sender says something true, and a
level-`k + 1` player best-responds to the belief that every level-`k` strategy is equally likely.
With flat priors this reduces to counting, since a sender picks the true messages with fewest
readings, a receiver the states that send fewest messages, and a message no state sends is read
literally. The probabilistic model behind the count agrees with it under flat priors and refines
it by the prior under nearly flat ones; every chain of reasoning reaches a fixed point, and the
fixed points are perfect Bayesian equilibria.

## Main statements

* `SomeAll.isNashEquilibrium_scalar_and_reversed`, `SomeAll.scalar_implicature`: the
  implicature of "some" and its reversal are both equilibria, and iterated best response selects
  the implicature.
* `TwoDisjuncts.free_choice`: free choice, simplification of disjunctive antecedents and a
  conjunctive reading of plain disjunction are one prediction.
* `SomeAllEpistemic.strong`, `DisjunctionEpistemic.ignorance`,
  `DisjunctionConjEpistemic.exclusivity_of_competencePrior`: epistemic implicatures under each
  assumption about the speaker's competence.
* `receiverLevel_eq_receiverChain`, `receiverLevel_eq_receiverChainBy`: the probabilistic model is
  the count under flat priors and the count refined by the prior under nearly flat ones.
* `exists_isFixedPt_iterate`, `exists_isFixedPt_receiverChain`: every chain reaches a fixed point.
* `exists_isPBE_of_isFixedPt`: fixed points are perfect Bayesian equilibria.
* `coe_receiverStep_subset_exhMW`: the first sophisticated reading entails exhaustification by
  minimal models.
* `exhIE_eq_setOf_indistinguishable`: innocent exclusion keeps the worlds that no alternative
  distinguishes from the minimal ones.

## Implementation notes

* The counting system depends only on denotations. The prior enters as a secondary criterion,
  which the competence assumption (67) turns into a count of undecided alternatives, so the
  examples are stated for every prior satisfying the assumption.
* In the probabilistic model a player type is a set of pure strategies and the belief in it is
  uniform over it. The truth filter of (117) and (122) is applied by maximising over true
  messages and reading an unsent message literally, which agrees with the paper along every
  chain.
* (83) refines by the prior the literal reading of a message nobody sends; the probabilistic
  model and Figure 16 leave it unrefined, as here. Condition (132) is stated with the inequality
  its proof needs; the paper prints it reversed.
* Theorem 3 is proved for interpretation games with positive priors. The proof completes the
  paper's sketch by showing that the sender's choices only grow around a cycle of the chain.
* Fact 2 holds for alternatives monotonically determined by the others, as in the paper's
  conjunctive example, and fails for the negation of an alternative (`not_ltALT_insert_compl`).
* Equilibrium in §7 is the library's Bayesian Nash equilibrium.

## TODO

* Fact 4, the condition on the alternatives under which the two exhaustivity operators agree.

## References

* [franke-2011]
* [vanrooij-schulz-2004]
* [fox-2007]
-/

@[expose] public section

namespace Franke2011

open Finset Function Exhaustification Convexity

/-! ### Interpretation games from belief-value tables

A base-level game distinguishes the truth-value vectors of the alternatives within the target
sentence (61), an epistemic game the belief-value vectors (66), with three values: believed
true, believed false and undecided. A message is true at a state when the state believes it
true. -/

/-- The three belief values of §6.2 are believed true, believed false and undecided. -/
inductive BeliefValue where
  | yes
  | no
  | unc
  deriving DecidableEq, Fintype, Repr

section Tables

variable {T M : Type*} [Fintype M] (table : T → M → BeliefValue)

/-- In the interpretation game of a belief-value table, `m` is true at `t` iff `t` believes `m`
true. -/
def ofTable (prior : T → ℝ) : InterpGame T M where
  meaning m t := table t m = .yes
  prior := prior

/-- `uncertaintyCount table t` counts the alternatives `t` is undecided about. -/
def uncertaintyCount (t : T) : ℕ := (univ.filter fun m ↦ table t m = .unc).card

/-- The belief value (65) of a proposition `A` in an epistemic state `X` is believed true when
`X ⊆ A`, believed false when `X` and `A` are disjoint, and undecided otherwise. -/
def beliefValue {W : Type*} [DecidableEq W] (X A : Finset W) : BeliefValue :=
  if X ⊆ A then .yes else if Disjoint X A then .no else .unc

/-- Under the competence assumption (67) the prior is a strictly decreasing function of the
number of alternatives a state is undecided about. -/
def CompetencePrior (prior : T → ℝ) : Prop :=
  ∃ f : ℕ → ℝ, StrictAnti f ∧ prior = f ∘ uncertaintyCount table

/-- Under the incompetence assumption (68) the prior is a strictly increasing function of the
number of alternatives a state is undecided about. -/
def IncompetencePrior (prior : T → ℝ) : Prop :=
  ∃ f : ℕ → ℝ, StrictMono f ∧ prior = f ∘ uncertaintyCount table

variable {table} {prior : T → ℝ}

/-- Under competence the most probable states of a set are the ones undecided about fewest
alternatives. -/
theorem CompetencePrior.argmax_eq (h : CompetencePrior table prior) (s : Finset T) :
    s.argmax prior = s.argmax (OrderDual.toDual ∘ uncertaintyCount table) := by
  obtain ⟨f, hf, rfl⟩ := h
  exact argmax_comp_strictMono (g := f ∘ OrderDual.ofDual) hf.dual_left

/-- Under incompetence the most probable states of a set are the ones undecided about most
alternatives. -/
theorem IncompetencePrior.argmax_eq (h : IncompetencePrior table prior) (s : Finset T) :
    s.argmax prior = s.argmax (uncertaintyCount table) := by
  obtain ⟨f, hf, rfl⟩ := h
  exact argmax_comp_strictMono hf

end Tables

/-! ### The light system

A player type is a set of pure strategies, written as a correspondence: a receiver type
`R : M → Finset T`, a sender type `S : T → Finset M`. Level 0 is literal meaning (73): the
receiver type is the denotation and the sender type its inverse. A level-`k + 1` sender in `t`
chooses, among the messages that can induce `t`, those with fewest interpretations (76), the
chance of being understood being one over their number (129); if no message can induce `t` she
sends any true message. The receiver's step (77) is the same computation with the roles of
states and messages exchanged, a surprise message being read literally. -/

section Correspondence

variable {α γ : Type*} [Fintype α] [DecidableEq γ]

/-- The inverse `X⁻¹(c)` of a correspondence `X : α → Finset γ` at `c` is the set of points
whose image contains `c` (footnote 25). -/
def inverse (X : α → Finset γ) (c : γ) : Finset α := univ.filter (c ∈ X ·)

@[simp]
theorem mem_inverse {X : α → Finset γ} {c : γ} {a : α} : a ∈ inverse X c ↔ c ∈ X a := by
  simp [inverse]

@[simp]
theorem inverse_inverse [Fintype γ] [DecidableEq α] (X : α → Finset γ) :
    inverse (inverse X) = X := by
  ext; simp

variable [DecidableEq α] {β β' : Type*} [LinearOrder β] [LinearOrder β']

/-- The best responses to the unbiased belief in the type `X` at `c` are the points of
`X⁻¹(c)` with fewest `X`-images, (76) and (77); when `X⁻¹(c)` is empty they are the literal
choices `lit c`. -/
def bestResponse (lit : γ → Finset α) (X : α → Finset γ) (c : γ) : Finset α :=
  if inverse X c = ∅ then lit c else (inverse X c).argmin fun a ↦ (X a).card

/-- The best responses refined by a secondary criterion `key`, as by a nearly flat prior (83) or
a nominal message cost (§9.2), keep the ones maximising `key`; literal choices stay
unrefined. -/
def bestResponseBy (key : α → β) (lit : γ → Finset α) (X : α → Finset γ) (c : γ) : Finset α :=
  if inverse X c = ∅ then lit c else ((inverse X c).argmin fun a ↦ (X a).card).argmax key

variable {lit : γ → Finset α} {X : α → Finset γ} {key : α → β}

theorem mem_bestResponse {c : γ} {a : α} :
    a ∈ bestResponse lit X c ↔ if inverse X c = ∅ then a ∈ lit c
      else c ∈ X a ∧ ∀ a', c ∈ X a' → (X a).card ≤ (X a').card := by
  unfold bestResponse; split_ifs <;> simp [mem_argmin]

theorem bestResponseBy_subset (c : γ) : bestResponseBy key lit X c ⊆ bestResponse lit X c := by
  unfold bestResponseBy bestResponse; split_ifs
  exacts [le_rfl, argmax_subset]

/-- A secondary criterion that ranks all points alike refines nothing. -/
theorem bestResponseBy_of_forall_eq (h : ∀ a b, key a = key b) :
    bestResponseBy key lit = bestResponse lit := by
  funext X c; unfold bestResponseBy bestResponse; split_ifs
  exacts [rfl, argmax_eq_self_of_forall_le fun a _ b _ ↦ (h b a).le]

theorem bestResponseBy_congr {key' : α → β'} (h : ∀ s : Finset α, s.argmax key = s.argmax key') :
    bestResponseBy key lit = bestResponseBy key' lit := by
  funext X c; simp only [bestResponseBy, h]

/-- Best responses respect literal meaning when the type does (Lemma 2). -/
theorem bestResponse_subset (h : ∀ a, ∀ c ∈ X a, a ∈ lit c) (c : γ) :
    bestResponse lit X c ⊆ lit c := by
  unfold bestResponse; split_ifs
  · exact le_rfl
  · exact fun a ha ↦ h a c (mem_inverse.mp (argmin_subset ha))

end Correspondence

section Light

variable {T M : Type*} [Fintype T] [Fintype M] [DecidableEq T] [DecidableEq M]
  (den : M → Finset T) {β : Type*} [LinearOrder β]

/-- `senderStep den R` is the level-`k + 1` sender type against the level-`k` receiver type `R`
(76). -/
def senderStep : (M → Finset T) → T → Finset M := bestResponse (inverse den)

/-- `receiverStep den S` is the level-`k + 1` receiver type against the level-`k` sender type `S`
(77). -/
def receiverStep : (T → Finset M) → M → Finset T := bestResponse den

/-- `senderStepBy den key` refines the sender step by a secondary criterion, such as nominal
costs. -/
def senderStepBy (key : M → β) : (M → Finset T) → T → Finset M := bestResponseBy key (inverse den)

/-- `receiverStepBy den key` refines the receiver step by a secondary criterion, such as the
prior (83). -/
def receiverStepBy (key : T → β) : (T → Finset M) → M → Finset T := bestResponseBy key den

/-- `receiverChain den n` is the receiver type `R₂ₙ` of the chain from the literal receiver. -/
def receiverChain (n : ℕ) : M → Finset T := (receiverStep den ∘ senderStep den)^[n] den

/-- `senderChain den n` is the sender type `S₂ₙ` of the chain from the literal sender. -/
def senderChain (n : ℕ) : T → Finset M := (senderStep den ∘ receiverStep den)^[n] (inverse den)

/-- `receiverChainBy den key n` is the receiver type `R₂ₙ` of the chain from the literal receiver
when every receiver step is refined by `key`. -/
def receiverChainBy (key : T → β) (n : ℕ) : M → Finset T :=
  (receiverStepBy den key ∘ senderStep den)^[n] den

/-- `senderChainBy den key n` is the sender type `S₂ₙ` of the chain from the literal sender when
every receiver step is refined by `key`. -/
def senderChainBy (key : T → β) (n : ℕ) : T → Finset M :=
  (senderStep den ∘ receiverStepBy den key)^[n] (inverse den)

omit [Fintype M] in
theorem receiverStepBy_congr {β' : Type*} [LinearOrder β'] {key : T → β} {key' : T → β'}
    (h : ∀ s : Finset T, s.argmax key = s.argmax key') :
    receiverStepBy den key = receiverStepBy den key' :=
  bestResponseBy_congr h

theorem receiverChainBy_congr {β' : Type*} [LinearOrder β'] {key : T → β} {key' : T → β'}
    (h : ∀ s : Finset T, s.argmax key = s.argmax key') :
    receiverChainBy den key = receiverChainBy den key' := by
  funext n; unfold receiverChainBy receiverStepBy; rw [bestResponseBy_congr h]

theorem senderChainBy_congr {β' : Type*} [LinearOrder β'] {key : T → β} {key' : T → β'}
    (h : ∀ s : Finset T, s.argmax key = s.argmax key') :
    senderChainBy den key = senderChainBy den key' := by
  funext n; unfold senderChainBy receiverStepBy; rw [bestResponseBy_congr h]

variable {den}

omit [Fintype T] in
/-- A sender who believes every interpretation true only sends true messages (Lemma 2). -/
theorem senderStep_subset {R : M → Finset T} (hR : ∀ m, R m ⊆ den m) (t : T) :
    senderStep den R t ⊆ inverse den t :=
  bestResponse_subset (fun m _ ht ↦ mem_inverse.mpr (hR m ht)) t

/-- A receiver who believes every message sent true only assigns true interpretations
(Lemma 2). -/
theorem receiverStep_subset {S : T → Finset M} (hS : ∀ t, S t ⊆ inverse den t) (m : M) :
    receiverStep den S m ⊆ den m :=
  bestResponse_subset (fun t _ hm ↦ mem_inverse.mp (hS t hm)) m

theorem receiverStepBy_subset {key : T → β} {S : T → Finset M}
    (hS : ∀ t, S t ⊆ inverse den t) (m : M) : receiverStepBy den key S m ⊆ den m :=
  (bestResponseBy_subset m).trans (receiverStep_subset hS m)

variable (den)

/-- The first sophisticated receiver of the chain from the literal sender reads a message as the
states where it is true that make fewest messages true (107). -/
theorem receiverStep_inverse (m : M) :
    receiverStep den (inverse den) m = (den m).argmin fun t ↦ (inverse den t).card := by
  rw [receiverStep, bestResponse, inverse_inverse]
  split_ifs with h
  · rw [h]; rfl
  · rfl

theorem receiverChain_succ (n : ℕ) :
    receiverChain den (n + 1) = receiverStep den (senderStep den (receiverChain den n)) :=
  iterate_succ_apply' _ _ _

theorem senderChain_succ (n : ℕ) :
    senderChain den (n + 1) = senderStep den (receiverStep den (senderChain den n)) :=
  iterate_succ_apply' _ _ _

theorem receiverChainBy_succ (key : T → β) (n : ℕ) :
    receiverChainBy den key (n + 1) =
      receiverStepBy den key (senderStep den (receiverChainBy den key n)) :=
  iterate_succ_apply' _ _ _

theorem senderChainBy_succ (key : T → β) (n : ℕ) :
    senderChainBy den key (n + 1) =
      senderStep den (receiverStepBy den key (senderChainBy den key n)) :=
  iterate_succ_apply' _ _ _

/-- Truth is preserved along the receiver chain (Lemma 2). -/
theorem receiverChain_subset (n : ℕ) (m : M) : receiverChain den n m ⊆ den m := by
  induction n generalizing m with
  | zero => exact le_rfl
  | succ n ih => rw [receiverChain_succ]; exact receiverStep_subset (senderStep_subset ih) m

/-- Truth is preserved along the sender chain (Lemma 2). -/
theorem senderChain_subset (n : ℕ) (t : T) : senderChain den n t ⊆ inverse den t := by
  induction n generalizing t with
  | zero => exact le_rfl
  | succ n ih =>
    rw [senderChain_succ]
    exact senderStep_subset (receiverStep_subset ih) t

theorem receiverChainBy_subset (key : T → β) (n : ℕ) (m : M) :
    receiverChainBy den key n m ⊆ den m := by
  induction n generalizing m with
  | zero => exact le_rfl
  | succ n ih =>
    rw [receiverChainBy_succ]; exact receiverStepBy_subset (senderStep_subset ih) m

theorem senderChainBy_subset (key : T → β) (n : ℕ) (t : T) :
    senderChainBy den key n t ⊆ inverse den t := by
  induction n generalizing t with
  | zero => exact le_rfl
  | succ n ih =>
    rw [senderChainBy_succ]; exact senderStep_subset (receiverStepBy_subset ih) t

end Light


/-! ### "Some" and "all" (Figure 4, §7)

Two states within the denotation of "some" (`Examples.ex4`): some-but-not-all, where only
"some" is true, and all, where both are. -/

namespace SomeAll

inductive State where
  | someNotAll
  | all
  deriving DecidableEq, Fintype, Repr

inductive Message where
  | some
  | all
  deriving DecidableEq, Fintype, Repr

/-- The interpretation game of Figure 4 has flat priors. -/
noncomputable def game : InterpGame State Message :=
  ofTable (fun t m ↦ match t, m with
    | _, .some | .all, .all => .yes
    | .someNotAll, .all => .no) fun _ ↦ 1 / 2

/-- In the attested play (69) the sender says "some" when not all. -/
def scalarSender : State → Message
  | .someNotAll => .some
  | .all => .all

/-- In the attested play (69) the receiver reads "some" as not all. -/
def scalarReceiver : Message → State
  | .some => .someNotAll
  | .all => .all

/-- The reversed play (71) swaps the messages. -/
def reversedSender : State → Message
  | .someNotAll => .all
  | .all => .some

/-- The receiver of the reversed play (71) reads "some" as all. -/
def reversedReceiver : Message → State
  | .some => .all
  | .all => .someNotAll

/-- The attested play and the reversed play are both Nash equilibria, so equilibrium does not
select the implicature (§7). -/
theorem isNashEquilibrium_scalar_and_reversed :
    game.toSignalingGame.isNashEquilibrium scalarSender scalarReceiver ∧
      game.toSignalingGame.isNashEquilibrium reversedSender reversedReceiver :=
  ⟨game.isNashEquilibrium_of_leftInverse (fun _ ↦ by norm_num [game, ofTable])
      fun t ↦ by cases t <;> rfl,
    game.isNashEquilibrium_of_leftInverse (fun _ ↦ by norm_num [game, ofTable])
      fun t ↦ by cases t <;> rfl⟩

/-- Both chains reach the attested play at their first sophisticated level and stay there, so
"some" conveys not-all. -/
theorem scalar_implicature :
    receiverChain game.trueStates 1 = (fun m ↦ {scalarReceiver m}) ∧
      senderChain game.trueStates 1 = (fun t ↦ {scalarSender t}) ∧
      IsFixedPt (receiverStep game.trueStates ∘ senderStep game.trueStates)
        fun m ↦ {scalarReceiver m} := by
  decide

/-- No chain reaches the reversed play, which reads "all" where it is false, since reasoning that
starts from literal meaning keeps to it (Lemma 2). -/
theorem receiverChain_ne_reversed (n : ℕ) :
    receiverChain game.trueStates n ≠ fun m ↦ {reversedReceiver m} := fun h ↦ by
  have := receiverChain_subset game.trueStates n .all
  rw [h] at this
  exact absurd (this (mem_singleton_self _)) (by decide)

end SomeAll

/-! ### Two disjuncts (Figures 5 and 7; tables (84)–(86))

Alternatives `A`, `B` and `A ∨ B` give three states whether the disjunction is plain
(`Examples.ex8`), under a possibility modal (`Examples.ex12a`), or in a conditional antecedent
(`Examples.ex18`): one game, three constructions. Its fixed point maps the disjunction to the
state where both disjuncts hold, which is the free choice inference, the simplification of
disjunctive antecedents, and at base level a conjunctive reading of plain disjunction (§9.2). -/

namespace TwoDisjuncts

inductive State where
  | onlyA
  | onlyB
  | both
  deriving DecidableEq, Fintype, Repr

inductive Message where
  | first
  | second
  | either
  deriving DecidableEq, Fintype, Repr

/-- The interpretation game of Figure 5 has flat priors. -/
noncomputable def game : InterpGame State Message :=
  ofTable (fun t m ↦ match t, m with
    | .onlyA, .first | .both, .first | .onlyB, .second | .both, .second | _, .either => .yes
    | _, _ => .no) fun _ ↦ 1 / 3

/-- In the free choice play (70) each state sends the message true at it alone. -/
def freeChoiceSender : State → Message
  | .onlyA => .first
  | .onlyB => .second
  | .both => .either

/-- In the free choice play (70) the disjunction is read as both disjuncts. -/
def freeChoiceReceiver : Message → State
  | .first => .onlyA
  | .second => .onlyB
  | .either => .both

/-- In the crossed play (72) the disjunction and the first disjunct swap roles. -/
def crossedSender : State → Message
  | .onlyA => .either
  | .onlyB => .second
  | .both => .first

/-- The receiver of the crossed play (72) reads the disjunction as the first disjunct alone. -/
def crossedReceiver : Message → State
  | .first => .both
  | .second => .onlyB
  | .either => .onlyA

/-- The free choice play and the crossed play both communicate perfectly, so both are Nash
equilibria and no refinement by payoffs separates them (§7). -/
theorem isNashEquilibrium_freeChoice_and_crossed :
    game.toSignalingGame.isNashEquilibrium freeChoiceSender freeChoiceReceiver ∧
      game.toSignalingGame.isNashEquilibrium crossedSender crossedReceiver :=
  ⟨game.isNashEquilibrium_of_leftInverse (fun _ ↦ by norm_num [game, ofTable])
      fun t ↦ by cases t <;> rfl,
    game.isNashEquilibrium_of_leftInverse (fun _ ↦ by norm_num [game, ofTable])
      fun t ↦ by cases t <;> rfl⟩

/-- Both chains reach the free choice play at level 4 (Figure 7), where it is a fixed point. -/
theorem free_choice :
    receiverChain game.trueStates 2 = (fun m ↦ {freeChoiceReceiver m}) ∧
      senderChain game.trueStates 2 = (fun t ↦ {freeChoiceSender t}) ∧
      IsFixedPt (receiverStep game.trueStates ∘ senderStep game.trueStates)
        fun m ↦ {freeChoiceReceiver m} := by
  decide

/-- On the way the disjunction is a surprise message to `R₂`, read literally (137). -/
theorem receiverChain_one_either :
    receiverChain game.trueStates 1 .either = {.onlyA, .onlyB, .both} := by
  decide

/-- The chain from the literal receiver never reaches the crossed play, although it respects
literal meaning as well. -/
theorem receiverChain_ne_crossed (n : ℕ) :
    receiverChain game.trueStates n ≠ fun m ↦ {crossedReceiver m} := by
  obtain ⟨h2, -, hfix⟩ := free_choice
  match n with
  | 0 | 1 => decide
  | k + 2 =>
    change (receiverStep game.trueStates ∘ senderStep game.trueStates)^[k]
      (receiverChain game.trueStates 2) ≠ _
    rw [h2, (hfix.iterate k).eq]
    decide

end TwoDisjuncts

/-! ### Epistemic "some" and "all" (Figures 6, 8 and 9)

Three speaker belief states within belief in "some": believes not-all, believes all, undecided
about all. Flat priors give the general epistemic implicature, competence (67) the strong and
incompetence (68) the weak one, in both chains. -/

namespace SomeAllEpistemic

/-- States are named by their belief-value vectors over ("some", "all"). -/
inductive State where
  | t10
  | t11
  | t1u
  deriving DecidableEq, Fintype, Repr

open SomeAll (Message)

/-- This table gives the belief values of Figure 6. -/
def table : State → Message → BeliefValue
  | _, .some => .yes
  | .t10, .all => .no
  | .t11, .all => .yes
  | .t1u, .all => .unc

/-- This is the game of Figure 6 with `a = b`. -/
noncomputable def game : InterpGame State Message := ofTable table fun _ ↦ 1 / 3

/-- The states of Figure 6 are the belief-value vectors of the nonempty sets of states of
Figure 4 (66). -/
theorem exists_table_eq_iff (v : Message → BeliefValue) :
    (∃ t, table t = v) ↔
      ∃ X : Finset SomeAll.State,
        X.Nonempty ∧ v = fun m ↦ beliefValue X (SomeAll.game.trueStates m) := by
  revert v; decide

/-- With flat priors both chains settle at their first sophisticated level on reading "some" as
the speaker not believing "all" (Figure 8). -/
theorem general :
    receiverChain game.trueStates 1 .some = {.t10, .t1u} ∧
      IsFixedPt (receiverStep game.trueStates ∘ senderStep game.trueStates)
        (receiverChain game.trueStates 1) ∧
      receiverStep game.trueStates (senderChain game.trueStates 1) =
        receiverChain game.trueStates 1 := by
  decide

/-- Under every competence prior both chains read "some" as the speaker believing "all" false
(Figure 9). -/
theorem strong {p : State → ℝ} (hp : CompetencePrior table p) :
    receiverChainBy game.trueStates p 1 .some = {.t10} ∧
      IsFixedPt (receiverStepBy game.trueStates p ∘ senderStep game.trueStates)
        (receiverChainBy game.trueStates p 1) ∧
      receiverStepBy game.trueStates p (senderChainBy game.trueStates p 1) =
        receiverChainBy game.trueStates p 1 := by
  rw [receiverChainBy_congr _ hp.argmax_eq, receiverStepBy_congr _ hp.argmax_eq,
    senderChainBy_congr _ hp.argmax_eq]
  decide

/-- Under every incompetence prior both chains read "some" as the speaker undecided about
"all". -/
theorem weak {p : State → ℝ} (hp : IncompetencePrior table p) :
    receiverChainBy game.trueStates p 1 .some = {.t1u} ∧
      IsFixedPt (receiverStepBy game.trueStates p ∘ senderStep game.trueStates)
        (receiverChainBy game.trueStates p 1) ∧
      receiverStepBy game.trueStates p (senderChainBy game.trueStates p 1) =
        receiverChainBy game.trueStates p 1 := by
  rw [receiverChainBy_congr _ hp.argmax_eq, receiverStepBy_congr _ hp.argmax_eq,
    senderChainBy_congr _ hp.argmax_eq]
  decide

end SomeAllEpistemic

/-! ### Epistemic disjunction (tables (87)–(88), Figure 10)

Six belief states within belief in `A ∨ B`. In all six constellations, two chains under three
prior regimes, the fixed point reads the disjunction as the state undecided about both
disjuncts, which is the ignorance implicature; a single disjunct is read as belief in it without
belief in the other, as knowledge that the other is false under competence, and as uncertainty
about the other under incompetence. -/

namespace DisjunctionEpistemic

/-- States are named by belief-value vectors over (`A`, `B`, `A ∨ B`). -/
inductive State where
  | t101
  | t011
  | t111
  | t1u1
  | tu11
  | tuu1
  deriving DecidableEq, Fintype, Repr

open TwoDisjuncts (Message)

/-- This table gives the belief values of (87). -/
def table : State → Message → BeliefValue
  | _, .either => .yes
  | .t101, .first | .t111, .first | .t1u1, .first => .yes
  | .t011, .first => .no
  | .tu11, .first | .tuu1, .first => .unc
  | .t011, .second | .t111, .second | .tu11, .second => .yes
  | .t101, .second => .no
  | .t1u1, .second | .tuu1, .second => .unc

/-- This is the game of table (87) with `a = b = c` in (88). -/
noncomputable def game : InterpGame State Message := ofTable table fun _ ↦ 1 / 6

/-- The states of (87) are the belief-value vectors of the nonempty sets of states of
(85) (66). -/
theorem exists_table_eq_iff (v : Message → BeliefValue) :
    (∃ t, table t = v) ↔ ∃ X : Finset TwoDisjuncts.State,
      X.Nonempty ∧ v = fun m ↦ beliefValue X (TwoDisjuncts.game.trueStates m) := by
  revert v; decide

/-- With flat priors both chains settle at their first sophisticated level on the ignorance
reading of the disjunction (Figure 10). -/
theorem ignorance :
    receiverChain game.trueStates 1 = (fun m ↦ match m with
      | .first => {.t101, .t1u1} | .second => {.t011, .tu11} | .either => {.tuu1}) ∧
      IsFixedPt (receiverStep game.trueStates ∘ senderStep game.trueStates)
        (receiverChain game.trueStates 1) ∧
      receiverStep game.trueStates (senderChain game.trueStates 1) =
        receiverChain game.trueStates 1 := by
  decide

/-- Under every competence prior the fixed point of both chains keeps the ignorance reading and
reads a single disjunct as knowledge that the other is false. -/
theorem ignorance_of_competencePrior {p : State → ℝ} (hp : CompetencePrior table p) :
    receiverChainBy game.trueStates p 1 = (fun m ↦ match m with
      | .first => {.t101} | .second => {.t011} | .either => {.tuu1}) ∧
      IsFixedPt (receiverStepBy game.trueStates p ∘ senderStep game.trueStates)
        (receiverChainBy game.trueStates p 1) ∧
      receiverStepBy game.trueStates p (senderChainBy game.trueStates p 1) =
        receiverChainBy game.trueStates p 1 := by
  rw [receiverChainBy_congr _ hp.argmax_eq, receiverStepBy_congr _ hp.argmax_eq,
    senderChainBy_congr _ hp.argmax_eq]
  decide

/-- Under every incompetence prior the fixed point of both chains keeps the ignorance reading
and reads a single disjunct as uncertainty about the other. -/
theorem ignorance_of_incompetencePrior {p : State → ℝ} (hp : IncompetencePrior table p) :
    receiverChainBy game.trueStates p 1 = (fun m ↦ match m with
      | .first => {.t1u1} | .second => {.tu11} | .either => {.tuu1}) ∧
      IsFixedPt (receiverStepBy game.trueStates p ∘ senderStep game.trueStates)
        (receiverChainBy game.trueStates p 1) ∧
      receiverStepBy game.trueStates p (senderChainBy game.trueStates p 1) =
        receiverChainBy game.trueStates p 1 := by
  rw [receiverChainBy_congr _ hp.argmax_eq, receiverStepBy_congr _ hp.argmax_eq,
    senderChainBy_congr _ hp.argmax_eq]
  decide

end DisjunctionEpistemic

/-! ### Disjunction with a conjunctive alternative (tables (89)–(92), Figures 11–14) -/

/-! Plain disjunction at base level with `A ∧ B` among the alternatives (table (89),
Figure 11). -/

namespace DisjunctionConj

open TwoDisjuncts (State)

inductive Message where
  | first
  | second
  | both
  | either
  deriving DecidableEq, Fintype, Repr

/-- The interpretation game of table (89) has flat priors. -/
noncomputable def game : InterpGame State Message :=
  ofTable (fun t m ↦ match t, m with
    | _, .either | .both, _ | .onlyA, .first | .onlyB, .second => .yes
    | _, _ => .no) fun _ ↦ 1 / 3

/-- In the fixed point of both chains no state sends the disjunction, so it is a surprise
message, read literally. -/
theorem disjunction_surprise :
    receiverChain game.trueStates 1 = (fun m ↦ match m with
      | .first => {.onlyA} | .second => {.onlyB} | .both => {.both}
      | .either => {.onlyA, .onlyB, .both}) ∧
      IsFixedPt (receiverStep game.trueStates ∘ senderStep game.trueStates)
        (receiverChain game.trueStates 1) ∧
      receiverStep game.trueStates (senderChain game.trueStates 1) =
        receiverChain game.trueStates 1 ∧
      inverse (senderStep game.trueStates (receiverChain game.trueStates 1)) .either = ∅ := by
  decide

end DisjunctionConj

/-! Free choice with the conjunctive alternative (table (90), Figure 12): the state where both
are permitted but not jointly is now possible, and the fixed point delivers free choice together
with the exclusivity implicature. Figure 12 draws the chain from the literal receiver, which the
text calls the `S₀`-sequence. -/

namespace FreeChoiceConj

/-- States are named by truth vectors over (`◇A`, `◇B`, `◇(A ∧ B)`, `◇(A ∨ B)`). -/
inductive State where
  | t1001
  | t0101
  | t1111
  | t1101
  deriving DecidableEq, Fintype, Repr

open DisjunctionConj (Message)

/-- The interpretation game of table (90) has flat priors. -/
noncomputable def game : InterpGame State Message :=
  ofTable (fun t m ↦ match t, m with
    | _, .either | .t1111, _ | .t1001, .first | .t0101, .second
    | .t1101, .first | .t1101, .second => .yes
    | _, _ => .no) fun _ ↦ 1 / 4

/-- From the literal receiver the chain reaches at level 4 a fixed point reading the
disjunction as free choice without joint permission. -/
theorem freeChoice_exclusivity :
    receiverChain game.trueStates 2 = (fun m ↦ match m with
      | .first => {.t1001} | .second => {.t0101} | .both => {.t1111} | .either => {.t1101}) ∧
      IsFixedPt (receiverStep game.trueStates ∘ senderStep game.trueStates)
        (receiverChain game.trueStates 2) := by
  decide

end FreeChoiceConj

/-! Simplification of disjunctive antecedents with the conjunctive alternative (table (91),
Figure 13): six states, and the fixed point after `R₄` gives simplification together with the
exclusivity implicature; the chain from the literal sender agrees on the disjunction
(footnote 29). -/

namespace SdaConj

/-- States are named by truth vectors over (`A > C`, `B > C`, `(A ∧ B) > C`, `(A ∨ B) > C`). -/
inductive State where
  | t1001
  | t0101
  | t1011
  | t0111
  | t1101
  | t1111
  deriving DecidableEq, Fintype, Repr

open DisjunctionConj (Message)

/-- The interpretation game of table (91) has flat priors. -/
noncomputable def game : InterpGame State Message :=
  ofTable (fun t m ↦ match t, m with
    | _, .either => .yes
    | .t1001, .first | .t1011, .first | .t1101, .first | .t1111, .first => .yes
    | .t0101, .second | .t0111, .second | .t1101, .second | .t1111, .second => .yes
    | .t1011, .both | .t0111, .both | .t1111, .both => .yes
    | _, _ => .no) fun _ ↦ 1 / 6

/-- Both chains reach a fixed point reading the disjunctive antecedent as both conditionals true
and the conjunctive one false. -/
theorem sda_exclusivity :
    receiverChain game.trueStates 2 .either = {.t1101} ∧
      IsFixedPt (receiverStep game.trueStates ∘ senderStep game.trueStates)
        (receiverChain game.trueStates 2) ∧
      receiverStep game.trueStates (senderChain game.trueStates 2) .either = {.t1101} ∧
      IsFixedPt (senderStep game.trueStates ∘ receiverStep game.trueStates)
        (senderChain game.trueStates 2) := by
  decide

end SdaConj

/-! Epistemic disjunction with the conjunctive alternative (table (92), Figure 14): without a
competence assumption the disjunction conveys that the speaker does not believe `A ∧ B`, under
competence that she believes it false, and under incompetence that she is undecided. -/

namespace DisjunctionConjEpistemic

/-- States are named by belief-value vectors over (`A`, `B`, `A ∧ B`, `A ∨ B`). -/
inductive State where
  | t1001
  | t0101
  | t1111
  | tuu01
  | t1uu1
  | tu1u1
  | tuuu1
  deriving DecidableEq, Fintype, Repr

open DisjunctionConj (Message)

/-- This table gives the belief values of (92). -/
def table : State → Message → BeliefValue
  | _, .either => .yes
  | .t1001, .first | .t1111, .first | .t1uu1, .first => .yes
  | .t0101, .first => .no
  | .tuu01, .first | .tu1u1, .first | .tuuu1, .first => .unc
  | .t0101, .second | .t1111, .second | .tu1u1, .second => .yes
  | .t1001, .second => .no
  | .tuu01, .second | .t1uu1, .second | .tuuu1, .second => .unc
  | .t1111, .both => .yes
  | .t1001, .both | .t0101, .both | .tuu01, .both => .no
  | .t1uu1, .both | .tu1u1, .both | .tuuu1, .both => .unc

/-- The game of table (92) has flat priors. -/
noncomputable def game : InterpGame State Message := ofTable table fun _ ↦ 1 / 7

/-- The states of (92) are the belief-value vectors of the nonempty sets of states of
(89) (66). -/
theorem exists_table_eq_iff (v : Message → BeliefValue) :
    (∃ t, table t = v) ↔ ∃ X : Finset TwoDisjuncts.State,
      X.Nonempty ∧ v = fun m ↦ beliefValue X (DisjunctionConj.game.trueStates m) := by
  revert v; decide

/-- With flat priors the chain from the literal sender reads the disjunction as the speaker not
believing `A ∧ B` (Figure 14). -/
theorem exclusivity :
    receiverStep game.trueStates (senderChain game.trueStates 1) .either = {.tuu01, .tuuu1} := by
  decide

/-- Under every competence prior the disjunction conveys that the speaker believes `A ∧ B`
false. -/
theorem exclusivity_of_competencePrior {p : State → ℝ} (hp : CompetencePrior table p) :
    receiverStepBy game.trueStates p (senderChainBy game.trueStates p 1) .either = {.tuu01} := by
  rw [receiverStepBy_congr _ hp.argmax_eq, senderChainBy_congr _ hp.argmax_eq]
  decide

/-- Under every incompetence prior the disjunction conveys that the speaker is undecided about
`A ∧ B`. -/
theorem exclusivity_of_incompetencePrior {p : State → ℝ} (hp : IncompetencePrior table p) :
    receiverStepBy game.trueStates p (senderChainBy game.trueStates p 1) .either = {.tuuu1} := by
  rw [receiverStepBy_congr _ hp.argmax_eq, senderChainBy_congr _ hp.argmax_eq]
  decide

end DisjunctionConjEpistemic

/-! ### Entailing disjuncts (table (97), Figure 16)

"John or (John and Mary)" (`Examples.ex95a`) is truth-conditionally "John", yet conveys that the
speaker considers Mary's coming possible. With the disjunction nominally costlier than its
equivalent and a competent speaker, the chain from the literal receiver reads the disjunction
as `t[1,u,1]`. -/

namespace EntailingDisjuncts

open SomeAllEpistemic (State)

inductive Message where
  | john
  | johnAndMary
  | johnOrBoth
  deriving DecidableEq, Fintype, Repr

/-- This table gives the belief values of (97). -/
def table : State → Message → BeliefValue
  | _, .john | _, .johnOrBoth => .yes
  | .t10, .johnAndMary => .no
  | .t11, .johnAndMary => .yes
  | .t1u, .johnAndMary => .unc

/-- The game of table (97) has flat priors. -/
noncomputable def game : InterpGame State Message := ofTable table fun _ ↦ 1 / 3

/-- The disjunction is nominally costlier than its equivalent. -/
def cost : Message → ℕ
  | .johnOrBoth => 1
  | _ => 0

/-- Under every competence prior, with costs breaking the sender's ties, the chain from the
literal receiver reaches at level 4 a fixed point reading the disjunction as the speaker knowing
that John came and being undecided about Mary. -/
theorem possibility_of_competencePrior {p : State → ℝ} (hp : CompetencePrior table p) :
    let round := receiverStepBy game.trueStates p ∘ senderStepBy game.trueStates
      (OrderDual.toDual ∘ cost)
    round^[2] game.trueStates .johnOrBoth = {.t1u} ∧
      IsFixedPt round (round^[2] game.trueStates) := by
  intro round
  simp only [round, receiverStepBy_congr _ hp.argmax_eq]
  decide

end EntailingDisjuncts

/-! ### Universal free choice (tables (101)–(102), Figure 17)

"Everybody may take an apple or a pear" (`Examples.ex99`) with alternatives "everybody may take
an apple" and "everybody may take a pear": the full game reads the sentence as a mixed group,
and pruning the mixed state by group homogeneity restores universal free choice. -/

namespace GroupPermission

/-- States are named by truth vectors over (`∀◇A`, `∀◇B`, `∀◇(A ∨ B)`). -/
inductive State where
  | t101
  | t011
  | t111
  | t001
  deriving DecidableEq, Fintype, Repr

open TwoDisjuncts (Message)

/-- This table gives the truth values of (101). -/
def table : State → Message → BeliefValue
  | _, .either => .yes
  | .t101, .first | .t111, .first => .yes
  | .t011, .second | .t111, .second => .yes
  | _, _ => .no

/-- The game of table (101) has flat priors. -/
noncomputable def game : InterpGame State Message := ofTable table fun _ ↦ 1 / 4

/-- The pruned game (102) drops the mixed state. -/
noncomputable def pruned : InterpGame {t : State // t ≠ .t001} Message :=
  ofTable (table ·.1) fun _ ↦ 1 / 3

/-- The full game reads the sentence as a mixed group (Figure 17). -/
theorem mixed_group :
    receiverStep game.trueStates (senderChain game.trueStates 0) .either = {.t001} ∧
    IsFixedPt (senderStep game.trueStates ∘ receiverStep game.trueStates)
      (senderChain game.trueStates 1) := by
  decide

/-- Pruned, the sentence conveys that everybody may take either (102). -/
theorem universal_free_choice :
    receiverStep pruned.trueStates (senderChain pruned.trueStates 1) .either =
      {⟨.t111, by decide⟩} := by
  decide

end GroupPermission

/-! ### The heavy system (Appendix B.1)

Player types are still sets of pure strategies, and an unbiased belief in a type is uniform over
it ((115), (118)). Under matching utility the expected utility of sending `m` in `t` is the
probability that the receiver guesses `t` after `m` (129), so a level-`k + 1` sender maximises
that probability among the true messages ((116), (117)). The receiver maximises the posterior,
which is the prior times the probability of the message up to normalisation ((119)–(121)), and
reads a message no state sends literally (122). -/

noncomputable section Heavy

variable {T M : Type*} [Fintype T] [Fintype M] [DecidableEq T] [DecidableEq M]
  (G : InterpGame T M)

omit [DecidableEq M] in
theorem inverse_trueStates : inverse G.trueStates = G.trueMessages := by
  ext; simp

/-- The level-`k + 1` sender type from the level-`k` receiver type `R` keeps, in each state, the
true messages after which the receiver is likeliest to guess it ((116), (117)). -/
def senderResponse (R : M → Finset T) (t : T) : Finset M :=
  (G.trueMessages t).argmax fun m ↦ ((R m).uniform t : ℝ)

/-- The level-`k + 1` receiver type from the level-`k` sender type `S` keeps, after each message,
the states of greatest posterior probability ((119)–(121)); a message no state sends is read
literally (122). -/
def receiverResponse (S : T → Finset M) (m : M) : Finset T :=
  if inverse S m = ∅ then G.trueStates m else univ.argmax fun t ↦ G.prior t * (S t).uniform m

/-- `receiverLevel G n` is the receiver type `R₂ₙ` of the heavy chain from the literal
receiver. -/
def receiverLevel (n : ℕ) : M → Finset T :=
  (receiverResponse G ∘ senderResponse G)^[n] G.trueStates

/-- `senderLevel G n` is the sender type `S₂ₙ` of the heavy chain from the literal sender. -/
def senderLevel (n : ℕ) : T → Finset M :=
  (senderResponse G ∘ receiverResponse G)^[n] G.trueMessages

/-- The expected gain (144) of a sender and a receiver type is the probability of successful
communication under the unbiased beliefs in them. -/
def expectedGain (S : T → Finset M) (R : M → Finset T) : ℝ :=
  ∑ t, G.prior t * ∑ m, (S t).uniform m * (R m).uniform t

/-- Under the near-flat condition (132), stated with the inequality its proof needs, prior
ratios stay above `(|M| - 1)/|M|`. -/
def NearFlat : Prop :=
  ∀ t t', ((Fintype.card M : ℝ) - 1) * G.prior t' < Fintype.card M * G.prior t

variable {G}

omit [Fintype T] [DecidableEq M] in
theorem mem_senderResponse {R : M → Finset T} {t : T} {m : M} :
    m ∈ senderResponse G R t ↔
      G.meaning m t ∧ ∀ m', G.meaning m' t → ((R m').uniform t : ℝ) ≤ (R m).uniform t := by
  simp [senderResponse, mem_argmax]

omit [Fintype T] [DecidableEq M] in
theorem senderResponse_subset (R : M → Finset T) (t : T) :
    senderResponse G R t ⊆ G.trueMessages t :=
  argmax_subset

omit [Fintype M] in
/-- With positive priors the receiver only chooses states that send the message. -/
theorem receiverResponse_subset_inverse (hprior : ∀ t, 0 < G.prior t) {S : T → Finset M}
    {m : M} (hm : inverse S m ≠ ∅) : receiverResponse G S m ⊆ inverse S m := by
  rw [receiverResponse, ite_eq_right hm,
    argmax_eq_argmax_of_support (subset_univ _) (nonempty_iff_ne_empty.mpr hm)
      (fun t ht ↦ mul_pos (hprior t) (uniform_pos_iff.mpr (mem_inverse.mp ht)))
      fun t _ ht ↦ by rw [uniform_of_notMem (mt mem_inverse.mpr ht), mul_zero]]
  exact argmax_subset

/-- A receiver who believes every message sent true only assigns true interpretations
(Lemma 2). -/
theorem receiverResponse_subset (hprior : ∀ t, 0 < G.prior t) {S : T → Finset M}
    (hS : ∀ t, S t ⊆ G.trueMessages t) (m : M) : receiverResponse G S m ⊆ G.trueStates m := by
  by_cases hm : inverse S m = ∅
  · rw [receiverResponse, ite_eq_left hm]
  · exact fun t ht ↦ G.mem_trueStates.mpr (G.mem_trueMessages.mp
      (hS t (mem_inverse.mp (receiverResponse_subset_inverse hprior hm ht))))

/-! ### Theorems 1 and 2: the light system is the heavy system with flat or near-flat priors -/

/-- Against the unbiased belief in a receiver type that respects truth, the heavy sender is the
light sender (76), since the probability of being understood is one over the number of
interpretations (129). -/
theorem senderResponse_eq_senderStep {R : M → Finset T} (hR : ∀ m, R m ⊆ G.trueStates m) :
    senderResponse G R = senderStep G.trueStates R := by
  funext t
  simp only [senderResponse, senderStep, bestResponse, inverse_trueStates]
  split_ifs with hemp
  · refine argmax_eq_self_of_forall_le fun m _ m' _ ↦ ?_
    have h : ∀ m, t ∉ R m := fun m hm ↦ (eq_empty_iff_forall_notMem.mp hemp) m (mem_inverse.mpr hm)
    simp [uniform_of_notMem (h m), uniform_of_notMem (h m')]
  · rw [argmax_eq_argmax_of_support (t := inverse R t)
      (fun m hm ↦ G.mem_trueMessages.mpr (G.mem_trueStates.mp (hR m (mem_inverse.mp hm))))
      (nonempty_iff_ne_empty.mpr hemp) (fun m hm ↦ uniform_pos_iff.mpr (mem_inverse.mp hm))
      fun m _ hm ↦ uniform_of_notMem (mt mem_inverse.mpr hm)]
    refine (argmin_eq_argmax_of_le_iff fun m hm m' hm' ↦ ?_).symm
    rw [uniform_of_mem (mem_inverse.mp hm), uniform_of_mem (mem_inverse.mp hm'),
      inv_le_inv₀ (by exact_mod_cast card_pos.mpr ⟨t, mem_inverse.mp hm'⟩)
        (by exact_mod_cast card_pos.mpr ⟨t, mem_inverse.mp hm⟩), Nat.cast_le]

omit [DecidableEq T] in
/-- Under near-flat priors the states maximising the prior times the probability of sending `m`
are the most probable of the light receiver's states, since sending fewer messages outweighs
any difference in prior. -/
theorem argmax_prior_mul_uniform_of_nearFlat (hprior : ∀ t, 0 < G.prior t) (hnf : NearFlat G)
    {S : T → Finset M} {m : M} (hne : inverse S m ≠ ∅) :
    (univ.argmax fun t ↦ G.prior t * (S t).uniform m) =
      ((inverse S m).argmin fun t ↦ (S t).card).argmax G.prior := by
  have hcard : ∀ t ∈ inverse S m, 0 < (S t).card := fun t ht ↦
    card_pos.mpr ⟨m, mem_inverse.mp ht⟩
  have hlt : ∀ t₁ ∈ inverse S m, ∀ t₂ ∈ inverse S m, (S t₁).card < (S t₂).card →
      G.prior t₂ * (S t₂).uniform m < G.prior t₁ * (S t₁).uniform m := by
    intro t₁ h₁ t₂ h₂ hk
    rw [uniform_of_mem (mem_inverse.mp h₁), uniform_of_mem (mem_inverse.mp h₂),
      ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_lt_div_iff₀ (by exact_mod_cast hcard t₂ h₂) (by exact_mod_cast hcard t₁ h₁)]
    have hk' : ((S t₁).card : ℝ) + 1 ≤ (S t₂).card := by exact_mod_cast hk
    have hM : ((S t₂).card : ℝ) ≤ Fintype.card M := by exact_mod_cast card_le_univ _
    have k₂ : (0 : ℝ) < (S t₂).card := by exact_mod_cast hcard t₂ h₂
    have p₂ := hprior t₂
    refine lt_of_mul_lt_mul_right ?_ (k₂.trans_le hM).le
    calc G.prior t₂ * (S t₁).card * Fintype.card M
        ≤ G.prior t₂ * ((S t₂).card - 1) * Fintype.card M := by gcongr; linarith
      _ ≤ G.prior t₂ * (Fintype.card M - 1) * (S t₂).card := by
        nlinarith [mul_nonneg p₂.le (sub_nonneg.mpr hM)]
      _ < G.prior t₁ * (S t₂).card * Fintype.card M := by
        linarith [mul_lt_mul_of_pos_right (hnf t₁ t₂) k₂]
  rw [argmax_eq_argmax_of_support (subset_univ _) (nonempty_iff_ne_empty.mpr hne)
    (fun t ht ↦ mul_pos (hprior t) (uniform_pos_iff.mpr (mem_inverse.mp ht)))
    fun t _ ht ↦ by rw [uniform_of_notMem (mt mem_inverse.mpr ht), mul_zero]]
  ext t
  simp only [mem_argmax, mem_argmin]
  constructor
  · rintro ⟨ht, hmax⟩
    have hmin : ∀ t' ∈ inverse S m, (S t).card ≤ (S t').card := fun t' ht' ↦
      not_lt.mp fun h ↦ absurd (hmax t' ht') (not_le.mpr (hlt t' ht' t ht h))
    refine ⟨⟨ht, hmin⟩, fun t' ⟨ht', hmin'⟩ ↦ ?_⟩
    have := hmax t' ht'
    rw [uniform_of_mem (mem_inverse.mp ht), uniform_of_mem (mem_inverse.mp ht'),
      show (S t').card = (S t).card from le_antisymm (hmin' t ht) (hmin t' ht')] at this
    exact le_of_mul_le_mul_right this (inv_pos.mpr (by exact_mod_cast hcard t ht))
  · rintro ⟨⟨ht, hmin⟩, hpr⟩
    refine ⟨ht, fun t' ht' ↦ ?_⟩
    rcases (hmin t' ht').lt_or_eq with h | h
    · exact (hlt t ht t' ht' h).le
    · rw [uniform_of_mem (mem_inverse.mp ht), uniform_of_mem (mem_inverse.mp ht'), ← h]
      exact mul_le_mul_of_nonneg_right (hpr t' ⟨ht', fun t'' ht'' ↦ h ▸ hmin t'' ht''⟩)
        (by positivity)

/-- Under near-flat priors the heavy receiver is the light receiver refined by the prior
(Theorem 2). -/
theorem receiverResponse_eq_receiverStepBy (hprior : ∀ t, 0 < G.prior t) (hnf : NearFlat G) :
    receiverResponse G = receiverStepBy G.trueStates G.prior := by
  funext S m
  unfold receiverResponse receiverStepBy bestResponseBy
  split_ifs with hemp
  · rfl
  · exact argmax_prior_mul_uniform_of_nearFlat hprior hnf hemp

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
theorem nearFlat_of_forall_eq (hprior : ∀ t, 0 < G.prior t)
    (hflat : ∀ t t', G.prior t = G.prior t') : NearFlat G := fun t t' ↦ by
  rw [hflat t' t]; linarith [hprior t]

/-- Under flat priors the heavy receiver is the light receiver (77). -/
theorem receiverResponse_eq_receiverStep (hprior : ∀ t, 0 < G.prior t)
    (hflat : ∀ t t', G.prior t = G.prior t') : receiverResponse G = receiverStep G.trueStates := by
  rw [receiverResponse_eq_receiverStepBy hprior (nearFlat_of_forall_eq hprior hflat)]
  exact bestResponseBy_of_forall_eq hflat

/-- Under near-flat priors the receiver chain of the heavy system is the light chain refined by
the prior (Theorem 2). -/
theorem receiverLevel_eq_receiverChainBy (hprior : ∀ t, 0 < G.prior t) (hnf : NearFlat G)
    (n : ℕ) : receiverLevel G n = receiverChainBy G.trueStates G.prior n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [receiverLevel, iterate_succ_apply', ← receiverLevel, ih, receiverChainBy_succ,
      comp_apply, senderResponse_eq_senderStep (receiverChainBy_subset _ _ n),
      receiverResponse_eq_receiverStepBy hprior hnf]

/-- Under near-flat priors the sender chain of the heavy system is the light chain with its
receivers refined by the prior (Theorem 2). -/
theorem senderLevel_eq_senderChainBy (hprior : ∀ t, 0 < G.prior t) (hnf : NearFlat G)
    (n : ℕ) : senderLevel G n = senderChainBy G.trueStates G.prior n := by
  induction n with
  | zero => exact (inverse_trueStates G).symm
  | succ n ih =>
    have hS := senderChainBy_subset G.trueStates G.prior n
    rw [senderLevel, iterate_succ_apply', ← senderLevel, ih, senderChainBy_succ, comp_apply,
      receiverResponse_eq_receiverStepBy hprior hnf,
      senderResponse_eq_senderStep (receiverStepBy_subset hS)]

/-- Under flat priors the heavy chains are the light chains (Theorem 1). -/
theorem receiverLevel_eq_receiverChain (hprior : ∀ t, 0 < G.prior t)
    (hflat : ∀ t t', G.prior t = G.prior t') (n : ℕ) :
    receiverLevel G n = receiverChain G.trueStates n := by
  rw [receiverLevel_eq_receiverChainBy hprior (nearFlat_of_forall_eq hprior hflat),
    receiverChainBy, receiverStepBy, bestResponseBy_of_forall_eq hflat]
  rfl

theorem senderLevel_eq_senderChain (hprior : ∀ t, 0 < G.prior t)
    (hflat : ∀ t t', G.prior t = G.prior t') (n : ℕ) :
    senderLevel G n = senderChain G.trueStates n := by
  rw [senderLevel_eq_senderChainBy hprior (nearFlat_of_forall_eq hprior hflat),
    senderChainBy, receiverStepBy, bestResponseBy_of_forall_eq hflat]
  rfl


/-! ### Lemma 3 and Theorem 3: convergence (Appendix B.4)

Expected gain never decreases along a chain: the sender step averages the receiver's
probability of the true state over its maximisers, and the receiver step averages the
posterior weight over its maximisers. A chain lives in a finite type, so it cycles; on a cycle
the gain is constant, so the sender's choices only grow around it, hence stay put, and the chain
has reached a fixed point. -/

section Convergence

omit [Fintype T] in
private theorem sum_mul_le_senderResponse {t : T} {A : Finset M} (hA : A ⊆ G.trueMessages t)
    (R : M → Finset T) :
    ∑ m, (A.uniform m : ℝ) * (R m).uniform t ≤
      ∑ m, (senderResponse G R t).uniform m * (R m).uniform t := by
  rcases (G.trueMessages t).eq_empty_or_nonempty with hemp | hne
  · obtain rfl : A = ∅ := subset_empty.mp (hemp ▸ hA)
    simp only [uniform_apply, notMem_empty, ite_false, zero_mul, sum_const_zero]
    exact sum_nonneg fun m _ ↦ mul_nonneg uniform_nonneg uniform_nonneg
  · obtain ⟨m₀, hm₀⟩ := argmax_nonempty hne (f := fun m ↦ ((R m).uniform t : ℝ))
    rw [senderResponse, sum_uniform_argmax_mul _ hm₀]
    exact sum_mul_le_of_support _ _ (fun _ ↦ uniform_nonneg) sum_uniform_le_one
      (fun m hm ↦ uniform_of_notMem fun h ↦ hm (hA h)) (fun _ ↦ uniform_nonneg) hm₀

/-- A level-`k + 1` sender does at least as well against `R` as any truthful sender type
(Lemma 3 (i)). -/
theorem expectedGain_le_senderResponse (hprior : ∀ t, 0 ≤ G.prior t) {S : T → Finset M}
    (hS : ∀ t, S t ⊆ G.trueMessages t) (R : M → Finset T) :
    expectedGain G S R ≤ expectedGain G (senderResponse G R) R :=
  sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left (sum_mul_le_senderResponse (hS t) R) (hprior t)

/-- A level-`k + 1` receiver does at least as well against `S` as any receiver type
(Lemma 3 (ii)). -/
theorem expectedGain_le_receiverResponse (hprior : ∀ t, 0 ≤ G.prior t) (S : T → Finset M)
    (R : M → Finset T) : expectedGain G S R ≤ expectedGain G S (receiverResponse G S) := by
  unfold expectedGain
  simp_rw [mul_sum, ← mul_assoc]
  rw [sum_comm, sum_comm (f := fun t m ↦
    G.prior t * (S t).uniform m * (receiverResponse G S m).uniform t)]
  refine sum_le_sum fun m _ ↦ ?_
  by_cases hm : inverse S m = ∅
  · have h0 : ∀ t, ((S t).uniform m : ℝ) = 0 := fun t ↦
      uniform_of_notMem fun h ↦ (eq_empty_iff_forall_notMem.mp hm) t (mem_inverse.mpr h)
    simp [h0]
  · obtain ⟨t₁, -⟩ := nonempty_iff_ne_empty.mpr hm
    obtain ⟨t₀, ht₀⟩ := argmax_nonempty ⟨t₁, mem_univ t₁⟩
      (f := fun t ↦ G.prior t * ((S t).uniform m : ℝ))
    rw [receiverResponse, ite_eq_right hm]
    simp_rw [mul_comm (G.prior _ * _ : ℝ)]
    rw [sum_uniform_argmax_mul _ ht₀]
    exact sum_mul_le_of_support _ _ (fun _ ↦ uniform_nonneg) sum_uniform_le_one
      (fun t ht ↦ absurd (mem_univ t) ht) (fun t ↦ mul_nonneg (hprior t) uniform_nonneg) ht₀

/-- If the sender's response to `R₁` does as well against `R₂` as the response to `R₂`, then
every message the first sends the second sends too. -/
theorem senderResponse_subset_of_expectedGain_eq (hprior : ∀ t, 0 < G.prior t)
    {R₁ R₂ : M → Finset T}
    (h : expectedGain G (senderResponse G R₁) R₂ = expectedGain G (senderResponse G R₂) R₂)
    (t : T) : senderResponse G R₁ t ⊆ senderResponse G R₂ t := by
  intro m hm
  have hinner : ∑ m, ((senderResponse G R₁ t).uniform m : ℝ) * (R₂ m).uniform t =
      ∑ m, (senderResponse G R₂ t).uniform m * (R₂ m).uniform t := by
    have hle := fun s ↦ sum_mul_le_senderResponse (G := G) (senderResponse_subset R₁ s) R₂
    have := (sum_eq_zero_iff_of_nonneg fun s _ ↦
      mul_nonneg (hprior s).le (sub_nonneg.mpr (hle s))).mp (by
        unfold expectedGain at h
        simp only [mul_sub, sum_sub_distrib, h, sub_self]) t (mem_univ t)
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (hprior t).ne'
    · linarith
  have htrue : G.meaning m t := G.mem_trueMessages.mp (senderResponse_subset R₁ t hm)
  obtain ⟨m₀, hm₀⟩ := argmax_nonempty ⟨m, G.mem_trueMessages.mpr htrue⟩
    (f := fun m ↦ ((R₂ m).uniform t : ℝ))
  have hmax : ∑ m, ((senderResponse G R₂ t).uniform m : ℝ) * (R₂ m).uniform t =
      (R₂ m₀).uniform t := sum_uniform_argmax_mul _ hm₀
  refine mem_senderResponse.mpr ⟨htrue, fun m' hm' ↦ ?_⟩
  by_contra hne
  have hlt : ((R₂ m).uniform t : ℝ) < (R₂ m₀).uniform t := lt_of_le_of_ne
    ((mem_argmax.mp hm₀).2 m (G.mem_trueMessages.mpr htrue))
    fun h ↦ hne (h ▸ (mem_argmax.mp hm₀).2 m' (G.mem_trueMessages.mpr hm'))
  have : ∑ m', ((senderResponse G R₁ t).uniform m' : ℝ) * (R₂ m').uniform t <
      (R₂ m₀).uniform t :=
    calc _ < ∑ m', ((senderResponse G R₁ t).uniform m' : ℝ) * (R₂ m₀).uniform t := by
          refine sum_lt_sum (fun m' _ ↦ ?_)
            ⟨m, mem_univ m, mul_lt_mul_of_pos_left hlt (uniform_pos_iff.mpr hm)⟩
          by_cases hm' : m' ∈ senderResponse G R₁ t
          · exact mul_le_mul_of_nonneg_left
              ((mem_argmax.mp hm₀).2 m' (senderResponse_subset R₁ t hm')) uniform_nonneg
          · simp [uniform_of_notMem hm']
      _ = (∑ m', ((senderResponse G R₁ t).uniform m' : ℝ)) * (R₂ m₀).uniform t := by
          rw [sum_mul]
      _ ≤ 1 * (R₂ m₀).uniform t := mul_le_mul_of_nonneg_right sum_uniform_le_one uniform_nonneg
      _ = (R₂ m₀).uniform t := one_mul _
  exact absurd (hinner.trans hmax) this.ne

private theorem eq_zero_of_monotone_of_periodic {α : Type*} [PartialOrder α] {u : ℕ → α}
    (hu : Monotone u) {p : ℕ} (hp : Periodic u p) (hp0 : 0 < p) (k : ℕ) : u k = u 0 :=
  le_antisymm ((hu (Nat.le_mul_of_pos_right k hp0)).trans_eq (hp.nat_mul_eq k)) (hu k.zero_le)

/-- Every chain of the heavy system reaches a fixed point (Theorem 3). -/
theorem exists_isFixedPt_iterate (hprior : ∀ t, 0 < G.prior t) (R : M → Finset T) :
    ∃ n, IsFixedPt (receiverResponse G ∘ senderResponse G)
      ((receiverResponse G ∘ senderResponse G)^[n] R) := by
  set f := receiverResponse G ∘ senderResponse G
  obtain ⟨a, b, hab, heq⟩ : ∃ a b, a < b ∧ f^[a] R = f^[b] R := by
    obtain ⟨a, b, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite fun n ↦ f^[n] R
    rcases hne.lt_or_gt with h' | h'
    exacts [⟨a, b, h', h⟩, ⟨b, a, h', h.symm⟩]
  set x : ℕ → M → Finset T := fun k ↦ f^[a + k] R with hx
  have hper : Periodic x (b - a) := fun k ↦ by
    simp only [hx]
    rw [show a + (k + (b - a)) = k + b by omega, iterate_add_apply, ← heq, ← iterate_add_apply,
      add_comm]
  have hsucc : ∀ k, x (k + 1) = f (x k) := fun _ ↦ iterate_succ_apply' _ _ _
  have hp : 0 < b - a := by omega
  have hprior' := fun t ↦ (hprior t).le
  have hstep : ∀ k, expectedGain G (senderResponse G (x k)) (x k) ≤
      expectedGain G (senderResponse G (x k)) (x (k + 1)) ∧
      expectedGain G (senderResponse G (x k)) (x (k + 1)) ≤
        expectedGain G (senderResponse G (x (k + 1))) (x (k + 1)) := fun k ↦
    ⟨hsucc k ▸ expectedGain_le_receiverResponse hprior' _ _,
      expectedGain_le_senderResponse hprior' (senderResponse_subset _) _⟩
  have hmono : Monotone fun k ↦ expectedGain G (senderResponse G (x k)) (x k) :=
    monotone_nat_of_le_succ fun k ↦ (hstep k).1.trans (hstep k).2
  have hconst := eq_zero_of_monotone_of_periodic hmono
    (hper.comp fun y ↦ expectedGain G (senderResponse G y) y) hp
  have hEq : ∀ k, expectedGain G (senderResponse G (x k)) (x (k + 1)) =
      expectedGain G (senderResponse G (x (k + 1))) (x (k + 1)) := fun k ↦
    le_antisymm (hstep k).2 (((hconst (k + 1)).trans (hconst k).symm).le.trans (hstep k).1)
  have hsub : Monotone fun k ↦ senderResponse G (x k) := monotone_nat_of_le_succ fun k ↦
    Pi.le_def.mpr fun t ↦ senderResponse_subset_of_expectedGain_eq hprior (hEq k) t
  have h1 := eq_zero_of_monotone_of_periodic hsub (hper.comp (senderResponse G)) hp 1
  refine ⟨a + 1, ?_⟩
  change f (x 1) = x 1
  calc f (x 1) = receiverResponse G (senderResponse G (x 1)) := rfl
    _ = receiverResponse G (senderResponse G (x 0)) := congrArg _ h1
    _ = x 1 := (hsucc 0).symm

/-- The receiver chain of the heavy system reaches a fixed point (Theorem 3). -/
theorem exists_isFixedPt_receiverLevel (hprior : ∀ t, 0 < G.prior t) :
    ∃ n, IsFixedPt (receiverResponse G ∘ senderResponse G) (receiverLevel G n) :=
  exists_isFixedPt_iterate hprior _

/-- The sender chain of the heavy system reaches a fixed point (Theorem 3). -/
theorem exists_isFixedPt_senderLevel (hprior : ∀ t, 0 < G.prior t) :
    ∃ n, IsFixedPt (senderResponse G ∘ receiverResponse G) (senderLevel G n) := by
  obtain ⟨n, hn⟩ := exists_isFixedPt_iterate hprior (receiverResponse G G.trueMessages)
  have hsc : Semiconj (senderResponse G) (receiverResponse G ∘ senderResponse G)
      (senderResponse G ∘ receiverResponse G) := fun _ ↦ rfl
  refine ⟨n + 1, ?_⟩
  rw [senderLevel, iterate_succ_apply, comp_apply, ← (hsc.iterate_right n).eq]
  exact hn.map hsc

/-- Counting reasoning reaches a fixed point along the chain from the literal receiver, for every
denotation (Theorems 1 and 3). -/
theorem exists_isFixedPt_receiverChain (den : M → Finset T) :
    ∃ n, IsFixedPt (receiverStep den ∘ senderStep den) (receiverChain den n) := by
  let G : InterpGame T M := ⟨fun m t ↦ t ∈ den m, fun _ ↦ 1⟩
  have hden : G.trueStates = den := by ext; simp [G]
  have hprior : ∀ t, 0 < G.prior t := fun _ ↦ one_pos
  have hflat : ∀ t t', G.prior t = G.prior t' := fun _ _ ↦ rfl
  obtain ⟨n, hn⟩ := exists_isFixedPt_receiverLevel hprior
  refine ⟨n, ?_⟩
  rw [receiverLevel_eq_receiverChain hprior hflat, hden] at hn
  have hR : ∀ m, receiverChain den n m ⊆ G.trueStates m := hden ▸ receiverChain_subset den n
  rwa [IsFixedPt, comp_apply, senderResponse_eq_senderStep hR,
    receiverResponse_eq_receiverStep hprior hflat, hden] at hn

/-- Counting reasoning reaches a fixed point along the chain from the literal sender, for every
denotation (Theorems 1 and 3). -/
theorem exists_isFixedPt_senderChain (den : M → Finset T) :
    ∃ n, IsFixedPt (senderStep den ∘ receiverStep den) (senderChain den n) := by
  let G : InterpGame T M := ⟨fun m t ↦ t ∈ den m, fun _ ↦ 1⟩
  have hden : G.trueStates = den := by ext; simp [G]
  have hprior : ∀ t, 0 < G.prior t := fun _ ↦ one_pos
  have hflat : ∀ t t', G.prior t = G.prior t' := fun _ _ ↦ rfl
  obtain ⟨n, hn⟩ := exists_isFixedPt_senderLevel hprior
  refine ⟨n, ?_⟩
  rw [senderLevel_eq_senderChain hprior hflat, hden] at hn
  have hR : ∀ m, receiverStep den (senderChain den n) m ⊆ G.trueStates m := by
    rw [hden]; exact receiverStep_subset (senderChain_subset den n)
  rwa [IsFixedPt, comp_apply, receiverResponse_eq_receiverStep hprior hflat, hden,
    senderResponse_eq_senderStep hR, hden] at hn

end Convergence


/-- Under a competence prior that is nearly flat, the heavy receiver chain is the light chain
refined by fewest undecided alternatives, so the competence results below are predictions of the
heavy system. -/
theorem receiverLevel_ofTable_of_competencePrior {table : T → M → BeliefValue} {p : T → ℝ}
    (hp : CompetencePrior table p) (hpos : ∀ t, 0 < p t) (hnf : NearFlat (ofTable table p))
    (n : ℕ) : receiverLevel (ofTable table p) n =
      receiverChainBy (ofTable table p).trueStates
        (OrderDual.toDual ∘ uncertaintyCount table) n := by
  rw [receiverLevel_eq_receiverChainBy hpos hnf]
  exact congrFun (receiverChainBy_congr _ hp.argmax_eq) n

/-! ### Theorem 4: fixed points are perfect Bayesian equilibria -/

section Equilibrium

variable (G) in
/-- A sender strategy `σ`, a receiver strategy `ρ` and posterior beliefs `μ` form a perfect
Bayesian equilibrium when every message `σ` sends maximises, among all messages, the probability
that the receiver guesses the sender's state, every interpretation `ρ` chooses is a most
probable state under `μ`, and `μ` conditions the prior on `σ` after every message some state
sends. -/
structure IsPBE (σ : T → M → ℝ) (ρ : M → T → ℝ) (μ : M → StdSimplex ℝ T) : Prop where
  sender_rational : ∀ t m, 0 < σ t m → ∀ m', ρ m' t ≤ ρ m t
  receiver_rational : ∀ m t, 0 < ρ m t → t ∈ univ.argmax ⇑(μ m).weights
  consistent : ∀ m, (∃ t, σ t m ≠ 0) →
    ∀ t, (μ m).weights t = G.prior t * σ t m / ∑ s, G.prior s * σ s m

/-- The unbiased beliefs in a fixed point of the heavy system form a perfect Bayesian
equilibrium, with the Bayesian posterior after every message sent and the literal reading after
the others (Theorem 4). -/
theorem exists_isPBE_of_isFixedPt [Nonempty T] (hprior : ∀ t, 0 < G.prior t)
    {R : M → Finset T} (hR : IsFixedPt (receiverResponse G ∘ senderResponse G) R) :
    ∃ μ, IsPBE G (fun t ↦ (senderResponse G R t).uniform) (fun m ↦ (R m).uniform) μ := by
  set S := senderResponse G R
  have hRS : receiverResponse G S = R := hR
  have hRtrue : ∀ m, R m ⊆ G.trueStates m := fun m ↦
    hRS ▸ receiverResponse_subset hprior (senderResponse_subset R) m
  have hZ : ∀ m, inverse S m ≠ ∅ → 0 < ∑ s, G.prior s * (S s).uniform m := fun m hm ↦ by
    obtain ⟨s, hs⟩ := nonempty_iff_ne_empty.mpr hm
    exact sum_pos' (fun s _ ↦ mul_nonneg (hprior s).le uniform_nonneg)
      ⟨s, mem_univ s, mul_pos (hprior s) (uniform_pos_iff.mpr (mem_inverse.mp hs))⟩
  let lit (m : M) : Finset T := if (G.trueStates m).Nonempty then G.trueStates m else univ
  have hlit : ∀ m, (lit m).Nonempty := fun m ↦ by
    simp only [lit]; split_ifs with h; exacts [h, univ_nonempty]
  let post (m : M) (t : T) : ℝ := if inverse S m = ∅ then (lit m).uniform t
    else G.prior t * (S t).uniform m / ∑ s, G.prior s * (S s).uniform m
  have hpost : ∀ m, ∃ μm : StdSimplex ℝ T, ⇑μm.weights = post m := fun m ↦ by
    have : post m ∈ Set.range fun w : StdSimplex ℝ T ↦ ⇑w.weights := by
      rw [StdSimplex.range_toFun_comp_weights]
      refine ⟨Set.mem_iInter.2 fun t ↦ ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq, post]
        split_ifs with h
        exacts [uniform_nonneg, div_nonneg (mul_nonneg (hprior t).le uniform_nonneg) (hZ m h).le]
      · simp only [Set.mem_ofPred_eq, post]
        split_ifs with h
        · rw [sum_uniform, ite_eq_right (hlit m).ne_empty]
        · rw [← sum_div, div_self (hZ m h).ne']
    exact this
  choose μ hμ using hpost
  refine ⟨μ, fun t m hm m' ↦ ?_, fun m t ht ↦ ?_, fun m ⟨t₀, ht₀⟩ t ↦ ?_⟩
  · obtain ⟨-, hmax⟩ := mem_senderResponse.mp (uniform_pos_iff.mp hm)
    by_cases hm' : G.meaning m' t
    · exact hmax m' hm'
    · rw [uniform_of_notMem fun h ↦ hm' (G.mem_trueStates.mp (hRtrue m' h))]
      exact uniform_nonneg
  · have htR : t ∈ R m := uniform_pos_iff.mp ht
    rw [hμ]
    by_cases hs : inverse S m = ∅
    · have hRm : R m = G.trueStates m := by rw [← hRS, receiverResponse, ite_eq_left hs]
      have htm : t ∈ G.trueStates m := hRm ▸ htR
      have hlm : lit m = G.trueStates m := ite_eq_left ⟨t, htm⟩
      simp only [post, ite_eq_left hs, hlm]
      refine mem_argmax.mpr ⟨mem_univ t, fun t' _ ↦ ?_⟩
      rw [uniform_of_mem htm]
      by_cases ht' : t' ∈ G.trueStates m <;> simp [ht']
    · have hRm : R m = univ.argmax fun t ↦ G.prior t * (S t).uniform m := by
        rw [← hRS, receiverResponse, ite_eq_right hs]
      simp only [post, ite_eq_right hs]
      simp_rw [div_eq_mul_inv]
      change t ∈ univ.argmax ((fun x ↦ x * (∑ s, G.prior s * (S s).uniform m)⁻¹) ∘
        fun t ↦ G.prior t * (S t).uniform m)
      rw [argmax_comp_strictMono (strictMono_mul_right_of_pos (inv_pos.mpr (hZ m hs)))]
      exact hRm ▸ htR
  · have hs : inverse S m ≠ ∅ := fun h ↦ ht₀ (uniform_of_notMem fun hm ↦
      (eq_empty_iff_forall_notMem.mp h) t₀ (mem_inverse.mpr hm))
    rw [hμ]
    simp only [post, ite_eq_right hs]

end Equilibrium

end Heavy

/-! ### The free choice implicature in the heavy system (Appendix B.3) -/

namespace TwoDisjuncts

/-- With the flat priors of Figure 5 the heavy system's second receiver reads the disjunction
literally (137) and its fourth reads it as free choice (139). -/
theorem receiverLevel_free_choice :
    receiverLevel game 1 .either = {.onlyA, .onlyB, .both} ∧
      receiverLevel game 2 = fun m ↦ {freeChoiceReceiver m} := by
  have hprior : ∀ t, 0 < game.prior t := fun _ ↦ by norm_num [game, ofTable]
  rw [receiverLevel_eq_receiverChain hprior (fun _ _ ↦ rfl),
    receiverLevel_eq_receiverChain hprior (fun _ _ ↦ rfl)]
  exact ⟨receiverChain_one_either, free_choice.1⟩

end TwoDisjuncts

/-! ### Level-1 interpretation and exhaustification by minimal models (§10)

The first sophisticated receiver of the chain from the literal sender keeps the states where a
message is true that make fewest messages true (107); exhaustification by minimal models keeps
those minimal in the inclusion order on true messages. -/

section Exhaustification

variable {T M : Type*} [Fintype T] [Fintype M] [DecidableEq T] [DecidableEq M]

variable (G : InterpGame T M) in
/-- The alternatives of an interpretation game are the sets of states where its messages are
true. -/
def alternatives : Set (Set T) := Set.range fun m ↦ {t | G.meaning m t}

variable {G : InterpGame T M}

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
theorem leALT_alternatives_iff {t' t : T} :
    leALT (alternatives G) t' t ↔ G.trueMessages t' ⊆ G.trueMessages t := by
  simp only [leALT, alternatives, Set.forall_mem_range, subset_iff, InterpGame.mem_trueMessages]
  exact Iff.rfl

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
theorem ltALT_alternatives_iff {t' t : T} :
    ltALT (alternatives G) t' t ↔ G.trueMessages t' ⊂ G.trueMessages t := by
  rw [ltALT, leALT_alternatives_iff, leALT_alternatives_iff, ssubset_iff_subset_not_subset]

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
theorem mem_exhMW_alternatives {m : M} {t : T} :
    t ∈ exhMW (alternatives G) {t | G.meaning m t} ↔
      G.meaning m t ∧ ∀ t', G.meaning m t' → ¬ G.trueMessages t' ⊂ G.trueMessages t := by
  simp only [mem_exhMW, ltALT_alternatives_iff, Set.mem_ofPred_eq, not_exists, not_and]

/-- The first sophisticated receiver's reading of a message entails its exhaustification by
minimal models (Fact 1). -/
theorem coe_receiverStep_subset_exhMW (m : M) :
    ↑(receiverStep G.trueStates (inverse G.trueStates) m) ⊆
      exhMW (alternatives G) {t | G.meaning m t} := by
  intro t ht
  rw [mem_coe, receiverStep_inverse, mem_argmin] at ht
  simp only [inverse_trueStates] at ht
  refine mem_exhMW_alternatives.mpr ⟨G.mem_trueStates.mp ht.1, fun t' ht' hlt ↦ ?_⟩
  exact absurd (card_lt_card hlt) (not_lt.mpr (ht.2 t' (G.mem_trueStates.mpr ht')))

end Exhaustification

namespace TwoDisjuncts

/-- In the free choice game exhaustification by minimal models is the first sophisticated
receiver's reading, as footnote 37 says of all the examples, and not the second's (§10,
Figure 7). -/
theorem exhMW_eq_receiverStep (m : Message) :
    exhMW (alternatives game) {t | game.meaning m t} =
      ↑(receiverStep game.trueStates (inverse game.trueStates) m) := by
  ext t
  rw [mem_exhMW_alternatives, mem_coe]
  revert m t; decide

theorem exhMW_ne_receiverChain :
    exhMW (alternatives game) {t | game.meaning .either t} ≠
      ↑(receiverChain game.trueStates 1 .either) := by
  rw [exhMW_eq_receiverStep, Ne, coe_inj]; decide

end TwoDisjuncts

/-! ### Comparison of exhaustivity operators (Appendix A)

Exhaustification by minimal models entails innocent exclusion (Fact 3,
`Exhaustification.exhMW_subset_exhIE`). Fact 2 claims that the order on worlds, hence
exhaustification by minimal models, is invariant under adding an alternative whose truth value
the others determine; this holds when the determination is monotone, as for conjunctions in the
paper's example, and fails for the negation of an alternative. -/

section Appendix

variable {W : Type*} (ALT : Set (Set W)) (φ : Set W)

/-- `A` is monotonically determined by the alternatives when, whenever every alternative true at
`w` is true at `v`, `A` at `w` forces `A` at `v`. -/
def MonotoneDetermined (A : Set W) : Prop := ∀ w v, leALT ALT w v → w ∈ A → v ∈ A

/-- Adding a monotonically determined alternative leaves the order on worlds unchanged
(Fact 2). -/
theorem ltALT_insert_of_monotoneDetermined {A : Set W} (hA : MonotoneDetermined ALT A) :
    ltALT (insert A ALT) = ltALT ALT := by
  have key : ∀ w v, leALT (insert A ALT) w v ↔ leALT ALT w v := fun w v ↦
    ⟨fun h a ha ↦ h a (Set.mem_insert_of_mem _ ha),
     fun h a ha ↦ (Set.mem_insert_iff.mp ha).elim (fun e ↦ e ▸ hA w v h) (h a)⟩
  funext w v; simp only [ltALT, key]

/-- Exhaustification by minimal models ignores a monotonically determined alternative. -/
theorem exhMW_insert_of_monotoneDetermined {A : Set W} (hA : MonotoneDetermined ALT A) :
    exhMW (insert A ALT) φ = exhMW ALT φ := by
  unfold exhMW; rw [ltALT_insert_of_monotoneDetermined ALT hA]

/-- Fact 2 as printed fails. Over two worlds with one alternative, adding its negation, which
the alternative determines but not monotonically, removes the strict order between them. -/
theorem not_ltALT_insert_compl :
    ltALT ({(· = true)} : Set (Set Bool)) false true ∧
      ¬ ltALT (insert (· = false) {(· = true)}) false true := by
  refine ⟨⟨fun a ha h ↦ ?_, fun h ↦ ?_⟩, fun h ↦ ?_⟩
  · rw [Set.mem_singleton_iff] at ha; subst ha; exact absurd h Bool.false_ne_true
  · exact Bool.false_ne_true (h _ rfl rfl)
  · exact absurd (h.1 (· = false) (Set.mem_insert _ _) rfl) (by decide)

/-- A world is indistinguishable from a set of worlds by the alternatives when every alternative
true throughout the set is true at it and every alternative false throughout the set is false
at it. -/
def Indistinguishable (X : Set W) (w : W) : Prop :=
  ∀ a ∈ ALT, (X ⊆ a → w ∈ a) ∧ (X ⊆ aᶜ → w ∉ a)

/-- With finitely many alternatives, innocent exclusion keeps the prejacent worlds that the
alternatives cannot distinguish from the minimal worlds (Lemma 1). -/
theorem exhIE_eq_setOf_indistinguishable (hfin : ALT.Finite) :
    exhIE ALT φ = {w | w ∈ φ ∧ Indistinguishable ALT (exhMW ALT φ) w} := by
  rw [exhIE_eq_setOf_exhMW_subset_compl]
  ext w
  refine ⟨fun ⟨hw, h⟩ ↦ ⟨hw, fun a ha ↦ ⟨fun hX ↦ ?_, h a ha⟩⟩,
    fun ⟨hw, h⟩ ↦ ⟨hw, fun a ha ↦ (h a ha).2⟩⟩
  obtain ⟨u, hu, huw⟩ := exists_isMinimal_le ALT φ hfin hw
  exact huw a ha (hX hu)

end Appendix

/-! The paper's example (108)–(113): "A or B" with and without the conjunctive alternative. -/

namespace DisjunctionOperators

/-- A world is a pair of truth values for `A` and `B`, and `A` is the set of worlds where the
first is true. -/
def A : Set (Bool × Bool) := {w | w.1}

/-- `B` is the set of worlds where the second truth value is true. -/
def B : Set (Bool × Bool) := {w | w.2}

/-- These are the alternatives (109a). -/
def alt₁ : Set (Set (Bool × Bool)) := {A, B, A ∪ B}

/-- The alternatives (109b) add the conjunction. -/
def alt₂ : Set (Set (Bool × Bool)) := insert (A ∩ B) alt₁

theorem exhMW_alt₁ : exhMW alt₁ (A ∪ B) = {(true, false), (false, true)} := by
  ext ⟨a, b⟩
  simp only [mem_exhMW, ltALT, leALT_iff, alt₁, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, A, B, Set.mem_union, Set.mem_ofPred_eq, Prod.exists,
    Bool.exists_bool, Prod.mk.injEq]
  cases a <;> cases b <;> simp

theorem exhMW_alt₂ : exhMW alt₂ (A ∪ B) = exhMW alt₁ (A ∪ B) :=
  exhMW_insert_of_monotoneDetermined _ _ fun _ _ h hw ↦
    ⟨h A (by simp [alt₁]) hw.1, h B (by simp [alt₁]) hw.2⟩

/-- The minimal-models exhaustifier does not see the conjunctive alternative and agrees with
innocent exclusion over the larger set, while innocent exclusion over the smaller set excludes
nothing (113). -/
theorem exhaustivity_operators :
    exhMW alt₁ (A ∪ B) = exhMW alt₂ (A ∪ B) ∧ exhMW alt₂ (A ∪ B) = exhIE alt₂ (A ∪ B) ∧
      exhIE alt₂ (A ∪ B) ⊂ exhIE alt₁ (A ∪ B) := by
  have h₁ : exhIE alt₁ (A ∪ B) = A ∪ B := by
    rw [exhIE_eq_setOf_exhMW_subset_compl, exhMW_alt₁]
    ext ⟨a, b⟩
    cases a <;> cases b <;> simp [alt₁, A, B, Set.subset_def, Set.mem_ofPred_eq]
  have h₂ : exhIE alt₂ (A ∪ B) = {(true, false), (false, true)} := by
    rw [exhIE_eq_setOf_exhMW_subset_compl, exhMW_alt₂, exhMW_alt₁]
    ext ⟨a, b⟩
    cases a <;> cases b <;> simp [alt₂, alt₁, A, B, Set.subset_def, Set.mem_ofPred_eq]
  refine ⟨exhMW_alt₂.symm, by rw [exhMW_alt₂, exhMW_alt₁, h₂], ?_⟩
  rw [h₁, h₂, Set.ssubset_iff_subset_ne]
  refine ⟨fun w hw ↦ ?_, fun h ↦ ?_⟩
  · rcases hw with rfl | rfl <;> simp [A, B]
  · have : ((true, true) : Bool × Bool) ∈ A ∪ B := by simp [A]
    rw [← h] at this
    simp at this

end DisjunctionOperators

end Franke2011
