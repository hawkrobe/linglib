import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Linglib.Core.Order.Argmax
import Linglib.Pragmatics.SignalingGame.Interpretation
import Linglib.Semantics.Exhaustification.Operators.Basic
import Linglib.Data.Examples.Franke2011

/-!
# [franke-2011]: Quantity implicatures, exhaustive interpretation, and rational conversation

Quantity implicatures as rational behaviour in an interpretation game
(`InterpGame`): the context of an utterance is a signaling game whose states
are the belief-value vectors over the alternatives (§6) and whose solution is
*iterated best response* — level-0 players stick to conventional meaning,
level-(k+1) players best-respond to an unbiased belief in level-k behaviour,
and truth is kept ceteris paribus (§8). The "light system" computes the
reasoning by counting: a level-(k+1) sender in `t` picks the message with
fewest level-k interpretations (eq. (76)), a receiver of `m` the state with
fewest level-k messages (eq. (77)); surprise messages and uninducible
interpretations fall back to the literal level. Both reasoning chains — from
the naive sender `S₀` and from the naive receiver `R₀` — are run on the
paper's games by `decide`, reproducing Figures 7–14, 16 and 17: free choice,
simplification of disjunctive antecedents and the base-level conjunctive
reading of plain disjunction are one and the same game (tables (84)–(86)),
epistemic games deliver ignorance implicatures, conjunctive alternatives
deliver exclusivity, and priors implement competence lexicographically.

The "heavy system" (Appendix B) is the same dynamics over behavioural
strategies: a level-(k+1) sender is uniform over her optimal messages
(`bestResponse`), a receiver is uniform over the maximum-a-posteriori states
(`hearerBR`), surprise messages interpreted literally. Theorem 1 identifies
the two systems under flat priors (`receiverLevel_isUniformOver`), Theorem 2
the lexicographic reading of near-flat priors (`receiverResponse_nearFlat`),
Lemma 3 and Theorem 3 give convergence through the monotone expected gain
(`eg_monotone`, `receiverLevel_reaches_fixedPoint`), and Theorem 4 reads the
fixed point as a perfect Bayesian equilibrium (`isPBE_of_fixedPoint`).

§10 relates the model to exhaustive interpretation: level-1 interpretation is
contained in minimal-models exhaustification ([vanrooij-schulz-2004]; Fact 1,
`receiver1_subset_exhMW`), and in general strictly (`R₁ ≠ R₂` in the
free-choice game). Appendix A compares `exhMW` with [fox-2007]'s innocent
exclusion `exhIE` on the substrate of [spector-2016]: Fact 3 is
`Exhaustification.exhMW_entails_exhIE`, Lemma 1 is
`exhIE_eq_exhMW_indistinguishable`, and Fact 2 holds for alternatives that are
*monotonically* determined by the others (`ltALT_insert_of_monotoneDetermined`)
but not, as printed, for every truth-determined alternative
(`not_ltALT_insert_compl`: adding the negation of an alternative changes the
order). Theorem 2's condition (132) is stated with the inequality the proof
requires, `Pr(t_min)/Pr(t_max) > (|M|-1)/|M|`; the paper prints it reversed.
The paper's example sentences are `Examples.ex4` through `Examples.ex99`.

## Main results

* `senderStep`, `receiverStep`, `receiverChain`, `senderChain` — the light
  system (76)–(77) and its two reasoning chains.
* `receiverChain_subset_trueStates`, `senderChain_subset_trueMessages` — Lemma 2:
  truth is preserved at every level.
* `TwoDisjuncts.receiverChain_two`, `TwoDisjuncts.senderChain_two` — Figure 7:
  free choice / SDA / conjunctive disjunction.
* `SomeAllEpistemic.receiver_general`, `.receiver_competent`,
  `.receiver_incompetent` — Figures 8–9: general, strong and weak epistemic
  implicature from the prior.
* `DisjunctionEpistemic.receiver_ignorance` — Figure 10: ignorance implicature.
* `DisjunctionConj.receiver_surprise`, `FreeChoiceConj.receiver_fixed`,
  `SdaConj.receiver_fixed`, `DisjunctionConjEpistemic.receiver_exclusivity` —
  Figures 11–14: exclusivity with conjunctive alternatives.
* `EntailingDisjuncts.receiver_fixed`, `GroupPermission.receiver_mixed`,
  `GroupPermission.receiver_pruned` — Figures 16–17.
* `receiver1_subset_exhMW` — Fact 1.
* `receiverLevel_isUniformOver` — Theorem 1; `receiverResponse_nearFlat` —
  Theorem 2; `receiverLevel_reaches_fixedPoint` — Theorem 3;
  `isPBE_of_fixedPoint` — Theorem 4.
-/

namespace Franke2011

open Exhaustification

/-! ### Interpretation games from belief-value tables

A base-level game distinguishes the truth-value vectors of the alternatives
within the target sentence (eq. (61)); an epistemic game the belief-value
vectors (eq. (66)), with three values — believed true, believed false,
uncertain (fn. 4). A message is true at a state when the state believes it
true. -/

/-- The three belief values of fn. 4: believed true (`1`), believed false
(`0`), uncertain (`u`). Base-level states use only the first two. -/
inductive BeliefValue where
  | yes
  | no
  | unc
  deriving DecidableEq, Fintype, Repr

variable {T M : Type*} [Fintype T] [Fintype M] [DecidableEq T] [DecidableEq M]

/-- The interpretation game of a belief-value table: `m` is true at `t` iff
`t` believes `m` true. -/
def ofTable (table : T → M → BeliefValue) (prior : T → ℚ) : InterpGame T M where
  meaning m t := table t m = .yes
  prior := prior

/-- The number of alternatives a state is undecided about. -/
def uncertaintyCount (table : T → M → BeliefValue) (t : T) : ℕ :=
  (Finset.univ.filter λ m => table t m = .unc).card

/-- The competence assumption (67): the prior strictly decreases in the number
of undecided alternatives. -/
def CompetencePrior (table : T → M → BeliefValue) (prior : T → ℚ) : Prop :=
  ∀ t t', uncertaintyCount table t < uncertaintyCount table t' → prior t' < prior t

/-- The incompetence assumption (68): the prior strictly increases in the number
of undecided alternatives. -/
def IncompetencePrior (table : T → M → BeliefValue) (prior : T → ℚ) : Prop :=
  ∀ t t', uncertaintyCount table t < uncertaintyCount table t' → prior t < prior t'

/-! ### The light system

Player types are sets of pure strategies, written as correspondences: a
receiver type `R : M → Finset T`, a sender type `S : T → Finset M`. Level 0 is
conventional meaning (73). A level-(k+1) sender in `t` chooses among the
messages that can induce `t` those with fewest interpretations (76) — the
chance of being understood is `1/|R m|`, eq. (129) — and if no message can
induce `t` she sends any true message; dually for the receiver (77), who
interprets a surprise message literally. -/

variable (G : InterpGame T M)

/-- The level-(k+1) sender type from the level-k receiver type (76). -/
def senderStep (R : M → Finset T) (t : T) : Finset M :=
  let inducing := Finset.univ.filter λ m => t ∈ R m
  if inducing = ∅ then G.trueMessages t else inducing.argmin λ m => (R m).card

/-- The level-(k+1) receiver type from the level-k sender type (77). -/
def receiverStep (S : T → Finset M) (m : M) : Finset T :=
  let senders := Finset.univ.filter λ t => m ∈ S t
  if senders = ∅ then G.trueStates m else senders.argmin λ t => (S t).card

/-- The chain starting from the naive receiver: `receiverChain n` is `R₂ₙ`. -/
def receiverChain : ℕ → M → Finset T
  | 0 => G.trueStates
  | n + 1 => receiverStep G (senderStep G (receiverChain n))

/-- The chain starting from the naive sender: `senderChain n` is `S₂ₙ`. -/
def senderChain : ℕ → T → Finset M
  | 0 => G.trueMessages
  | n + 1 => senderStep G (receiverStep G (senderChain n))

/-- A sender–receiver pair of types that reproduces itself. -/
def IsLightFixedPoint (S : T → Finset M) (R : M → Finset T) : Prop :=
  senderStep G R = S ∧ receiverStep G S = R

/-- Near-flat priors (83): among the light-system interpretations of a
non-surprise message, the a priori most likely states. -/
def receiverStepPrior (S : T → Finset M) (m : M) : Finset T :=
  if Finset.univ.filter (λ t => m ∈ S t) = ∅ then G.trueStates m
  else (receiverStep G S m).argmax G.prior

/-- Nominal message costs (§9.2): among the light-system messages for an
inducible state, the cheapest. -/
def senderStepCost (cost : M → ℚ) (R : M → Finset T) (t : T) : Finset M :=
  if Finset.univ.filter (λ m => t ∈ R m) = ∅ then G.trueMessages t
  else (senderStep G R t).argmax λ m => -cost m

omit [Fintype T] in
theorem mem_senderStep {R : M → Finset T} {t : T} {m : M} :
    m ∈ senderStep G R t ↔
      if Finset.univ.filter (λ m => t ∈ R m) = ∅ then G.meaning m t
      else t ∈ R m ∧ ∀ m', t ∈ R m' → (R m).card ≤ (R m').card := by
  simp only [senderStep]; split_ifs <;> simp

omit [Fintype M] in
theorem mem_receiverStep {S : T → Finset M} {m : M} {t : T} :
    t ∈ receiverStep G S m ↔
      if Finset.univ.filter (λ t => m ∈ S t) = ∅ then G.meaning m t
      else m ∈ S t ∧ ∀ t', m ∈ S t' → (S t).card ≤ (S t').card := by
  simp only [receiverStep]; split_ifs <;> simp

/-- Lemma 2, sender half: a level-(k+1) sender only sends true messages,
given that the level-k receiver only assigns true interpretations. -/
theorem senderStep_subset_trueMessages {R : M → Finset T} (hR : ∀ m, R m ⊆ G.trueStates m)
    (t : T) : senderStep G R t ⊆ G.trueMessages t := by
  intro m hm
  rw [mem_senderStep] at hm
  split_ifs at hm with h
  · exact G.mem_trueMessages.mpr hm
  · exact G.mem_trueMessages.mpr (G.mem_trueStates.mp (hR m hm.1))

/-- Lemma 2, receiver half. -/
theorem receiverStep_subset_trueStates {S : T → Finset M} (hS : ∀ t, S t ⊆ G.trueMessages t)
    (m : M) : receiverStep G S m ⊆ G.trueStates m := by
  intro t ht
  rw [mem_receiverStep] at ht
  split_ifs at ht with h
  · exact G.mem_trueStates.mpr ht
  · exact G.mem_trueStates.mpr (G.mem_trueMessages.mp (hS t ht.1))

/-- Lemma 2: truth is preserved along the receiver chain. -/
theorem receiverChain_subset_trueStates (n : ℕ) (m : M) :
    receiverChain G n m ⊆ G.trueStates m := by
  induction n generalizing m with
  | zero => exact le_rfl
  | succ n ih =>
    exact receiverStep_subset_trueStates G (senderStep_subset_trueMessages G ih) m

/-- Lemma 2: truth is preserved along the sender chain. -/
theorem senderChain_subset_trueMessages (n : ℕ) (t : T) :
    senderChain G n t ⊆ G.trueMessages t := by
  induction n generalizing t with
  | zero => exact le_rfl
  | succ n ih =>
    exact senderStep_subset_trueMessages G (receiverStep_subset_trueStates G ih) t

/-! ### "Some" and "all" (Figure 4)

Two states within the denotation of "some" (`Examples.ex4`): some-but-not-all,
where only "some" is true, and all, where both are. -/

namespace SomeAll

inductive State where
  | someNotAll
  | all
  deriving DecidableEq, Fintype, Repr

inductive Message where
  | some
  | all
  deriving DecidableEq, Fintype, Repr

/-- The interpretation game of Figure 4. -/
def game : InterpGame State Message :=
  ofTable (λ t m => match t, m with
    | _, .some | .all, .all => .yes
    | .someNotAll, .all => .no) λ _ => 1 / 2

/-- The empirically correct play (69): "some" conveys some-but-not-all. -/
def receiver69 : Message → State
  | .some => .someNotAll
  | .all => .all

def sender69 : State → Message
  | .someNotAll => .some
  | .all => .all

/-- The reversed play (71): also a Nash equilibrium — equilibrium does not
select the attested reading. -/
def receiver71 : Message → State
  | .some => .all
  | .all => .someNotAll

def sender71 : State → Message
  | .someNotAll => .all
  | .all => .some

/-- Both chains reach (69) at level 2: the scalar implicature. -/
theorem receiverChain_one :
    receiverChain game 1 = λ m => {receiver69 m} := by decide

theorem senderChain_one :
    senderChain game 1 = λ t => {sender69 t} := by decide

theorem fixed : IsLightFixedPoint game (λ t => {sender69 t}) (λ m => {receiver69 m}) := by
  unfold IsLightFixedPoint; decide

end SomeAll

/-! ### Two disjuncts (Figures 5 and 7; tables (84)–(86))

Alternatives `A`, `B` and `A ∨ B` give three states whether the disjunction
is plain (`Examples.ex8`), under a possibility modal (`Examples.ex12a`), or in a
conditional antecedent (`Examples.ex18`): one game, three constructions. Its
fixed point (82) maps the disjunction to the state where both disjuncts hold —
the free choice inference, simplification of disjunctive antecedents, and, at
base level, a conjunctive reading of plain disjunction (§9.2). -/

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

/-- The interpretation game of Figure 5. -/
def game : InterpGame State Message :=
  ofTable (λ t m => match t, m with
    | .onlyA, .first | .both, .first | .onlyB, .second | .both, .second | _, .either => .yes
    | _, _ => .no) λ _ => 1 / 3

/-- The target play (70) / (82). -/
def receiver70 : Message → State
  | .first => .onlyA
  | .second => .onlyB
  | .either => .both

def sender70 : State → Message
  | .onlyA => .first
  | .onlyB => .second
  | .both => .either

/-- The perverse Nash equilibrium (72), which no refinement rules out. -/
def receiver72 : Message → State
  | .first => .both
  | .second => .onlyB
  | .either => .onlyA

def sender72 : State → Message
  | .onlyA => .either
  | .onlyB => .second
  | .both => .first

/-- The receiver chain reaches (82) at `R₄` (Figure 7, lower strand). -/
theorem receiverChain_two : receiverChain game 2 = λ m => {receiver70 m} := by decide

/-- On the way, `R₂` finds the disjunction a surprise message and reads it
literally (eq. (137)). -/
theorem receiverChain_one_either : receiverChain game 1 .either = {.onlyA, .onlyB, .both} := by
  decide

/-- The sender chain reaches (82) at `S₄` (Figure 7, upper strand). -/
theorem senderChain_two : senderChain game 2 = λ t => {sender70 t} := by decide

/-- `R₁` on the sender chain reads the disjunction as either single-disjunct
state (eq. (141)) — the minimal-models exhaustification (50) — while `R₂` on
the receiver chain does not: `R₁ ≠ R₂` (§10). -/
theorem receiver1_either : receiverStep game (senderChain game 0) .either = {.onlyA, .onlyB} := by
  decide

theorem fixed : IsLightFixedPoint game (λ t => {sender70 t}) (λ m => {receiver70 m}) := by
  unfold IsLightFixedPoint; decide

end TwoDisjuncts

/-! ### Epistemic "some"/"all" (Figures 6, 8, 9)

Three speaker belief states within belief in "some": believes not-all,
believes all, uncertain about all. With flat priors the general epistemic
implicature; with competence (67) the strong, with incompetence (68) the
weak one. -/

namespace SomeAllEpistemic

/-- States named by their belief-value vectors over (some, all). -/
inductive State where
  | t10
  | t11
  | t1u
  deriving DecidableEq, Fintype, Repr

open SomeAll (Message)

def table : State → Message → BeliefValue
  | _, .some => .yes
  | .t10, .all => .no
  | .t11, .all => .yes
  | .t1u, .all => .unc

/-- Flat priors: the game of Figure 6 with `a = b`. -/
def game : InterpGame State Message := ofTable table λ _ => 1 / 3

/-- Competent speaker: the uncertain state is less likely (`a > b`). -/
def competent : InterpGame State Message :=
  ofTable table λ t => if t = .t1u then 1 / 5 else 2 / 5

/-- Incompetent speaker: the uncertain state is more likely. -/
def incompetent : InterpGame State Message :=
  ofTable table λ t => if t = .t1u then 3 / 5 else 1 / 5

theorem competent_prior : CompetencePrior table competent.prior := by
  unfold CompetencePrior uncertaintyCount; decide +kernel

theorem incompetent_prior : IncompetencePrior table incompetent.prior := by
  unfold IncompetencePrior uncertaintyCount; decide +kernel

/-- Figure 8: "some" conveys that the speaker does not believe "all" —
believes not-all or is uncertain. -/
theorem receiver_general : receiverChain game 1 .some = {.t10, .t1u} := by decide

theorem sender_general : receiverStep game (senderChain game 0) .some = {.t10, .t1u} := by
  decide

/-- Figure 9: under competence, "some" conveys that the speaker believes
not-all (the strong epistemic implicature). -/
theorem receiver_competent :
    receiverStepPrior competent (senderStep competent competent.trueStates) .some = {.t10} := by
  decide +kernel

/-- Under incompetence, "some" conveys that the speaker is uncertain about
"all" (the weak epistemic implicature). -/
theorem receiver_incompetent :
    receiverStepPrior incompetent (senderStep incompetent incompetent.trueStates) .some =
      {.t1u} := by
  decide +kernel

end SomeAllEpistemic

/-! ### Epistemic disjunction (tables (87)–(88), Figure 10)

Six belief states within belief in `A ∨ B`. The disjunction is interpreted, in
every chain and under every competence assumption, as the state uncertain
about both disjuncts: the ignorance implicature. -/

namespace DisjunctionEpistemic

/-- States named by belief-value vectors over (A, B, A ∨ B). -/
inductive State where
  | t101
  | t011
  | t111
  | t1u1
  | tu11
  | tuu1
  deriving DecidableEq, Fintype, Repr

open TwoDisjuncts (Message)

def table : State → Message → BeliefValue
  | _, .either => .yes
  | .t101, .first | .t111, .first | .t1u1, .first => .yes
  | .t011, .first => .no
  | .tu11, .first | .tuu1, .first => .unc
  | .t011, .second | .t111, .second | .tu11, .second => .yes
  | .t101, .second => .no
  | .t1u1, .second | .tuu1, .second => .unc

def game : InterpGame State Message := ofTable table λ _ => 1 / 6

def competent : InterpGame State Message :=
  ofTable table λ t => match t with
    | .t101 | .t011 | .t111 => 3 / 12
    | .t1u1 | .tu11 => 1 / 12
    | .tuu1 => 1 / 12

/-- Figure 10: on the sender chain the disjunction is read as uncertainty
about both disjuncts from `R₁` on, and a single disjunct as belief in it
without belief in the other. -/
theorem receiver_ignorance :
    receiverStep game (senderChain game 1) = λ m => match m with
      | .first => {.t101, .t1u1}
      | .second => {.t011, .tu11}
      | .either => {.tuu1} := by
  decide

theorem receiver_ignorance_one : receiverStep game (senderChain game 0) .either = {.tuu1} := by
  decide

theorem receiverChain_ignorance : receiverChain game 1 .either = {.tuu1} := by decide

/-- Under competence a single disjunct conveys that the speaker knows the other
is false. -/
theorem receiver_competent :
    receiverStepPrior competent (senderChain competent 1) .first = {.t101} := by
  decide +kernel

end DisjunctionEpistemic

/-! ### Disjunction with a conjunctive alternative (tables (89)–(92), Figures 11–14) -/

/-! Plain disjunction at base level with `A ∧ B` among the alternatives:
the disjunction becomes a surprise message, read literally (Figure 11). -/

namespace DisjunctionConj

open TwoDisjuncts (State)

inductive Message where
  | first
  | second
  | both
  | either
  deriving DecidableEq, Fintype, Repr

def game : InterpGame State Message :=
  ofTable (λ t m => match t, m with
    | _, .either | .both, _ | .onlyA, .first | .onlyB, .second => .yes
    | _, _ => .no) λ _ => 1 / 3

theorem receiver_surprise :
    receiverChain game 1 = λ m => match m with
      | .first => {.onlyA}
      | .second => {.onlyB}
      | .both => {.both}
      | .either => {.onlyA, .onlyB, .both} := by
  decide

theorem receiverChain_fixed : receiverChain game 2 = receiverChain game 1 := by decide

end DisjunctionConj

/-! Free choice with the conjunctive alternative (table (90), Figure 12): the
state where both are permitted but not jointly is now possible, and the fixed
point delivers free choice plus the exclusivity implicature. -/

namespace FreeChoiceConj

/-- States named by truth vectors over (◇A, ◇B, ◇(A ∧ B), ◇(A ∨ B)). -/
inductive State where
  | t1001
  | t0101
  | t1111
  | t1101
  deriving DecidableEq, Fintype, Repr

open DisjunctionConj (Message)

def game : InterpGame State Message :=
  ofTable (λ t m => match t, m with
    | _, .either | .t1111, _ | .t1001, .first | .t0101, .second
    | .t1101, .first | .t1101, .second => .yes
    | _, _ => .no) λ _ => 1 / 4

theorem receiver_fixed :
    receiverChain game 2 = λ m => match m with
      | .first => {.t1001}
      | .second => {.t0101}
      | .both => {.t1111}
      | .either => {.t1101} := by
  decide

theorem receiverChain_stable : receiverChain game 3 = receiverChain game 2 := by decide +kernel

end FreeChoiceConj

/-! Simplification of disjunctive antecedents with the conjunctive
alternative (table (91), Figure 13): six states, and the fixed point after
`R₄` gives SDA together with the exclusivity implicature. -/

namespace SdaConj

/-- States named by truth vectors over (A > C, B > C, (A ∧ B) > C, (A ∨ B) > C). -/
inductive State where
  | t1001
  | t0101
  | t1011
  | t0111
  | t1101
  | t1111
  deriving DecidableEq, Fintype, Repr

open DisjunctionConj (Message)

def game : InterpGame State Message :=
  ofTable (λ t m => match t, m with
    | _, .either => .yes
    | .t1001, .first | .t1011, .first | .t1101, .first | .t1111, .first => .yes
    | .t0101, .second | .t0111, .second | .t1101, .second | .t1111, .second => .yes
    | .t1011, .both | .t0111, .both | .t1111, .both => .yes
    | _, _ => .no) λ _ => 1 / 6

theorem receiver_fixed : receiverChain game 2 .either = {.t1101} := by decide

theorem receiverChain_stable : receiverChain game 3 = receiverChain game 2 := by decide +kernel

end SdaConj

/-! Epistemic disjunction with the conjunctive alternative (table (92),
Figure 14): without competence the disjunction conveys that the speaker does
not believe `A ∧ B`; with competence that she believes it false; with
incompetence that she is uncertain. -/

namespace DisjunctionConjEpistemic

/-- States named by belief-value vectors over (A, B, A ∧ B, A ∨ B). -/
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

def game : InterpGame State Message := ofTable table λ _ => 1 / 7

def competent : InterpGame State Message :=
  ofTable table λ t => match t with
    | .t1001 | .t0101 | .t1111 => 4 / 20
    | .tuu01 | .t1uu1 | .tu1u1 => 2 / 20
    | .tuuu1 => 1 / 20

def incompetent : InterpGame State Message :=
  ofTable table λ t => match t with
    | .t1001 | .t0101 | .t1111 => 1 / 20
    | .tuu01 | .t1uu1 | .tu1u1 => 2 / 20
    | .tuuu1 => 6 / 20

theorem receiver_exclusivity :
    receiverStep game (senderChain game 1) .either = {.tuu01, .tuuu1} := by decide

theorem receiver_competent :
    receiverStepPrior competent (senderChain competent 1) .either = {.tuu01} := by
  decide +kernel

theorem receiver_incompetent :
    receiverStepPrior incompetent (senderChain incompetent 1) .either = {.tuuu1} := by
  decide +kernel

end DisjunctionConjEpistemic

/-! ### Entailing disjuncts (table (97), Figure 16)

"John or (John and Mary)" (`Examples.ex95a`) is truth-conditionally "John", yet
conveys that the speaker considers Mary's coming possible. With the disjunction nominally
costlier than its equivalent and a competent speaker, the receiver chain
reaches the reading `t[1,u,1]` for the disjunction. -/

namespace EntailingDisjuncts

open SomeAllEpistemic (State)

inductive Message where
  | john
  | johnAndMary
  | johnOrBoth
  deriving DecidableEq, Fintype, Repr

def table : State → Message → BeliefValue
  | _, .john | _, .johnOrBoth => .yes
  | .t10, .johnAndMary => .no
  | .t11, .johnAndMary => .yes
  | .t1u, .johnAndMary => .unc

def game : InterpGame State Message :=
  ofTable table λ t => if t = .t1u then 1 / 5 else 2 / 5

/-- The disjunction is nominally costlier than its equivalent. -/
def cost : Message → ℚ
  | .johnOrBoth => 1
  | _ => 0

/-- One round of the receiver chain with costs and priors as secondary criteria. -/
def step (R : Message → Finset State) : Message → Finset State :=
  receiverStepPrior game (senderStepCost game cost R)

theorem receiver_fixed :
    step (step game.trueStates) = λ m => match m with
      | .john => {.t10}
      | .johnAndMary => {.t11}
      | .johnOrBoth => {.t1u} := by
  decide +kernel

theorem receiver_stable : step (step (step game.trueStates)) = step (step game.trueStates) := by
  decide +kernel

end EntailingDisjuncts

/-! ### Universal free choice (tables (101)–(102), Figure 17)

"Everybody may take an apple or a pear" (`Examples.ex99`) with alternatives
"everybody may take an apple/a pear": the full game reads the sentence as a mixed group; pruning
the mixed state by group homogeneity restores universal free choice. -/

namespace GroupPermission

/-- States named by truth vectors over (∀◇A, ∀◇B, ∀◇(A ∨ B)). -/
inductive State where
  | t101
  | t011
  | t111
  | t001
  deriving DecidableEq, Fintype, Repr

open TwoDisjuncts (Message)

def table : State → Message → BeliefValue
  | _, .either => .yes
  | .t101, .first | .t111, .first => .yes
  | .t011, .second | .t111, .second => .yes
  | _, _ => .no

def game : InterpGame State Message := ofTable table λ _ => 1 / 4

/-- Figure 17: the mixed-group reading. -/
theorem receiver_mixed : receiverStep game (senderChain game 0) .either = {.t001} := by decide

/-- The pruned game (102), without the mixed state. -/
def pruned : InterpGame TwoDisjuncts.State Message := TwoDisjuncts.game

/-- Pruned, the sentence conveys that everybody may take either. -/
theorem receiver_pruned : receiverStep pruned (senderChain pruned 1) .either = {.both} := by
  decide

end GroupPermission

/-! ### The heavy system (Appendix B.1)

Behavioural strategies: a sender `T → M → ℚ`, a receiver `M → T → ℚ`. The
unbiased belief in a set of pure strategies is the uniform behavioural
strategy over it ((115), (118)). Under the matching utilities of an
interpretation game the sender's expected utility of `m` in `t` is the
receiver's probability of `t` after `m`, so a level-(k+1) sender is uniform
over the messages maximising it ((116)–(117)); a level-(k+1) receiver is
uniform over the maximum-a-posteriori states ((119)–(122)), and reads a
surprise message — one no state sends — literally, by the truth ceteris
paribus assumption. -/

/-- Maximal receiver probability of `t` over the true messages, `0` if none. -/
def maxUtility (H : M → T → ℚ) (t : T) : ℚ := (G.trueMessages t).fold max 0 λ m => H m t

/-- The true messages attaining `maxUtility` — the level-(k+1) sender's
choices in `t` (116). -/
def optimalMessages (H : M → T → ℚ) (t : T) : Finset M :=
  (G.trueMessages t).filter λ m => H m t = maxUtility G H t

/-- The unbiased belief in the level-(k+1) sender type: uniform over the optimal
messages (117). -/
def senderResponse (H : M → T → ℚ) (t : T) (m : M) : ℚ :=
  if m ∈ optimalMessages G H t then (1 : ℚ) / (optimalMessages G H t).card else 0

/-- The unbiased belief in the level-(k+1) receiver type: uniform over the
states maximising `Pr(t) · S(t, m)`, the posterior (119)–(120) up to
normalisation; a surprise message is read literally (122). -/
def receiverResponse (S : T → M → ℚ) (m : M) (t : T) : ℚ :=
  let w : T → ℚ := λ s => S s m * G.prior s
  let maxW := Finset.univ.fold max 0 w
  if maxW = 0 then G.literal m t
  else if w t = maxW then (1 : ℚ) / (Finset.univ.filter λ s => w s = maxW).card else 0

/-- The receiver levels of the heavy system starting from the literal
receiver: `receiverLevel n` is `R₂ₙ`. -/
def receiverLevel : ℕ → M → T → ℚ
  | 0 => G.literal
  | n + 1 => receiverResponse G (senderResponse G (receiverLevel n))

/-- A receiver strategy the heavy dynamics reproduce. -/
def IsFixedPoint (H : M → T → ℚ) : Prop := receiverResponse G (senderResponse G H) = H

/-- Expected gain (144): the probability of successful communication. -/
def expectedGain (S : T → M → ℚ) (H : M → T → ℚ) : ℚ :=
  ∑ t, G.prior t * ∑ m, S t m * H m t

/-- A behavioural strategy uniform over a correspondence. -/
def IsUniformOver (H : M → T → ℚ) (R : M → Finset T) : Prop :=
  ∀ m t, H m t = if t ∈ R m then (1 : ℚ) / (R m).card else 0

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
theorem optimalMessages_subset (H : M → T → ℚ) (t : T) :
    optimalMessages G H t ⊆ G.trueMessages t :=
  Finset.filter_subset _ _

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
theorem maxUtility_nonneg (H : M → T → ℚ) (t : T) : 0 ≤ maxUtility G H t :=
  (Finset.le_fold_max 0).mpr (Or.inl le_rfl)

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
theorem le_maxUtility (H : M → T → ℚ) {t : T} {m : M} (hm : m ∈ G.trueMessages t) :
    H m t ≤ maxUtility G H t :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨m, hm, le_rfl⟩)

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
/-- For nonnegative receiver probabilities the optimal messages are the argmax
over the true messages. -/
theorem optimalMessages_eq_argmax (H : M → T → ℚ) (t : T) (hH : ∀ m, 0 ≤ H m t) :
    optimalMessages G H t = (G.trueMessages t).argmax (H · t) := by
  ext m
  simp only [optimalMessages, Finset.mem_filter, Finset.mem_argmax]
  refine and_congr_right λ hm =>
    ⟨λ h m' hm' => (le_maxUtility G H hm').trans_eq h.symm,
     λ h => le_antisymm (le_maxUtility G H hm) ?_⟩
  rcases Finset.fold_max_attained (G.trueMessages t) (λ m' => H m' t) 0 with h0 | ⟨x, hx, hfx⟩
  · exact (show maxUtility G H t = 0 from h0).trans_le (hH m)
  · exact (show maxUtility G H t = H x t from hfx).trans_le (h x hx)

omit [Fintype T] [DecidableEq T] in
theorem senderResponse_nonneg (H : M → T → ℚ) (t : T) (m : M) : 0 ≤ senderResponse G H t m := by
  unfold senderResponse; split_ifs <;> positivity

omit [Fintype T] [DecidableEq T] in
theorem senderResponse_le_one (H : M → T → ℚ) (t : T) (m : M) :
    senderResponse G H t m ≤ 1 := by
  unfold senderResponse; split_ifs with h
  · exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_pos.mpr ⟨m, h⟩) (Nat.cast_nonneg _)
  · exact zero_le_one

omit [Fintype T] [DecidableEq T] in
theorem senderResponse_pos_iff (H : M → T → ℚ) (t : T) (m : M) :
    0 < senderResponse G H t m ↔ m ∈ optimalMessages G H t := by
  unfold senderResponse; split_ifs with h
  · exact ⟨λ _ => h, λ _ => one_div_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨m, h⟩))⟩
  · exact ⟨λ h' => absurd h' (lt_irrefl 0), λ h' => absurd h' h⟩

omit [Fintype T] [DecidableEq T] in
theorem senderResponse_eq_zero_of_not_meaning (H : M → T → ℚ) {t : T} {m : M}
    (hm : ¬ G.meaning m t) : senderResponse G H t m = 0 := by
  rw [senderResponse, if_neg]
  exact λ h => hm (G.mem_trueMessages.mp (optimalMessages_subset G H t h))

omit [Fintype T] [DecidableEq T] in
theorem senderResponse_sum_le_one (H : M → T → ℚ) (t : T) :
    ∑ m, senderResponse G H t m ≤ 1 := by
  simp only [senderResponse]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (optimalMessages G H t).card with h | h
  · simp [h]
  · rw [mul_one_div_cancel (by exact_mod_cast h.ne')]

omit [Fintype M] [DecidableEq T] [DecidableEq M] in
theorem receiverResponse_nonneg (S : T → M → ℚ) (m : M) (t : T) :
    0 ≤ receiverResponse G S m t := by
  simp only [receiverResponse, InterpGame.literal]
  split_ifs <;> positivity

omit [Fintype M] [DecidableEq M] in
/-- The literal receiver is the unbiased belief in the level-0 receiver type. -/
theorem literal_isUniformOver : IsUniformOver G.literal G.trueStates := by
  intro m t
  simp only [InterpGame.literal, InterpGame.mem_trueStates, one_div]

/-! ### Theorem 1: the light system is the heavy system with flat priors -/

/-- The unbiased belief in the level-(k+1) sender type is uniform over the
light-system sender type (76). -/
theorem optimalMessages_eq_senderStep {H : M → T → ℚ} {R : M → Finset T}
    (hH : IsUniformOver H R) (hR : ∀ m, R m ⊆ G.trueStates m) (t : T) :
    optimalMessages G H t = senderStep G R t := by
  have hnn : ∀ m, 0 ≤ H m t := λ m => by rw [hH]; split_ifs <;> positivity
  rw [optimalMessages_eq_argmax G H t hnn]
  ext m
  rw [Finset.mem_argmax, mem_senderStep]
  split_ifs with hemp
  · have h0 : ∀ m', H m' t = 0 := λ m' => by
      rw [hH, if_neg]
      exact λ h => Finset.eq_empty_iff_forall_notMem.mp hemp m'
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    simp [h0, G.mem_trueMessages]
  · obtain ⟨m₀, hm₀⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
    have hm₀ : t ∈ R m₀ := (Finset.mem_filter.mp hm₀).2
    have hpos : ∀ m', t ∈ R m' → 0 < H m' t := λ m' h => by
      rw [hH, if_pos h]; exact one_div_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨t, h⟩))
    have htrue : ∀ m', t ∈ R m' → m' ∈ G.trueMessages t := λ m' h =>
      G.mem_trueMessages.mpr (G.mem_trueStates.mp (hR m' h))
    constructor
    · rintro ⟨hm, hmax⟩
      have hin : t ∈ R m := by
        by_contra hnot
        have : H m t = 0 := by rw [hH, if_neg hnot]
        exact absurd (hmax m₀ (htrue m₀ hm₀)) (not_le.mpr (this ▸ hpos m₀ hm₀))
      refine ⟨hin, λ m' hm' => ?_⟩
      have := hmax m' (htrue m' hm')
      rw [hH, hH, if_pos hm', if_pos hin] at this
      exact_mod_cast (one_div_le_one_div (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨t, hm'⟩))
        (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨t, hin⟩))).mp this
    · rintro ⟨hin, hmin⟩
      refine ⟨htrue m hin, λ m' _ => ?_⟩
      by_cases hm' : t ∈ R m'
      · rw [hH, hH, if_pos hm', if_pos hin]
        exact one_div_le_one_div_of_le (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨t, hin⟩))
          (by exact_mod_cast hmin m' hm')
      · rw [hH m', if_neg hm']; exact (hpos m hin).le

theorem senderResponse_isUniformOver {H : M → T → ℚ} {R : M → Finset T}
    (hH : IsUniformOver H R) (hR : ∀ m, R m ⊆ G.trueStates m) :
    ∀ t m, senderResponse G H t m =
      if m ∈ senderStep G R t then (1 : ℚ) / (senderStep G R t).card else 0 := by
  intro t m; simp only [senderResponse, optimalMessages_eq_senderStep G hH hR]

/-- The states maximising a weight that is positive exactly on a nonempty
set and inversely proportional to a size there. -/
theorem filter_eq_fold_max {A : Finset T} (hA : A.Nonempty) (w : T → ℚ)
    (k : T → ℕ) (c : ℚ) (hc : 0 < c) (hk : ∀ s ∈ A, 0 < k s)
    (hw : ∀ s, w s = if s ∈ A then c / k s else 0) :
    0 < Finset.univ.fold max 0 w ∧
      Finset.univ.filter (λ s => w s = Finset.univ.fold max 0 w) = A.argmin k := by
  obtain ⟨s₀, hs₀, hmin⟩ := A.exists_min_image k hA
  have hpos : ∀ s ∈ A, 0 < w s := λ s hs => by
    rw [hw, if_pos hs]; exact div_pos hc (Nat.cast_pos.mpr (hk s hs))
  have hle : ∀ s, w s ≤ w s₀ := λ s => by
    by_cases hs : s ∈ A
    · rw [hw s, hw s₀, if_pos hs, if_pos hs₀]
      exact div_le_div_of_nonneg_left hc.le (Nat.cast_pos.mpr (hk s₀ hs₀))
        (by exact_mod_cast hmin s hs)
    · rw [hw s, if_neg hs]; exact (hpos s₀ hs₀).le
  have hmax : Finset.univ.fold max 0 w = w s₀ := by
    refine le_antisymm ?_ ((Finset.le_fold_max _).mpr (Or.inr ⟨s₀, Finset.mem_univ _, le_rfl⟩))
    rcases Finset.fold_max_attained Finset.univ w 0 with h | ⟨x, _, hx⟩
    · rw [h]; exact (hpos s₀ hs₀).le
    · rw [hx]; exact hle x
  refine ⟨hmax ▸ hpos s₀ hs₀, ?_⟩
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_argmin, hmax]
  constructor
  · intro h
    have hs : s ∈ A := by
      by_contra hs
      rw [hw s, if_neg hs] at h; exact absurd (h ▸ hpos s₀ hs₀) (lt_irrefl (0 : ℚ))
    refine ⟨hs, λ s' hs' => ?_⟩
    rw [hw s, hw s₀, if_pos hs, if_pos hs₀, div_eq_mul_inv, div_eq_mul_inv] at h
    have := inv_inj.mp (mul_left_cancel₀ hc.ne' h)
    exact (Nat.cast_inj.mp this : k s = k s₀) ▸ hmin s' hs'
  · rintro ⟨hs, hmins⟩
    rw [hw s, hw s₀, if_pos hs, if_pos hs₀]
    congr 2
    exact_mod_cast le_antisymm (hmins s₀ hs₀) (hmin s hs)

omit [Fintype M] in
/-- The unbiased belief in the level-(k+1) receiver type under flat priors is
uniform over the light-system receiver type (77). -/
theorem receiverResponse_isUniformOver (hprior : ∀ t, 0 < G.prior t)
    (hflat : ∀ t t', G.prior t = G.prior t') {Sb : T → M → ℚ} {S : T → Finset M}
    (hSb : ∀ t m, Sb t m = if m ∈ S t then (1 : ℚ) / (S t).card else 0) :
    IsUniformOver (receiverResponse G Sb) (receiverStep G S) := by
  intro m t
  simp only [receiverResponse, receiverStep]
  set senders := Finset.univ.filter λ s => m ∈ S s with hsenders
  have hw : ∀ s, Sb s m * G.prior s = if s ∈ senders then G.prior t / (S s).card else 0 := by
    intro s
    by_cases h : m ∈ S s
    · simp only [hSb, hsenders, Finset.mem_filter, Finset.mem_univ, h, true_and, if_true,
        hflat s t]
      ring
    · simp [hSb, hsenders, h]
  by_cases hemp : senders = ∅
  · have h0 : ∀ s, Sb s m * G.prior s = 0 := λ s => by
      rw [hw, if_neg (hemp ▸ Finset.notMem_empty s)]
    have hmax : Finset.univ.fold max 0 (λ s => Sb s m * G.prior s) = 0 := by
      simp only [h0]; exact (Finset.fold_max_attained _ _ _).elim id λ ⟨_, _, h⟩ => h
    rw [if_pos hmax, if_pos hemp]
    simp only [InterpGame.literal, InterpGame.mem_trueStates, one_div]
  · obtain ⟨hpos, hfilt⟩ := filter_eq_fold_max (Finset.nonempty_iff_ne_empty.mpr hemp)
      (λ s => Sb s m * G.prior s) (λ s => (S s).card) (G.prior t) (hprior t)
      (λ s hs => Finset.card_pos.mpr ⟨m, (Finset.mem_filter.mp hs).2⟩) hw
    have hcond : ∀ s, Sb s m * G.prior s = Finset.univ.fold max 0 (λ s => Sb s m * G.prior s) ↔
        s ∈ senders.argmin λ s => (S s).card := λ s => by
      rw [← hfilt, Finset.mem_filter]; simp
    rw [if_neg hpos.ne', if_neg hemp, hfilt]
    by_cases ht : t ∈ senders.argmin λ s => (S s).card
    · rw [if_pos ((hcond t).mpr ht), if_pos ht]
    · rw [if_neg (mt (hcond t).mp ht), if_neg ht]

/-- Theorem 1: with flat priors the heavy receiver levels are the unbiased
beliefs in the light receiver chain. -/
theorem receiverLevel_isUniformOver (hprior : ∀ t, 0 < G.prior t)
    (hflat : ∀ t t', G.prior t = G.prior t') (n : ℕ) :
    IsUniformOver (receiverLevel G n) (receiverChain G n) := by
  induction n with
  | zero => exact literal_isUniformOver G
  | succ n ih =>
    exact receiverResponse_isUniformOver G hprior hflat
      (senderResponse_isUniformOver G ih (receiverChain_subset_trueStates G n))

/-- Theorem 1, sender side: the optimal messages at every heavy level are the
light sender type. -/
theorem optimalMessages_receiverLevel (hprior : ∀ t, 0 < G.prior t)
    (hflat : ∀ t t', G.prior t = G.prior t') (n : ℕ) (t : T) :
    optimalMessages G (receiverLevel G n) t = senderStep G (receiverChain G n) t :=
  optimalMessages_eq_senderStep G (receiverLevel_isUniformOver G hprior hflat n)
    (receiverChain_subset_trueStates G n) t

/-! ### Theorem 2: near-flat priors -/

/-- The near-flat condition (132), with the inequality the proof needs:
`Pr(t_min)/Pr(t_max) > (|M|-1)/|M|` (the paper prints it reversed). -/
def NearFlat : Prop :=
  ∀ t t', ((Fintype.card M : ℚ) - 1) * G.prior t' < Fintype.card M * G.prior t

/-- Theorem 2: under near-flat priors the heavy receiver is uniform over the
light receiver type refined lexicographically by the prior (83). -/
theorem receiverResponse_nearFlat (hprior : ∀ t, 0 < G.prior t) (hnf : NearFlat G)
    {Sb : T → M → ℚ} {S : T → Finset M}
    (hSb : ∀ t m, Sb t m = if m ∈ S t then (1 : ℚ) / (S t).card else 0) :
    IsUniformOver (receiverResponse G Sb) (receiverStepPrior G S) := by
  intro m t
  simp only [receiverResponse, receiverStepPrior]
  set senders := Finset.univ.filter λ s => m ∈ S s with hsenders
  have hw : ∀ s, Sb s m * G.prior s = if s ∈ senders then G.prior s / (S s).card else 0 := by
    intro s
    by_cases h : m ∈ S s
    · simp only [hSb, hsenders, Finset.mem_filter, Finset.mem_univ, h, true_and, if_true]
      ring
    · simp [hSb, hsenders, h]
  by_cases hemp : senders = ∅
  · have h0 : ∀ s, Sb s m * G.prior s = 0 := λ s => by
      rw [hw, if_neg (hemp ▸ Finset.notMem_empty s)]
    have hmax : Finset.univ.fold max 0 (λ s => Sb s m * G.prior s) = 0 := by
      simp only [h0]; exact (Finset.fold_max_attained _ _ _).elim id λ ⟨_, _, h⟩ => h
    rw [if_pos hmax, if_pos hemp]
    simp only [InterpGame.literal, InterpGame.mem_trueStates, one_div]
  · -- the weight is maximised exactly on the prior-lexicographic refinement of the argmin
    have hcard : ∀ s ∈ senders, 0 < (S s).card := λ s hs =>
      Finset.card_pos.mpr ⟨m, (Finset.mem_filter.mp hs).2⟩
    have hle : ∀ s ∈ senders, (S s).card ≤ Fintype.card M := λ s _ =>
      Finset.card_le_univ _
    -- fewer messages beats any prior difference
    have hlt : ∀ s₁ ∈ senders, ∀ s₂ ∈ senders, (S s₁).card < (S s₂).card →
        G.prior s₂ / (S s₂).card < G.prior s₁ / (S s₁).card := by
      intro s₁ h₁ s₂ h₂ hk
      have k₁ := hcard s₁ h₁; have k₂ := hcard s₂ h₂; have hM := hle s₂ h₂
      have hnf' := hnf s₁ s₂
      have p₁ := hprior s₁; have p₂ := hprior s₂
      rw [div_lt_div_iff₀ (by exact_mod_cast k₂) (by exact_mod_cast k₁)]
      have hk' : ((S s₁).card : ℚ) + 1 ≤ (S s₂).card := by exact_mod_cast hk
      have hM' : ((S s₂).card : ℚ) ≤ Fintype.card M := by exact_mod_cast hM
      have k₂' : (0 : ℚ) < (S s₂).card := by exact_mod_cast k₂
      have hMpos : (0 : ℚ) < Fintype.card M := k₂'.trans_le hM'
      refine lt_of_mul_lt_mul_right ?_ hMpos.le
      calc G.prior s₂ * (S s₁).card * Fintype.card M
          ≤ G.prior s₂ * ((S s₂).card - 1) * Fintype.card M := by gcongr; linarith
        _ ≤ G.prior s₂ * (Fintype.card M - 1) * (S s₂).card := by
          nlinarith [mul_nonneg p₂.le (sub_nonneg.mpr hM')]
        _ < G.prior s₁ * (S s₂).card * Fintype.card M := by
          linarith [mul_lt_mul_of_pos_right hnf' k₂']
    have hmemb : ∀ s, s ∈ (senders.argmin λ s => (S s).card).argmax G.prior ↔
        s ∈ senders ∧ ∀ s' ∈ senders,
          G.prior s' / (S s').card ≤ G.prior s / (S s).card := by
      intro s
      simp only [Finset.mem_argmax, Finset.mem_argmin]
      constructor
      · rintro ⟨⟨hs, hmin⟩, hpr⟩
        refine ⟨hs, λ s' hs' => ?_⟩
        rcases lt_or_eq_of_le (hmin s' hs') with h | h
        · exact (hlt s hs s' hs' h).le
        · rw [h]
          exact div_le_div_of_nonneg_right (hpr s' ⟨hs', λ s'' hs'' => h ▸ hmin s'' hs''⟩)
            (by positivity)
      · rintro ⟨hs, hbest⟩
        have hmin : ∀ s' ∈ senders, (S s).card ≤ (S s').card := λ s' hs' => by
          by_contra h
          exact absurd (hbest s' hs') (not_le.mpr (hlt s' hs' s hs (not_le.mp h)))
        refine ⟨⟨hs, hmin⟩, λ s' ⟨hs', hmin'⟩ => ?_⟩
        have heq : ((S s').card : ℚ) = (S s).card := by
          exact_mod_cast le_antisymm (hmin' s hs) (hmin s' hs')
        have := hbest s' hs'
        rw [heq] at this
        exact (div_le_div_iff_of_pos_right (by exact_mod_cast hcard s hs)).mp this
    obtain ⟨s₀, hs₀⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
    obtain ⟨s₁, hs₁⟩ := Finset.argmax_nonempty
      (Finset.argmin_nonempty ⟨s₀, hs₀⟩ (f := λ s => (S s).card)) (f := G.prior)
    have hs₁' := (hmemb s₁).mp hs₁
    have hpos : ∀ s ∈ senders, 0 < Sb s m * G.prior s := λ s hs => by
      rw [hw, if_pos hs]; exact div_pos (hprior s) (by exact_mod_cast hcard s hs)
    have hle' : ∀ s, Sb s m * G.prior s ≤ Sb s₁ m * G.prior s₁ := λ s => by
      by_cases hs : s ∈ senders
      · rw [hw s, hw s₁, if_pos hs, if_pos hs₁'.1]; exact hs₁'.2 s hs
      · rw [hw s, if_neg hs]; exact (hpos s₁ hs₁'.1).le
    have hmax : Finset.univ.fold max 0 (λ s => Sb s m * G.prior s) = Sb s₁ m * G.prior s₁ := by
      refine le_antisymm ?_ ((Finset.le_fold_max _).mpr (Or.inr ⟨s₁, Finset.mem_univ _, le_rfl⟩))
      rcases Finset.fold_max_attained Finset.univ (λ s => Sb s m * G.prior s) 0 with h | ⟨x, _, hx⟩
      · rw [h]; exact (hpos s₁ hs₁'.1).le
      · rw [hx]; exact hle' x
    have hfilt : Finset.univ.filter (λ s => Sb s m * G.prior s = Sb s₁ m * G.prior s₁) =
        (senders.argmin λ s => (S s).card).argmax G.prior := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmemb]
      constructor
      · intro h
        have hs : s ∈ senders := by
          by_contra hs
          rw [hw s, if_neg hs] at h; exact absurd (h ▸ hpos s₁ hs₁'.1) (lt_irrefl (0 : ℚ))
        refine ⟨hs, λ s' hs' => ?_⟩
        have := hs₁'.2 s' hs'
        rw [hw s, hw s₁, if_pos hs, if_pos hs₁'.1] at h
        exact this.trans h.ge
      · rintro ⟨hs, hbest⟩
        rw [hw s, hw s₁, if_pos hs, if_pos hs₁'.1]
        exact le_antisymm (hs₁'.2 s hs) (hbest s₁ hs₁'.1)
    have hrs : receiverStep G S m = senders.argmin λ s => (S s).card := by
      simp only [receiverStep, ← hsenders]; rw [if_neg hemp]
    have hcond : ∀ s, Sb s m * G.prior s = Sb s₁ m * G.prior s₁ ↔
        s ∈ (senders.argmin λ s => (S s).card).argmax G.prior := λ s => by
      rw [← hfilt, Finset.mem_filter]; simp
    rw [hmax, if_neg (hpos s₁ hs₁'.1).ne', if_neg hemp, hfilt, hrs]
    by_cases ht : t ∈ (senders.argmin λ s => (S s).card).argmax G.prior
    · rw [if_pos ((hcond t).mpr ht), if_pos ht]
    · rw [if_neg (mt (hcond t).mp ht), if_neg ht]

/-! ### Lemma 3 and Theorem 3: convergence (Appendix B.4)

Expected gain never decreases along the dynamics: the sender step because
`senderResponse` attains `maxUtility` at every state, the receiver step because
`receiverResponse` attains the maximal weight after every message. Receiver
strategies take values in a finite set, so the sequence repeats; on a cycle
the gain is constant, which forces the optimal-message sets to grow around
the cycle and hence to stabilise — a fixed point. -/

section Convergence

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
theorem sender_inner_le_maxUtility (S : T → M → ℚ) (H : M → T → ℚ) (t : T)
    (hSNonneg : ∀ m, 0 ≤ S t m) (hSSum : ∑ m, S t m ≤ 1)
    (hSTruth : ∀ m, ¬ G.meaning m t → S t m = 0) :
    ∑ m, S t m * H m t ≤ maxUtility G H t :=
  calc ∑ m, S t m * H m t ≤ ∑ m, S t m * maxUtility G H t := by
        refine Finset.sum_le_sum λ m _ => ?_
        by_cases hm : G.meaning m t
        · exact mul_le_mul_of_nonneg_left (le_maxUtility G H (G.mem_trueMessages.mpr hm))
            (hSNonneg m)
        · simp [hSTruth m hm]
    _ = (∑ m, S t m) * maxUtility G H t := by rw [Finset.sum_mul]
    _ ≤ 1 * maxUtility G H t := mul_le_mul_of_nonneg_right hSSum (maxUtility_nonneg G H t)
    _ = maxUtility G H t := one_mul _

omit [Fintype T] [DecidableEq T] in
theorem senderResponse_inner_ge_maxUtility (H : M → T → ℚ) (t : T) :
    maxUtility G H t ≤ ∑ m, senderResponse G H t m * H m t := by
  have hval : ∀ m, senderResponse G H t m * H m t =
      if m ∈ optimalMessages G H t then 1 / ((optimalMessages G H t).card : ℚ) * H m t else 0 := by
    intro m; unfold senderResponse; split_ifs <;> simp
  simp_rw [hval]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  rcases Nat.eq_zero_or_pos (optimalMessages G H t).card with hk0 | hk
  · have : maxUtility G H t = 0 := by
      refine le_antisymm ?_ (maxUtility_nonneg G H t)
      rcases Finset.fold_max_attained (G.trueMessages t) (λ m => H m t) 0 with h0 | ⟨m₀, hm₀, heq⟩
      · exact h0.le
      · have hm : m₀ ∈ optimalMessages G H t := Finset.mem_filter.mpr ⟨hm₀, heq.symm⟩
        exact absurd hk0 (Finset.card_pos.mpr ⟨m₀, hm⟩).ne'
    simp [Finset.card_eq_zero.mp hk0, this]
  · rw [Finset.sum_congr rfl (λ m hm => by rw [(Finset.mem_filter.mp hm).2]), Finset.sum_const,
      nsmul_eq_mul, show ((optimalMessages G H t).card : ℚ) *
        (1 / (optimalMessages G H t).card * maxUtility G H t) =
        maxUtility G H t * ((optimalMessages G H t).card * (1 / (optimalMessages G H t).card))
        by ring,
      mul_one_div_cancel (by exact_mod_cast hk.ne'), mul_one]

omit [DecidableEq T] in
/-- Lemma 3 (i): the sender step does not decrease expected gain. -/
theorem eg_sender_improvement (S : T → M → ℚ) (H : M → T → ℚ)
    (hPrior : ∀ t, 0 ≤ G.prior t) (hSNonneg : ∀ t m, 0 ≤ S t m)
    (hSSum : ∀ t, ∑ m, S t m ≤ 1) (hSTruth : ∀ t m, ¬ G.meaning m t → S t m = 0) :
    expectedGain G S H ≤ expectedGain G (senderResponse G H) H := by
  unfold expectedGain
  refine Finset.sum_le_sum λ t _ => mul_le_mul_of_nonneg_left ?_ (hPrior t)
  exact (sender_inner_le_maxUtility G S H t (hSNonneg t) (hSSum t) (hSTruth t)).trans
    (senderResponse_inner_ge_maxUtility G H t)

theorem per_message_bound {ι : Type*} [Fintype ι] (w h : ι → ℚ) (hh : ∀ i, 0 ≤ h i)
    (hhsum : ∑ i, h i ≤ 1) (maxW : ℚ) (hmaxW_nonneg : 0 ≤ maxW) (hmaxW : ∀ i, w i ≤ maxW) :
    ∑ i, w i * h i ≤ maxW :=
  calc ∑ i, w i * h i ≤ ∑ i, maxW * h i :=
        Finset.sum_le_sum λ i _ => mul_le_mul_of_nonneg_right (hmaxW i) (hh i)
    _ = maxW * ∑ i, h i := by rw [← Finset.mul_sum]
    _ ≤ maxW * 1 := mul_le_mul_of_nonneg_left hhsum hmaxW_nonneg
    _ = maxW := mul_one maxW

omit [Fintype M] [DecidableEq M] in
theorem literal_sum_le_one (m : M) : ∑ t, G.literal m t ≤ 1 := by
  have hval : ∀ t, G.literal m t =
      if t ∈ G.trueStates m then ((G.trueStates m).card : ℚ)⁻¹ else 0 := λ t => by
    simp only [InterpGame.literal, InterpGame.mem_trueStates]
  simp_rw [hval]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (G.trueStates m).card with hn | hn
  · simp [hn]
  · exact le_of_eq (mul_inv_cancel₀ (by exact_mod_cast hn.ne'))

omit [Fintype M] [DecidableEq M] in
theorem receiverResponse_sum_le_one (S : T → M → ℚ) (m : M) :
    ∑ t, receiverResponse G S m t ≤ 1 := by
  set w : T → ℚ := λ s => S s m * G.prior s
  set maxW := Finset.univ.fold max 0 w
  by_cases hmaxW : maxW = 0
  · have hL0 : ∀ t, receiverResponse G S m t = G.literal m t := λ t => by
      simp only [receiverResponse]; rw [if_pos hmaxW]
    simp_rw [hL0]; exact literal_sum_le_one G m
  · set best := Finset.univ.filter λ s => w s = maxW
    have hval : ∀ t, receiverResponse G S m t = if t ∈ best then 1 / (best.card : ℚ) else 0 := by
      intro t
      simp only [receiverResponse]; rw [if_neg hmaxW]
      simp only [best, Finset.mem_filter, Finset.mem_univ, true_and]; rfl
    simp_rw [hval]
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, Finset.univ_inter]
    rcases Nat.eq_zero_or_pos best.card with hk | hk
    · simp [hk]
    · exact le_of_eq (mul_one_div_cancel (by exact_mod_cast hk.ne'))

omit [DecidableEq T] in
theorem receiverLevel_nonneg (n : ℕ) (m : M) (t : T) : 0 ≤ receiverLevel G n m t := by
  cases n with
  | zero => simp only [receiverLevel, InterpGame.literal]; split_ifs <;> positivity
  | succ n => exact receiverResponse_nonneg G _ m t

theorem receiverLevel_sum_le_one (n : ℕ) (m : M) : ∑ t, receiverLevel G n m t ≤ 1 := by
  cases n with
  | zero => exact literal_sum_le_one G m
  | succ n => exact receiverResponse_sum_le_one G _ m

omit [Fintype M] [DecidableEq T] [DecidableEq M] in
/-- The receiver response attains the maximal weight after every message. -/
theorem receiverResponse_inner_ge_max (S : T → M → ℚ) (m : M)
    (hw_nonneg : ∀ t, 0 ≤ S t m * G.prior t) :
    Finset.univ.fold max 0 (λ s => S s m * G.prior s) ≤
      ∑ t, S t m * G.prior t * receiverResponse G S m t := by
  set w : T → ℚ := λ s => S s m * G.prior s with hw
  set maxW := Finset.univ.fold max 0 w with hmaxW
  have hmaxW_nonneg : 0 ≤ maxW := (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
  rcases hmaxW_nonneg.lt_or_eq with hpos | hzero
  · obtain ⟨t₀, ht₀⟩ : ∃ t₀, w t₀ = maxW := by
      rcases Finset.fold_max_attained Finset.univ w 0 with h | ⟨x, _, hx⟩
      · exact absurd (hmaxW ▸ h : maxW = 0) hpos.ne'
      · exact ⟨x, hx.symm⟩
    set best := Finset.univ.filter λ t => w t = maxW
    have hbest : ∀ t ∈ best, receiverResponse G S m t = 1 / (best.card : ℚ) := λ t ht => by
      simp only [receiverResponse]
      rw [if_neg hpos.ne', if_pos (Finset.mem_filter.mp ht).2]
    have hk : 0 < best.card :=
      Finset.card_pos.mpr ⟨t₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht₀⟩⟩
    calc maxW = ∑ t ∈ best, maxW * (1 / (best.card : ℚ)) := by
          rw [Finset.sum_const, nsmul_eq_mul,
            show (best.card : ℚ) * (maxW * (1 / best.card)) = maxW * (best.card * (1 / best.card))
              by ring, mul_one_div_cancel (by exact_mod_cast hk.ne'), mul_one]
      _ = ∑ t ∈ best, w t * receiverResponse G S m t :=
          Finset.sum_congr rfl λ t ht => by rw [(Finset.mem_filter.mp ht).2, hbest t ht]
      _ ≤ ∑ t, w t * receiverResponse G S m t :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            λ t _ _ => mul_nonneg (hw_nonneg t) (receiverResponse_nonneg G S m t)
  · rw [← hzero]
    exact Finset.sum_nonneg λ t _ => mul_nonneg (hw_nonneg t) (receiverResponse_nonneg G S m t)

omit [DecidableEq T] [DecidableEq M] in
/-- Lemma 3 (ii): the receiver step does not decrease expected gain. -/
theorem eg_receiver_improvement (S : T → M → ℚ) (H : M → T → ℚ)
    (hPrior : ∀ t, 0 ≤ G.prior t) (hSNonneg : ∀ t m, 0 ≤ S t m)
    (hHNonneg : ∀ m t, 0 ≤ H m t) (hHSum : ∀ m, ∑ t, H m t ≤ 1) :
    expectedGain G S H ≤ expectedGain G S (receiverResponse G S) := by
  unfold expectedGain
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := λ t m => G.prior t * (S t m * H m t)),
    Finset.sum_comm (f := λ t m => G.prior t * (S t m * receiverResponse G S m t))]
  refine Finset.sum_le_sum λ m _ => ?_
  have hcomm : ∀ (K : M → T → ℚ) t, G.prior t * (S t m * K m t) = S t m * G.prior t * K m t :=
    λ K t => by ring
  simp_rw [hcomm]
  have hw_nonneg : ∀ t, 0 ≤ S t m * G.prior t := λ t => mul_nonneg (hSNonneg t m) (hPrior t)
  exact (per_message_bound (λ t => S t m * G.prior t) (H m) (hHNonneg m) (hHSum m) _
    ((Finset.le_fold_max 0).mpr (Or.inl le_rfl))
    λ t => (Finset.le_fold_max _).mpr (Or.inr ⟨t, Finset.mem_univ t, le_rfl⟩)).trans
    (receiverResponse_inner_ge_max G S m hw_nonneg)

/-- Lemma 3: expected gain is monotone along the receiver levels. -/
theorem eg_monotone (hPrior : ∀ t, 0 ≤ G.prior t) (n : ℕ) :
    expectedGain G (senderResponse G (receiverLevel G n)) (receiverLevel G n) ≤
      expectedGain G (senderResponse G (receiverLevel G (n + 1))) (receiverLevel G (n + 1)) :=
  calc _ ≤ expectedGain G (senderResponse G (receiverLevel G n)) (receiverLevel G (n + 1)) :=
        eg_receiver_improvement G _ _ hPrior (senderResponse_nonneg G _)
          (receiverLevel_nonneg G n) (receiverLevel_sum_le_one G n)
    _ ≤ _ := eg_sender_improvement G _ _ hPrior (senderResponse_nonneg G _)
          (senderResponse_sum_le_one G _) (λ _ _ => senderResponse_eq_zero_of_not_meaning G _)

omit [DecidableEq T] [DecidableEq M] in
/-- Expected gain is at most one. -/
theorem expectedGain_le_one (S : T → M → ℚ) (H : M → T → ℚ) (hPriorSum : ∑ t, G.prior t = 1)
    (hPrior : ∀ t, 0 ≤ G.prior t) (hSNonneg : ∀ t m, 0 ≤ S t m) (hSSum : ∀ t, ∑ m, S t m ≤ 1)
    (hH : ∀ m t, H m t ≤ 1) : expectedGain G S H ≤ 1 := by
  unfold expectedGain
  calc ∑ t, G.prior t * ∑ m, S t m * H m t ≤ ∑ t, G.prior t * 1 := by
        refine Finset.sum_le_sum λ t _ => mul_le_mul_of_nonneg_left ?_ (hPrior t)
        calc ∑ m, S t m * H m t ≤ ∑ m, S t m * 1 :=
              Finset.sum_le_sum λ m _ => mul_le_mul_of_nonneg_left (hH m t) (hSNonneg t m)
          _ = ∑ m, S t m := by simp only [mul_one]
          _ ≤ 1 := hSSum t
    _ = 1 := by simp [hPriorSum]

omit [DecidableEq T] in
/-- Equal expected gain against the sender best response forces every
positively used message to be optimal, at every positive-prior state. -/
theorem mem_optimalMessages_of_eg_eq (S : T → M → ℚ) (H : M → T → ℚ)
    (hPrior : ∀ t, 0 ≤ G.prior t) (hSNonneg : ∀ t m, 0 ≤ S t m)
    (hSSum : ∀ t, ∑ m, S t m ≤ 1) (hSTruth : ∀ t m, ¬ G.meaning m t → S t m = 0)
    (hEG : expectedGain G S H = expectedGain G (senderResponse G H) H)
    (t : T) (hPt : 0 < G.prior t) (m : M) (hSm : 0 < S t m) : m ∈ optimalMessages G H t := by
  have h_best_eq : ∀ s, ∑ m, senderResponse G H s m * H m s = maxUtility G H s := λ s =>
    le_antisymm (sender_inner_le_maxUtility G _ H s (senderResponse_nonneg G H s)
      (senderResponse_sum_le_one G H s) λ m hm => senderResponse_eq_zero_of_not_meaning G H hm)
      (senderResponse_inner_ge_maxUtility G H s)
  have h_old_le : ∀ s, ∑ m, S s m * H m s ≤ maxUtility G H s := λ s =>
    sender_inner_le_maxUtility G S H s (hSNonneg s) (hSSum s) (hSTruth s)
  have hdiff : ∑ s, G.prior s * (maxUtility G H s - ∑ m, S s m * H m s) = 0 := by
    have hnew : ∑ s, G.prior s * ∑ m, S s m * H m s = ∑ s, G.prior s * maxUtility G H s := by
      unfold expectedGain at hEG
      rw [hEG]; exact Finset.sum_congr rfl λ s _ => by rw [h_best_eq s]
    simp only [mul_sub, Finset.sum_sub_distrib, hnew, sub_self]
  have hinner : ∑ m, S t m * H m t = maxUtility G H t := by
    have := (Finset.sum_eq_zero_iff_of_nonneg λ s _ =>
      mul_nonneg (hPrior s) (sub_nonneg.mpr (h_old_le s))).mp hdiff t (Finset.mem_univ t)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hPt.ne'
    · linarith
  have hTrue : G.meaning m t := by
    by_contra hF; exact absurd hSm (by rw [hSTruth t m hF]; exact lt_irrefl 0)
  refine Finset.mem_filter.mpr ⟨G.mem_trueMessages.mpr hTrue, ?_⟩
  by_contra hne
  have hlt : H m t < maxUtility G H t :=
    lt_of_le_of_ne (le_maxUtility G H (G.mem_trueMessages.mpr hTrue)) hne
  have : ∑ m', S t m' * H m' t < maxUtility G H t :=
    calc ∑ m', S t m' * H m' t < ∑ m', S t m' * maxUtility G H t := by
          refine Finset.sum_lt_sum (λ m' _ => ?_)
            ⟨m, Finset.mem_univ m, mul_lt_mul_of_pos_left hlt hSm⟩
          by_cases hm' : G.meaning m' t
          · exact mul_le_mul_of_nonneg_left (le_maxUtility G H (G.mem_trueMessages.mpr hm'))
              (hSNonneg t m')
          · simp [hSTruth t m' hm']
      _ = (∑ m', S t m') * maxUtility G H t := by rw [Finset.sum_mul]
      _ ≤ 1 * maxUtility G H t := mul_le_mul_of_nonneg_right (hSSum t) (maxUtility_nonneg G H t)
      _ = maxUtility G H t := one_mul _
  exact absurd hinner this.ne

omit [DecidableEq T] in
theorem optimalMessages_subset_of_eg_eq (H₁ H₂ : M → T → ℚ) (hPrior : ∀ t, 0 < G.prior t)
    (hEG : expectedGain G (senderResponse G H₁) H₂ = expectedGain G (senderResponse G H₂) H₂)
    (t : T) :
    optimalMessages G H₁ t ⊆ optimalMessages G H₂ t := λ m hm =>
  mem_optimalMessages_of_eg_eq G (senderResponse G H₁) H₂ (λ t => (hPrior t).le)
    (senderResponse_nonneg G H₁) (senderResponse_sum_le_one G H₁)
    (λ _ _ hm' => senderResponse_eq_zero_of_not_meaning G H₁ hm') hEG t (hPrior t) m
    ((senderResponse_pos_iff G H₁ t m).mpr hm)

omit [DecidableEq T] in
theorem receiverLevel_add (n k : ℕ) (h : receiverLevel G n = receiverLevel G (n + 1)) :
    receiverLevel G (n + k) = receiverLevel G (n + 1 + k) := by
  induction k with
  | zero => simpa
  | succ k ih => exact congrArg (receiverResponse G ∘ senderResponse G) ih

theorem monotone_cycle_all_eq {f : ℕ → ℚ} {n p : ℕ} (hMono : ∀ k, f k ≤ f (k + 1))
    (hCycle : f n = f (n + p)) (k : ℕ) (hk : k < p) : f (n + k) = f (n + k + 1) := by
  have shift : ∀ a j, f a ≤ f (a + j) := λ a j => by
    induction j with
    | zero => simp
    | succ j ih => exact ih.trans (hMono (a + j))
  have h3 := shift (n + k + 1) (p - k - 1)
  rw [show n + k + 1 + (p - k - 1) = n + p by omega] at h3
  linarith [shift n k, hMono (n + k)]

theorem cycle_containment_eq {α : Type*} {p : ℕ} (A : ℕ → Finset α) (hp : 0 < p)
    (hContain : ∀ k, k < p → A k ⊆ A (k + 1)) (hCycle : A p = A 0) : A 0 = A 1 := by
  refine Finset.Subset.antisymm (hContain 0 hp) (hCycle ▸ ?_)
  suffices ∀ j, 1 ≤ j → j ≤ p → A 1 ⊆ A j from this p hp le_rfl
  intro j; induction j with
  | zero => omega
  | succ j ih =>
    intro hj1 hjp
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; exact le_rfl
    · exact (ih hj (by omega)).trans (hContain j (by omega))

omit [Fintype T] [DecidableEq T] in
theorem senderResponse_congr (H₁ H₂ : M → T → ℚ)
    (hOpt : ∀ t, optimalMessages G H₁ t = optimalMessages G H₂ t) :
    senderResponse G H₁ = senderResponse G H₂ := by
  funext t m; unfold senderResponse; rw [hOpt t]

/-- The values a receiver level can take: `0` and `1/k` for `1 ≤ k ≤ |T|`. -/
def valueSet (T : Type*) [Fintype T] : Finset ℚ :=
  insert 0 ((Finset.range (Fintype.card T)).image λ k : ℕ => 1 / ((k : ℚ) + 1))

omit [DecidableEq T] in
theorem one_div_mem_valueSet {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ Fintype.card T) :
    (1 : ℚ) / n ∈ valueSet T := by
  simp only [valueSet, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  exact Or.inr ⟨n - 1, by omega, by congr 1; rw [Nat.cast_sub hn1]; ring⟩

omit [Fintype M] [DecidableEq M] [DecidableEq T] in
theorem literal_mem_valueSet (m : M) (t : T) : G.literal m t ∈ valueSet T := by
  simp only [InterpGame.literal]
  split_ifs with hm
  · rw [← one_div]
    exact one_div_mem_valueSet (Finset.card_pos.mpr ⟨t, G.mem_trueStates.mpr hm⟩)
      (Finset.card_le_univ _)
  · exact Finset.mem_insert_self 0 _

omit [Fintype M] [DecidableEq M] [DecidableEq T] in
theorem receiverResponse_mem_valueSet (S : T → M → ℚ) (m : M) (t : T) :
    receiverResponse G S m t ∈ valueSet T := by
  simp only [receiverResponse]
  split_ifs with hmaxW hwm
  · exact literal_mem_valueSet G m t
  · exact one_div_mem_valueSet
      (Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, hwm⟩⟩)
      (Finset.card_le_univ _)
  · exact Finset.mem_insert_self 0 _

omit [DecidableEq T] in
theorem receiverLevel_mem_valueSet (n : ℕ) (m : M) (t : T) :
    receiverLevel G n m t ∈ valueSet T := by
  cases n with
  | zero => exact literal_mem_valueSet G m t
  | succ n => exact receiverResponse_mem_valueSet G _ m t

omit [DecidableEq T] in
/-- The receiver levels repeat: they range over a finite set of strategies. -/
theorem receiverLevel_repeats :
    ∃ n₁ n₂, n₁ < n₂ ∧ receiverLevel G n₁ = receiverLevel G n₂ := by
  let encode : ℕ → M → T → valueSet T :=
    λ n m t => ⟨receiverLevel G n m t, receiverLevel_mem_valueSet G n m t⟩
  obtain ⟨n₁, n₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite encode
  have hstrat : receiverLevel G n₁ = receiverLevel G n₂ := by
    funext m t; exact Subtype.mk.inj (congr_fun (congr_fun heq m) t)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨n₁, n₂, h, hstrat⟩
  · exact ⟨n₂, n₁, h, hstrat.symm⟩

/-- Theorem 3: the receiver levels reach a fixed point. -/
theorem receiverLevel_reaches_fixedPoint (hPrior : ∀ t, 0 < G.prior t) :
    ∃ n, IsFixedPoint G (receiverLevel G n) := by
  obtain ⟨n₁, n₂, hlt, heq⟩ := receiverLevel_repeats G
  set p := n₂ - n₁ with hp
  have hp0 : 0 < p := by omega
  have hperiod : receiverLevel G n₁ = receiverLevel G (n₁ + p) := by
    rwa [hp, Nat.add_sub_cancel' hlt.le]
  set eg := λ n => expectedGain G (senderResponse G (receiverLevel G n)) (receiverLevel G n)
  have hEGmono : ∀ k, eg k ≤ eg (k + 1) := eg_monotone G λ t => (hPrior t).le
  have hEGcycle : eg n₁ = eg (n₁ + p) := by simp only [eg]; rw [hperiod]
  have hOptSub : ∀ k, k < p → ∀ t, optimalMessages G (receiverLevel G (n₁ + k)) t ⊆
      optimalMessages G (receiverLevel G (n₁ + k + 1)) t := by
    intro k hk
    have hEGk := monotone_cycle_all_eq hEGmono hEGcycle k hk
    refine optimalMessages_subset_of_eg_eq G _ _ hPrior (le_antisymm ?_ ?_)
    · exact eg_sender_improvement G _ _ (λ t => (hPrior t).le) (senderResponse_nonneg G _)
        (senderResponse_sum_le_one G _) (λ _ _ => senderResponse_eq_zero_of_not_meaning G _)
    · have := eg_receiver_improvement G (senderResponse G (receiverLevel G (n₁ + k)))
        (receiverLevel G (n₁ + k)) (λ t => (hPrior t).le) (senderResponse_nonneg G _)
        (receiverLevel_nonneg G _) (receiverLevel_sum_le_one G _)
      simp only [eg] at hEGk
      exact hEGk ▸ this
  have hOptEq : ∀ t, optimalMessages G (receiverLevel G n₁) t =
      optimalMessages G (receiverLevel G (n₁ + 1)) t := λ t =>
    cycle_containment_eq (λ k => optimalMessages G (receiverLevel G (n₁ + k)) t) hp0
      (λ k hk => hOptSub k hk t)
      (by show optimalMessages G (receiverLevel G (n₁ + p)) t = _; rw [← hperiod]; rfl)
  refine ⟨n₁ + 1, ?_⟩
  show receiverResponse G (senderResponse G (receiverLevel G (n₁ + 1))) =
    receiverResponse G (senderResponse G (receiverLevel G n₁))
  exact congrArg (receiverResponse G) (senderResponse_congr G _ _ λ t => (hOptEq t).symm)

end Convergence

/-! ### Theorem 4: fixed points are perfect Bayesian equilibria -/

/-- Posterior beliefs consistent with the prior and a sender strategy (119);
after a surprise message the receiver keeps the literal belief. -/
def posterior (S : T → M → ℚ) (m : M) (t : T) : ℚ :=
  if ∑ s, G.prior s * S s m = 0 then G.literal m t
  else G.prior t * S t m / ∑ s, G.prior s * S s m

/-- Sender rationality (116): every message sent maximises the chance of
being understood. -/
def SenderRational (S : T → M → ℚ) (H : M → T → ℚ) : Prop :=
  ∀ t m, 0 < S t m → m ∈ optimalMessages G H t

/-- Receiver rationality (120): every interpretation chosen is maximum a
posteriori. -/
def ReceiverRational (H : M → T → ℚ) (S : T → M → ℚ) : Prop :=
  ∀ m t, 0 < H m t → t ∈ Finset.univ.argmax (posterior G S m)

/-- A perfect Bayesian equilibrium in behavioural strategies. -/
def IsPBE (S : T → M → ℚ) (H : M → T → ℚ) : Prop :=
  SenderRational G S H ∧ ReceiverRational G H S

omit [DecidableEq T] in
/-- Theorem 4: a fixed point of the heavy dynamics, with its sender best
response, is a perfect Bayesian equilibrium. -/
theorem isPBE_of_fixedPoint (hprior : ∀ t, 0 < G.prior t) {H : M → T → ℚ}
    (hH : IsFixedPoint G H) : IsPBE G (senderResponse G H) H := by
  refine ⟨λ t m h => (senderResponse_pos_iff G H t m).mp h, λ m t hpos => ?_⟩
  set S := senderResponse G H
  rw [← hH] at hpos
  simp only [receiverResponse] at hpos
  set w : T → ℚ := λ s => S s m * G.prior s with hw
  set maxW := Finset.univ.fold max 0 w with hmaxW
  have hz : ∑ s, G.prior s * S s m = ∑ s, w s := Finset.sum_congr rfl λ s _ => mul_comm _ _
  have hwle : ∀ s, w s ≤ maxW := λ s =>
    (Finset.le_fold_max _).mpr (Or.inr ⟨s, Finset.mem_univ s, le_rfl⟩)
  have hwnn : ∀ s, 0 ≤ w s := λ s => mul_nonneg (senderResponse_nonneg G H s m) (hprior s).le
  rw [Finset.mem_argmax]
  refine ⟨Finset.mem_univ t, λ s _ => ?_⟩
  by_cases h0 : maxW = 0
  · rw [if_pos h0] at hpos
    have hw0 : ∀ s, w s = 0 := λ s => le_antisymm (h0 ▸ hwle s) (hwnn s)
    have hz0 : ∑ s, G.prior s * S s m = 0 := by rw [hz]; exact Finset.sum_eq_zero λ s _ => hw0 s
    simp only [posterior, hz0, if_true, InterpGame.literal] at hpos ⊢
    split_ifs at hpos with ht
    · split_ifs <;> simp
    · exact absurd hpos (lt_irrefl 0)
  · rw [if_neg h0] at hpos
    split_ifs at hpos with ht
    · have hzpos : 0 < ∑ s, G.prior s * S s m := by
        rw [hz]
        calc (0 : ℚ) < maxW :=
            lt_of_le_of_ne ((Finset.le_fold_max 0).mpr (Or.inl le_rfl)) (Ne.symm h0)
          _ = w t := ht.symm
          _ ≤ ∑ s, w s := Finset.single_le_sum (λ s _ => hwnn s) (Finset.mem_univ t)
      simp only [posterior, if_neg hzpos.ne']
      refine div_le_div_of_nonneg_right ?_ hzpos.le
      calc G.prior s * S s m = w s := mul_comm _ _
        _ ≤ maxW := hwle s
        _ = w t := ht.symm
        _ = G.prior t * S t m := mul_comm _ _
    · exact absurd hpos (lt_irrefl 0)

/-! ### Level-1 interpretation and minimal-models exhaustification (§10)

`R₁` on the sender chain keeps, among the states where `m` is true, those
where fewest alternatives are true (107); minimal-models exhaustification
keeps the states minimal in the inclusion order on true alternatives. -/

/-- The alternatives of a game as propositions over states. -/
def alternatives : Set (Set T) := {λ t => G.meaning m t | m : M}

/-- The prejacent of a message. -/
def prejacent (m : M) : Set T := λ t => G.meaning m t

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
theorem trueMessages_ssubset_of_ltALT {t' t : T} (h : ltALT (alternatives G) t' t) :
    G.trueMessages t' ⊂ G.trueMessages t := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨λ m hm => ?_, λ heq => h.2 λ a ha hat => ?_⟩
  · exact G.mem_trueMessages.mpr (h.1 _ ⟨m, rfl⟩ (G.mem_trueMessages.mp hm))
  · obtain ⟨m, rfl⟩ := ha
    exact G.mem_trueMessages.mp (heq ▸ G.mem_trueMessages.mpr hat)

/-- Fact 1: `R₁(m) ⊆ ExhMM(m)`. -/
theorem receiver1_subset_exhMW (m : M) (t : T) (ht : t ∈ receiverStep G G.trueMessages m) :
    exhMW (alternatives G) (prejacent G m) t := by
  rw [mem_receiverStep] at ht
  have hne : Finset.univ.filter (λ t => m ∈ G.trueMessages t) ≠ ∅ := by
    rintro h
    simp only [h, if_true] at ht
    exact Finset.eq_empty_iff_forall_notMem.mp h t (by simpa using ht)
  rw [if_neg hne] at ht
  refine ⟨G.mem_trueMessages.mp ht.1, λ ⟨t', ht', hlt⟩ => ?_⟩
  exact absurd (Finset.card_lt_card (trueMessages_ssubset_of_ltALT G hlt))
    (not_lt.mpr (ht.2 t' (G.mem_trueMessages.mpr ht')))

/-! ### Comparison of exhaustivity operators (Appendix A)

Fact 3, `ExhMM ⊆ ExhIE`, is `Exhaustification.exhMW_entails_exhIE`. Lemma 1
characterises innocent exclusion as closure of the minimal worlds: a
`φ`-world survives `ExhIE` iff every alternative false throughout `ExhMM` is
false at it. Fact 2 claims the order is invariant under adding an
alternative whose truth value is determined by the others; that holds when
the determination is monotone (conjunctions, as in the paper's example), and
fails for the negation of an alternative. -/

section Appendix

variable {W : Type*} (ALT : Set (Set W)) (φ : Set W)

/-- `A` is a monotone function of the alternatives in `X`: whenever every
`X`-alternative true at `w` is true at `v`, `A` at `w` forces `A` at `v`. -/
def MonotoneDetermined (A : Set W) : Prop := ∀ w v, leALT ALT w v → w ∈ A → v ∈ A

/-- Fact 2, for monotonically determined alternatives: the strict order is
unchanged. -/
theorem ltALT_insert_of_monotoneDetermined {A : Set W} (hA : MonotoneDetermined ALT A) :
    ltALT (insert A ALT) = ltALT ALT := by
  have key : ∀ w v, leALT (insert A ALT) w v ↔ leALT ALT w v := λ w v =>
    ⟨λ h a ha => h a (Set.mem_insert_of_mem _ ha),
     λ h a ha => (Set.mem_insert_iff.mp ha).elim (λ e => e ▸ hA w v h) (h a)⟩
  funext w v; simp only [ltALT, key]

/-- Fact 2 as printed fails: over two worlds with one alternative, adding its
negation — truth-determined, but not monotonically — destroys the strict
order between the worlds. -/
theorem not_ltALT_insert_compl :
    ltALT ({(· = true)} : Set (Set Bool)) false true ∧
      ¬ ltALT (insert (· = false) {(· = true)}) false true := by
  refine ⟨⟨λ a ha h => ?_, λ h => ?_⟩, λ h => ?_⟩
  · rw [Set.mem_singleton_iff] at ha; subst ha; exact absurd h Bool.false_ne_true
  · exact Bool.false_ne_true (h _ rfl rfl)
  · exact absurd (h.1 (· = false) (Set.mem_insert _ _) rfl) (by decide)

/-- Lemma 1: innocent exclusion keeps the `φ`-worlds indistinguishable from
the minimal worlds by any alternative — every alternative false throughout
`ExhMM` is false at them. -/
theorem exhIE_eq_exhMW_indistinguishable (hfin : ALT.Finite) :
    exhIE ALT φ = {w | w ∈ φ ∧ ∀ a ∈ ALT, exhMW ALT φ ⊆ aᶜ → w ∉ a} :=
  exhIE_eq_phi_and_exhMW_negated ALT φ hfin

end Appendix

end Franke2011
