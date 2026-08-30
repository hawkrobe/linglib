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
import Linglib.Semantics.Exhaustification.InnocentExclusion
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
strategies, written with `Finset.uniform` and `Finset.argmax`: a level-(k+1)
sender is uniform over her optimal messages (`senderResponse`), a receiver is
uniform over the maximum-a-posteriori states (`receiverResponse`), surprise
messages interpreted literally. Theorem 1 identifies the two systems under
flat priors (`receiverLevel_eq_uniform`), Theorem 2 the lexicographic reading
of near-flat priors (`receiverResponse_uniform_nearFlat`), Lemma 3 and
Theorem 3 give convergence through the monotone expected gain (`eg_monotone`,
`receiverLevel_reaches_fixedPoint`), and Theorem 4 reads the fixed point as a
perfect Bayesian equilibrium (`isPBE_of_fixedPoint`).

§10 relates the model to exhaustive interpretation: level-1 interpretation is
contained in minimal-models exhaustification ([vanrooij-schulz-2004]; Fact 1,
`receiver1_subset_exhMW`), and in general strictly (`R₁ ≠ R₂` in the
free-choice game). Appendix A compares `exhMW` with [fox-2007]'s innocent
exclusion `exhIE` on the substrate of [spector-2016]: Fact 3 is
`Exhaustification.exhMW_subset_exhIE`, Lemma 1 is
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
* `receiverLevel_eq_uniform` — Theorem 1; `receiverResponse_uniform_nearFlat`
  — Theorem 2; `receiverLevel_reaches_fixedPoint` — Theorem 3;
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
unbiased belief in a set of pure strategies is the uniform vector on it
((115), (118)). Under the matching utilities of an interpretation game the
sender's expected utility of `m` in `t` is the receiver's probability of `t`
after `m`, so a level-(k+1) sender is uniform over the messages maximising it
((116)–(117)); a level-(k+1) receiver is uniform over the maximum-a-posteriori
states ((119)–(122)), and reads a surprise message — one no state sends —
literally, by the truth ceteris paribus assumption. -/

/-- The true messages maximising the receiver's probability of the true state:
the level-(k+1) sender's choices in `t` (116). -/
def optimalMessages (H : M → T → ℚ) (t : T) : Finset M := (G.trueMessages t).argmax (H · t)

/-- The unbiased belief in the level-(k+1) sender type: uniform over the optimal
messages (117). -/
def senderResponse (H : M → T → ℚ) (t : T) : M → ℚ := (optimalMessages G H t).uniform

/-- A surprise message: no state sends it, so Bayesian conditioning is
undefined (B.3). -/
def IsSurprise (S : T → M → ℚ) (m : M) : Prop := ∀ t, S t m = 0

instance (S : T → M → ℚ) (m : M) : Decidable (IsSurprise S m) :=
  inferInstanceAs (Decidable (∀ t, S t m = 0))

/-- The unbiased belief in the level-(k+1) receiver type: uniform over the
states maximising `Pr(t) · S(t, m)`, the posterior (119)–(120) up to
normalisation; a surprise message is read literally (122). -/
def receiverResponse (S : T → M → ℚ) (m : M) : T → ℚ :=
  if IsSurprise S m then G.literal m else (Finset.univ.argmax λ t => G.prior t * S t m).uniform

/-- The receiver levels of the heavy system from the literal receiver:
`receiverLevel n` is `R₂ₙ`. -/
def receiverLevel : ℕ → M → T → ℚ
  | 0 => G.literal
  | n + 1 => receiverResponse G (senderResponse G (receiverLevel n))

/-- A receiver strategy the heavy dynamics reproduce. -/
def IsFixedPoint (H : M → T → ℚ) : Prop := receiverResponse G (senderResponse G H) = H

/-- Expected gain (144): the probability of successful communication. -/
def expectedGain (S : T → M → ℚ) (H : M → T → ℚ) : ℚ :=
  ∑ t, G.prior t * ∑ m, S t m * H m t

omit [Fintype T] [DecidableEq T] [DecidableEq M] in
theorem mem_optimalMessages {H : M → T → ℚ} {t : T} {m : M} :
    m ∈ optimalMessages G H t ↔ G.meaning m t ∧ ∀ m', G.meaning m' t → H m' t ≤ H m t := by
  simp [optimalMessages, Finset.mem_argmax]

omit [Fintype T] [DecidableEq T] in
theorem senderResponse_pos_iff (H : M → T → ℚ) (t : T) (m : M) :
    0 < senderResponse G H t m ↔ m ∈ optimalMessages G H t :=
  Finset.uniform_pos_iff

omit [Fintype T] [DecidableEq T] in
theorem senderResponse_eq_zero_of_not_meaning (H : M → T → ℚ) {t : T} {m : M}
    (hm : ¬ G.meaning m t) : senderResponse G H t m = 0 :=
  Finset.uniform_of_notMem λ h => hm ((mem_optimalMessages G).mp h).1

omit [Fintype M] [DecidableEq M] in
/-- Every receiver response is uniform over a set of states. -/
theorem receiverResponse_eq_uniform (S : T → M → ℚ) (m : M) :
    receiverResponse G S m =
      (if IsSurprise S m then G.trueStates m
        else Finset.univ.argmax λ t => G.prior t * S t m).uniform := by
  unfold receiverResponse; split_ifs <;> rfl

omit [Fintype M] [DecidableEq M] in
theorem receiverResponse_nonneg (S : T → M → ℚ) (m : M) (t : T) :
    0 ≤ receiverResponse G S m t := by
  rw [receiverResponse_eq_uniform]; exact Finset.uniform_nonneg

omit [Fintype M] [DecidableEq M] in
theorem receiverResponse_sum_le_one (S : T → M → ℚ) (m : M) :
    ∑ t, receiverResponse G S m t ≤ 1 := by
  rw [receiverResponse_eq_uniform]; exact Finset.sum_uniform_le_one

theorem receiverLevel_nonneg (n : ℕ) (m : M) (t : T) : 0 ≤ receiverLevel G n m t := by
  cases n with
  | zero => exact Finset.uniform_nonneg
  | succ n => exact receiverResponse_nonneg G _ m t

theorem receiverLevel_sum_le_one (n : ℕ) (m : M) : ∑ t, receiverLevel G n m t ≤ 1 := by
  cases n with
  | zero => exact Finset.sum_uniform_le_one
  | succ n => exact receiverResponse_sum_le_one G _ m

/-! ### Theorem 1: the light system is the heavy system with flat priors -/

/-- The level-(k+1) sender's optimal messages against the unbiased belief in a
receiver type are the light-system sender type (76). -/
theorem optimalMessages_uniform {R : M → Finset T} (hR : ∀ m, R m ⊆ G.trueStates m) (t : T) :
    optimalMessages G (λ m => (R m).uniform) t = senderStep G R t := by
  simp only [optimalMessages, senderStep]
  split_ifs with hemp
  · refine Finset.argmax_eq_self_of_forall_le λ m _ m' _ => ?_
    have h : ∀ m, t ∉ R m := λ m hm =>
      Finset.eq_empty_iff_forall_notMem.mp hemp m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)
    simp [Finset.uniform_of_notMem (h m), Finset.uniform_of_notMem (h m')]
  · rw [Finset.argmax_eq_argmax_of_support (t := Finset.univ.filter λ m => t ∈ R m)
      (λ m hm => G.mem_trueMessages.mpr (G.mem_trueStates.mp (hR m (Finset.mem_filter.mp hm).2)))
      (Finset.nonempty_iff_ne_empty.mpr hemp)
      (λ m hm => Finset.uniform_pos_iff.mpr (Finset.mem_filter.mp hm).2)
      (λ m _ hm => Finset.uniform_of_notMem λ h =>
        hm (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))]
    refine (Finset.argmin_eq_argmax_of_le_iff λ m hm m' hm' => ?_).symm
    rw [Finset.uniform_of_mem (Finset.mem_filter.mp hm).2,
      Finset.uniform_of_mem (Finset.mem_filter.mp hm').2, inv_le_inv₀
      (by exact_mod_cast Finset.card_pos.mpr ⟨t, (Finset.mem_filter.mp hm').2⟩)
      (by exact_mod_cast Finset.card_pos.mpr ⟨t, (Finset.mem_filter.mp hm).2⟩), Nat.cast_le]

omit [Fintype M] [DecidableEq T] in
/-- A surprise message under the unbiased belief in a sender type is one no
state sends. -/
theorem isSurprise_uniform_iff (S : T → Finset M) (m : M) :
    IsSurprise (λ t => (S t).uniform) m ↔ Finset.univ.filter (λ t => m ∈ S t) = ∅ := by
  simp only [IsSurprise, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
  exact forall_congr' λ t => by rw [← Finset.uniform_pos_iff (K := ℚ), not_lt,
    le_antisymm_iff, and_iff_left Finset.uniform_nonneg]

omit [Fintype M] [DecidableEq T] in
/-- The states where the unbiased belief in a sender type sends `m`, weighted by
a flat prior, are maximised on the light-system receiver type (77). -/
theorem argmax_prior_mul_uniform (hprior : ∀ t, 0 < G.prior t)
    (hflat : ∀ t t', G.prior t = G.prior t') {S : T → Finset M} {m : M}
    (hne : Finset.univ.filter (λ t => m ∈ S t) ≠ ∅) :
    (Finset.univ.argmax λ t => G.prior t * (S t).uniform m) =
      (Finset.univ.filter λ t => m ∈ S t).argmin λ t => (S t).card := by
  obtain ⟨t₀, ht₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hp : ∀ t, G.prior t = G.prior t₀ := λ t => hflat t t₀
  simp_rw [hp]
  show Finset.univ.argmax ((λ x => G.prior t₀ * x) ∘ λ t => (S t).uniform m) = _
  rw [Finset.argmax_comp_strictMono (strictMono_mul_left_of_pos (hprior t₀)),
    Finset.argmax_eq_argmax_of_support (t := Finset.univ.filter λ t => m ∈ S t)
      (Finset.filter_subset _ _) ⟨t₀, ht₀⟩
      (λ t ht => Finset.uniform_pos_iff.mpr (Finset.mem_filter.mp ht).2)
      (λ t _ ht => Finset.uniform_of_notMem λ h =>
        ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))]
  refine (Finset.argmin_eq_argmax_of_le_iff λ t ht t' ht' => ?_).symm
  rw [Finset.uniform_of_mem (Finset.mem_filter.mp ht).2,
    Finset.uniform_of_mem (Finset.mem_filter.mp ht').2,
    inv_le_inv₀ (by exact_mod_cast Finset.card_pos.mpr ⟨m, (Finset.mem_filter.mp ht').2⟩)
      (by exact_mod_cast Finset.card_pos.mpr ⟨m, (Finset.mem_filter.mp ht).2⟩), Nat.cast_le]

omit [Fintype M] in
/-- The level-(k+1) receiver's response to the unbiased belief in a sender type,
under flat priors, is the unbiased belief in the light-system receiver type. -/
theorem receiverResponse_uniform (hprior : ∀ t, 0 < G.prior t)
    (hflat : ∀ t t', G.prior t = G.prior t') (S : T → Finset M) (m : M) :
    receiverResponse G (λ t => (S t).uniform) m = (receiverStep G S m).uniform := by
  rw [receiverResponse_eq_uniform, receiverStep]
  by_cases hemp : Finset.univ.filter (λ t => m ∈ S t) = ∅
  · rw [if_pos ((isSurprise_uniform_iff S m).mpr hemp), if_pos hemp]
  · rw [if_neg (mt (isSurprise_uniform_iff S m).mp hemp), if_neg hemp,
      argmax_prior_mul_uniform G hprior hflat hemp]

/-- Theorem 1: with flat priors the heavy receiver levels are the unbiased
beliefs in the light receiver chain. -/
theorem receiverLevel_eq_uniform (hprior : ∀ t, 0 < G.prior t)
    (hflat : ∀ t t', G.prior t = G.prior t') (n : ℕ) :
    receiverLevel G n = λ m => (receiverChain G n m).uniform := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hS : senderResponse G (receiverLevel G n) =
        λ t => (senderStep G (receiverChain G n) t).uniform := funext λ t => by
      rw [ih, senderResponse, optimalMessages_uniform G (receiverChain_subset_trueStates G n)]
    funext m
    rw [receiverLevel, receiverChain, hS]
    exact receiverResponse_uniform G hprior hflat _ m

/-! ### Theorem 2: near-flat priors -/

/-- The near-flat condition (132), with the inequality the proof needs:
`Pr(t_min)/Pr(t_max) > (|M|-1)/|M|` (the paper prints it reversed). -/
def NearFlat : Prop :=
  ∀ t t', ((Fintype.card M : ℚ) - 1) * G.prior t' < Fintype.card M * G.prior t

omit [DecidableEq T] in
/-- Theorem 2: under near-flat priors the states where the unbiased belief in a
sender type sends `m`, weighted by the prior, are maximised on the
prior-lexicographic refinement of the light receiver type (83). -/
theorem argmax_prior_mul_uniform_nearFlat (hprior : ∀ t, 0 < G.prior t) (hnf : NearFlat G)
    {S : T → Finset M} {m : M} (hne : Finset.univ.filter (λ t => m ∈ S t) ≠ ∅) :
    (Finset.univ.argmax λ t => G.prior t * (S t).uniform m) =
      ((Finset.univ.filter λ t => m ∈ S t).argmin λ t => (S t).card).argmax G.prior := by
  set senders := Finset.univ.filter λ t => m ∈ S t with hsenders
  have hmem : ∀ t, t ∈ senders ↔ m ∈ S t := λ t => by simp [hsenders]
  have hcard : ∀ t ∈ senders, 0 < (S t).card := λ t ht => Finset.card_pos.mpr ⟨m, (hmem t).mp ht⟩
  -- fewer messages beats any prior difference
  have hlt : ∀ t₁ ∈ senders, ∀ t₂ ∈ senders, (S t₁).card < (S t₂).card →
      G.prior t₂ * (S t₂).uniform m < G.prior t₁ * (S t₁).uniform m := by
    intro t₁ h₁ t₂ h₂ hk
    rw [Finset.uniform_of_mem ((hmem t₁).mp h₁), Finset.uniform_of_mem ((hmem t₂).mp h₂),
      ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_lt_div_iff₀ (by exact_mod_cast hcard t₂ h₂) (by exact_mod_cast hcard t₁ h₁)]
    have hk' : ((S t₁).card : ℚ) + 1 ≤ (S t₂).card := by exact_mod_cast hk
    have hM : ((S t₂).card : ℚ) ≤ Fintype.card M := by exact_mod_cast Finset.card_le_univ _
    have k₂ : (0 : ℚ) < (S t₂).card := by exact_mod_cast hcard t₂ h₂
    have p₂ := hprior t₂
    refine lt_of_mul_lt_mul_right ?_ (k₂.trans_le hM).le
    calc G.prior t₂ * (S t₁).card * Fintype.card M
        ≤ G.prior t₂ * ((S t₂).card - 1) * Fintype.card M := by gcongr; linarith
      _ ≤ G.prior t₂ * (Fintype.card M - 1) * (S t₂).card := by
        nlinarith [mul_nonneg p₂.le (sub_nonneg.mpr hM)]
      _ < G.prior t₁ * (S t₂).card * Fintype.card M := by
        linarith [mul_lt_mul_of_pos_right (hnf t₁ t₂) k₂]
  rw [Finset.argmax_eq_argmax_of_support (t := senders) (Finset.filter_subset _ _)
    (Finset.nonempty_iff_ne_empty.mpr hne)
    (λ t ht => mul_pos (hprior t) (Finset.uniform_pos_iff.mpr ((hmem t).mp ht)))
    (λ t _ ht => by rw [Finset.uniform_of_notMem (mt (hmem t).mpr ht), mul_zero])]
  ext t
  simp only [Finset.mem_argmax, Finset.mem_argmin]
  constructor
  · rintro ⟨ht, hmax⟩
    have hmin : ∀ t' ∈ senders, (S t).card ≤ (S t').card := λ t' ht' => by
      by_contra h
      exact absurd (hmax t' ht') (not_le.mpr (hlt t' ht' t ht (not_le.mp h)))
    refine ⟨⟨ht, hmin⟩, λ t' ⟨ht', hmin'⟩ => ?_⟩
    have := hmax t' ht'
    rw [Finset.uniform_of_mem ((hmem t).mp ht), Finset.uniform_of_mem ((hmem t').mp ht'),
      show (S t').card = (S t).card from le_antisymm (hmin' t ht) (hmin t' ht')] at this
    exact le_of_mul_le_mul_right this (inv_pos.mpr (by exact_mod_cast hcard t ht))
  · rintro ⟨⟨ht, hmin⟩, hpr⟩
    refine ⟨ht, λ t' ht' => ?_⟩
    rcases lt_or_eq_of_le (hmin t' ht') with h | h
    · exact (hlt t ht t' ht' h).le
    · rw [Finset.uniform_of_mem ((hmem t).mp ht), Finset.uniform_of_mem ((hmem t').mp ht'), ← h]
      exact mul_le_mul_of_nonneg_right (hpr t' ⟨ht', λ t'' ht'' => h ▸ hmin t'' ht''⟩)
        (by positivity)

/-- Theorem 2, as a receiver response. -/
theorem receiverResponse_uniform_nearFlat (hprior : ∀ t, 0 < G.prior t) (hnf : NearFlat G)
    (S : T → Finset M) (m : M) :
    receiverResponse G (λ t => (S t).uniform) m = (receiverStepPrior G S m).uniform := by
  rw [receiverResponse_eq_uniform, receiverStepPrior, receiverStep]
  by_cases hemp : Finset.univ.filter (λ t => m ∈ S t) = ∅
  · rw [if_pos ((isSurprise_uniform_iff S m).mpr hemp), if_pos hemp]
  · rw [if_neg (mt (isSurprise_uniform_iff S m).mp hemp), if_neg hemp, if_neg hemp,
      argmax_prior_mul_uniform_nearFlat G hprior hnf hemp]

/-! ### Lemma 3 and Theorem 3: convergence (Appendix B.4)

Expected gain never decreases along the dynamics: the sender step because the
sender response averages the receiver's probability over its argmax, the
receiver step because the receiver response averages the posterior weight
over its argmax. Receiver levels are uniform vectors over finitely many
sets, so the sequence repeats; on a cycle the gain is constant, which forces
the optimal-message sets to grow around the cycle and hence to stabilise — a
fixed point. -/

section Convergence

omit [Fintype T] [DecidableEq T] in
/-- At each state the sender response is at least as good as any truthful
sub-probability sender. -/
theorem sender_inner_le (S : T → M → ℚ) (H : M → T → ℚ) (t : T) (hSNonneg : ∀ m, 0 ≤ S t m)
    (hSSum : ∑ m, S t m ≤ 1) (hSTruth : ∀ m, ¬ G.meaning m t → S t m = 0)
    (hH : ∀ m, 0 ≤ H m t) :
    ∑ m, S t m * H m t ≤ ∑ m, senderResponse G H t m * H m t := by
  rcases (G.trueMessages t).eq_empty_or_nonempty with hemp | hne
  · have : ∀ m, S t m = 0 := λ m =>
      hSTruth m λ h => Finset.notMem_empty m (hemp ▸ G.mem_trueMessages.mpr h)
    simp only [this, zero_mul, Finset.sum_const_zero]
    exact Finset.sum_nonneg λ m _ => mul_nonneg Finset.uniform_nonneg (hH m)
  · obtain ⟨m₀, hm₀⟩ := Finset.argmax_nonempty hne (f := (H · t))
    rw [senderResponse, optimalMessages, Finset.sum_uniform_argmax_mul _ hm₀]
    exact Finset.sum_mul_le_of_support _ _ hSNonneg hSSum
      (λ m hm => hSTruth m (mt G.mem_trueMessages.mpr hm)) hH hm₀

omit [DecidableEq T] in
/-- Lemma 3 (i): the sender step does not decrease expected gain. -/
theorem eg_sender_improvement (S : T → M → ℚ) (H : M → T → ℚ)
    (hPrior : ∀ t, 0 ≤ G.prior t) (hSNonneg : ∀ t m, 0 ≤ S t m)
    (hSSum : ∀ t, ∑ m, S t m ≤ 1) (hSTruth : ∀ t m, ¬ G.meaning m t → S t m = 0)
    (hH : ∀ m t, 0 ≤ H m t) :
    expectedGain G S H ≤ expectedGain G (senderResponse G H) H :=
  Finset.sum_le_sum λ t _ => mul_le_mul_of_nonneg_left
    (sender_inner_le G S H t (hSNonneg t) (hSSum t) (hSTruth t) (hH · t)) (hPrior t)

omit [Fintype M] [DecidableEq M] in
/-- After each message the receiver response is at least as good as any
sub-probability receiver. -/
theorem receiver_inner_le (S : T → M → ℚ) (H : M → T → ℚ) (m : M)
    (hPrior : ∀ t, 0 ≤ G.prior t) (hSNonneg : ∀ t, 0 ≤ S t m) (hH : ∀ t, 0 ≤ H m t)
    (hHSum : ∑ t, H m t ≤ 1) :
    ∑ t, G.prior t * S t m * H m t ≤ ∑ t, G.prior t * S t m * receiverResponse G S m t := by
  have hw : ∀ t, 0 ≤ G.prior t * S t m := λ t => mul_nonneg (hPrior t) (hSNonneg t)
  by_cases hs : IsSurprise S m
  · have h0 : ∀ t, S t m = 0 := hs
    simp [h0]
  · obtain ⟨t₁, _⟩ := not_forall.mp hs
    obtain ⟨t₀, ht₀⟩ :=
      Finset.argmax_nonempty ⟨t₁, Finset.mem_univ t₁⟩ (f := λ t => G.prior t * S t m)
    rw [receiverResponse, if_neg hs]
    simp_rw [mul_comm (G.prior _ * S _ m)]
    rw [Finset.sum_uniform_argmax_mul _ ht₀]
    exact Finset.sum_mul_le_of_support _ _ hH hHSum (λ t ht => absurd (Finset.mem_univ t) ht) hw ht₀

omit [DecidableEq M] in
/-- Lemma 3 (ii): the receiver step does not decrease expected gain. -/
theorem eg_receiver_improvement (S : T → M → ℚ) (H : M → T → ℚ)
    (hPrior : ∀ t, 0 ≤ G.prior t) (hSNonneg : ∀ t m, 0 ≤ S t m)
    (hH : ∀ m t, 0 ≤ H m t) (hHSum : ∀ m, ∑ t, H m t ≤ 1) :
    expectedGain G S H ≤ expectedGain G S (receiverResponse G S) := by
  unfold expectedGain
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm, Finset.sum_comm (f := λ t m => G.prior t * S t m * receiverResponse G S m t)]
  exact Finset.sum_le_sum λ m _ =>
    receiver_inner_le G S H m hPrior (hSNonneg · m) (hH m) (hHSum m)

/-- Lemma 3: expected gain is monotone along the receiver levels. -/
theorem eg_monotone (hPrior : ∀ t, 0 ≤ G.prior t) (n : ℕ) :
    expectedGain G (senderResponse G (receiverLevel G n)) (receiverLevel G n) ≤
      expectedGain G (senderResponse G (receiverLevel G (n + 1))) (receiverLevel G (n + 1)) :=
  calc _ ≤ expectedGain G (senderResponse G (receiverLevel G n)) (receiverLevel G (n + 1)) :=
        eg_receiver_improvement G _ _ hPrior (λ _ _ => Finset.uniform_nonneg)
          (receiverLevel_nonneg G n) (receiverLevel_sum_le_one G n)
    _ ≤ _ := eg_sender_improvement G _ _ hPrior (λ _ _ => Finset.uniform_nonneg)
          (λ _ => Finset.sum_uniform_le_one) (λ _ _ => senderResponse_eq_zero_of_not_meaning G _)
          (receiverLevel_nonneg G _)

omit [DecidableEq T] [DecidableEq M] in
/-- Expected gain is at most one. -/
theorem expectedGain_le_one (S : T → M → ℚ) (H : M → T → ℚ) (hPriorSum : ∑ t, G.prior t = 1)
    (hPrior : ∀ t, 0 ≤ G.prior t) (hSNonneg : ∀ t m, 0 ≤ S t m) (hSSum : ∀ t, ∑ m, S t m ≤ 1)
    (hH : ∀ m t, H m t ≤ 1) : expectedGain G S H ≤ 1 :=
  calc expectedGain G S H ≤ ∑ t, G.prior t * 1 := Finset.sum_le_sum λ t _ =>
        mul_le_mul_of_nonneg_left
          ((Finset.sum_le_sum λ m _ => mul_le_mul_of_nonneg_left (hH m t) (hSNonneg t m)).trans
            (by simpa using hSSum t)) (hPrior t)
    _ = 1 := by simp [hPriorSum]

omit [DecidableEq T] in
/-- Equal expected gain against the sender response forces every positively
used message to be optimal, at every positive-prior state. -/
theorem mem_optimalMessages_of_eg_eq (S : T → M → ℚ) (H : M → T → ℚ)
    (hPrior : ∀ t, 0 ≤ G.prior t) (hSNonneg : ∀ t m, 0 ≤ S t m)
    (hSSum : ∀ t, ∑ m, S t m ≤ 1) (hSTruth : ∀ t m, ¬ G.meaning m t → S t m = 0)
    (hH : ∀ m t, 0 ≤ H m t) (hEG : expectedGain G S H = expectedGain G (senderResponse G H) H)
    (t : T) (hPt : 0 < G.prior t) (m : M) (hSm : 0 < S t m) : m ∈ optimalMessages G H t := by
  have hle : ∀ s, ∑ m, S s m * H m s ≤ ∑ m, senderResponse G H s m * H m s := λ s =>
    sender_inner_le G S H s (hSNonneg s) (hSSum s) (hSTruth s) (hH · s)
  have hinner : ∑ m, S t m * H m t = ∑ m, senderResponse G H t m * H m t := by
    have := (Finset.sum_eq_zero_iff_of_nonneg λ s _ =>
      mul_nonneg (hPrior s) (sub_nonneg.mpr (hle s))).mp (by
        unfold expectedGain at hEG
        simp only [mul_sub, Finset.sum_sub_distrib, hEG, sub_self]) t (Finset.mem_univ t)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hPt.ne'
    · linarith
  have hTrue : G.meaning m t := by
    by_contra hF; exact absurd hSm (by rw [hSTruth t m hF]; exact lt_irrefl 0)
  obtain ⟨m₀, hm₀⟩ := Finset.argmax_nonempty ⟨m, G.mem_trueMessages.mpr hTrue⟩ (f := (H · t))
  rw [senderResponse, optimalMessages, Finset.sum_uniform_argmax_mul _ hm₀] at hinner
  refine (mem_optimalMessages G).mpr ⟨hTrue, λ m' hm' => ?_⟩
  by_contra hne
  have hlt : H m t < H m₀ t := lt_of_le_of_ne
    ((Finset.mem_argmax.mp hm₀).2 m (G.mem_trueMessages.mpr hTrue))
    λ h => hne (h ▸ (Finset.mem_argmax.mp hm₀).2 m' (G.mem_trueMessages.mpr hm'))
  have : ∑ m', S t m' * H m' t < H m₀ t :=
    calc ∑ m', S t m' * H m' t < ∑ m', S t m' * H m₀ t := by
          refine Finset.sum_lt_sum (λ m' _ => ?_)
            ⟨m, Finset.mem_univ m, mul_lt_mul_of_pos_left hlt hSm⟩
          by_cases hm' : G.meaning m' t
          · exact mul_le_mul_of_nonneg_left ((Finset.mem_argmax.mp hm₀).2 m'
              (G.mem_trueMessages.mpr hm')) (hSNonneg t m')
          · simp [hSTruth t m' hm']
      _ = (∑ m', S t m') * H m₀ t := by rw [Finset.sum_mul]
      _ ≤ 1 * H m₀ t := mul_le_mul_of_nonneg_right (hSSum t) (hH m₀ t)
      _ = H m₀ t := one_mul _
  exact absurd hinner this.ne

omit [DecidableEq T] in
theorem optimalMessages_subset_of_eg_eq (H₁ H₂ : M → T → ℚ) (hPrior : ∀ t, 0 < G.prior t)
    (hH₂ : ∀ m t, 0 ≤ H₂ m t)
    (hEG : expectedGain G (senderResponse G H₁) H₂ = expectedGain G (senderResponse G H₂) H₂)
    (t : T) : optimalMessages G H₁ t ⊆ optimalMessages G H₂ t := λ m hm =>
  mem_optimalMessages_of_eg_eq G (senderResponse G H₁) H₂ (λ t => (hPrior t).le)
    (λ _ _ => Finset.uniform_nonneg) (λ _ => Finset.sum_uniform_le_one)
    (λ _ _ hm' => senderResponse_eq_zero_of_not_meaning G H₁ hm') hH₂ hEG t (hPrior t) m
    ((senderResponse_pos_iff G H₁ t m).mpr hm)

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

/-- The set of states a receiver level assigns positive probability. -/
def receiverSupport (n : ℕ) (m : M) : Finset T :=
  Finset.univ.filter λ t => 0 < receiverLevel G n m t

/-- Receiver levels are uniform over their supports. -/
theorem receiverLevel_eq_uniform_support (n : ℕ) :
    receiverLevel G n = λ m => (receiverSupport G n m).uniform := by
  have : ∀ n, ∃ A : M → Finset T, receiverLevel G n = λ m => (A m).uniform := λ n => by
    cases n with
    | zero => exact ⟨G.trueStates, rfl⟩
    | succ n => exact ⟨_, funext λ m => receiverResponse_eq_uniform G _ m⟩
  obtain ⟨A, hA⟩ := this n
  rw [hA]; funext m; congr 1; ext t
  rw [receiverSupport, Finset.mem_filter, hA]
  simp [Finset.uniform_pos_iff]

/-- The receiver levels repeat: there are finitely many supports. -/
theorem receiverLevel_repeats :
    ∃ n₁ n₂, n₁ < n₂ ∧ receiverLevel G n₁ = receiverLevel G n₂ := by
  obtain ⟨n₁, n₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (receiverSupport G)
  have hstrat : receiverLevel G n₁ = receiverLevel G n₂ := by
    rw [receiverLevel_eq_uniform_support, receiverLevel_eq_uniform_support, heq]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨n₁, n₂, h, hstrat⟩
  · exact ⟨n₂, n₁, h, hstrat.symm⟩

/-- Theorem 3: the receiver levels reach a fixed point. -/
theorem receiverLevel_reaches_fixedPoint (hPrior : ∀ t, 0 < G.prior t) :
    ∃ n, IsFixedPoint G (receiverLevel G n) := by
  obtain ⟨n₁, n₂, hlt, heq⟩ := receiverLevel_repeats G
  have hperiod : receiverLevel G n₁ = receiverLevel G (n₁ + (n₂ - n₁)) := by
    rwa [Nat.add_sub_cancel' hlt.le]
  set eg := λ n => expectedGain G (senderResponse G (receiverLevel G n)) (receiverLevel G n)
  have hOptSub : ∀ k, k < n₂ - n₁ → ∀ t, optimalMessages G (receiverLevel G (n₁ + k)) t ⊆
      optimalMessages G (receiverLevel G (n₁ + k + 1)) t := by
    intro k hk
    have hEGk := monotone_cycle_all_eq (eg_monotone G λ t => (hPrior t).le)
      (show eg n₁ = eg (n₁ + (n₂ - n₁)) by simp only [eg]; rw [hperiod]) k hk
    refine optimalMessages_subset_of_eg_eq G _ _ hPrior (receiverLevel_nonneg G _)
      (le_antisymm ?_ ?_)
    · exact eg_sender_improvement G _ _ (λ t => (hPrior t).le) (λ _ _ => Finset.uniform_nonneg)
        (λ _ => Finset.sum_uniform_le_one) (λ _ _ => senderResponse_eq_zero_of_not_meaning G _)
        (receiverLevel_nonneg G _)
    · have := eg_receiver_improvement G (senderResponse G (receiverLevel G (n₁ + k)))
        (receiverLevel G (n₁ + k)) (λ t => (hPrior t).le) (λ _ _ => Finset.uniform_nonneg)
        (receiverLevel_nonneg G _) (receiverLevel_sum_le_one G _)
      have hlev : receiverLevel G (n₁ + k + 1) =
          receiverResponse G (senderResponse G (receiverLevel G (n₁ + k))) := rfl
      rw [← hEGk, hlev]; exact this
  have hOptEq : ∀ t, optimalMessages G (receiverLevel G n₁) t =
      optimalMessages G (receiverLevel G (n₁ + 1)) t := λ t =>
    cycle_containment_eq (λ k => optimalMessages G (receiverLevel G (n₁ + k)) t) (by omega)
      (λ k hk => hOptSub k hk t)
      (by show optimalMessages G (receiverLevel G (n₁ + (n₂ - n₁))) t = _; rw [← hperiod]; rfl)
  refine ⟨n₁ + 1, ?_⟩
  have hS : senderResponse G (receiverLevel G (n₁ + 1)) = senderResponse G (receiverLevel G n₁) :=
    funext λ t => by simp only [senderResponse, hOptEq t]
  show receiverResponse G (senderResponse G (receiverLevel G (n₁ + 1))) =
    receiverResponse G (senderResponse G (receiverLevel G n₁))
  rw [hS]

end Convergence

/-! ### Theorem 4: fixed points are perfect Bayesian equilibria -/

/-- Posterior beliefs consistent with the prior and a sender strategy (119);
after a surprise message the receiver keeps the literal belief. -/
def posterior (S : T → M → ℚ) (m : M) (t : T) : ℚ :=
  if IsSurprise S m then G.literal m t else G.prior t * S t m / ∑ s, G.prior s * S s m

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

/-- Theorem 4: a fixed point of the heavy dynamics, with its sender response,
is a perfect Bayesian equilibrium. -/
theorem isPBE_of_fixedPoint (hprior : ∀ t, 0 < G.prior t) {H : M → T → ℚ}
    (hH : IsFixedPoint G H) : IsPBE G (senderResponse G H) H := by
  refine ⟨λ t m h => (senderResponse_pos_iff G H t m).mp h, λ m t hpos => ?_⟩
  rw [← hH, receiverResponse_eq_uniform, Finset.uniform_pos_iff] at hpos
  unfold posterior
  split_ifs at hpos ⊢ with hs
  · show t ∈ Finset.univ.argmax λ t => (G.trueStates m).uniform t
    rw [Finset.argmax_eq_argmax_of_support (t := G.trueStates m) (Finset.subset_univ _) ⟨t, hpos⟩
      (λ t ht => Finset.uniform_pos_iff.mpr ht) (λ t _ ht => Finset.uniform_of_notMem ht),
      Finset.argmax_eq_self_of_forall_le λ t ht t' ht' => by
        rw [Finset.uniform_of_mem ht, Finset.uniform_of_mem ht']]
    exact hpos
  · have hz : 0 < ∑ s, G.prior s * senderResponse G H s m := by
      obtain ⟨s, hs⟩ := not_forall.mp hs
      exact Finset.sum_pos' (λ s _ => mul_nonneg (hprior s).le Finset.uniform_nonneg)
        ⟨s, Finset.mem_univ s,
          mul_pos (hprior s) (lt_of_le_of_ne Finset.uniform_nonneg (Ne.symm hs))⟩
    simp_rw [div_eq_mul_inv]
    show t ∈ Finset.univ.argmax ((λ x => x * (∑ s, G.prior s * senderResponse G H s m)⁻¹) ∘
      λ s => G.prior s * senderResponse G H s m)
    rwa [Finset.argmax_comp_strictMono (strictMono_mul_right_of_pos (inv_pos.mpr hz))]

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

Fact 3, `ExhMM ⊆ ExhIE`, is `Exhaustification.exhMW_subset_exhIE`. Lemma 1
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
