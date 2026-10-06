module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Linglib.Core.Order.Argmax

/-!
# Signaling games

In a signaling game a sender who privately knows her type `t : T` sends a message `m : M`, and a
receiver who observes the message chooses an action `a : A`. Each player's utility depends on
all three, so a message can be costly to send. Lewisian conventions, games of partial
information and iterated best response are analyses of this one structure; interpretation games
are the case where the actions are the types.

Pure strategies are functions `σ : T → M` and `ρ : M → A`. Best responses form a set, so after a
message that no type sends the posterior is zero, every action is a best response, and the
equilibrium condition constrains nothing there.

## Main definitions

* `SignalingGame`: types, messages, actions, a prior and the two utilities.
* `SignalingGame.Cooperative`, `SignalingGame.ZeroSum`: aligned and opposed interests.
* `SignalingGame.posterior`: the receiver's Bayesian belief after a message under a pure sender
  strategy.
* `SignalingGame.bestResponseSet`: the receiver's best responses to a belief.
* `SignalingGame.isNashEquilibrium`, `isSeparatingEquilibrium`, `isPoolingEquilibrium`.

## Main statements

* `posterior_of_injective`: under a separating sender strategy the posterior after a sent
  message is the point mass on its sender.
* `posterior_eq_zero_of_forall_ne`: the posterior after an unsent message is zero.

## References

* [lewis-1969]
* [benz-stevens-2018]
* [franke-2011]
-/

@[expose] public section

/-- In a signaling game the sender privately knows her type and chooses a message, and the
receiver observes the message and chooses an action; utilities may depend on the message. -/
structure SignalingGame (T M A : Type*) where
  /-- `senderUtility t m a` is the sender's utility when type `t` sends `m` and the receiver
  takes `a`. -/
  senderUtility : T → M → A → ℝ
  /-- `receiverUtility t m a` is the receiver's utility when type `t` sends `m` and the receiver
  takes `a`. -/
  receiverUtility : T → M → A → ℝ
  /-- `prior t` is the prior weight of type `t`. -/
  prior : T → ℝ

namespace SignalingGame

variable {T M A : Type*} (g : SignalingGame T M A)

/-! ### Alignment of interests -/

/-- A game is cooperative when the two players' utilities coincide. -/
class Cooperative (g : SignalingGame T M A) : Prop where
  utility_eq : ∀ t m a, g.senderUtility t m a = g.receiverUtility t m a

/-- A game is zero-sum when the two players' utilities are opposite. -/
class ZeroSum (g : SignalingGame T M A) : Prop where
  utility_neg : ∀ t m a, g.senderUtility t m a = -g.receiverUtility t m a

/-! ### Beliefs and best responses -/

/-- `receiverEU μ m a` is the receiver's expected utility of action `a` after message `m` under
the belief `μ`. -/
def receiverEU [Fintype T] (μ : T → ℝ) (m : M) (a : A) : ℝ :=
  ∑ t, μ t * g.receiverUtility t m a

/-- The posterior after `m` under the pure sender strategy `σ` is `Pr(t)/Z` on the types that
send `m`, where `Z` is their total prior weight, and zero when no type sends `m`. -/
noncomputable def posterior [Fintype T] [DecidableEq M] (σ : T → M) (m : M) (t : T) : ℝ :=
  let Z := ∑ t' ∈ Finset.univ.filter (σ · = m), g.prior t'
  if Z = 0 then 0 else if σ t = m then g.prior t / Z else 0

/-- The receiver's best responses to `m` under the belief `μ` are the actions of greatest
expected utility. -/
noncomputable def bestResponseSet [Fintype T] [Fintype A] (μ : T → ℝ) (m : M) : Finset A :=
  Finset.univ.argmax (g.receiverEU μ m)

/-! ### Equilibrium -/

section Equilibrium

variable [Fintype T] [Fintype A] [DecidableEq M]

/-- A pure strategy profile is a Nash equilibrium when at every type no other message serves
the sender better against `ρ`, and after every message the receiver's action is a best
response to the posterior. -/
def isNashEquilibrium (σ : T → M) (ρ : M → A) : Prop :=
  (∀ t m', g.senderUtility t m' (ρ m') ≤ g.senderUtility t (σ t) (ρ (σ t))) ∧
  (∀ m, ρ m ∈ g.bestResponseSet (g.posterior σ m) m)

/-- A separating equilibrium is a Nash equilibrium in which distinct types send distinct
messages. -/
def isSeparatingEquilibrium (σ : T → M) (ρ : M → A) : Prop :=
  g.isNashEquilibrium σ ρ ∧ Function.Injective σ

/-- A pooling equilibrium is a Nash equilibrium in which all types send the same message. -/
def isPoolingEquilibrium (σ : T → M) (ρ : M → A) : Prop :=
  g.isNashEquilibrium σ ρ ∧ ∀ t t', σ t = σ t'

end Equilibrium

/-- Under a separating sender strategy with positive priors, the posterior after the message
of `t` is the point mass on `t`. -/
theorem posterior_of_injective [Fintype T] [DecidableEq T] [DecidableEq M] (σ : T → M)
    (hσ : Function.Injective σ) (hprior : ∀ t, 0 < g.prior t) (t : T) :
    g.posterior σ (σ t) = Pi.single t 1 := by
  ext t'
  rcases eq_or_ne t' t with rfl | hne
  · simp [posterior, hσ.eq_iff, Finset.filter_eq', (hprior t').ne', div_self]
  · simp [posterior, hσ.eq_iff, Finset.filter_eq', (hprior t).ne', hne]

/-- The posterior after a message that no type sends is zero. -/
theorem posterior_eq_zero_of_forall_ne [Fintype T] [DecidableEq M] {σ : T → M} {m : M}
    (h : ∀ t, σ t ≠ m) : g.posterior σ m = 0 := by
  ext t
  simp [posterior, h]

/-! ### Conventional and speaker's meaning

[lewis-1969]'s contrast between what a message conventionally means and what its sender
means by it, in signaling terms. -/

/-- A conventional meaning maps each message to a proposition over types. -/
def ConventionalMeaning (M T : Type*) := M → T → Prop

/-- The speaker's meaning of `t`'s message under `σ` is the set of types sending the same
message as `t`. -/
def speakerMeaning (σ : T → M) (t : T) : T → Prop :=
  fun t' ↦ σ t' = σ t

/-- What the receiver can infer from `t`'s message is the intersection of its conventional
meaning and the speaker's meaning. -/
def communicatedMeaning (conv : ConventionalMeaning M T) (σ : T → M) (t : T) : T → Prop :=
  fun t' ↦ conv (σ t) t' ∧ speakerMeaning σ t t'

/-- A sender strategy is truthful when every type's message conventionally includes it. -/
def isTruthful (conv : ConventionalMeaning M T) (σ : T → M) : Prop :=
  ∀ t, conv (σ t) t

end SignalingGame
