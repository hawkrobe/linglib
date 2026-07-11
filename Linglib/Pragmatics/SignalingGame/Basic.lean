import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.BigOperators
import Linglib.Core.Order.Argmax

/-!
# Signaling games

The shared carrier for game-theoretic pragmatics: a sender who privately
knows her type `t : T` chooses a message `m : M`; a receiver observes `m`
and chooses an action `a : A`; utilities depend on all three (the message
argument carries signalling costs). Lewisian conventions ([lewis-1969]),
credible communication ([van-rooy-2003]), and iterated-best-response
pragmatics ([franke-2011]) are all analyses of this carrier; interpretation
games arise as the specialization `A = T` with matching utility
(conditions C1/C2 of [franke-2011]'s Theorem 1).

Pure strategies are plain functions (`σ : T → M`, `ρ : M → A`); mixed
strategies are Kleisli arrows into `PMF` and live with the consumers that
need them. Best responses are *set-valued* (`Finset.argmax`), which gives
off-path messages the standard "unconstrained belief" reading for free:
after a message no type sends, the posterior is identically zero, every
action is trivially expected-utility-maximal, and the equilibrium condition
constrains nothing.

## Main definitions

* `SignalingGame` — types, messages, actions, prior, sender/receiver utility.
* `SignalingGame.Cooperative` / `ZeroSum` — alignment mixins.
* `SignalingGame.posterior` — Bayesian beliefs after a message under a pure
  sender strategy (zero off path).
* `SignalingGame.bestResponseSet` — receiver argmax set under given beliefs.
* `SignalingGame.isNashEquilibrium`, `isSeparatingEquilibrium`,
  `isPoolingEquilibrium` — pure-strategy equilibrium notions.

## Main statements

* `posterior_of_injective` — under a separating (injective) sender strategy,
  the on-path posterior is a point mass: full information transmission.
-/

set_option autoImplicit false

/-- A signaling game: the sender privately knows her type and chooses a
message; the receiver observes the message and chooses an action. Utilities
may depend on the message (signalling costs). -/
structure SignalingGame (T M A : Type*) where
  /-- Sender's utility, as a function of type, sent message, and action. -/
  senderUtility : T → M → A → ℚ
  /-- Receiver's utility, as a function of type, observed message, and action. -/
  receiverUtility : T → M → A → ℚ
  /-- Prior probability over types. -/
  prior : T → ℚ

namespace SignalingGame

variable {T M A : Type*} (g : SignalingGame T M A)

/-! ## Alignment mixins -/

/-- A cooperative game: sender and receiver utilities coincide (Lewisian
common interest, [lewis-1969]). -/
class Cooperative (g : SignalingGame T M A) : Prop where
  utility_eq : ∀ t m a, g.senderUtility t m a = g.receiverUtility t m a

/-- A zero-sum game: utilities are opposite. No credible communication is
possible. -/
class ZeroSum (g : SignalingGame T M A) : Prop where
  utility_neg : ∀ t m a, g.senderUtility t m a = -g.receiverUtility t m a

/-! ## Beliefs and best responses -/

/-- Receiver's expected utility of action `a` after message `m`, under
beliefs `μ` over types. -/
def receiverEU [Fintype T] (μ : T → ℚ) (m : M) (a : A) : ℚ :=
  ∑ t, μ t * g.receiverUtility t m a

/-- Bayesian beliefs over types after observing `m`, given the pure sender
strategy `σ`: `Pr(t)/Z` on the senders of `m`, where `Z` is their total
prior mass. Identically zero off path (`Z = 0`). -/
def posterior [Fintype T] [DecidableEq M] (σ : T → M) (m : M) (t : T) : ℚ :=
  let Z := ∑ t' ∈ Finset.univ.filter (σ · = m), g.prior t'
  if Z = 0 then 0 else if σ t = m then g.prior t / Z else 0

/-- The set of receiver best responses to message `m` under beliefs `μ`:
the actions maximizing expected receiver utility. -/
def bestResponseSet [Fintype T] [Fintype A] (μ : T → ℚ) (m : M) : Finset A :=
  Finset.univ.argmax (g.receiverEU μ m)

/-! ## Equilibrium -/

section Equilibrium

variable [Fintype T] [Fintype A] [DecidableEq M]

/-- Pure-strategy Nash equilibrium: at every type the sender's message is
optimal given the receiver's response rule, and after every message the
receiver's action is a best response to the Bayesian posterior. Off-path
messages constrain nothing: the posterior is zero, so `bestResponseSet` is
all of `A`. -/
def isNashEquilibrium (σ : T → M) (ρ : M → A) : Prop :=
  (∀ t m', g.senderUtility t m' (ρ m') ≤ g.senderUtility t (σ t) (ρ (σ t))) ∧
  (∀ m, ρ m ∈ g.bestResponseSet (g.posterior σ m) m)

/-- Separating equilibrium: distinct types send distinct messages — full
information transmission ([lewis-1969] signaling conventions). -/
def isSeparatingEquilibrium (σ : T → M) (ρ : M → A) : Prop :=
  g.isNashEquilibrium σ ρ ∧ Function.Injective σ

/-- Pooling equilibrium: all types send the same message — no information
transmission. -/
def isPoolingEquilibrium (σ : T → M) (ρ : M → A) : Prop :=
  g.isNashEquilibrium σ ρ ∧ ∀ t t', σ t = σ t'

end Equilibrium

/-- Under an injective (separating) sender strategy with positive priors,
the on-path posterior is a point mass on the actual type: separating
strategies transmit full information. -/
theorem posterior_of_injective [Fintype T] [DecidableEq T] [DecidableEq M] (σ : T → M)
    (hσ : Function.Injective σ) (hprior : ∀ t, 0 < g.prior t) (t t' : T) :
    g.posterior σ (σ t) t' = if t' = t then 1 else 0 := by
  have hfilter : Finset.univ.filter (σ · = σ t) = {t} := by
    ext x
    simp [hσ.eq_iff]
  rw [posterior, hfilter]
  simp only [Finset.sum_singleton]
  rw [if_neg (ne_of_gt (hprior t))]
  rcases eq_or_ne t' t with rfl | hne
  · rw [if_pos rfl, if_pos rfl, div_self (ne_of_gt (hprior t'))]
  · rw [if_neg (fun h => hne (hσ h)), if_neg hne]

/-! ## Conventional vs speaker's meaning

The Gricean contrast in signaling terms ([lewis-1969], [van-rooy-2003]):
*conventional* meaning is an exogenous interpretation function; the
*speaker's* meaning of `σ t` is the cell of the partition that the sender
strategy induces on types; what the receiver can infer is their
intersection. -/

/-- Conventional meaning: an exogenous interpretation function from
messages to propositions over types. -/
def ConventionalMeaning (M T : Type*) := M → T → Prop

/-- Speaker's meaning of `t`'s message under sender strategy `σ`: the types
sending the same message as `t`. -/
def speakerMeaning (σ : T → M) (t : T) : T → Prop :=
  fun t' => σ t' = σ t

/-- Communicated meaning: what the receiver can infer, the intersection of
conventional and speaker's meaning. -/
def communicatedMeaning (conv : ConventionalMeaning M T) (σ : T → M)
    (t : T) : T → Prop :=
  fun t' => conv (σ t) t' ∧ speakerMeaning σ t t'

/-- A sender strategy is truthful if every type's message conventionally
includes that type. -/
def isTruthful (conv : ConventionalMeaning M T) (σ : T → M) : Prop :=
  ∀ t, conv (σ t) t

end SignalingGame
