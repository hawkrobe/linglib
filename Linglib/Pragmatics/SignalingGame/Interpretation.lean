import Linglib.Pragmatics.SignalingGame.Basic

/-!
# Interpretation games

The interpretation-game specialization of `SignalingGame`: receiver actions
are type guesses (`A = T`) and both players are paid by the match indicator —
conditions C1 and C2 of [franke-2011]'s Theorem 1, made true by construction
in `InterpGame.toSignalingGame`. The extra datum an interpretation game
carries is the semantic `meaning` relation between messages and types, which
drives the literal listener and the pragmatic dynamics; it does not enter
the utilities.

General/specialized file split on the mathlib `Kernel.Defs` /
`Kernel.Deterministic` pattern: `Basic.lean` states the general carrier,
this file the specialization with its own ergonomic profile, connected by
construction (`toSignalingGame`) rather than by a bridge theorem.

## Main definitions

* `InterpGame` — meaning relation and prior; messages denote sets of types.
* `InterpGame.trueStates` / `trueMessages` — extension of a message / the
  messages true at a type.
* `InterpGame.literal` — the literal listener, uniform over the extension.
* `InterpGame.toSignalingGame` — Franke's C1/C2 reduction, with a
  `Cooperative` instance.

## Main statements

* `bestResponseSet_toSignalingGame` — under matching utility the receiver's
  best-response set is the argmax of his beliefs: interpretation is
  maximum-a-posteriori estimation.
-/

set_option autoImplicit false

/-- An interpretation game: a semantic `meaning` relation between messages
and types, and a prior over types. The receiver's task is to guess the
sender's type; utilities are fixed by the `toSignalingGame` reduction. -/
structure InterpGame (T M : Type*) where
  /-- Semantic meaning: is message `m` true at type `t`? -/
  meaning : M → T → Prop
  /-- Prior probability over types. -/
  prior : T → ℚ
  [meaningDecidable : ∀ m, DecidablePred (meaning m)]

attribute [instance] InterpGame.meaningDecidable

namespace InterpGame

variable {T M : Type*} (G : InterpGame T M)

/-! ## Extensions and the literal listener -/

section Extension

variable [Fintype T]

/-- The extension of message `m`: the types at which it is true. -/
def trueStates (m : M) : Finset T :=
  Finset.univ.filter (G.meaning m)

@[simp]
theorem mem_trueStates {m : M} {t : T} : t ∈ G.trueStates m ↔ G.meaning m t := by
  simp [trueStates]

/-- The literal listener: uniform over the extension of the message — the
level-0 receiver of [franke-2011] (eq. (73)) in its Bayesian heavy-system
rendering. -/
def literal (m : M) (t : T) : ℚ :=
  if G.meaning m t then ((G.trueStates m).card : ℚ)⁻¹ else 0

end Extension

/-- The messages true at type `t`. -/
def trueMessages [Fintype M] (t : T) : Finset M :=
  Finset.univ.filter (G.meaning · t)

@[simp]
theorem mem_trueMessages [Fintype M] {t : T} {m : M} :
    m ∈ G.trueMessages t ↔ G.meaning m t := by
  simp [trueMessages]

/-! ## The signaling-game reduction -/

variable [DecidableEq T]

/-- Franke's reduction: the signaling game with actions = types (C1) and
matching utility for both players (C2). The meaning relation does not enter
the utilities — it constrains the *dynamics* (literal listener, truthful
speakers), not the payoffs. -/
def toSignalingGame : SignalingGame T M T where
  senderUtility t _ a := if a = t then 1 else 0
  receiverUtility t _ a := if a = t then 1 else 0
  prior := G.prior

/-- Interpretation games are cooperative: C2 gives both players the same
matching utility. -/
instance : G.toSignalingGame.Cooperative :=
  ⟨fun _ _ _ => rfl⟩

/-- Under matching utility, the expected receiver utility of guessing `a`
is exactly the belief in `a`. -/
@[simp]
theorem receiverEU_toSignalingGame [Fintype T] (μ : T → ℚ) (m : M) (a : T) :
    G.toSignalingGame.receiverEU μ m a = μ a := by
  simp [SignalingGame.receiverEU, toSignalingGame, mul_ite]

/-- **Interpretation is MAP estimation**: in an interpretation game the
receiver's best responses to beliefs `μ` are exactly the
maximum-a-posteriori types. -/
theorem bestResponseSet_toSignalingGame [Fintype T] (μ : T → ℚ) (m : M) :
    G.toSignalingGame.bestResponseSet μ m = Finset.univ.argmax μ := by
  unfold SignalingGame.bestResponseSet
  congr 1
  funext a
  exact G.receiverEU_toSignalingGame μ m a

end InterpGame
