module

public import Linglib.Core.Probability.Uniform
public import Linglib.Pragmatics.SignalingGame.Basic

/-!
# Interpretation games

An interpretation game is a signaling game in which the receiver guesses the sender's type and
both players receive `1` for a correct guess and `0` otherwise. It is given by a meaning relation
between messages and types, which drives the literal listener and pragmatic reasoning, and a
prior over types; the meaning does not enter the utilities. Under these utilities the receiver's
best responses are the most probable types, and any strategy profile under which the receiver
always recovers the sender's type is a Nash equilibrium.

## Main definitions

* `InterpGame`: a meaning relation and a prior.
* `InterpGame.trueStates`, `InterpGame.trueMessages`: the types at which a message is true, and
  the messages true at a type.
* `InterpGame.literal`: the literal listener, uniform over the types at which the message is
  true.
* `InterpGame.toSignalingGame`: the cooperative signaling game whose actions are the types.

## Main statements

* `bestResponseSet_toSignalingGame`: the receiver's best responses are the most probable types.
* `isNashEquilibrium_of_leftInverse`: perfect communication is a Nash equilibrium.

## References

* [franke-2011]
-/

@[expose] public section

/-- An interpretation game is a meaning relation between messages and types together with a
prior over types. -/
structure InterpGame (T M : Type*) where
  /-- `meaning m t` holds when message `m` is true at type `t`. -/
  meaning : M → T → Prop
  /-- `prior t` is the prior weight of type `t`. -/
  prior : T → ℝ
  [meaningDecidable : ∀ m, DecidablePred (meaning m)]

attribute [instance] InterpGame.meaningDecidable

namespace InterpGame

variable {T M : Type*} (G : InterpGame T M)

/-! ### Extensions and the literal listener -/

section Extension

variable [Fintype T]

/-- The extension of `m` is the set of types at which it is true. -/
def trueStates (m : M) : Finset T :=
  Finset.univ.filter (G.meaning m)

@[simp]
theorem mem_trueStates {m : M} {t : T} : t ∈ G.trueStates m ↔ G.meaning m t := by
  simp [trueStates]

/-- The literal listener is uniform over the extension of the message. -/
noncomputable def literal [DecidableEq T] (m : M) : T → ℝ := (G.trueStates m).uniform

theorem literal_apply [DecidableEq T] (m : M) (t : T) :
    G.literal m t = if G.meaning m t then ((G.trueStates m).card : ℝ)⁻¹ else 0 := by
  simp only [literal, Finset.uniform_apply, mem_trueStates]

end Extension

/-- `trueMessages t` is the set of messages true at `t`. -/
def trueMessages [Fintype M] (t : T) : Finset M :=
  Finset.univ.filter (G.meaning · t)

@[simp]
theorem mem_trueMessages [Fintype M] {t : T} {m : M} :
    m ∈ G.trueMessages t ↔ G.meaning m t := by
  simp [trueMessages]

/-! ### The signaling game -/

variable [DecidableEq T]

/-- The signaling game of an interpretation game has the types as actions and pays both players
`1` exactly when the action is the sender's type. -/
def toSignalingGame : SignalingGame T M T where
  senderUtility t _ a := if a = t then 1 else 0
  receiverUtility t _ a := if a = t then 1 else 0
  prior := G.prior

instance : G.toSignalingGame.Cooperative :=
  ⟨fun _ _ _ ↦ rfl⟩

/-- Under matching utility the expected utility of guessing `a` is the belief in `a`. -/
@[simp]
theorem receiverEU_toSignalingGame [Fintype T] (μ : T → ℝ) (m : M) (a : T) :
    G.toSignalingGame.receiverEU μ m a = μ a := by
  simp [SignalingGame.receiverEU, toSignalingGame, mul_ite]

/-- The receiver's best responses to a belief are its most probable types. -/
theorem bestResponseSet_toSignalingGame [Fintype T] (μ : T → ℝ) (m : M) :
    G.toSignalingGame.bestResponseSet μ m = Finset.univ.argmax μ := by
  unfold SignalingGame.bestResponseSet
  congr 1
  funext a
  exact G.receiverEU_toSignalingGame μ m a

/-- With positive priors, a profile under which the receiver recovers every type from its
message is a Nash equilibrium. -/
theorem isNashEquilibrium_of_leftInverse [Fintype T] [DecidableEq M]
    (hprior : ∀ t, 0 < G.prior t) {σ : T → M} {ρ : M → T} (h : Function.LeftInverse ρ σ) :
    G.toSignalingGame.isNashEquilibrium σ ρ := by
  refine ⟨fun t m' ↦ ?_, fun m ↦ ?_⟩
  · simp only [toSignalingGame, h t, ite_true]
    split_ifs <;> norm_num
  · rw [bestResponseSet_toSignalingGame]
    by_cases hm : ∃ t, σ t = m
    · obtain ⟨t, rfl⟩ := hm
      rw [SignalingGame.posterior_of_injective _ σ h.injective hprior, h t]
      refine Finset.mem_argmax.mpr ⟨Finset.mem_univ _, fun b _ ↦ ?_⟩
      rcases eq_or_ne b t with rfl | hb <;> simp [*]
    · rw [SignalingGame.posterior_eq_zero_of_forall_ne _ (not_exists.mp hm)]
      exact Finset.mem_argmax.mpr ⟨Finset.mem_univ _, fun _ _ ↦ le_rfl⟩

end InterpGame
