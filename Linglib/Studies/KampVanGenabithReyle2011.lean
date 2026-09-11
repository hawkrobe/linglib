import Linglib.Semantics.Dynamic.DRS.Indexed
import Mathlib.Data.Fin.VecNotation

/-!
# Kamp, van Genabith and Reyle (2011): Discourse Representation Theory

This file formalizes the information-state architecture of the Handbook of Philosophical Logic
chapter [kamp-vangenabith-reyle-2011] on the indexed DRS substrate. Partee's marbles (42), the
argument for Definition 22, are rendered minimally: two information states that determine the
same proposition (Definition 23(v)) but record different witnesses for their referent, so that
anaphoric potential lives strictly below truth conditions and propositions cannot be the objects
of context change (`marble_worlds_eq_coin`, `marble_ne_coin`). The worked discourse (43), "John
owns a donkey. It loves him.", instantiates the chapter's remark after Definition 24: applying
the context change potential of the second sentence to the state the first expresses is the
state of their merge (`ccp_action`), the second sentence being improper on its own, with its free
referents supplied by the context.

## References

* [kamp-vangenabith-reyle-2011]
-/

open FirstOrder FirstOrder.Language DRT
open DynamicSemantics (Possibility State)

namespace KampVanGenabithReyle2011

/-! ### Partee's marbles: propositions are too coarse ((42), Definition 22)

The first sentences of (42)(i) and (ii), nine of the ten coins in the bag and one marble out
against nine of the ten marbles in the bag and one coin out, are truth-conditionally
equivalent but make different antecedents available for the following *it*. Two worlds
(`Bool`), one live referent (`Unit`), two entities (`Fin 2`): in world `true` a marble (`0`)
and a coin (`1`) are each missing, and the two states differ only in which one the referent
carries. -/

/-- (42)(i): the referent carries the missing marble `0`, in world `true`. -/
def marbleState : State Bool Unit (Fin 2) :=
  {p | p.world = true ∧ p.assignment () = Part.some 0}

/-- (42)(ii): the referent carries the missing coin `1`, in world `true`. -/
def coinState : State Bool Unit (Fin 2) :=
  {p | p.world = true ∧ p.assignment () = Part.some 1}

/-- The two states determine the same proposition, Definition 23(v). -/
theorem marble_worlds_eq_coin :
    Possibility.world '' marbleState = Possibility.world '' coinState := by
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨p, ⟨hw, -⟩, rfl⟩
    exact ⟨⟨p.world, λ _ => Part.some 1⟩, ⟨hw, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨hw, -⟩, rfl⟩
    exact ⟨⟨p.world, λ _ => Part.some 0⟩, ⟨hw, rfl⟩, rfl⟩

/-- But the states differ: the marble witness is not a coin witness. With
`marble_worlds_eq_coin`, this is Partee's argument that context change operates on information
states, not on propositions. -/
theorem marble_ne_coin : marbleState ≠ coinState := by
  intro h
  have hmem : (⟨true, λ _ => Part.some 0⟩ : Possibility Bool Unit (Part (Fin 2))) ∈
      coinState := by
    rw [← h]
    exact ⟨rfl, rfl⟩
  exact absurd (Part.some_inj.mp hmem.2) (by simp)

/-! ### The action of a context change potential ((43), Definition 24) -/

/-- The relation symbols of the worked discourse (43). -/
inductive DRel : ℕ → Type
  | john : DRel 1
  | donkey : DRel 1
  | own : DRel 2
  | love : DRel 2

/-- The first-order language of the discourse (no function symbols). -/
def dLang : Language := ⟨λ _ => Empty, DRel⟩

/-- The context DRS of (43), "John owns a donkey.": `[x y | John x, donkey y, x owns y]`. -/
def context : DRS dLang ℕ :=
  .mk {0, 1} [.rel .john (![0]), .rel .donkey (![1]), .rel .own (![0, 1])]

/-- The update DRS of (43), "It loves him.": `[z u | u loves z, z = x, u = y]`, the pronouns
resolved by equations to the context's referents. -/
def update : DRS dLang ℕ := .mk {2, 3} [.rel .love (![3, 2]), .eq 2 0, .eq 3 1]

/-- The context DRS is proper. -/
theorem context_proper : context.IsProper := by simp [DRS.IsProper, context]; decide

/-- The update DRS is not: `x` and `y` occur free in it. -/
theorem update_improper : ¬ update.IsProper := by simp [DRS.IsProper, update]; decide

/-- Its free referents are supplied by the context's universe, the condition under which the
context change potential of Definition 24 is defined on the context's state. -/
theorem update_bound : update.freeVarFinset ⊆ context.referents := by
  simp [update, context]; decide

/-- No capture: the update introduces no referent occurring in the context. -/
theorem update_fresh : Disjoint update.referents (Condition.varFinsetL context.conditions) := by
  simp [update, context]

/-- The chapter's remark after Definition 24: applying the context change potential of the
second sentence to the information state expressed by the first yields the information state
expressed by their merge, the DRS of the whole discourse (43). -/
theorem ccp_action {W M : Type*} [dLang.Structure M] :
    (update.transition (M := M) W context.referents update_bound).applyState
        (context.state W context_proper) =
      (context.merge update).state W (DRS.isProper_merge context_proper update_bound) :=
  DRS.state_merge W context update context_proper update_bound update_fresh

end KampVanGenabithReyle2011
