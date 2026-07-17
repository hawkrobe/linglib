import Linglib.Semantics.Dynamic.DRS.Indexed
import Mathlib.Data.Fin.VecNotation

/-!
# Kamp, van Genabith & Reyle (2011): Discourse Representation Theory
[kamp-vangenabith-reyle-2011]

The Handbook of Philosophical Logic chapter's information-state architecture,
run against the indexed substrate (`Semantics/Dynamic/State.lean`,
`DRS/Indexed.lean`).

* **Partee's marbles** ((42), the argument for Def. 22): two information
  states that determine the *same proposition* but differ — anaphoric
  potential lives strictly below truth conditions, so propositions cannot be
  the objects of context change (`marble_worlds_eq_coin`, `marble_ne_coin`).
* **The action equation on a discourse** (p. 159): "A¹ man walked in. He₁
  sat down." — applying the second sentence's transition to the state the
  first expresses is the state of the merge (`persistence_action`).
-/

open FirstOrder FirstOrder.Language DRT
open DynamicSemantics (Possibility State)

namespace KampVanGenabithReyle2011

/-! ### Partee's marbles: propositions are too coarse (Def. 22)

Two worlds (`Bool`), one live referent (`Unit`), two entities (`Fin 2`): in
world `true` a marble (`0`) and a coin (`1`) are each missing. "A marble is
missing" and "a coin is missing" express the same proposition — true in
exactly world `true` — but the states record different witnesses for the
referent, so anaphora can distinguish them. -/

/-- "A marble is missing": the referent carries the marble `0`, in world
`true`. -/
def marbleState : State Bool Unit (Fin 2) :=
  {p | p.world = true ∧ p.assignment () = Part.some 0}

/-- "A coin is missing": the referent carries the coin `1`, in world
`true`. -/
def coinState : State Bool Unit (Fin 2) :=
  {p | p.world = true ∧ p.assignment () = Part.some 1}

/-- The two states determine the same worldly content (Def. 23(v)'s
proposition). -/
theorem marble_worlds_eq_coin :
    Possibility.world '' marbleState = Possibility.world '' coinState := by
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨p, ⟨hw, -⟩, rfl⟩
    exact ⟨⟨p.world, fun _ => Part.some 1⟩, ⟨hw, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨hw, -⟩, rfl⟩
    exact ⟨⟨p.world, fun _ => Part.some 0⟩, ⟨hw, rfl⟩, rfl⟩

/-- But the states differ: the marble witness is not a coin witness. The
worldly collapse (`marble_worlds_eq_coin`) plus this separation is Partee's
argument that context change operates on information states, not
propositions. -/
theorem marble_ne_coin : marbleState ≠ coinState := by
  intro h
  have hmem : (⟨true, fun _ => Part.some 0⟩ : Possibility Bool Unit (Part (Fin 2))) ∈
      coinState := by
    rw [← h]
    exact ⟨rfl, rfl⟩
  exact absurd (Part.some_inj.mp hmem.2) (by simp)

/-! ### The action equation on a two-sentence discourse (p. 159) -/

/-- The relation symbols of the worked discourse. -/
inductive DRel : ℕ → Type
  | man : DRel 1
  | walkedIn : DRel 1
  | satDown : DRel 1

/-- The first-order language of the example (no function symbols). -/
def dLang : Language := ⟨fun _ => Empty, DRel⟩

/-- "A¹ man walked in." — `[u₁ | man u₁, walked-in u₁]`. -/
def sentence₁ : DRS dLang ℕ := .mk {0} [.rel .man (![0]), .rel .walkedIn (![0])]

/-- "He₁ sat down." — `[ | sat-down u₁]`: improper, its free referent is the
first sentence's — the referential presupposition in action. -/
def sentence₂ : DRS dLang ℕ := .mk ∅ [.rel .satDown (![0])]

/-- `sentence₁` is proper: it introduces its own referent `u₁`. -/
theorem sentence₁_proper : sentence₁.IsProper := by simp [DRS.IsProper, sentence₁]

/-- The referential presupposition: `sentence₂`'s free referent is supplied by
`sentence₁`'s universe. -/
theorem sentence₂_bound : sentence₂.fv ⊆ sentence₁.referents := by simp [sentence₂, sentence₁]

/-- No capture: `sentence₂` introduces no referent occurring in `sentence₁`. -/
theorem sentence₂_fresh :
    Disjoint sentence₂.referents (Condition.occL sentence₁.conditions) := by simp [sentence₂]

/-- The action equation for the discourse: interpreting sentence two against
the context sentence one expresses is interpreting their merge from scratch. -/
theorem persistence_action {M : Type} [dLang.Structure M] :
    (sentence₂.transition (M := M) Bool sentence₁.referents sentence₂_bound).applyState
        (sentence₁.state Bool sentence₁_proper) =
      (sentence₁.merge sentence₂).state Bool
        (DRS.isProper_merge sentence₁_proper sentence₂_bound) :=
  DRS.state_merge Bool sentence₁ sentence₂ sentence₁_proper sentence₂_bound sentence₂_fresh

end KampVanGenabithReyle2011
