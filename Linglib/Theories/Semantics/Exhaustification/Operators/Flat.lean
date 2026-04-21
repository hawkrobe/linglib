import Linglib.Theories.Semantics.Exhaustification.Operators.Basic

/-!
# FLAT: Collapsing Nested Alternative Sets @cite{wang-2025} @cite{groenendijk-stokhof-1984}

@cite{wang-2025} Ch4 defines the FLAT operator for collapsing nested
alternative sets (sets of sets of propositions) into a flat set via
cross-product conjunction.

Given `S = {A₁, A₂,...}` where each `Aᵢ` is a set of propositions,
`FLAT(S) = {⋂₀ {f(Aᵢ) | i} | f is a choice function picking one from each Aᵢ}`.

Equivalent to @cite{groenendijk-stokhof-1984} pointwise answerhood (Ans_PW).
-/

namespace Exhaustification

variable {World : Type*}

/-- FLAT: Collapse a family of alternative sets into a flat set via
    cross-product conjunction. Each element of `FLAT(S)` is the conjunction
    of one choice from each alternative set in `S`.

    @cite{wang-2025} Ch4: `FLAT({A₁,...,Aₙ}) = {a₁ ∧... ∧ aₙ | aᵢ ∈ Aᵢ}`.

    Uses a total choice function restricted to `S` to avoid dependent types. -/
def flat (S : Set (Set (Set World))) : Set (Set World) :=
  {p | ∃ (f : Set (Set World) → Set World),
    (∀ A ∈ S, f A ∈ A) ∧
    p = λ u => ∀ A ∈ S, f A u}

/-- FLAT of a singleton is the set itself. -/
@[simp] theorem flat_singleton (A : Set (Set World)) :
    flat {A} = A := by
  ext p; constructor
  · rintro ⟨f, hf, heq⟩
    have key : p = f A := by
      rw [heq]; funext u; apply propext; constructor
      · intro h; exact h A rfl
      · intro h B hB; rw [Set.mem_singleton_iff.mp hB]; exact h
    rw [key]; exact hf A rfl
  · intro hp
    refine ⟨λ _ => p, λ B hB => ?_, ?_⟩
    · rw [Set.mem_singleton_iff.mp hB]; exact hp
    · funext u; apply propext; constructor
      · intro h B _; exact h
      · intro h; exact h A rfl

/-- FLAT of the empty family is the tautology set. -/
@[simp] theorem flat_empty : flat (∅ : Set (Set (Set World))) = {λ _ => True} := by
  ext p; constructor
  · rintro ⟨_, -, rfl⟩
    show _ = λ _ => True
    funext u; apply propext; constructor
    · intro _ ; trivial
    · intro _ B hB; exact absurd hB (by simp only [Set.mem_empty_iff_false, not_false_eq_true])
  · intro (hp : p = λ _ => True)
    refine ⟨λ _ _ => True, λ B hB => ?_, ?_⟩
    · simp only [Set.mem_empty_iff_false] at hB
    · rw [hp]; funext u; apply propext; constructor
      · intro _ B hB; simp only [Set.mem_empty_iff_false] at hB
      · intro _; trivial

end Exhaustification
