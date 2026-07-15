import Linglib.Semantics.Dynamic.Update

/-!
# Update Semantics
[veltman-1996]

In Update Semantics:
- Information states are sets of worlds (not assignments)
- Sentences update states by eliminating incompatible worlds
- "Might φ" is a TEST: passes if some φ-worlds remain
- No discourse referents (simpler than DRT/DPL)

⟦φ⟧ : State → State where State = Set World

-/

namespace UpdateSemantics

variable {W : Type*}

/--
Update Semantics state: a set of possible worlds.

Unlike DPL/DRT, no assignment component - US focuses on propositional content.
-/
abbrev State (W : Type*) := Set W

/--
Update function: how a sentence modifies a state. This is the spine's
`CCP W` (set-transformer context change potential) under Veltman's name.
-/
abbrev Update (W : Type*) := DynamicSemantics.CCP W

/--
Propositional update: eliminate worlds where φ fails.

⟦φ⟧(s) = { w ∈ s | φ(w) }
-/
def Update.prop (φ : W → Prop) : Update W :=
  λ s => { w ∈ s | φ w }

/--
Conjunction: sequential update.

⟦φ ∧ ψ⟧ = ⟦ψ⟧ ∘ ⟦φ⟧

Delegates to `DynamicSemantics.CCP.seq`.
-/
abbrev Update.conj (φ ψ : Update W) : Update W :=
  DynamicSemantics.CCP.seq φ ψ

/--
Negation: complement within the input state.

⟦¬φ⟧(s) = s \ ⟦φ⟧(s)   ([veltman-1996])

Delegates to `DynamicSemantics.CCP.neg`. The whole-state consistency test is
`DynamicSemantics.CCP.negTest`.
-/
abbrev Update.neg (φ : Update W) : Update W :=
  DynamicSemantics.CCP.neg φ

/--
Epistemic "might": compatibility test.

⟦might φ⟧(s) = s if ⟦φ⟧(s) ≠ ∅, else ∅

Delegates to `DynamicSemantics.CCP.might`.
-/
noncomputable abbrev Update.might (φ : Update W) : Update W :=
  DynamicSemantics.CCP.might φ

/--
Epistemic "must": universal test.

⟦must φ⟧(s) = s if ⟦φ⟧(s) = s, else ∅

Delegates to `DynamicSemantics.CCP.must`.
-/
noncomputable abbrev Update.must (φ : Update W) : Update W :=
  DynamicSemantics.CCP.must φ

/--
Might is a TEST: it doesn't change the state (if it passes).
-/
theorem Update.might_eq_self_of_nonempty (φ : Update W) (s : State W)
    (h : (φ s).Nonempty) : Update.might φ s = s :=
  DynamicSemantics.CCP.guard_pos h

/--
Order matters for epistemic might.

"It's raining and it might not be raining" is contradictory:
after learning rain, the might-not-rain test fails (no ¬rain worlds remain).
But "it might not be raining and it's raining" can succeed:
the might test passes on the initial state, then learning eliminates ¬rain worlds.

Requires `Nontrivial W`: for empty or singleton W, no state has both
p-worlds and ¬p-worlds, making the second conjunct unsatisfiable. -/
theorem might_order_matters [Nontrivial W] :
    ∃ (p : W → Prop) (_ : DecidablePred p) (s : State W),
      Update.conj (Update.prop p) (Update.might (Update.prop fun w => ¬p w)) s = ∅ ∧
      (Update.conj (Update.might (Update.prop fun w => ¬p w)) (Update.prop p) s).Nonempty := by
  obtain ⟨w₁, w₂, hne⟩ := exists_pair_ne W
  refine ⟨fun w => w = w₁, Classical.decPred _, {w₁, w₂}, ?_, ?_⟩
  · -- "p and might(not p)" fails: after learning p, only w₁ remains, and ¬p w₁ is false
    simp only [Update.conj, DynamicSemantics.CCP.seq, DynamicSemantics.CCP.might]
    refine DynamicSemantics.CCP.guard_neg ?_
    rintro ⟨w, ⟨_, hw_p⟩, hw_np⟩; exact hw_np hw_p
  · -- "might(not p) and p" succeeds: might test passes on {w₁, w₂}, then p keeps w₁
    have h : Update.might (Update.prop fun w => ¬w = w₁) ({w₁, w₂} : State W) = {w₁, w₂} :=
      DynamicSemantics.CCP.guard_pos ⟨w₂, Or.inr rfl, hne.symm⟩
    simp only [Update.conj, DynamicSemantics.CCP.seq, h]
    exact ⟨w₁, Or.inl rfl, rfl⟩

/--
State s supports φ iff updating with φ doesn't change s.

s ⊨ φ iff ⟦φ⟧(s) = s
-/
def supports (s : State W) (φ : Update W) : Prop :=
  φ s = s

/--
State s accepts φ iff updating with φ yields a non-empty state.

s accepts φ iff ⟦φ⟧(s) ≠ ∅
-/
def accepts (s : State W) (φ : Update W) : Prop :=
  (φ s).Nonempty

/-! ### Three notions of validity -/

/-- **Validity₁**: updating the minimal state **0** with the premises
    in order yields a state that supports the conclusion.

    ψ₁,...,ψₙ ⊩₁ φ  iff  **0**[ψ₁]⋯[ψₙ] ⊨ φ

    [veltman-1996], §1.2. This is the notion Veltman concentrates on:
    it captures the fact that default conclusions depend on exactly what
    information is available. -/
def valid₁ (premises : List (Update W)) (conclusion : Update W) : Prop :=
  supports (premises.foldl (fun s u => u s) Set.univ) conclusion

/-- **Validity₂**: for *every* state σ, updating with the premises
    in order yields a state that supports the conclusion.

    ψ₁,...,ψₙ ⊩₂ φ  iff  ∀σ, σ[ψ₁]⋯[ψₙ] ⊨ φ -/
def valid₂ (premises : List (Update W)) (conclusion : Update W) : Prop :=
  ∀ σ : State W, supports (premises.foldl (fun s u => u s) σ) conclusion

/-- **Validity₃**: one cannot accept all premises without accepting
    the conclusion. Closest to the classical notion.

    ψ₁,...,ψₙ ⊩₃ φ  iff  ∀σ, (σ ⊨ ψ₁ ∧ ... ∧ σ ⊨ ψₙ) → σ ⊨ φ -/
def valid₃ (premises : List (Update W)) (conclusion : Update W) : Prop :=
  ∀ σ : State W, (∀ p ∈ premises, supports σ p) → supports σ conclusion

/-- Validity₂ implies validity₁: specializing σ = **0**.

    [veltman-1996], Proposition 1.3 (one direction, unconditional). -/
theorem valid₂_imp_valid₁ (premises : List (Update W)) (conclusion : Update W) :
    valid₂ premises conclusion → valid₁ premises conclusion :=
  fun h => h Set.univ

/-- Validity₃ is monotonic: adding premises preserves validity.

    [veltman-1996], §1.2: validity₃ is the only notion that is
    both left and right monotonic. -/
theorem valid₃_monotone (premises extra : List (Update W)) (conclusion : Update W) :
    valid₃ premises conclusion → valid₃ (premises ++ extra) conclusion :=
  fun h σ hsup => h σ (fun p hp => hsup p (List.mem_append_left extra hp))

end UpdateSemantics
