import Mathlib.Data.Fintype.Order
import Mathlib.Order.GaloisConnection.Basic

/-!
# The poset adjoint functor theorem

`[UPSTREAM]` candidate: a map between complete lattices is a left adjoint iff it preserves
arbitrary suprema (`exists_galoisConnection_iff_forall_sSup`); mathlib has
`GaloisConnection.l_sSup` but not the converse. On a finite lattice the criterion reduces to
binary sup-preservation plus `⊥`-preservation
(`exists_galoisConnection_iff_forall_sup`).
-/

section AdjointFunctorTheorem

variable {α β : Type*} [CompleteLattice α] [CompleteLattice β]

/-- Poset adjoint functor theorem, construction half: a `sSup`-preserving
map between complete lattices is a left adjoint, with right adjoint
`λ b => sSup {a | f a ≤ b}`. -/
theorem galoisConnection_of_forall_sSup {f : α → β}
    (hf : ∀ s : Set α, f (sSup s) = ⨆ a ∈ s, f a) :
    GaloisConnection f λ b => sSup {a | f a ≤ b} := by
  have hmono : Monotone f := λ a b hab => by
    have h := hf {a, b}
    rw [sSup_pair, sup_eq_right.mpr hab, iSup_pair] at h
    exact le_sup_left.trans h.ge
  intro a b
  refine ⟨λ h => le_sSup h, λ h => (hmono h).trans ?_⟩
  rw [hf]
  exact iSup₂_le λ x hx => hx

/-- Poset adjoint functor theorem: a map between complete lattices is a
left adjoint iff it preserves arbitrary suprema. -/
theorem exists_galoisConnection_iff_forall_sSup (f : α → β) :
    (∃ u, GaloisConnection f u) ↔ ∀ s : Set α, f (sSup s) = ⨆ a ∈ s, f a :=
  ⟨λ ⟨_, gc⟩ _ => gc.l_sSup, λ hf => ⟨_, galoisConnection_of_forall_sSup hf⟩⟩

end AdjointFunctorTheorem

/-- On a finite lattice, left-adjointness is exactly binary sup-preservation
plus `⊥`-preservation. -/
theorem exists_galoisConnection_iff_forall_sup
    {α β : Type*} [Lattice α] [BoundedOrder α] [Finite α]
    [SemilatticeSup β] [OrderBot β] (f : α → β) :
    (∃ u, GaloisConnection f u) ↔ (∀ p q, f (p ⊔ q) = f p ⊔ f q) ∧ f ⊥ = ⊥ := by
  constructor
  · rintro ⟨u, gc⟩
    exact ⟨λ _ _ => gc.l_sup, gc.l_bot⟩
  · rintro ⟨hadd, hbot⟩
    cases nonempty_fintype α
    let _ : CompleteLattice α := Fintype.toCompleteLattice α
    have hmono : Monotone f := λ a b hab => by
      have h := hadd a b
      rw [sup_eq_right.mpr hab] at h
      exact le_sup_left.trans h.ge
    have key : ∀ s : Set α, ∀ b, (∀ x ∈ s, f x ≤ b) → f (sSup s) ≤ b := by
      intro s
      induction s, (Set.toFinite s) using Set.Finite.induction_on with
      | empty => intro b _; rw [sSup_empty, hbot]; exact bot_le
      | insert _ _ ih =>
          intro b hb
          rw [sSup_insert, hadd]
          exact sup_le (hb _ (Set.mem_insert ..))
            (ih b λ x hx => hb x (Set.mem_insert_of_mem _ hx))
    refine ⟨λ b => sSup {a | f a ≤ b}, λ a b => ⟨λ h => le_sSup h, λ h => ?_⟩⟩
    exact (hmono h).trans (key _ b λ x hx => hx)
