/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.FixedPoints
import Mathlib.Data.Fintype.Card

/-!
# Least fixed points by bottom-up iteration

`[UPSTREAM]` Kleene-style certificates for `OrderHom.lfp` without continuity
hypotheses: the iterates `f^[k] ⊥` of a monotone map sit below every prefixed point,
so as soon as one is a fixed point it *is* the least fixed point
(`OrderHom.lfp_eq_iterate_bot`). In a finite lattice some iterate is always fixed —
a monotone chain can rise at most `Fintype.card` times (`OrderHom.iterate_bot_fixed`).

Together these give the computable face of Knaster–Tarski used by the recursive-scheme
and modal-μ semantics (`Core/Computability/Subregular/Logic/`): compute `f^[k] ⊥`,
check one more application, conclude `lfp`.
-/

/-- **A well-founded descent has eventually-constant iterates**: if `f` moves every
non-fixed point strictly down a well-founded relation, then from any start the orbit
reaches a fixed point — there is an `N` past which further iteration does nothing.

Absent from mathlib: the nearest neighbor is the chain condition
(`wellFoundedGT_iff_monotone_chain_condition`), which is keyed to preorders and
`ℕ →o α` sequences rather than a bare relation and a self-map; the lemma is also the
deterministic case of strong normalization, a rewriting theory mathlib lacks. -/
theorem WellFounded.iterate_eventually_constant {α : Type*} {lt : α → α → Prop}
    (wf : WellFounded lt) {f : α → α} (hmove : ∀ x, f x ≠ x → lt (f x) x) (x : α) :
    ∃ N, ∀ m, N ≤ m → f^[m] x = f^[N] x := by
  induction x using wf.induction with
  | _ x IH =>
    by_cases hfix : f x = x
    · exact ⟨0, fun m _ =>
        Eq.trans (Function.IsFixedPt.iterate hfix m) (Function.iterate_zero_apply f x).symm⟩
    · obtain ⟨N, hN⟩ := IH (f x) (hmove x hfix)
      refine ⟨N + 1, fun m hm => ?_⟩
      match m, hm with
      | m + 1, hm =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
          hN m (Nat.le_of_succ_le_succ hm)]

namespace OrderHom

variable {L : Type*}

section CompleteLattice
variable [CompleteLattice L] (f : L →o L)

/-- Bottom-up iterates never overtake the least fixed point. -/
theorem iterate_bot_le_lfp (k : ℕ) : f^[k] ⊥ ≤ lfp f := by
  induction k with
  | zero => exact bot_le
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc f (f^[k] ⊥) ≤ f (lfp f) := f.monotone ih
      _ = lfp f := f.map_lfp

/-- **Iteration certificate for `lfp`**: an iterate of `⊥` that `f` fixes is the least
fixed point. The computable face of Knaster–Tarski: no continuity needed. -/
theorem lfp_eq_iterate_bot {k : ℕ} (h : f (f^[k] ⊥) = f^[k] ⊥) : lfp f = f^[k] ⊥ :=
  le_antisymm (f.lfp_le h.le) (iterate_bot_le_lfp f k)

/-- The bottom-up chain is monotone in the iteration count. -/
theorem iterate_bot_mono : Monotone fun k => f^[k] ⊥ := by
  have hstep : ∀ k, f^[k] ⊥ ≤ f^[k + 1] ⊥ := by
    intro k
    induction k with
    | zero => exact bot_le
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact f.monotone ih
    -- (each step applies `f` to the previous inequality)
  exact monotone_nat_of_le_succ hstep

end CompleteLattice

section Fintype
variable [CompleteLattice L] [Fintype L] (f : L →o L)

/-- In a finite lattice the bottom-up chain reaches a fixed point within
`Fintype.card L` steps: a monotone chain can rise at most `card` times. -/
theorem iterate_bot_fixed : f (f^[Fintype.card L] ⊥) = f^[Fintype.card L] ⊥ := by
  by_contra hne
  -- if no iterate up to `card` were fixed, the chain would be strictly increasing,
  -- giving an injection `Fin (card + 1) ↪ L`
  have hstrict : ∀ k ≤ Fintype.card L, f^[k] ⊥ ≠ f^[k + 1] ⊥ := by
    intro k hk hfix
    -- once fixed, the chain is constant from `k` on, so `card` would be fixed too
    have hconst : ∀ m, k ≤ m → f^[m] ⊥ = f^[k] ⊥ := by
      intro m hm
      induction m with
      | zero =>
        obtain rfl : k = 0 := by omega
        rfl
      | succ m ih =>
        rcases Nat.lt_or_ge k (m + 1) with hlt | hge
        · rw [Function.iterate_succ_apply', ih (by omega),
            ← Function.iterate_succ_apply' (⇑f) k ⊥]
          exact hfix.symm
        · obtain rfl : k = m + 1 := by omega
          rfl
    exact hne (by
      rw [← Function.iterate_succ_apply' (⇑f) (Fintype.card L) ⊥,
        hconst (Fintype.card L + 1) (by omega), hconst (Fintype.card L) hk])
  have hinj : Function.Injective fun k : Fin (Fintype.card L + 1) => f^[(k : ℕ)] ⊥ := by
    intro a b hab
    simp only at hab
    by_contra hne'
    wlog hlt : (a : ℕ) < (b : ℕ) generalizing a b
    · exact this hab.symm (Ne.symm hne') (by omega)
    have hle : f^[(a : ℕ) + 1] ⊥ ≤ f^[(b : ℕ)] ⊥ := iterate_bot_mono f (by omega)
    have hge : f^[(a : ℕ)] ⊥ ≤ f^[(a : ℕ) + 1] ⊥ := iterate_bot_mono f (by omega)
    exact hstrict a (by omega) (le_antisymm hge (by rw [← hab] at hle; exact hle))
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- In a finite lattice, `lfp` is computed by `Fintype.card`-fold iteration from `⊥`. -/
theorem lfp_eq_iterate_bot_card : lfp f = f^[Fintype.card L] ⊥ :=
  lfp_eq_iterate_bot f (iterate_bot_fixed f)

end Fintype

end OrderHom
