import Linglib.Semantics.Causation.SEM.Deterministic

/-!
# Forced development

Developing a partial valuation in Kleene's three-valued way. A vertex the valuation leaves
undetermined is forced to `x` when every completion of its parents' forced values yields `x`
under its mechanism, so a turned handle on an unlocked door forces the door open while the
circuit is still undetermined. `ForcedFuel M s n v x` is the `n`-step approximation and
`Forced M s v x` its limit, which is reached at any fuel above a ranking of the graph. The
strict development `developDetVtxFuel` settles a vertex only once all its parents are
settled, so whatever it settles is forced.

## References

* [bar-asher-siegal-2026]
* [baglini-bar-asher-siegal-2025]
-/

namespace Causation.SEM

variable {V : Type*} {α : V → Type*} (M : SEM V α) [IsDeterministic M] (s : Valuation α)

/-- `v` is forced to `x` within `n` steps: settled by `s`, or, for an inner vertex, every
completion of its parents' values forced within `n - 1` steps yields `x`. -/
def ForcedFuel : ℕ → (v : V) → α v → Prop
  | 0, v, x => s.get v = some x
  | n + 1, v, x => s.get v = some x ∨ s.get v = none ∧ M.graph.parents v ≠ ∅ ∧
      ∀ σ : ∀ u : M.graph.parents v, α u.val,
        (∀ u y, ForcedFuel n u.val y → σ u = y) →
          Mechanism.IsDeterministic.toFun (M.mech v) σ = x

/-- `v` is forced to `x`: within some number of steps. -/
def Forced (v : V) (x : α v) : Prop := ∃ n, ForcedFuel M s n v x

section Decidable

variable [DecidableEq V] [Fintype V] [DecidableValuation α] [∀ v, Fintype (α v)]

/-- Deciding `ForcedFuel` by recursion on the fuel. -/
def decidableForcedFuel : ∀ (n : ℕ) (v : V) (x : α v), Decidable (ForcedFuel M s n v x)
  | 0, v, x => inferInstanceAs (Decidable (s.get v = some x))
  | n + 1, v, x => by
      letI := decidableForcedFuel n
      unfold ForcedFuel; infer_instance

instance (n : ℕ) (v : V) (x : α v) : Decidable (ForcedFuel M s n v x) :=
  decidableForcedFuel M s n v x

end Decidable

variable {M s}

theorem ForcedFuel.succ : ∀ {n : ℕ} {v : V} {x : α v}, ForcedFuel M s n v x →
    ForcedFuel M s (n + 1) v x
  | 0, _, _, h => Or.inl h
  | _ + 1, _, _, h => h.imp_right λ ⟨hn, hp, hσ⟩ =>
      ⟨hn, hp, λ σ hσ' => hσ σ λ u y hy => hσ' u y hy.succ⟩

theorem ForcedFuel.mono {m n : ℕ} (h : m ≤ n) {v : V} {x : α v} (hf : ForcedFuel M s m v x) :
    ForcedFuel M s n v x :=
  Nat.le_induction hf (λ _ _ ih => ih.succ) n h

theorem ForcedFuel.forced {n : ℕ} {v : V} {x : α v} (h : ForcedFuel M s n v x) :
    Forced M s v x := ⟨n, h⟩

/-- Above a ranking of the graph, more fuel forces nothing new. -/
theorem forcedFuel_iff_of_lt (r : CausalGraph.Ranking M.graph) {v : V} {n : ℕ} (hn : r v < n)
    {x : α v} : ForcedFuel M s n v x ↔ ForcedFuel M s (r v + 1) v x := by
  induction n using Nat.strong_induction_on generalizing v x with
  | _ n ih =>
    rcases n with _ | n
    · omega
    rcases Nat.lt_or_ge n (r v + 1) with hlt | hge
    · obtain rfl : n = r v := by omega
      exact Iff.rfl
    simp only [ForcedFuel]
    refine or_congr_right (and_congr_right λ _ => and_congr_right λ _ =>
      forall_congr' λ σ => imp_congr_left (forall_congr' λ u => forall_congr' λ y => ?_))
    have hu : r u.val < r v := r.map_rel u.property
    rw [ih n (by omega) (by omega), ih (r v) (by omega) (by omega)]

/-- The limit is reached at any fuel above a ranking. -/
theorem forced_iff_fuel (r : CausalGraph.Ranking M.graph) {v : V} {n : ℕ} (hn : r v < n)
    {x : α v} : Forced M s v x ↔ ForcedFuel M s n v x :=
  ⟨λ ⟨m, hm⟩ => (Nat.lt_or_ge m n).elim (λ h => hm.mono h.le) λ h =>
      (forcedFuel_iff_of_lt r hn).2 ((forcedFuel_iff_of_lt r (by omega)).1 hm),
    ForcedFuel.forced⟩

/-- Whatever the strict development settles is forced. -/
theorem ForcedFuel.of_developDetVtxFuel [DecidableEq V] : ∀ {n : ℕ} {v : V} {x : α v},
    developDetVtxFuel M s n v = some x → ForcedFuel M s n v x
  | 0, _, _, h => h
  | n + 1, v, x, h => by
    simp only [developDetVtxFuel] at h
    split at h
    · rename_i x' heq
      exact Or.inl (heq.trans (by simpa using h))
    · rename_i hnone
      split at h
      · simp at h
      · split at h
        · rename_i hp hAll
          refine Or.inr ⟨hnone, hp, λ σ hσ => ?_⟩
          rw [← Option.some_inj.1 h]
          congr 1; funext u
          exact hσ u _ (ForcedFuel.of_developDetVtxFuel (Option.some_get (hAll u)).symm)
        · simp at h

end Causation.SEM
