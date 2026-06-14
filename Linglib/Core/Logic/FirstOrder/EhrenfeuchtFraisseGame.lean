import Linglib.Core.Logic.FirstOrder.EhrenfeuchtFraisse

/-!
# The finite-rank Ehrenfeucht–Fraïssé back-and-forth relation

`[UPSTREAM]` candidate. The rank-`k` **back-and-forth relation** `BackForth k v w`
on structures-with-tuples `(M, v)`, `(N, w)` is the syntax-free combinatorial
characterization of `k`-equivalence: `BackForth 0` is agreement on quantifier-free
formulas, and `BackForth (k+1)` is the *forth* (every `a : M` is matched by some
`b : N`) and *back* (dually) conditions, recursing at rank `k`. This is the
rank-bounded refinement of mathlib's *unbounded* `IsExtensionPair` /
`FGEquiv`-based back-and-forth.

The **soundness** direction — `BackForth k v w` implies the two tuples satisfy the
same formulas of quantifier rank `≤ k` (`BackForth.agree`), hence the structures
are `≡ₖ` (`nEquiv_of_backForth`, feeding `not_foDefinable_of_nEquiv`) — is the
tractable half and is proved here in full (under the finite-model-theory convention
that the domains are `[Nonempty]`, used to extract quantifier-free agreement of a tuple
from the higher-rank forth/back data). The converse (Libkin "1 ⟹ 3", via rank-`k`
Hintikka formulas / `k`-types) is left as future work.

Construction: Libkin, *Elements of Finite Model Theory*, Thm 3.18; Hodges,
*Model Theory*, §3.2 (general back-and-forth systems).

## Main definitions / results

* `FirstOrder.Language.BackForth` — the rank-`k` back-and-forth relation.
* `FirstOrder.Language.BackForth.agree` — soundness: back-and-forth ⟹ agreement on
  rank-`≤ k` formulas.
* `FirstOrder.Language.nEquiv_of_backForth` — back-and-forth on the empty tuples ⟹ `≡ₖ`.
-/

universe u v w

namespace FirstOrder.Language

open BoundedFormula CategoryTheory
open scoped FirstOrder

variable {L : Language.{u, v}}

section BackForth

variable (M : Type w) (N : Type w) [L.Structure M] [L.Structure N]

/-- The rank-`k` **Ehrenfeucht–Fraïssé back-and-forth relation** between a structure
`M` with an `m`-tuple `v` and a structure `N` with an `m`-tuple `w`.

* At rank `0`: `v` and `w` satisfy the same quantifier-free formulas (here phrased as
  all formulas of quantifier rank `0`).
* At rank `k + 1`: the **forth** condition (every `a : M` extends `v` to a pair still
  related at rank `k` by some `b : N`) and the dual **back** condition. -/
def BackForth : (k : ℕ) → {m : ℕ} → (Fin m → M) → (Fin m → N) → Prop
  | 0, m, v, w =>
    ∀ φ : L.BoundedFormula (Fin m) 0, φ.qr = 0 → (φ.Realize v default ↔ φ.Realize w default)
  | k + 1, _, v, w =>
    (∀ a : M, ∃ b : N, BackForth k (Fin.snoc v a) (Fin.snoc w b)) ∧
      (∀ b : N, ∃ a : M, BackForth k (Fin.snoc v a) (Fin.snoc w b))

end BackForth

namespace BackForth

variable {M : Type w} {N : Type w} [L.Structure M] [L.Structure N] {m : ℕ}

/-- Lift a free-variable formula `φ` over `Fin m` to one over `Fin (m + 1)` by
ignoring the new last variable; rank-preserving, and realizing the lift at
`Fin.snoc v a` agrees with realizing `φ` at `v`. -/
private def liftLast (φ : L.BoundedFormula (Fin m) 0) : L.BoundedFormula (Fin (m + 1)) 0 :=
  φ.relabel (fun i => Sum.inl i.castSucc)

private theorem realize_liftLast (φ : L.BoundedFormula (Fin m) 0) (v : Fin m → M) (a : M) :
    (liftLast φ).Realize (Fin.snoc v a) default ↔ φ.Realize v default := by
  rw [liftLast, realize_relabel]
  refine Iff.of_eq (congrArg₂ _ ?_ (Subsingleton.elim _ _))
  funext i
  simp [Fin.snoc_castSucc]

private theorem qr_relabel {α β : Type*} {n' : ℕ} (g : α → β ⊕ (Fin n')) :
    ∀ {k} (φ : L.BoundedFormula α k), (φ.relabel g).qr = φ.qr
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel _ _ => rfl
  | _, .imp f₁ f₂ => by
      rw [relabel_imp, qr_imp, qr_imp, qr_relabel g f₁, qr_relabel g f₂]
  | _, .all f => by
      rw [relabel_all, qr_all, qr_all, qr_relabel g f]

private theorem qr_liftLast (φ : L.BoundedFormula (Fin m) 0) : (liftLast φ).qr = φ.qr :=
  qr_relabel _ φ

/-- **Monotonicity:** a rank-`k+1` back-and-forth pair is also a rank-`k` one. The base
step (rank `1 → 0`) recovers quantifier-free agreement of the tuple `(v, w)` itself by
extending along the *forth* clause at an arbitrary element (whence `[Nonempty M]`) and
discarding the new last variable via `liftLast`. -/
theorem mono [Nonempty M] {k : ℕ} :
    ∀ {m} {v : Fin m → M} {w : Fin m → N},
      BackForth (L := L) M N (k + 1) v w → BackForth (L := L) M N k v w := by
  induction k with
  | zero =>
      intro m v w h φ hφ
      obtain ⟨b, hab⟩ := h.1 (Classical.arbitrary M)
      have := hab (liftLast φ) (by rw [qr_liftLast]; exact hφ)
      rwa [realize_liftLast, realize_liftLast] at this
  | succ k ih =>
      intro m v w h
      exact ⟨fun a => (h.1 a).imp fun _ hb => ih hb,
        fun b => (h.2 b).imp fun _ ha => ih ha⟩

/-- A rank-`k` back-and-forth pair is also a rank-`0` one (quantifier-free agreement). -/
theorem mono_zero [Nonempty M] [Nonempty N] :
    ∀ {k} {m} {v : Fin m → M} {w : Fin m → N},
      BackForth (L := L) M N k v w → BackForth (L := L) M N 0 v w
  | 0, _, _, _, h => h
  | _ + 1, _, _, _, h => mono_zero (mono h)

/-- The "combined" valuation on `Fin (m + n)` formed by appending the bound tuple to the
free tuple is the appropriate reindexing of the `Sum.elim` valuation that `Realize` uses. -/
private theorem append_eq_elim {m n : ℕ} (v : Fin m → M) (xs : Fin n → M) :
    Fin.append v xs = Sum.elim v xs ∘ finSumFinEquiv.symm := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [Fin.append_left, finSumFinEquiv_symm_apply_castAdd]
  · simp [Fin.append_right, finSumFinEquiv_symm_apply_natAdd]

/-- The variable reindexing `Fin m ⊕ Fin n → Fin (m + n) ⊕ Fin 0` that frees the bound
slots into the free index. -/
private def combineVar {m n : ℕ} : Fin m ⊕ (Fin n) → Fin (m + n) ⊕ (Fin 0) :=
  Sum.inl ∘ finSumFinEquiv

private theorem elim_comp_combineVar {m n : ℕ} (v : Fin m → M) (xs : Fin n → M) :
    Sum.elim (Fin.append v xs) (default : Fin 0 → M) ∘ combineVar = Sum.elim v xs := by
  funext x
  rcases x with i | i
  · simp [combineVar, Function.comp_apply, Fin.append_left]
  · simp [combineVar, Function.comp_apply, Fin.append_right]

/-- An atomic formula over `Fin m` with `n` bound slots, relabelled to free its bound slots,
yielding a formula over `Fin (m + n)` with none — used to feed atomic agreement of the
combined tuple into the back-and-forth base case. -/
private def combineAtomic {m n : ℕ} : (φ : L.BoundedFormula (Fin m) n) → φ.IsAtomic →
    L.BoundedFormula (Fin (m + n)) 0
  | .equal t₁ t₂, _ => .equal (t₁.relabel combineVar) (t₂.relabel combineVar)
  | .rel R ts, _ => .rel R (fun i => (ts i).relabel combineVar)

private theorem realize_combineAtomic {m n : ℕ} {v : Fin m → M} {xs : Fin n → M} :
    ∀ {φ : L.BoundedFormula (Fin m) n} (hφ : φ.IsAtomic),
      (combineAtomic φ hφ).Realize (Fin.append v xs) default ↔ φ.Realize v xs
  | .equal t₁ t₂, _ => by
      simp only [combineAtomic, Realize, Term.realize_relabel]
      rw [elim_comp_combineVar]
  | .rel R ts, _ => by
      simp only [combineAtomic, Realize]
      refine Iff.of_eq (congrArg _ (funext fun i => ?_))
      rw [Term.realize_relabel, elim_comp_combineVar]

/-- **Generalized soundness** (induction on rank, then formula). If the combined free+bound
tuples are rank-`k` back-and-forth related, then any formula of quantifier rank `≤ k` is
agreed on. The bound tuples `xs`, `ys` are absorbed into the back-and-forth via
`Fin.append`; the `all` case uses the *forth*/*back* clauses to extend them. -/
private theorem agree_aux [Nonempty M] [Nonempty N] {m : ℕ}
    {v : Fin m → M} {w : Fin m → N} :
    ∀ {n} (φ : L.BoundedFormula (Fin m) n) {k} {xs : Fin n → M} {ys : Fin n → N},
      BackForth (L := L) M N k (Fin.append v xs) (Fin.append w ys) →
      φ.qr ≤ k → (φ.Realize v xs ↔ φ.Realize w ys) := by
  intro n φ
  induction φ with
  | falsum => intro k xs ys _ _; exact Iff.rfl
  | equal t₁ t₂ =>
      intro k xs ys h _
      have := (mono_zero h) (combineAtomic _ (.equal t₁ t₂)) rfl
      rwa [realize_combineAtomic, realize_combineAtomic] at this
  | rel R ts =>
      intro k xs ys h _
      have := (mono_zero h) (combineAtomic _ (.rel R ts)) rfl
      rwa [realize_combineAtomic, realize_combineAtomic] at this
  | imp f₁ f₂ ih₁ ih₂ =>
      intro k xs ys h hφ
      simp only [realize_imp]
      rw [ih₁ h (le_trans (le_max_left _ _) hφ), ih₂ h (le_trans (le_max_right _ _) hφ)]
  | all f ih =>
      intro k xs ys h hφ
      rw [qr_all] at hφ
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hf : f.qr ≤ k := by omega
      simp only [realize_all]
      constructor
      · intro hM b
        obtain ⟨a, hab⟩ := h.2 b
        rw [← Fin.append_snoc, ← Fin.append_snoc] at hab
        exact (ih hab hf).mp (hM a)
      · intro hN a
        obtain ⟨b, hab⟩ := h.1 a
        rw [← Fin.append_snoc, ← Fin.append_snoc] at hab
        exact (ih hab hf).mpr (hN b)

/-- **Soundness of back-and-forth (Libkin Thm 3.18, "3 ⟹ 1").** If `(M, v)` and
`(N, w)` are related by the rank-`k` back-and-forth relation, then they satisfy the
same formulas of quantifier rank `≤ k`. Proof: the `all` case uses the *forth* clause and
the rank-`k` recursion, the dual `ex` case the *back* clause; atomic agreement descends to
the quantifier-free base case via `mono_zero`. -/
theorem agree [Nonempty M] [Nonempty N] {k : ℕ} {v : Fin m → M} {w : Fin m → N}
    (h : BackForth (L := L) M N k v w) :
    ∀ φ : L.BoundedFormula (Fin m) 0, φ.qr ≤ k →
      (φ.Realize v default ↔ φ.Realize w default) := by
  have hv : Fin.append v (default : Fin 0 → M) = v := by
    rw [Subsingleton.elim (default : Fin 0 → M) Fin.elim0, Fin.append_elim0]; rfl
  have hw : Fin.append w (default : Fin 0 → N) = w := by
    rw [Subsingleton.elim (default : Fin 0 → N) Fin.elim0, Fin.append_elim0]; rfl
  intro φ hφ
  exact agree_aux (v := v) (w := w) φ (xs := default) (ys := default) (by rw [hv, hw]; exact h) hφ

end BackForth

/-- A rank-`k` back-and-forth relation between the structures themselves (on the empty
tuples) witnesses `k`-equivalence — and so feeds `not_foDefinable_of_nEquiv`. -/
theorem nEquiv_of_backForth {k : ℕ} (M N : Bundled.{w} L.Structure)
    [Nonempty M] [Nonempty N]
    (h : BackForth (L := L) M N k (default : Fin 0 → M) (default : Fin 0 → N)) :
    NEquiv k M N := fun φ hφ => by
  -- relabel the sentence's free variables `Empty` to `Fin 0` to match `agree`
  let e : Empty ≃ Fin 0 := Equiv.equivOfIsEmpty Empty (Fin 0)
  have hqr : (BoundedFormula.relabelEquiv e φ).qr ≤ k := by
    rwa [BoundedFormula.qr_relabelEquiv]
  have key := BackForth.agree h (BoundedFormula.relabelEquiv e φ) hqr
  rw [BoundedFormula.realize_relabelEquiv, BoundedFormula.realize_relabelEquiv] at key
  simpa only [Sentence.Realize, Formula.Realize,
    Subsingleton.elim (default ∘ e.symm) default] using key

end FirstOrder.Language
