module

public import Linglib.Core.ModelTheory.EhrenfeuchtFraisse
public import Mathlib.Data.Set.Card

/-!
# The Ehrenfeucht–Fraïssé game on monadic structures

`[UPSTREAM]` candidate. A language is monadic when its only symbols are unary relation symbols, so
each element of a structure has a unary type, the set of symbols holding of it. On monadic
structures the Ehrenfeucht–Fraïssé game is decided by counting: duplicator answers a played
element by its partner and a fresh element by a fresh element of the same type, which is possible
while, for each type, the unplayed elements on the two sides are equinumerous or both at least the
number of rounds left. Hence two monadic structures are `t`-equivalent when, for each unary type,
their elements of that type are equinumerous or both at least `t`, the first-order case of Peters
and Westerståhl's Theorem 13.

## Main definitions

* `FirstOrder.Language.IsMonadic`: the language has only unary relation symbols.
* `FirstOrder.Language.unaryType`: the unary relation symbols holding of an element.
* `FirstOrder.Language.MonadicMatch`: tuples with the same equality pattern and unary types.

## Main results

* `FirstOrder.Language.MonadicMatch.backForth`: the counting strategy wins the game.
* `FirstOrder.Language.nEquiv_of_min_encard_eq`: the `t`-equivalence criterion.

## References

* [peters-westerstahl-2006]
-/

@[expose] public section

universe u v w w'

namespace FirstOrder.Language

open BoundedFormula

variable (L : Language.{u, v}) {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- A language is monadic when its only symbols are unary relation symbols. -/
class IsMonadic : Prop where
  isEmpty_functions : ∀ n, IsEmpty (L.Functions n)
  isEmpty_relations : ∀ n, n ≠ 1 → IsEmpty (L.Relations n)

instance (priority := 100) IsMonadic.isRelational [L.IsMonadic] : L.IsRelational :=
  IsMonadic.isEmpty_functions

/-- The unary type of `a` is the set of unary relation symbols that hold of it. -/
def unaryType (a : M) : L.Relations 1 → Prop := fun R => Structure.RelMap R ![a]

/-- Two tuples match when they have the same equality pattern and corresponding entries have the
same unary type, so that they form a partial isomorphism between monadic structures. -/
structure MonadicMatch {n : ℕ} (v : Fin n → M) (w : Fin n → N) : Prop where
  eq_iff : ∀ i j, v i = v j ↔ w i = w j
  unaryType_eq : ∀ i, L.unaryType (v i) = L.unaryType (w i)

variable {L} {n : ℕ} {v : Fin n → M} {w : Fin n → N}

private theorem sdiff_range_snoc (s : Set M) (v : Fin n → M) (a : M) :
    s \ Set.range (Fin.snoc v a) = (s \ Set.range v) \ {a} := by
  rw [Fin.range_snoc, Set.insert_eq, Set.union_comm, ← Set.sdiff_sdiff]

private theorem min_eq_of_succ {j : ℕ} {x y : ℕ∞}
    (h : min ((j + 1 : ℕ) : ℕ∞) x = min ((j + 1 : ℕ) : ℕ∞) y) :
    min (j : ℕ∞) x = min (j : ℕ∞) y := by
  have hj : (j : ℕ∞) ≤ ((j + 1 : ℕ) : ℕ∞) := by exact_mod_cast j.le_succ
  rw [← min_eq_left hj, min_assoc, h, ← min_assoc, min_eq_left hj]

private theorem min_eq_of_succ_add_one {j : ℕ} {x y : ℕ∞}
    (h : min ((j + 1 : ℕ) : ℕ∞) (x + 1) = min ((j + 1 : ℕ) : ℕ∞) (y + 1)) :
    min (j : ℕ∞) x = min (j : ℕ∞) y := by
  push_cast at h
  rw [min_add_add_right, min_add_add_right] at h
  exact (WithTop.add_right_inj WithTop.one_ne_top).1 h

namespace MonadicMatch

theorem symm (h : L.MonadicMatch v w) : L.MonadicMatch w v :=
  ⟨fun i j => (h.eq_iff i j).symm, fun i => (h.unaryType_eq i).symm⟩

theorem snoc (h : L.MonadicMatch v w) {a : M} {b : N} (heq : ∀ i, v i = a ↔ w i = b)
    (hab : L.unaryType a = L.unaryType b) : L.MonadicMatch (Fin.snoc v a) (Fin.snoc w b) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, h.eq_iff, heq, iff_self]
    exact eq_comm.trans ((heq _).trans eq_comm)
  · induction i using Fin.lastCases <;> simp [hab, h.unaryType_eq]

/-- In the *forth* move of the counting strategy, a played element is answered by its partner
and a fresh element of type `S` by a fresh element of type `S`, which exists because the fresh
elements of type `S` are equinumerous on the two sides or both at least `j + 1`. -/
theorem exists_snoc {j : ℕ} (h : L.MonadicMatch v w)
    (hc : ∀ S, min ((j + 1 : ℕ) : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range v).encard =
      min ((j + 1 : ℕ) : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range w).encard) (a : M) :
    ∃ b, L.MonadicMatch (Fin.snoc v a) (Fin.snoc w b) ∧
      ∀ S, min (j : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range (Fin.snoc v a)).encard =
        min (j : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range (Fin.snoc w b)).encard := by
  by_cases ha : a ∈ Set.range v
  · obtain ⟨i, rfl⟩ := ha
    refine ⟨w i, h.snoc (fun _ => h.eq_iff _ _) (h.unaryType_eq i), fun S => ?_⟩
    rw [sdiff_range_snoc, sdiff_range_snoc, Set.sdiff_singleton_eq_self fun hx => hx.2 ⟨i, rfl⟩,
      Set.sdiff_singleton_eq_self fun hx => hx.2 ⟨i, rfl⟩]
    exact min_eq_of_succ (hc S)
  · have haf : a ∈ L.unaryType ⁻¹' {L.unaryType a} \ Set.range v := ⟨rfl, ha⟩
    obtain ⟨b, hbf⟩ : (L.unaryType ⁻¹' {L.unaryType a} \ Set.range w).Nonempty := by
      rw [← Set.one_le_encard_iff_nonempty]
      have h1 : (1 : ℕ∞) ≤
          min ((j + 1 : ℕ) : ℕ∞) (L.unaryType ⁻¹' {L.unaryType a} \ Set.range v).encard :=
        le_min (by exact_mod_cast Nat.le_add_left 1 j) (Set.one_le_encard_iff_nonempty.2 ⟨a, haf⟩)
      exact (hc _ ▸ h1).trans (min_le_right _ _)
    have hb : L.unaryType b = L.unaryType a := hbf.1
    refine ⟨b, h.snoc (fun i => iff_of_false (fun e => ha ⟨i, e⟩) fun e => hbf.2 ⟨i, e⟩) hb.symm,
      fun S => ?_⟩
    rw [sdiff_range_snoc, sdiff_range_snoc]
    by_cases hS : S = L.unaryType a
    · subst hS
      have := hc (L.unaryType a)
      rw [← Set.encard_sdiff_singleton_add_one haf,
        ← Set.encard_sdiff_singleton_add_one hbf] at this
      exact min_eq_of_succ_add_one this
    · rw [Set.sdiff_singleton_eq_self fun hx => hS (hx.1 : _ = S).symm,
        Set.sdiff_singleton_eq_self fun hx => hS ((hx.1 : _ = S).symm.trans hb)]
      exact min_eq_of_succ (hc S)

variable [L.IsMonadic]

/-- Matched tuples in a monadic language satisfy the same atomic formulas, which are equalities
and unary predications of variables. -/
theorem realize_iff_of_isAtomic (h : L.MonadicMatch v w) {φ : L.BoundedFormula Empty n}
    (hφ : φ.IsAtomic) : φ.Realize default v ↔ φ.Realize default w := by
  have hvar : ∀ t : L.Term (Empty ⊕ Fin n), ∃ i, t = &i := by
    rintro (⟨x | i⟩ | ⟨f, _⟩)
    exacts [x.elim, ⟨i, rfl⟩, isEmptyElim f]
  cases hφ with
  | equal t₁ t₂ =>
    obtain ⟨i, rfl⟩ := hvar t₁
    obtain ⟨j, rfl⟩ := hvar t₂
    exact h.eq_iff i j
  | @rel l R ts =>
    obtain rfl : l = 1 := by_contra fun hl => (IsMonadic.isEmpty_relations l hl).elim R
    obtain ⟨i, hi⟩ := hvar (ts 0)
    have hv : (fun k => (ts k).realize (Sum.elim default v)) = ![v i] := by
      funext k; obtain rfl := Subsingleton.elim k 0; simp [hi]
    have hw : (fun k => (ts k).realize (Sum.elim default w)) = ![w i] := by
      funext k; obtain rfl := Subsingleton.elim k 0; simp [hi]
    simp only [BoundedFormula.Realize, Relations.boundedFormula]
    rw [hv, hw]
    exact Iff.of_eq (congrFun (h.unaryType_eq i) R)

/-- In a monadic language the counting strategy wins `j` rounds from matched tuples when, for
every unary type, the unplayed elements of that type are equinumerous on the two sides or both at
least `j`. -/
theorem backForth : ∀ {j n : ℕ} {v : Fin n → M} {w : Fin n → N}, L.MonadicMatch v w →
    (∀ S, min (j : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range v).encard =
      min (j : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range w).encard) →
    L.BackForth j v w
  | 0, _, _, _, h, _ => fun _ hφ => h.realize_iff_of_isAtomic hφ
  | _ + 1, _, _, _, h, hc =>
    ⟨fun _ hφ => h.realize_iff_of_isAtomic hφ,
      fun a => let ⟨b, hb, hbc⟩ := h.exists_snoc hc a; ⟨b, backForth hb hbc⟩,
      fun b => let ⟨a, ha, hac⟩ := h.symm.exists_snoc (fun S => (hc S).symm) b
        ⟨a, backForth ha.symm fun S => (hac S).symm⟩⟩

end MonadicMatch

/-- Two structures for a monadic language are `t`-equivalent when, for every unary type, their
elements of that type are equinumerous or both at least `t` ([peters-westerstahl-2006]
Theorem 13 with condition (13.7), first-order case). -/
theorem nEquiv_of_min_encard_eq [L.IsMonadic] {t : ℕ}
    (h : ∀ S, min (t : ℕ∞) (L.unaryType ⁻¹' {S} : Set M).encard =
      min (t : ℕ∞) (L.unaryType ⁻¹' {S} : Set N).encard) :
    L.NEquiv t M N :=
  BackForth.nEquiv <| MonadicMatch.backForth ⟨fun i => i.elim0, fun i => i.elim0⟩ fun S => by
    simpa [Set.range_eq_empty] using h S

end FirstOrder.Language
