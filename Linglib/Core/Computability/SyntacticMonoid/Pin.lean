/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.IdempotentPower
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.Computability.SyntacticMonoid.Equations
import Linglib.Core.Computability.Subregular.Definite
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Pin's algebraic characterization of definite languages

A regular language `L` is **definite** (i.e. `k`-definite for some `k`)
iff its syntactic monoid satisfies the **omega-power equation**

> `s · [w]^ω = [w]^ω`     for every `s ∈ L.syntacticMonoid` and every
                          non-empty word `w : List α`,

where `[w]^ω = Monoid.omegaPow (L.toSyntacticMonoid (FreeMonoid.ofList w))`
is the unique idempotent in the cyclic submonoid of `[w]` (see
`Linglib/Core/Algebra/IdempotentPower.lean`). This is Pin's classical
characterization of the variety **D** of definite languages, lifted to
the monoid setting using the same alphabet-relativized quantification
as `kDefiniteEquation` (see `Equations.lean` for the trivial-letter
counterexample that motivates the relativization).

## Why omega-power and not finite-`k`?

@cite{lambert-2026} Prop 53 (in `Equations.lean`) gives a **finite-`k`**
characterization, parameterized by the suffix-length `k`. Pin's
characterization is the **unbounded** version: a language is definite
(for some `k`) iff a single `k`-free equation holds in the syntactic
monoid. The `omegaPow` substrate is what eliminates the `k` parameter.

The two characterizations cohere: `IsDefinite k L → kDefiniteEquation L k`
is the finite-`k` half; `(∃ k, IsDefinite k L) ↔ pinDefiniteEquation L`
is the unbounded half. The unbounded form is the natural Pin/Eilenberg
form used throughout algebraic automata theory.

## References

* Pin, *Mathematical Foundations of Automata Theory*, Chapter II.
* @cite{eilenberg-1976}.
* @cite{lambert-2026} §6.2 (finite-`k` companion in `Equations.lean`).
-/

open Core.Computability.Subregular

namespace Language

variable {α : Type*}

/-- **Pin's algebraic equation for definite languages**:
`∀ s : L.syntacticMonoid, ∀ w : List α, w ≠ [] → s · [w]^ω = [w]^ω`.

The non-empty `w` quantifier (alphabet-relativized form) handles the
trivial-letter case the same way `kDefiniteEquation` does — see the
counterexample in `Equations.lean`. Despite living in a sibling file
to Lambert's `kDefiniteEquation`, this is a *classical* Pin/Eilenberg
omega-power equation, not Lambert-specific — hence the namespace is
`Language` rather than `Lambert.Equations`. -/
def pinDefiniteEquation (L : Language α) [Finite L.syntacticMonoid] : Prop :=
  ∀ (s : L.syntacticMonoid) (w : List α), w ≠ [] →
    s * Monoid.omegaPow (L.toSyntacticMonoid (FreeMonoid.ofList w)) =
    Monoid.omegaPow (L.toSyntacticMonoid (FreeMonoid.ofList w))

-- ============================================================================
-- §1. FreeMonoid power length
-- ============================================================================

private lemma freeMonoid_ofList_pow_length (w : List α) (n : ℕ) :
    ((FreeMonoid.ofList w) ^ n).length = n * w.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, FreeMonoid.length_mul, ih]
    show n * w.length + (FreeMonoid.ofList w).length = (n + 1) * w.length
    have hw : (FreeMonoid.ofList w).length = w.length := rfl
    rw [hw, Nat.succ_mul]

-- ============================================================================
-- §2. Long-suffix lemma (under `kDefiniteEquation`)
-- ============================================================================

/-- Under the `k`-definite equation, the syntactic class of any word
of length `≥ k` is **left-absorbing**. -/
private lemma left_absorbing_of_kDefiniteEquation {L : Language α} {k : ℕ}
    (hkEq : Lambert.Equations.kDefiniteEquation L k)
    {v : List α} (hv : k ≤ v.length) (s : L.syntacticMonoid) :
    s * L.toSyntacticMonoid (FreeMonoid.ofList v) =
    L.toSyntacticMonoid (FreeMonoid.ofList v) := by
  set vM := L.toSyntacticMonoid (FreeMonoid.ofList v) with hvM_def
  set suf := Edge.right.takeAt k v with hsuf_def
  set sufM := L.toSyntacticMonoid (FreeMonoid.ofList suf) with hsufM_def
  have hsuf_len : suf.length = k := by
    show (v.drop (v.length - k)).length = k
    rw [List.length_drop]; omega
  have hv_decomp : v = v.take (v.length - k) ++ suf := by
    show v = v.take (v.length - k) ++ v.drop (v.length - k)
    exact (List.take_append_drop _ _).symm
  have hvM_eq_sufM : vM = sufM := by
    rw [hvM_def, hv_decomp, FreeMonoid.ofList_append, MonoidHom.map_mul]
    exact hkEq (L.toSyntacticMonoid (FreeMonoid.ofList (v.take (v.length - k))))
                suf hsuf_len
  rw [hvM_eq_sufM]
  exact hkEq s suf hsuf_len

-- ============================================================================
-- §3. Pin's theorem (forward direction)
-- ============================================================================

/-- **Pin's theorem (forward direction)**: if `L` is `k`-definite for
some `k`, then its syntactic monoid satisfies Pin's omega-power
equation.

Proof: reduce to `IsDefinite.satisfies_kDefiniteEquation` plus the
absorbing-power trick — `[w]^ω = [w]^N` for some `N`, and by
idempotence `[w]^N = [w]^(N·k)` whenever `k ≥ 1`, giving a long-enough
representative `w^(N·k)` (length `N·k·|w| ≥ k`) of `[w]^ω`. The `k = 0`
case forces the syntactic monoid to be trivial, so the equation holds
vacuously. -/
theorem IsDefinite.satisfies_pinDefiniteEquation
    {L : Language α} {k : ℕ} [Finite L.syntacticMonoid]
    (hk : IsDefinite k L) : pinDefiniteEquation L := by
  intro s w hw
  set wM := L.toSyntacticMonoid (FreeMonoid.ofList w) with hwM_def
  have hkEq := IsDefinite.satisfies_kDefiniteEquation hk
  by_cases hk0 : k = 0
  · subst hk0
    have hM_triv : ∀ x : L.syntacticMonoid, x = 1 := fun x => by
      have := hkEq x [] rfl
      simpa using this
    rw [hM_triv s, hM_triv (Monoid.omegaPow wM), one_mul]
  · set N := Monoid.omegaPowExponent wM with hN_def
    have h_omega_eq_long : wM ^ (N * k) = Monoid.omegaPow wM := by
      rw [pow_mul, ← Monoid.omegaPow_eq_pow, Monoid.omegaPow_pow wM hk0]
    rw [← h_omega_eq_long]
    set v := ((FreeMonoid.ofList w) ^ (N * k)).toList with hv_def
    have hw_len : 0 < w.length := List.length_pos_iff.mpr hw
    have hN_pos : 0 < N := Monoid.omegaPowExponent_pos wM
    have hv_len : k ≤ v.length := by
      show k ≤ ((FreeMonoid.ofList w) ^ (N * k)).length
      rw [freeMonoid_ofList_pow_length]
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have h1 : k ≤ N * k := Nat.le_mul_of_pos_left k hN_pos
      have h2 : N * k ≤ N * k * w.length := Nat.le_mul_of_pos_right (N * k) hw_len
      omega
    have hv_eq : L.toSyntacticMonoid (FreeMonoid.ofList v) = wM ^ (N * k) := by
      have h_id : (FreeMonoid.ofList v : FreeMonoid α) =
                  (FreeMonoid.ofList w) ^ (N * k) := rfl
      rw [h_id, MonoidHom.map_pow]
    rw [← hv_eq]
    exact left_absorbing_of_kDefiniteEquation hkEq hv_len s

-- ============================================================================
-- §4. Pin's theorem (reverse direction)
-- ============================================================================

/-- Helper for the reverse direction: given a pigeonhole pair
`i.val < j.val` of indices into `v` whose prefixes have the same
syntactic class, conclude that `[v]` is left-absorbing. -/
private lemma left_absorbing_of_pin_pigeonhole
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinDefiniteEquation L)
    {v : List α}
    {i_lo i_hi : ℕ} (hij : i_lo < i_hi) (hi_hi_le : i_hi ≤ v.length)
    (h_eq : L.toSyntacticMonoid (FreeMonoid.ofList (v.take i_lo)) =
            L.toSyntacticMonoid (FreeMonoid.ofList (v.take i_hi)))
    (s : L.syntacticMonoid) :
    s * L.toSyntacticMonoid (FreeMonoid.ofList v) =
    L.toSyntacticMonoid (FreeMonoid.ofList v) := by
  -- Decompose v = pre ++ middle ++ suf, where pre has length i_lo,
  -- middle has length (i_hi - i_lo), suf is the rest.
  set pre := v.take i_lo with hpre_def
  set middle := (v.drop i_lo).take (i_hi - i_lo) with hmiddle_def
  set suf := v.drop i_hi with hsuf_def
  have hmiddle_len : middle.length = i_hi - i_lo := by
    show ((v.drop i_lo).take (i_hi - i_lo)).length = i_hi - i_lo
    rw [List.length_take, List.length_drop]
    have hi_lo_le : i_lo ≤ v.length := le_trans (le_of_lt hij) hi_hi_le
    omega
  have h_middle_ne : middle ≠ [] := by
    intro hcontra
    have h_zero : middle.length = 0 := by rw [hcontra]; simp
    omega
  have h_take_j_decomp : v.take i_hi = pre ++ middle := by
    rw [hpre_def, hmiddle_def, ← List.take_append_drop i_lo (v.take i_hi),
        List.take_take, List.drop_take]
    (congr 2; omega)
  have h_v_decomp : v = pre ++ middle ++ suf := by
    rw [show pre ++ middle = v.take i_hi from h_take_j_decomp.symm, hsuf_def,
        List.take_append_drop]
  set preM := L.toSyntacticMonoid (FreeMonoid.ofList pre) with hpreM_def
  set middleM := L.toSyntacticMonoid (FreeMonoid.ofList middle) with hmiddleM_def
  set sufM := L.toSyntacticMonoid (FreeMonoid.ofList suf) with hsufM_def
  -- [v.take i_hi] = preM * middleM
  have h_take_j_M : L.toSyntacticMonoid (FreeMonoid.ofList (v.take i_hi)) =
                    preM * middleM := by
    rw [h_take_j_decomp, FreeMonoid.ofList_append, MonoidHom.map_mul]
  -- preM = preM * middleM (from pigeonhole)
  have h_pre_idemp : preM = preM * middleM := h_eq.trans h_take_j_M
  -- preM = preM * middleM^n for all n ≥ 0
  have h_iter : ∀ n : ℕ, preM = preM * middleM ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ← ih]; exact h_pre_idemp
  -- preM = preM * omegaPow middleM
  have h_pre_omega : preM = preM * Monoid.omegaPow middleM := by
    rw [Monoid.omegaPow_eq_pow]; exact h_iter _
  -- preM * omegaPow middleM = omegaPow middleM (Pin)
  have h_pin : preM * Monoid.omegaPow middleM = Monoid.omegaPow middleM :=
    h preM middle h_middle_ne
  -- preM = omegaPow middleM
  have h_pre_eq : preM = Monoid.omegaPow middleM := h_pre_omega.trans h_pin
  -- [v] = preM * middleM * sufM
  have h_v_M : L.toSyntacticMonoid (FreeMonoid.ofList v) = preM * middleM * sufM := by
    rw [h_v_decomp, FreeMonoid.ofList_append, MonoidHom.map_mul,
        FreeMonoid.ofList_append, MonoidHom.map_mul]
  -- preM * middleM = preM (h_pre_idemp reversed)
  -- So [v] = preM * sufM = omegaPow middleM * sufM
  have h_v_omega : L.toSyntacticMonoid (FreeMonoid.ofList v) =
                   Monoid.omegaPow middleM * sufM := by
    rw [h_v_M, ← h_pre_idemp, h_pre_eq]
  -- s * [v] = s * (omegaPow middleM * sufM) = (s * omegaPow middleM) * sufM
  --         = omegaPow middleM * sufM = [v]
  rw [h_v_omega, ← mul_assoc, h s middle h_middle_ne]

/-- Under Pin's omega-power equation, the syntactic class of any word
of length `≥ Nat.card L.syntacticMonoid` is left-absorbing. -/
private lemma left_absorbing_of_pinDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinDefiniteEquation L)
    {v : List α} (hv : Nat.card L.syntacticMonoid ≤ v.length)
    (s : L.syntacticMonoid) :
    s * L.toSyntacticMonoid (FreeMonoid.ofList v) =
    L.toSyntacticMonoid (FreeMonoid.ofList v) := by
  classical
  haveI : Fintype L.syntacticMonoid := Fintype.ofFinite _
  have hNat : Nat.card L.syntacticMonoid = Fintype.card L.syntacticMonoid :=
    Nat.card_eq_fintype_card
  rw [hNat] at hv
  -- Pigeonhole on the |M|+1 prefixes v.take 0, …, v.take |M|.
  have hcard : Fintype.card L.syntacticMonoid <
               Fintype.card (Fin (Fintype.card L.syntacticMonoid + 1)) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨i, j, h_ne, h_eq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card L.syntacticMonoid + 1) =>
        L.toSyntacticMonoid (FreeMonoid.ofList (v.take n.val)))
      hcard
  have h_val_ne : i.val ≠ j.val := fun h => h_ne (Fin.ext h)
  -- Bound on j.val (and i.val): ≤ |M| ≤ v.length.
  have hi_le : i.val ≤ v.length := le_trans (Nat.lt_succ_iff.mp i.isLt) hv
  have hj_le : j.val ≤ v.length := le_trans (Nat.lt_succ_iff.mp j.isLt) hv
  rcases lt_or_gt_of_ne h_val_ne with hij | hij
  · exact left_absorbing_of_pin_pigeonhole h hij hj_le h_eq s
  · exact left_absorbing_of_pin_pigeonhole h hij hi_le h_eq.symm s

/-- **Pin's theorem (reverse direction)**: if a regular language's
syntactic monoid satisfies Pin's omega-power equation, then `L` is
`k`-definite for some `k` (specifically, `k = Fintype.card L.syntacticMonoid`). -/
theorem exists_isDefinite_of_satisfies_pinDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinDefiniteEquation L) :
    ∃ k, IsDefinite k L := by
  refine ⟨Nat.card L.syntacticMonoid, ?_⟩
  apply isDefinite_of_satisfies_kDefiniteEquation
  intro s αs hαs_len
  exact left_absorbing_of_pinDefiniteEquation h (by rw [hαs_len]) s

/-- **Pin's theorem**: a language is `k`-definite for some `k` iff its
(necessarily finite) syntactic monoid satisfies Pin's omega-power
equation. -/
theorem exists_isDefinite_iff_satisfies_pinDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid] :
    (∃ k, IsDefinite k L) ↔ pinDefiniteEquation L := by
  refine ⟨fun ⟨_, hk⟩ => IsDefinite.satisfies_pinDefiniteEquation hk, ?_⟩
  exact exists_isDefinite_of_satisfies_pinDefiniteEquation

-- ============================================================================
-- §5. Pin's K-variety (reverse-definite languages)
-- ============================================================================

/-- **Pin's algebraic equation for reverse-definite languages**
(@cite{lambert-2026} Prop 57 limit; Almeida 1995:90):
`∀ s : L.syntacticMonoid, ∀ w : List α, w ≠ [] → [w]^ω · s = [w]^ω`.

Mirror of `pinDefiniteEquation` with right-multiplication instead of
left. Same alphabet-relativized non-empty `w` quantifier. -/
def pinReverseDefiniteEquation (L : Language α) [Finite L.syntacticMonoid] : Prop :=
  ∀ (s : L.syntacticMonoid) (w : List α), w ≠ [] →
    Monoid.omegaPow (L.toSyntacticMonoid (FreeMonoid.ofList w)) * s =
    Monoid.omegaPow (L.toSyntacticMonoid (FreeMonoid.ofList w))

/-- **Right-absorbing from `kReverseDefiniteEquation`**: mirror of
`left_absorbing_of_kDefiniteEquation`. The syntactic class of any word
of length `≥ k` is right-absorbing, decomposing `v = pre ++ suf` with
`pre` of length `k`. -/
private lemma right_absorbing_of_kReverseDefiniteEquation {L : Language α} {k : ℕ}
    (hkEq : Lambert.Equations.kReverseDefiniteEquation L k)
    {v : List α} (hv : k ≤ v.length) (s : L.syntacticMonoid) :
    L.toSyntacticMonoid (FreeMonoid.ofList v) * s =
    L.toSyntacticMonoid (FreeMonoid.ofList v) := by
  set vM := L.toSyntacticMonoid (FreeMonoid.ofList v) with hvM_def
  set pre := Edge.left.takeAt k v with hpre_def
  set preM := L.toSyntacticMonoid (FreeMonoid.ofList pre) with hpreM_def
  have hpre_len : pre.length = k := by
    show (v.take k).length = k
    rw [List.length_take]; omega
  have hv_decomp : v = pre ++ v.drop k := by
    show v = v.take k ++ v.drop k
    exact (List.take_append_drop _ _).symm
  have hvM_eq_preM : vM = preM := by
    rw [hvM_def, hv_decomp, FreeMonoid.ofList_append, MonoidHom.map_mul]
    exact hkEq (L.toSyntacticMonoid (FreeMonoid.ofList (v.drop k))) pre hpre_len
  rw [hvM_eq_preM]
  exact hkEq s pre hpre_len

/-- **Pin's K-theorem (forward direction)**: a reverse-`k`-definite
language's syntactic monoid satisfies Pin's right-absorbing
omega-power equation. Mirror of `IsDefinite.satisfies_pinDefiniteEquation`. -/
theorem IsReverseDefinite.satisfies_pinReverseDefiniteEquation
    {L : Language α} {k : ℕ} [Finite L.syntacticMonoid]
    (hk : IsReverseDefinite k L) : pinReverseDefiniteEquation L := by
  intro s w hw
  set wM := L.toSyntacticMonoid (FreeMonoid.ofList w) with hwM_def
  have hkEq := IsReverseDefinite.satisfies_kReverseDefiniteEquation hk
  by_cases hk0 : k = 0
  · subst hk0
    have hM_triv : ∀ x : L.syntacticMonoid, x = 1 := fun x => by
      have := hkEq x [] rfl
      simpa using this
    rw [hM_triv s, hM_triv (Monoid.omegaPow wM), mul_one]
  · set N := Monoid.omegaPowExponent wM with hN_def
    have h_omega_eq_long : wM ^ (N * k) = Monoid.omegaPow wM := by
      rw [pow_mul, ← Monoid.omegaPow_eq_pow, Monoid.omegaPow_pow wM hk0]
    rw [← h_omega_eq_long]
    set v := ((FreeMonoid.ofList w) ^ (N * k)).toList with hv_def
    have hw_len : 0 < w.length := List.length_pos_iff.mpr hw
    have hN_pos : 0 < N := Monoid.omegaPowExponent_pos wM
    have hv_len : k ≤ v.length := by
      show k ≤ ((FreeMonoid.ofList w) ^ (N * k)).length
      rw [freeMonoid_ofList_pow_length]
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have h1 : k ≤ N * k := Nat.le_mul_of_pos_left k hN_pos
      have h2 : N * k ≤ N * k * w.length := Nat.le_mul_of_pos_right (N * k) hw_len
      omega
    have hv_eq : L.toSyntacticMonoid (FreeMonoid.ofList v) = wM ^ (N * k) := by
      have h_id : (FreeMonoid.ofList v : FreeMonoid α) =
                  (FreeMonoid.ofList w) ^ (N * k) := rfl
      rw [h_id, MonoidHom.map_pow]
    rw [← hv_eq]
    exact right_absorbing_of_kReverseDefiniteEquation hkEq hv_len s

/-- Helper for K's reverse direction: given a pigeonhole pair of
**suffixes** `i_lo < i_hi` of `v` with the same syntactic class,
conclude that `[v]` is right-absorbing.

Mirror of `left_absorbing_of_pin_pigeonhole` but using suffix pigeonhole.
For suffixes, smaller index ⇒ longer suffix, so `[v.drop i_lo]` is the
longer one. The decomposition is
`v.drop i_lo = middle ++ v.drop i_hi` where `middle = (v.drop i_lo).take (i_hi - i_lo)`. -/
private lemma right_absorbing_of_pin_pigeonhole_K
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinReverseDefiniteEquation L)
    {v : List α}
    {i_lo i_hi : ℕ} (hij : i_lo < i_hi) (hi_hi_le : i_hi ≤ v.length)
    (h_eq : L.toSyntacticMonoid (FreeMonoid.ofList (v.drop i_lo)) =
            L.toSyntacticMonoid (FreeMonoid.ofList (v.drop i_hi)))
    (s : L.syntacticMonoid) :
    L.toSyntacticMonoid (FreeMonoid.ofList v) * s =
    L.toSyntacticMonoid (FreeMonoid.ofList v) := by
  -- v = pre ++ middle ++ suf, where pre = v.take i_lo, middle = v.drop i_lo .take (i_hi - i_lo), suf = v.drop i_hi.
  set pre := v.take i_lo with hpre_def
  set middle := (v.drop i_lo).take (i_hi - i_lo) with hmiddle_def
  set suf := v.drop i_hi with hsuf_def
  have hi_lo_le : i_lo ≤ v.length := le_trans (le_of_lt hij) hi_hi_le
  have hmiddle_len : middle.length = i_hi - i_lo := by
    show ((v.drop i_lo).take (i_hi - i_lo)).length = i_hi - i_lo
    rw [List.length_take, List.length_drop]
    omega
  have h_middle_ne : middle ≠ [] := by
    intro hcontra
    have h_zero : middle.length = 0 := by rw [hcontra]; simp
    omega
  -- Decompose v.drop i_lo = middle ++ v.drop i_hi.
  have h_drop_lo_decomp : v.drop i_lo = middle ++ v.drop i_hi := by
    rw [hmiddle_def]
    -- v.drop i_lo = (v.drop i_lo).take (i_hi - i_lo) ++ (v.drop i_lo).drop (i_hi - i_lo)
    -- And (v.drop i_lo).drop (i_hi - i_lo) = v.drop i_hi (by drop_drop, omega)
    rw [show v.drop i_hi = (v.drop i_lo).drop (i_hi - i_lo) by
          rw [List.drop_drop]; congr 1; omega]
    exact (List.take_append_drop _ _).symm
  -- Whole v = pre ++ (v.drop i_lo) = pre ++ middle ++ suf.
  have h_v_decomp : v = pre ++ middle ++ suf := by
    rw [show pre ++ middle ++ suf = pre ++ (middle ++ suf) by simp [List.append_assoc],
        ← h_drop_lo_decomp]
    exact (List.take_append_drop _ _).symm
  set preM := L.toSyntacticMonoid (FreeMonoid.ofList pre) with hpreM_def
  set middleM := L.toSyntacticMonoid (FreeMonoid.ofList middle) with hmiddleM_def
  set sufM := L.toSyntacticMonoid (FreeMonoid.ofList suf) with hsufM_def
  -- [v.drop i_lo] = middleM * sufM
  have h_drop_lo_M : L.toSyntacticMonoid (FreeMonoid.ofList (v.drop i_lo)) =
                     middleM * sufM := by
    rw [h_drop_lo_decomp, FreeMonoid.ofList_append, MonoidHom.map_mul]
  -- Pigeonhole gives [v.drop i_lo] = [v.drop i_hi] = sufM. With h_drop_lo_M
  -- expressing [v.drop i_lo] as middleM * sufM, transitivity closes.
  have h_mid_idemp : middleM * sufM = sufM := h_drop_lo_M.symm.trans h_eq
  -- By induction: middleM^n * sufM = sufM for all n.
  have h_iter : ∀ n : ℕ, middleM ^ n * sufM = sufM := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, h_mid_idemp]; exact ih
  -- omegaPow middleM * sufM = sufM
  have h_omega_idemp : Monoid.omegaPow middleM * sufM = sufM := by
    rw [Monoid.omegaPow_eq_pow]; exact h_iter _
  -- Pin K: omegaPow middleM * s' = omegaPow middleM for all s'.
  have h_pin : Monoid.omegaPow middleM * sufM = Monoid.omegaPow middleM :=
    h sufM middle h_middle_ne
  -- So sufM = omegaPow middleM.
  have h_suf_eq : sufM = Monoid.omegaPow middleM := h_omega_idemp.symm.trans h_pin
  -- [v] = preM * middleM * sufM
  have h_v_M : L.toSyntacticMonoid (FreeMonoid.ofList v) = preM * middleM * sufM := by
    rw [h_v_decomp, FreeMonoid.ofList_append, MonoidHom.map_mul,
        FreeMonoid.ofList_append, MonoidHom.map_mul]
  -- Substitute h_suf_eq → preM * middleM * omegaPow middleM
  -- Simplify middleM * omegaPow middleM = ? Hmm.
  -- Actually: [v] = preM * (middleM * sufM) = preM * sufM (by h_mid_idemp).
  -- And sufM = omegaPow middleM, so [v] = preM * omegaPow middleM.
  have h_v_omega : L.toSyntacticMonoid (FreeMonoid.ofList v) =
                   preM * Monoid.omegaPow middleM := by
    rw [h_v_M, mul_assoc, h_mid_idemp, h_suf_eq]
  -- For any s: [v] * s = preM * omegaPow middleM * s = preM * omegaPow middleM = [v]
  rw [h_v_omega, mul_assoc, h s middle h_middle_ne]

/-- Under Pin's reverse-definite equation, the syntactic class of any
word of length `≥ Nat.card L.syntacticMonoid` is right-absorbing. -/
private lemma right_absorbing_of_pinReverseDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinReverseDefiniteEquation L)
    {v : List α} (hv : Nat.card L.syntacticMonoid ≤ v.length)
    (s : L.syntacticMonoid) :
    L.toSyntacticMonoid (FreeMonoid.ofList v) * s =
    L.toSyntacticMonoid (FreeMonoid.ofList v) := by
  classical
  haveI : Fintype L.syntacticMonoid := Fintype.ofFinite _
  have hNat : Nat.card L.syntacticMonoid = Fintype.card L.syntacticMonoid :=
    Nat.card_eq_fintype_card
  rw [hNat] at hv
  -- Pigeonhole on |M|+1 SUFFIXES v.drop 0, …, v.drop |M|.
  have hcard : Fintype.card L.syntacticMonoid <
               Fintype.card (Fin (Fintype.card L.syntacticMonoid + 1)) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨i, j, h_ne, h_eq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card L.syntacticMonoid + 1) =>
        L.toSyntacticMonoid (FreeMonoid.ofList (v.drop n.val)))
      hcard
  have h_val_ne : i.val ≠ j.val := fun h => h_ne (Fin.ext h)
  have hi_le : i.val ≤ v.length := le_trans (Nat.lt_succ_iff.mp i.isLt) hv
  have hj_le : j.val ≤ v.length := le_trans (Nat.lt_succ_iff.mp j.isLt) hv
  rcases lt_or_gt_of_ne h_val_ne with hij | hij
  · exact right_absorbing_of_pin_pigeonhole_K h hij hj_le h_eq s
  · exact right_absorbing_of_pin_pigeonhole_K h hij hi_le h_eq.symm s

/-- **Pin's K-theorem (reverse direction)**: if a regular language's
syntactic monoid satisfies Pin's reverse-definite omega-power equation,
then `L` is reverse-`k`-definite for some `k`. -/
theorem exists_isReverseDefinite_of_satisfies_pinReverseDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinReverseDefiniteEquation L) :
    ∃ k, IsReverseDefinite k L := by
  refine ⟨Nat.card L.syntacticMonoid, ?_⟩
  apply isReverseDefinite_of_satisfies_kReverseDefiniteEquation
  intro s αs hαs_len
  exact right_absorbing_of_pinReverseDefiniteEquation h (by rw [hαs_len]) s

/-- **Pin's K-theorem**: a language is reverse-`k`-definite for some
`k` iff its (necessarily finite) syntactic monoid satisfies Pin's
reverse-definite omega-power equation. -/
theorem exists_isReverseDefinite_iff_satisfies_pinReverseDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid] :
    (∃ k, IsReverseDefinite k L) ↔ pinReverseDefiniteEquation L := by
  refine ⟨fun ⟨_, hk⟩ => IsReverseDefinite.satisfies_pinReverseDefiniteEquation hk, ?_⟩
  exact exists_isReverseDefinite_of_satisfies_pinReverseDefiniteEquation

end Language
