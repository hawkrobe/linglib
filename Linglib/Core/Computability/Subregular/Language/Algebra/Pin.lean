/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.IdempotentPower
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.Computability.Subregular.Language.Algebra.Equations
import Linglib.Core.Computability.Subregular.Language.Definite
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Pin's algebraic characterization of subregular language classes

The classical algebraic-automata-theory characterization of four
basic subregular varieties via **omega-power equations** on the
syntactic monoid:

| Variety | Equation | Meaning |
|---|---|---|
| `𝒟` (definite) | `s · [w]^ω = [w]^ω` | left-absorbing |
| `𝒦` (reverse-definite) | `[w]^ω · s = [w]^ω` | right-absorbing |
| `𝒩` (co/finite) | both `𝒟`'s and `𝒦`'s | both-sided absorbing |
| `ℒℐ` (generalized definite) | `[w]^ω · s · [w]^ω = [w]^ω` | sandwich-absorbing |

Where `[w]^ω = Monoid.omegaPow (L.syntacticClass w)`
is the unique idempotent in the cyclic submonoid of `[w]` (see
`Linglib/Core/Algebra/IdempotentPower.lean`). The variables `s` range
over `L.syntacticMonoid` and `w` over non-empty `List α`
(alphabet-relativized form — see `Equations.lean` for the trivial-letter
counterexample motivating the non-empty-`w` restriction).

## Why omega-power and not finite-`k`?

[lambert-2026] Props 53/57 (in `Equations.lean`) give **finite-`k`**
characterizations parameterized by the suffix/prefix length `k`. Pin's
forms are the **unbounded** versions: a single `k`-free equation in
the syntactic monoid characterizes membership in the variety. The
`omegaPow` substrate is what eliminates the `k` parameter.

The two characterizations cohere: `L.IsDefinite k → kDefiniteEquation L k`
is the finite-`k` half; `(∃ k, L.IsDefinite k) ↔ pinDefiniteEquation L`
is the unbounded half. The unbounded form is the natural Pin/Eilenberg
form used throughout algebraic automata theory.

## Main definitions

* `Language.pinDefiniteEquation L` — `s · [w]^ω = [w]^ω`.
* `Language.pinReverseDefiniteEquation L` — `[w]^ω · s = [w]^ω`.
* `Language.pinCofiniteEquation L` — conjunction of the above two.
* `Language.pinGeneralizedDefiniteEquation L` — `[w]^ω · s · [w]^ω = [w]^ω`.

All four require `[Finite L.syntacticMonoid]` (equivalent to `L` being
regular, by `IsRegular.finite_syntacticMonoid`).

## Main results

* `Language.exists_isDefinite_iff_satisfies_pinDefiniteEquation` —
  Pin's `𝒟`-iff.
* `Language.exists_isReverseDefinite_iff_satisfies_pinReverseDefiniteEquation` —
  Pin's `𝒦`-iff.
* `Language.isFiniteOrCofinite_iff_satisfies_pinCofiniteEquation` —
  Pin's `𝒩`-iff (additionally requires `[Finite α]`; the
  language-level reverse direction in `Subregular/Language/Definite.lean` does
  not hold for infinite alphabets).
* `Language.exists_isGeneralizedDefinite_iff_satisfies_pinGeneralizedDefiniteEquation` —
  Pin's `ℒℐ`-iff. The reverse direction uses the same prefix-pigeonhole
  template as `𝒟`/`𝒦`, replacing one-sided absorption with the LI
  sandwich identity (`sandwich_absorbing_of_pin_pigeonhole`).

## References

* [pin-mfa].
* [eilenberg-1976].
* [almeida-1995].
* [perles-rabin-shamir-1963] (the original definite/reverse-definite/
  generalized-definite hierarchy).
* [mcnaughton-papert-1971] (variety theory of finite monoids).
* [lambert-2026] §6.2 (finite-`k` companion in `Equations.lean`).
-/

open Subregular

namespace Language

variable {α : Type*}

/-- **Pin's algebraic equation for definite languages**:
`∀ s : L.syntacticMonoid, ∀ w : List α, w ≠ [] → s · [w]^ω = [w]^ω`.

The non-empty `w` quantifier (alphabet-relativized form) handles the
trivial-letter case the same way `kDefiniteEquation` does — see the
counterexample in `Equations.lean`. Despite living in a sibling file
to Lambert's `kDefiniteEquation`, this is a *classical* Pin/Eilenberg
omega-power equation, not Lambert-specific — hence the namespace is
`Language` (no author-named namespace). -/
def pinDefiniteEquation (L : Language α) [Finite L.syntacticMonoid] : Prop :=
  ∀ (s : L.syntacticMonoid) (w : List α), w ≠ [] →
    s * Monoid.omegaPow (L.syntacticClass w) =
    Monoid.omegaPow (L.syntacticClass w)

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
    (hkEq : Language.kDefiniteEquation L k)
    {v : List α} (hv : k ≤ v.length) (s : L.syntacticMonoid) :
    s * L.syntacticClass v =
    L.syntacticClass v := by
  set vM := L.syntacticClass v with hvM_def
  set suf := Edge.right.takeAt k v with hsuf_def
  set sufM := L.syntacticClass suf with hsufM_def
  have hsuf_len : suf.length = k := by
    show (v.drop (v.length - k)).length = k
    rw [List.length_drop]; omega
  have hv_decomp : v = v.take (v.length - k) ++ suf := by
    show v = v.take (v.length - k) ++ v.drop (v.length - k)
    exact (List.take_append_drop _ _).symm
  have hvM_eq_sufM : vM = sufM := by
    rw [hvM_def, hv_decomp, syntacticClass_append]
    exact hkEq suf hsuf_len (L.syntacticClass (v.take (v.length - k)))
  rw [hvM_eq_sufM]
  exact hkEq suf hsuf_len s

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
    (hk : L.IsDefinite k) : pinDefiniteEquation L := by
  intro s w hw
  set wM := L.syntacticClass w with hwM_def
  have hkEq := IsDefinite.satisfies_kDefiniteEquation hk
  by_cases hk0 : k = 0
  · subst hk0
    have hM_triv : ∀ x : L.syntacticMonoid, x = 1 := fun x => by
      have := hkEq [] rfl x
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
    have hv_eq : L.syntacticClass v = wM ^ (N * k) := by
      rw [hwM_def]
      simp only [syntacticClass]
      rw [show FreeMonoid.ofList v = (FreeMonoid.ofList w) ^ (N * k) from rfl, map_pow]
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
    (h_eq : L.syntacticClass (v.take i_lo) =
            L.syntacticClass (v.take i_hi))
    (s : L.syntacticMonoid) :
    s * L.syntacticClass v =
    L.syntacticClass v := by
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
  set preM := L.syntacticClass pre with hpreM_def
  set middleM := L.syntacticClass middle with hmiddleM_def
  set sufM := L.syntacticClass suf with hsufM_def
  -- [v.take i_hi] = preM * middleM
  have h_take_j_M : L.syntacticClass (v.take i_hi) =
                    preM * middleM := by
    rw [h_take_j_decomp, syntacticClass_append]
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
  have h_v_M : L.syntacticClass v = preM * middleM * sufM := by
    rw [h_v_decomp, syntacticClass_append,
        syntacticClass_append]
  -- preM * middleM = preM (h_pre_idemp reversed)
  -- So [v] = preM * sufM = omegaPow middleM * sufM
  have h_v_omega : L.syntacticClass v =
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
    s * L.syntacticClass v =
    L.syntacticClass v := by
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
        L.syntacticClass (v.take n.val))
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
    ∃ k, L.IsDefinite k := by
  refine ⟨Nat.card L.syntacticMonoid, ?_⟩
  apply isDefinite_of_satisfies_kDefiniteEquation
  intro αs hαs_len s
  exact left_absorbing_of_pinDefiniteEquation h (by rw [hαs_len]) s

/-- **Pin's theorem**: a language is `k`-definite for some `k` iff its
(necessarily finite) syntactic monoid satisfies Pin's omega-power
equation. -/
theorem exists_isDefinite_iff_satisfies_pinDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid] :
    (∃ k, L.IsDefinite k) ↔ pinDefiniteEquation L := by
  refine ⟨fun ⟨_, hk⟩ => IsDefinite.satisfies_pinDefiniteEquation hk, ?_⟩
  exact exists_isDefinite_of_satisfies_pinDefiniteEquation

-- ============================================================================
-- §5. Pin's K-variety (reverse-definite languages)
-- ============================================================================

/-- **Pin's algebraic equation for reverse-definite languages**
([lambert-2026] Prop 57 limit; [almeida-1995]):
`∀ s : L.syntacticMonoid, ∀ w : List α, w ≠ [] → [w]^ω · s = [w]^ω`.

Mirror of `pinDefiniteEquation` with right-multiplication instead of
left. Same alphabet-relativized non-empty `w` quantifier. -/
def pinReverseDefiniteEquation (L : Language α) [Finite L.syntacticMonoid] : Prop :=
  ∀ (s : L.syntacticMonoid) (w : List α), w ≠ [] →
    Monoid.omegaPow (L.syntacticClass w) * s =
    Monoid.omegaPow (L.syntacticClass w)

/-- **Right-absorbing from `kReverseDefiniteEquation`**: mirror of
`left_absorbing_of_kDefiniteEquation`. The syntactic class of any word
of length `≥ k` is right-absorbing, decomposing `v = pre ++ suf` with
`pre` of length `k`. -/
private lemma right_absorbing_of_kReverseDefiniteEquation {L : Language α} {k : ℕ}
    (hkEq : Language.kReverseDefiniteEquation L k)
    {v : List α} (hv : k ≤ v.length) (s : L.syntacticMonoid) :
    L.syntacticClass v * s =
    L.syntacticClass v := by
  set vM := L.syntacticClass v with hvM_def
  set pre := Edge.left.takeAt k v with hpre_def
  set preM := L.syntacticClass pre with hpreM_def
  have hpre_len : pre.length = k := by
    show (v.take k).length = k
    rw [List.length_take]; omega
  have hv_decomp : v = pre ++ v.drop k := by
    show v = v.take k ++ v.drop k
    exact (List.take_append_drop _ _).symm
  have hvM_eq_preM : vM = preM := by
    rw [hvM_def, hv_decomp, syntacticClass_append]
    exact hkEq pre hpre_len (L.syntacticClass (v.drop k))
  rw [hvM_eq_preM]
  exact hkEq pre hpre_len s

/-- **Pin's K-theorem (forward direction)**: a reverse-`k`-definite
language's syntactic monoid satisfies Pin's right-absorbing
omega-power equation. Mirror of `IsDefinite.satisfies_pinDefiniteEquation`. -/
theorem IsReverseDefinite.satisfies_pinReverseDefiniteEquation
    {L : Language α} {k : ℕ} [Finite L.syntacticMonoid]
    (hk : L.IsReverseDefinite k) : pinReverseDefiniteEquation L := by
  intro s w hw
  set wM := L.syntacticClass w with hwM_def
  have hkEq := IsReverseDefinite.satisfies_kReverseDefiniteEquation hk
  by_cases hk0 : k = 0
  · subst hk0
    have hM_triv : ∀ x : L.syntacticMonoid, x = 1 := fun x => by
      have := hkEq [] rfl x
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
    have hv_eq : L.syntacticClass v = wM ^ (N * k) := by
      rw [hwM_def]
      simp only [syntacticClass]
      rw [show FreeMonoid.ofList v = (FreeMonoid.ofList w) ^ (N * k) from rfl, map_pow]
    rw [← hv_eq]
    exact right_absorbing_of_kReverseDefiniteEquation hkEq hv_len s

/-- Helper for K's reverse direction: given a pigeonhole pair of
**suffixes** `i_lo < i_hi` of `v` with the same syntactic class,
conclude that `[v]` is right-absorbing.

Mirror of `left_absorbing_of_pin_pigeonhole` but using suffix pigeonhole.
For suffixes, smaller index ⇒ longer suffix, so `[v.drop i_lo]` is the
longer one. The decomposition is
`v.drop i_lo = middle ++ v.drop i_hi` where `middle = (v.drop i_lo).take (i_hi - i_lo)`. -/
private lemma right_absorbing_of_pin_pigeonhole
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinReverseDefiniteEquation L)
    {v : List α}
    {i_lo i_hi : ℕ} (hij : i_lo < i_hi) (hi_hi_le : i_hi ≤ v.length)
    (h_eq : L.syntacticClass (v.drop i_lo) =
            L.syntacticClass (v.drop i_hi))
    (s : L.syntacticMonoid) :
    L.syntacticClass v * s =
    L.syntacticClass v := by
  -- v = pre ++ middle ++ suf, where pre = v.take i_lo,
  -- middle = (v.drop i_lo).take (i_hi - i_lo), suf = v.drop i_hi.
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
  set preM := L.syntacticClass pre with hpreM_def
  set middleM := L.syntacticClass middle with hmiddleM_def
  set sufM := L.syntacticClass suf with hsufM_def
  -- [v.drop i_lo] = middleM * sufM
  have h_drop_lo_M : L.syntacticClass (v.drop i_lo) =
                     middleM * sufM := by
    rw [h_drop_lo_decomp, syntacticClass_append]
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
  have h_v_M : L.syntacticClass v = preM * middleM * sufM := by
    rw [h_v_decomp, syntacticClass_append,
        syntacticClass_append]
  -- Substitute h_suf_eq → preM * middleM * omegaPow middleM
  -- Simplify middleM * omegaPow middleM = ? Hmm.
  -- Actually: [v] = preM * (middleM * sufM) = preM * sufM (by h_mid_idemp).
  -- And sufM = omegaPow middleM, so [v] = preM * omegaPow middleM.
  have h_v_omega : L.syntacticClass v =
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
    L.syntacticClass v * s =
    L.syntacticClass v := by
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
        L.syntacticClass (v.drop n.val))
      hcard
  have h_val_ne : i.val ≠ j.val := fun h => h_ne (Fin.ext h)
  have hi_le : i.val ≤ v.length := le_trans (Nat.lt_succ_iff.mp i.isLt) hv
  have hj_le : j.val ≤ v.length := le_trans (Nat.lt_succ_iff.mp j.isLt) hv
  rcases lt_or_gt_of_ne h_val_ne with hij | hij
  · exact right_absorbing_of_pin_pigeonhole h hij hj_le h_eq s
  · exact right_absorbing_of_pin_pigeonhole h hij hi_le h_eq.symm s

/-- **Pin's K-theorem (reverse direction)**: if a regular language's
syntactic monoid satisfies Pin's reverse-definite omega-power equation,
then `L` is reverse-`k`-definite for some `k`. -/
theorem exists_isReverseDefinite_of_satisfies_pinReverseDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinReverseDefiniteEquation L) :
    ∃ k, L.IsReverseDefinite k := by
  refine ⟨Nat.card L.syntacticMonoid, ?_⟩
  apply isReverseDefinite_of_satisfies_kReverseDefiniteEquation
  intro αs hαs_len s
  exact right_absorbing_of_pinReverseDefiniteEquation h (by rw [hαs_len]) s

/-- **Pin's K-theorem**: a language is reverse-`k`-definite for some
`k` iff its (necessarily finite) syntactic monoid satisfies Pin's
reverse-definite omega-power equation. -/
theorem exists_isReverseDefinite_iff_satisfies_pinReverseDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid] :
    (∃ k, L.IsReverseDefinite k) ↔ pinReverseDefiniteEquation L := by
  refine ⟨fun ⟨_, hk⟩ => IsReverseDefinite.satisfies_pinReverseDefiniteEquation hk, ?_⟩
  exact exists_isReverseDefinite_of_satisfies_pinReverseDefiniteEquation

-- ============================================================================
-- §6. Pin's N-variety (co/finite languages)
-- ============================================================================

/-- **Pin's algebraic equation for co/finite languages**
([lambert-2026] Prop 59; [almeida-1995]): `𝒩 = ⟦sx^ω = x^ω = x^ω s⟧`.
The conjunction of D's left-absorbing equation and K's right-absorbing
equation. -/
def pinCofiniteEquation (L : Language α) [Finite L.syntacticMonoid] : Prop :=
  pinDefiniteEquation L ∧ pinReverseDefiniteEquation L

/-- **Pin's N-theorem (forward direction)**: a finite-or-cofinite
language's syntactic monoid satisfies the conjunction of Pin's D and K
omega-power equations. Composes the substrate lemma
`IsFiniteOrCofinite.exists_isDefinite_and_isReverseDefinite` (in
`Subregular/Language/Definite.lean`) with the Pin D and Pin K iff theorems. -/
theorem IsFiniteOrCofinite.satisfies_pinCofiniteEquation
    {L : Language α} [Finite L.syntacticMonoid]
    (h : IsFiniteOrCofinite L) : pinCofiniteEquation L := by
  obtain ⟨⟨k, hD⟩, ⟨k', hRD⟩⟩ := h.exists_isDefinite_and_isReverseDefinite
  exact ⟨IsDefinite.satisfies_pinDefiniteEquation hD,
         IsReverseDefinite.satisfies_pinReverseDefiniteEquation hRD⟩

/-- **Pin's N-theorem (reverse direction, α-finite case)**: if a
language over a finite alphabet has a syntactic monoid satisfying both
Pin's D and K equations, then it is finite-or-cofinite.

Requires `[Finite α]` because the language-level reverse direction
(`isFiniteOrCofinite_of_isDefinite_and_isReverseDefinite` in
`Subregular/Language/Definite.lean`) needs it: with infinite α, words of
bounded length need not form a finite set. -/
theorem isFiniteOrCofinite_of_satisfies_pinCofiniteEquation [Finite α]
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinCofiniteEquation L) : IsFiniteOrCofinite L := by
  obtain ⟨hD, hRD⟩ := h
  exact isFiniteOrCofinite_of_isDefinite_and_isReverseDefinite
    ⟨exists_isDefinite_of_satisfies_pinDefiniteEquation hD,
     exists_isReverseDefinite_of_satisfies_pinReverseDefiniteEquation hRD⟩

/-- **Pin's N-theorem**: over a finite alphabet, a language is
finite-or-cofinite iff its syntactic monoid satisfies the conjunction
of Pin's D and K omega-power equations. -/
theorem isFiniteOrCofinite_iff_satisfies_pinCofiniteEquation [Finite α]
    {L : Language α} [Finite L.syntacticMonoid] :
    IsFiniteOrCofinite L ↔ pinCofiniteEquation L :=
  ⟨IsFiniteOrCofinite.satisfies_pinCofiniteEquation,
   isFiniteOrCofinite_of_satisfies_pinCofiniteEquation⟩

-- ============================================================================
-- §7. Pin's ℒℐ-variety (generalized definite, sandwich form)
-- ============================================================================

/-- **Pin's algebraic equation for generalized-definite languages**
([lambert-2026] Prop 58 limit, simplified form; [straubing-1985]):
`ℒℐ = ⟦x^ω · s · x^ω = x^ω⟧`. Sandwiching `s` between two copies of
the same omega-power absorbs `s`.

Lambert (paper p. 25) notes this simplified one-variable form is
equivalent to the more general two-variable form
`x^ω · s · z^ω = x^ω · z^ω`; the equivalence proof itself uses
omega-power idempotence. -/
def pinGeneralizedDefiniteEquation (L : Language α) [Finite L.syntacticMonoid] : Prop :=
  ∀ (s : L.syntacticMonoid) (w : List α), w ≠ [] →
    Monoid.omegaPow (L.syntacticClass w) * s *
    Monoid.omegaPow (L.syntacticClass w) =
    Monoid.omegaPow (L.syntacticClass w)

/-- **Pin's ℒℐ-theorem (forward direction)**: a generalized-`k`-definite
language's syntactic monoid satisfies the LI omega-power equation.

Strategy: pick `v = w^(N·k)` long enough (length `≥ k`); apply
`L.IsGeneralizedDefinite k` directly to the pair
`(v ++ s' ++ v, v)` — both have the same length-`k` left-prefix (the
first `k` chars of `v`) and same length-`k` right-suffix (the last
`k` chars of `v`). The omega-power identity `[w]^N · s · [w]^N = [w]^N`
follows by lifting through `[w]^(N·k) = omegaPow [w]`. -/
theorem IsGeneralizedDefinite.satisfies_pinGeneralizedDefiniteEquation
    {L : Language α} {k : ℕ} [Finite L.syntacticMonoid]
    (hk : L.IsGeneralizedDefinite k) :
    pinGeneralizedDefiniteEquation L := by
  intro s w hw
  set wM := L.syntacticClass w with hwM_def
  by_cases hk0 : k = 0
  · -- k = 0: IsGenDef 0 L means ∀ w₁ w₂, w₁ ∈ L ↔ w₂ ∈ L (vacuous prefix/suffix).
    -- So L is constant: L = ∅ or L = univ. Either way M is trivial.
    subst hk0
    have h_takeAt_right_zero : ∀ v : List α, Edge.right.takeAt 0 v = [] := by
      intro v; show v.drop (v.length - 0) = []; simp
    have hM_triv : ∀ x : L.syntacticMonoid, x = 1 := by
      intro x
      obtain ⟨u, hu⟩ := Quotient.exists_rep x
      rw [show x = L.toSyntacticMonoid u from hu.symm,
          show (1 : L.syntacticMonoid) = L.toSyntacticMonoid 1 from
            (L.toSyntacticMonoid.map_one).symm]
      apply Quotient.sound
      refine (syntacticCon_iff L).mpr ?_
      intro p q
      show p ++ FreeMonoid.toList u ++ q ∈ L ↔ p ++ FreeMonoid.toList 1 ++ q ∈ L
      apply isGeneralizedDefinite_iff_edges.mp hk
      · -- takeAt_left 0 : both .take 0 = []
        rfl
      · -- takeAt_right 0 : both = []
        rw [h_takeAt_right_zero, h_takeAt_right_zero]
    rw [hM_triv s, hM_triv (Monoid.omegaPow wM), one_mul, mul_one]
  · -- k ≥ 1: build v = w^(N·k) with |v| ≥ k.
    set N := Monoid.omegaPowExponent wM with hN_def
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
    have hv_eq : L.syntacticClass v = wM ^ (N * k) := by
      rw [hwM_def]
      simp only [syntacticClass]
      rw [show FreeMonoid.ofList v = (FreeMonoid.ofList w) ^ (N * k) from rfl, map_pow]
    rw [← hv_eq]
    -- Goal: [v] · s · [v] = [v]. Apply IsGenDef k L directly via context-extension.
    obtain ⟨s', rfl⟩ := L.syntacticClass_surjective s
    rw [← syntacticClass_append, ← syntacticClass_append, syntacticClass_eq_iff]
    intro x y
    -- Apply IsGenDef k L to (x ++ v ++ s' ++ v ++ y, x ++ v ++ y).
    apply isGeneralizedDefinite_iff_edges.mp hk
    · -- takeAt_left k matches: both have x ++ v as prefix; |x ++ v| ≥ k.
      show (x ++ (v ++ s' ++ v) ++ y).take k = (x ++ v ++ y).take k
      rw [show x ++ (v ++ s' ++ v) ++ y = (x ++ v) ++ (s' ++ v ++ y) by simp [List.append_assoc],
          show x ++ v ++ y = (x ++ v) ++ y by simp [List.append_assoc]]
      have h_xv_len : k ≤ (x ++ v).length := by rw [List.length_append]; omega
      rw [List.take_append_of_le_length h_xv_len, List.take_append_of_le_length h_xv_len]
    · -- takeAt_right k matches: both end with v ++ y; |v ++ y| ≥ k.
      show Edge.right.takeAt k (x ++ (v ++ s' ++ v) ++ y) = Edge.right.takeAt k (x ++ v ++ y)
      rw [show x ++ (v ++ s' ++ v) ++ y = (x ++ v ++ s') ++ (v ++ y) by simp [List.append_assoc],
          show x ++ v ++ y = x ++ (v ++ y) by simp [List.append_assoc]]
      have h_vy_len : k ≤ (v ++ y).length := by rw [List.length_append]; omega
      rw [takeAt_right_append_left_absorb (x ++ v ++ s') (v ++ y) h_vy_len,
          takeAt_right_append_left_absorb x (v ++ y) h_vy_len]

/-- Helper for the LI reverse direction: given a pigeonhole pair
`i_lo < i_hi` of indices into `v` whose prefixes have the same
syntactic class, conclude that `[v]` is **sandwich-absorbing**:
`[v] · s · [v] = [v]` for any `s ∈ M_L`.

Proof: pigeonhole gives `preM = preM * middleM` for `preM = [v.take i_lo]`,
`middleM = [v[i_lo..i_hi]]`. Iterating: `preM = preM * middleM^n`, hence
`preM = preM * ω(middleM)`. So `[v] = preM * sufM = preM * ω(middleM) * sufM`
(with `sufM = [v.drop i_hi]`). Then by Pin LI's omega equation
`ω · t · ω = ω`, sandwiching `s` between two copies of `[v]` yields
`preM * (ω * (sufM * s * preM) * ω) * sufM = preM * ω * sufM = [v]`.

Mirror of `left_absorbing_of_pin_pigeonhole` for the LI sandwich
form, sharing all of the prefix-pigeonhole substrate (h_pre_idemp,
h_iter, h_pre_omega) but using Pin LI's two-sided absorption instead
of D's one-sided absorption to close. -/
private lemma sandwich_absorbing_of_pin_pigeonhole
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinGeneralizedDefiniteEquation L)
    {v : List α}
    {i_lo i_hi : ℕ} (hij : i_lo < i_hi) (hi_hi_le : i_hi ≤ v.length)
    (h_eq : L.syntacticClass (v.take i_lo) =
            L.syntacticClass (v.take i_hi))
    (s : L.syntacticMonoid) :
    L.syntacticClass v * s *
    L.syntacticClass v =
    L.syntacticClass v := by
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
  set preM := L.syntacticClass pre with hpreM_def
  set middleM := L.syntacticClass middle with hmiddleM_def
  set sufM := L.syntacticClass suf with hsufM_def
  have h_take_j_M : L.syntacticClass (v.take i_hi) =
                    preM * middleM := by
    rw [h_take_j_decomp, syntacticClass_append]
  have h_pre_idemp : preM = preM * middleM := h_eq.trans h_take_j_M
  have h_iter : ∀ n : ℕ, preM = preM * middleM ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ← ih]; exact h_pre_idemp
  have h_pre_omega : preM = preM * Monoid.omegaPow middleM := by
    rw [Monoid.omegaPow_eq_pow]; exact h_iter _
  -- [v] = preM * middleM * sufM = preM * sufM = preM * ω(middleM) * sufM.
  have h_v_omega : L.syntacticClass v =
                   preM * Monoid.omegaPow middleM * sufM := by
    rw [h_v_decomp, syntacticClass_append,
        syntacticClass_append,
        ← h_pre_idemp, ← h_pre_omega]
  -- Apply Pin LI: ω · (sufM * s * preM) · ω = ω.
  have h_pin := h (sufM * s * preM) middle h_middle_ne
  rw [h_v_omega]
  -- Reshape preM * ω * sufM * s * (preM * ω * sufM) into
  -- preM * (ω * (sufM * s * preM) * ω) * sufM, apply h_pin.
  rw [show preM * Monoid.omegaPow middleM * sufM * s *
        (preM * Monoid.omegaPow middleM * sufM) =
      preM *
        (Monoid.omegaPow middleM * (sufM * s * preM) * Monoid.omegaPow middleM) *
        sufM by simp only [mul_assoc]]
  rw [h_pin]

/-- Under Pin's LI omega-power equation, the syntactic class of any
word of length `≥ Nat.card L.syntacticMonoid` is **sandwich-absorbing**:
`[v] · s · [v] = [v]` for any `s`. Mirror of
`left_absorbing_of_pinDefiniteEquation` for the LI sandwich form. -/
private lemma sandwich_absorbing_of_pinGeneralizedDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinGeneralizedDefiniteEquation L)
    {v : List α} (hv : Nat.card L.syntacticMonoid ≤ v.length)
    (s : L.syntacticMonoid) :
    L.syntacticClass v * s *
    L.syntacticClass v =
    L.syntacticClass v := by
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
        L.syntacticClass (v.take n.val))
      hcard
  have h_val_ne : i.val ≠ j.val := fun h => h_ne (Fin.ext h)
  have hi_le : i.val ≤ v.length := le_trans (Nat.lt_succ_iff.mp i.isLt) hv
  have hj_le : j.val ≤ v.length := le_trans (Nat.lt_succ_iff.mp j.isLt) hv
  rcases lt_or_gt_of_ne h_val_ne with hij | hij
  · exact sandwich_absorbing_of_pin_pigeonhole h hij hj_le h_eq s
  · exact sandwich_absorbing_of_pin_pigeonhole h hij hi_le h_eq.symm s

/-- **Pin's ℒℐ-theorem (reverse direction)**: if a regular language's
syntactic monoid satisfies Pin's LI omega-power equation, then `L` is
generalized-`k`-definite for some `k` (specifically,
`k = Nat.card L.syntacticMonoid`).

Proof: `sandwich_absorbing_of_pinGeneralizedDefiniteEquation` lifts the
omega-power equation to a finite-`k` sandwich on length-`k` words; this
is exactly `kGeneralizedDefiniteEquation L k`, which by Lambert Prop 58
(reverse direction in `Equations.lean`) gives `L.IsGeneralizedDefinite k`. -/
theorem exists_isGeneralizedDefinite_of_satisfies_pinGeneralizedDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid]
    (h : pinGeneralizedDefiniteEquation L) :
    ∃ k, L.IsGeneralizedDefinite k := by
  refine ⟨Nat.card L.syntacticMonoid, ?_⟩
  apply isGeneralizedDefinite_of_satisfies_kGeneralizedDefiniteEquation
  intro s αs hαs_len
  exact sandwich_absorbing_of_pinGeneralizedDefiniteEquation h (by rw [hαs_len]) s

/-- **Pin's ℒℐ-theorem**: a language is generalized-`k`-definite for
some `k` iff its syntactic monoid satisfies Pin's LI omega-power
equation. -/
theorem exists_isGeneralizedDefinite_iff_satisfies_pinGeneralizedDefiniteEquation
    {L : Language α} [Finite L.syntacticMonoid] :
    (∃ k, L.IsGeneralizedDefinite k) ↔ pinGeneralizedDefiniteEquation L := by
  refine ⟨fun ⟨_, hk⟩ =>
    IsGeneralizedDefinite.satisfies_pinGeneralizedDefiniteEquation hk, ?_⟩
  exact exists_isGeneralizedDefinite_of_satisfies_pinGeneralizedDefiniteEquation

end Language
