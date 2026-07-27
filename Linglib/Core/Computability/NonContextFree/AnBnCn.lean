import Linglib.Core.Computability.ContextFreeGrammar.Pumping
import Linglib.Core.Computability.NonContextFree.BlockWitness

/-!
# `{aⁿbⁿcⁿ}`: a three-symbol non-context-free witness

The classical three-symbol witness `anbnc = {aⁿbⁿcⁿ | n ≥ 0}`, shown non-context-free by the
CFL pumping lemma together with the adjacency lemma of `BlockWitness`: a pumped window short
enough to fit inside the witness cannot meet both the `a`-block and the `c`-block, so pumping
down leaves some symbol's count untouched while shortening the word.

Independent of `AnBnCnDn` and `AmBnCmDn`: it uses its own `ThreeSymbol` alphabet.

## Main definitions

* `makeString_anbnc n`: the witness word `aⁿbⁿcⁿ`.
* `anbnc`: the language `{aⁿbⁿcⁿ | n ≥ 0}`, as the range of `makeString_anbnc`.

## Main results

* `anbnc_not_pumpable`: `anbnc` lacks the CFL pumping property.
* `anbnc_not_contextFree`: `anbnc` is not context-free.
-/

/-- Alphabet for `{aⁿbⁿcⁿ}`. -/
inductive ThreeSymbol where
  | a | b | c
  deriving DecidableEq, Repr

/-- The witness word `aⁿbⁿcⁿ`. -/
def makeString_anbnc (n : ℕ) : List ThreeSymbol :=
  List.replicate n .a ++ List.replicate n .b ++ List.replicate n .c

/-- The language `{aⁿbⁿcⁿ | n ≥ 0}`, as the range of `makeString_anbnc`. -/
def anbnc : Language ThreeSymbol := {w | ∃ n, w = makeString_anbnc n}

/-- Membership characterization: every string in `anbnc` is `makeString_anbnc n` for some `n`.
Consumed by the homomorphic reduction `aⁿbⁿcⁿdⁿ → aⁿbⁿcⁿ` in `AnBnCnDn`. -/
theorem mem_anbnc_iff (w : List ThreeSymbol) : w ∈ anbnc ↔ ∃ n, w = makeString_anbnc n := Iff.rfl

theorem makeString_anbnc_mem (n : ℕ) : makeString_anbnc n ∈ anbnc := ⟨n, rfl⟩

/-- Each of the three symbols occurs exactly `n` times in the witness. -/
@[simp] theorem count_makeString_anbnc (n : ℕ) (s : ThreeSymbol) :
    (makeString_anbnc n).count s = n := by
  cases s <;> simp [makeString_anbnc, List.count_replicate]

@[simp] theorem length_makeString_anbnc (n : ℕ) : (makeString_anbnc n).length = 3 * n := by
  simp [makeString_anbnc]; omega

/-- The three-symbol witness is structurally `BlockWitness [a, b, c] n`. -/
private theorem makeString_anbnc_eq_blockwitness (n : ℕ) :
    makeString_anbnc n = BlockWitness ([ThreeSymbol.a, .b, .c] : List ThreeSymbol) n := by
  simp [makeString_anbnc, BlockWitness, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc]

/-- A window short enough to fit inside the witness cannot meet both the `a`- and `c`-blocks. -/
private theorem not_a_and_c_in_vxy3 (p : ℕ) (u vxy z : List ThreeSymbol)
    (hw : makeString_anbnc p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(ThreeSymbol.a ∈ vxy ∧ ThreeSymbol.c ∈ vxy) :=
  BlockWitness.not_both_in_vxy
    (by decide : ([ThreeSymbol.a, .b, .c] : List ThreeSymbol).Nodup)
    (i := 0) (j := 2) rfl rfl (by decide)
    (makeString_anbnc_eq_blockwitness p ▸ hw) hvxy

/-- `{aⁿbⁿcⁿ}` does not have the CFL pumping property.

Pumping down to `i = 0` gives `u ++ x ++ z = makeString_anbnc m`, so *every* symbol occurs `m`
times there. The pumped-out window is too short to meet both the `a`- and the `c`-block, so one
of those two symbols is absent from `v` and `y` — forcing `m = p`, while the removed window
makes the word strictly shorter. -/
theorem anbnc_not_pumpable : ¬ HasCFLPumpingProperty anbnc := by
  rintro ⟨p, hp, hpump⟩
  obtain ⟨u, v, x, y, z, hw, hvxy, hvy, hall⟩ :=
    hpump _ (makeString_anbnc_mem p) (by rw [length_makeString_anbnc]; omega)
  obtain ⟨m, hm⟩ := hall 0
  simp only [List.replicate_zero, List.flatten_nil, List.append_nil] at hm
  have hw' : makeString_anbnc p = u ++ (v ++ x ++ y) ++ z := by
    simp only [List.append_assoc] at hw ⊢; exact hw
  have hcontig := not_a_and_c_in_vxy3 p u (v ++ x ++ y) z hw' hvxy
  have hcount : ∀ s : ThreeSymbol, p = m + v.count s + y.count s := fun s => by
    have h1 : (makeString_anbnc p).count s = p := count_makeString_anbnc p s
    have h2 : (u ++ x ++ z).count s = m := by rw [hm]; exact count_makeString_anbnc m s
    rw [hw] at h1
    simp only [List.count_append] at h1 h2
    omega
  have hlen : 3 * p = 3 * m + v.length + y.length := by
    have h1 : (makeString_anbnc p).length = 3 * p := length_makeString_anbnc p
    have h2 : (u ++ x ++ z).length = 3 * m := by rw [hm]; exact length_makeString_anbnc m
    rw [hw] at h1
    simp only [List.length_append] at h1 h2
    omega
  have hpm : p = m := by
    by_cases ha : ThreeSymbol.a ∈ v ++ x ++ y
    · have hc : ThreeSymbol.c ∉ v ++ x ++ y := fun hc => hcontig ⟨ha, hc⟩
      have hcv : v.count .c = 0 := List.count_eq_zero.mpr fun h =>
        hc (List.mem_append_left _ (List.mem_append_left _ h))
      have hcy : y.count .c = 0 := List.count_eq_zero.mpr fun h => hc (List.mem_append_right _ h)
      have := hcount .c
      omega
    · have hav : v.count .a = 0 := List.count_eq_zero.mpr fun h =>
        ha (List.mem_append_left _ (List.mem_append_left _ h))
      have hay : y.count .a = 0 := List.count_eq_zero.mpr fun h => ha (List.mem_append_right _ h)
      have := hcount .a
      omega
  omega

/-- `{aⁿbⁿcⁿ}` is not context-free. -/
theorem anbnc_not_contextFree : ¬ Language.IsContextFree anbnc :=
  not_isContextFree_of_not_pumpable anbnc anbnc_not_pumpable
