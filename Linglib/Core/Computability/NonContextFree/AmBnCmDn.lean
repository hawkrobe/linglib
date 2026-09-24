module

public import Linglib.Core.Computability.NonContextFree.AnBnCnDn

/-!
# `{aᵐbⁿcᵐdⁿ}`: a two-parameter four-symbol non-context-free witness

This file proves that `{aᵐbⁿcᵐdⁿ}` is not context-free, the language Shieber's argument that
Swiss German is not weakly context-free requires. It follows from a stronger result: a language
containing every `aⁿbⁿcⁿdⁿ` whose words have no more `a` than `c` and no more `b` than `d` is not
context-free. Pumping `aᵖbᵖcᵖdᵖ` down and up forces the pumped window to carry as many `a` as `c`
and as many `b` as `d`, and a window of length at most `p` meets neither pair.

## Main definitions

* `makeString_ambncmdn m n`: the word `aᵐbⁿcᵐdⁿ`
* `ambncmdn`: the language `{aᵐbⁿcᵐdⁿ | m, n ≥ 0}`

## Main results

* `not_isContextFree_of_anbncndn_le`: a language containing `anbncndn` whose words have no more
  `a` than `c` and no more `b` than `d` is not context-free
* `ambncmdn_not_contextFree`: `ambncmdn` is not context-free

## References

* [shieber-1985]
-/

@[expose] public section

/-- `makeString_ambncmdn m n` is the word `aᵐbⁿcᵐdⁿ`. -/
def makeString_ambncmdn (m n : ℕ) : FourString :=
  List.replicate m .a ++ List.replicate n .b ++
  List.replicate m .c ++ List.replicate n .d

/-- `ambncmdn` is the language `{aᵐbⁿcᵐdⁿ | m, n ≥ 0}`, the range of `makeString_ambncmdn`. -/
def ambncmdn : Language FourSymbol := {w | ∃ m n, w = makeString_ambncmdn m n}

/-- Every word of `ambncmdn` is `makeString_ambncmdn m n` for some `m` and `n`. -/
theorem mem_ambncmdn_iff (w : FourString) :
    w ∈ ambncmdn ↔ ∃ m n, w = makeString_ambncmdn m n := Iff.rfl

theorem makeString_ambncmdn_in_language (m n : ℕ) : makeString_ambncmdn m n ∈ ambncmdn :=
  ⟨m, n, rfl⟩

theorem anbncndn_le_ambncmdn : anbncndn ≤ ambncmdn := fun _ ⟨n, hn⟩ ↦ ⟨n, n, hn⟩

@[simp] theorem count_a_makeString_ambncmdn (m n : ℕ) :
    (makeString_ambncmdn m n).count .a = m := by
  simp [makeString_ambncmdn, List.count_replicate]

@[simp] theorem count_b_makeString_ambncmdn (m n : ℕ) :
    (makeString_ambncmdn m n).count .b = n := by
  simp [makeString_ambncmdn, List.count_replicate]

@[simp] theorem count_c_makeString_ambncmdn (m n : ℕ) :
    (makeString_ambncmdn m n).count .c = m := by
  simp [makeString_ambncmdn, List.count_replicate]

@[simp] theorem count_d_makeString_ambncmdn (m n : ℕ) :
    (makeString_ambncmdn m n).count .d = n := by
  simp [makeString_ambncmdn, List.count_replicate]

/-- A language containing every `aⁿbⁿcⁿdⁿ` whose words have no more `a` than `c` and no more `b`
than `d` is not context-free. -/
theorem not_isContextFree_of_anbncndn_le {X : Language FourSymbol} (h₁ : anbncndn ≤ X)
    (h₂ : ∀ w ∈ X, w.count .a ≤ w.count .c ∧ w.count .b ≤ w.count .d) :
    ¬ X.IsContextFree := by
  refine mt Language.IsContextFree.hasCFLPumpingProperty ?_
  rintro ⟨p, hp, hpump⟩
  obtain ⟨u, v, x, y, z, hw, hvxy, hvy, hall⟩ :=
    hpump _ (h₁ (makeString_in_language p)) (by rw [length_makeString_anbncndn]; omega)
  have hw' : makeString_anbncndn p = u ++ (v ++ x ++ y) ++ z := by
    simpa [List.append_assoc] using hw
  have hac := not_a_and_c_in_vxy p u (v ++ x ++ y) z hw' hvxy
  have hbd := not_b_and_d_in_vxy p u (v ++ x ++ y) z hw' hvxy
  have hrel : ∀ s : FourSymbol, u.count s + v.count s + x.count s + y.count s + z.count s = p :=
    fun s ↦ by simpa [hw, Nat.add_assoc] using count_makeString_anbncndn p s
  have h0 := h₂ _ (hall 0)
  have h2 := h₂ _ (hall 2)
  simp only [List.replicate_zero, List.replicate_succ, List.flatten_nil, List.flatten_cons,
    List.append_nil, List.count_append] at h0 h2
  have hz : ∀ s, s ∉ v ++ x ++ y → v.count s = 0 ∧ y.count s = 0 := fun s hs ↦
    ⟨List.count_eq_zero.mpr fun h ↦ hs (by simp [h]),
      List.count_eq_zero.mpr fun h ↦ hs (by simp [h])⟩
  have ha := hrel .a; have hb := hrel .b; have hc := hrel .c; have hd := hrel .d
  have hv := fourSymbol_count_total v
  have hy := fourSymbol_count_total y
  rcases (not_and_or.mp hac).imp (hz _) (hz _) with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases (not_and_or.mp hbd).imp (hz _) (hz _) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

/-- `{aᵐbⁿcᵐdⁿ}` is not context-free. -/
theorem ambncmdn_not_contextFree : ¬ Language.IsContextFree ambncmdn :=
  not_isContextFree_of_anbncndn_le anbncndn_le_ambncmdn fun _ ⟨m, n, hw⟩ ↦ by simp [hw]
