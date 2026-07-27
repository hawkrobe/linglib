import Linglib.Core.Computability.NonContextFree.AnBnCnDn

/-!
# `{aᵐbⁿcᵐdⁿ}`: a two-parameter four-symbol non-context-free witness

The two-parameter relaxation of `anbncndn`: case-sorted strings whose `a`- and `c`-counts agree
and whose `b`- and `d`-counts agree — the diagonal pairs only, not all four counts equal. A
strict superset of `anbncndn`, and the language [shieber-1985]'s argument that Swiss German is
not weakly context-free actually requires.

Pumping runs on the **diagonal witness `makeString_anbncndn p`**, which lies in `ambncmdn`
because equal-all-four implies the diagonal pairs match. Deleting the pumped window breaks one
of the two diagonal equalities rather than all four — the substantive content beyond `AnBnCnDn`.

## Main definitions

* `makeString_ambncmdn m n`: the witness word `aᵐbⁿcᵐdⁿ`.
* `ambncmdn`: the language `{aᵐbⁿcᵐdⁿ | m, n ≥ 0}`, as the range of `makeString_ambncmdn`.

## Main results

* `ambncmdn_not_pumpable`: `ambncmdn` lacks the CFL pumping property.
* `ambncmdn_not_contextFree`: `ambncmdn` is not context-free.
-/

/-- The witness word `aᵐbⁿcᵐdⁿ`. -/
def makeString_ambncmdn (m n : ℕ) : FourString :=
  List.replicate m .a ++ List.replicate n .b ++
  List.replicate m .c ++ List.replicate n .d

/-- The language `{aᵐbⁿcᵐdⁿ | m, n ≥ 0}`, as the range of `makeString_ambncmdn`. -/
def ambncmdn : Language FourSymbol := {w | ∃ m n, w = makeString_ambncmdn m n}

/-- Membership characterization: every string in `ambncmdn` equals `makeString_ambncmdn m n`
for some `m, n`. -/
theorem mem_ambncmdn_iff (w : FourString) :
    w ∈ ambncmdn ↔ ∃ m n, w = makeString_ambncmdn m n := Iff.rfl

theorem makeString_ambncmdn_in_language (m n : ℕ) : makeString_ambncmdn m n ∈ ambncmdn :=
  ⟨m, n, rfl⟩

/-- The diagonal witness lies in `ambncmdn`: `aⁿbⁿcⁿdⁿ` *is* `aᵐbⁿcᵐdⁿ` at `m = n`. -/
theorem makeString_anbncndn_in_ambncmdn (n : ℕ) : makeString_anbncndn n ∈ ambncmdn :=
  ⟨n, n, rfl⟩

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

/-- Pumping breaks `ambncmdn` membership. Deleting `v` and `y` must break either the
`a`-count = `c`-count equality or the `b`-count = `d`-count equality, depending on which
blocks the window meets. -/
theorem pump_breaks_ambncmdn (p : ℕ) (_hp : 0 < p) :
    ∀ u v x y z : FourString,
      makeString_anbncndn p = u ++ v ++ x ++ y ++ z →
      (v ++ x ++ y).length ≤ p →
      (v.length + y.length) ≥ 1 →
      ∃ i : ℕ, (u ++ List.flatten (List.replicate i v) ++ x ++
                   List.flatten (List.replicate i y) ++ z) ∉ ambncmdn := by
  intro u v x y z hw hvxy hvy
  refine ⟨0, ?_⟩
  simp only [List.replicate_zero, List.flatten_nil, List.append_nil]
  rintro ⟨m, n, hm⟩
  have hw' : makeString_anbncndn p = u ++ (v ++ x ++ y) ++ z := by
    simp only [List.append_assoc] at hw ⊢; exact hw
  have hac := not_a_and_c_in_vxy p u (v ++ x ++ y) z hw' hvxy
  have hbd := not_b_and_d_in_vxy p u (v ++ x ++ y) z hw' hvxy
  -- for each symbol: its count in `u ++ x ++ z`, plus those in `v` and `y`, is `p`
  have hrel : ∀ s : FourSymbol,
      (u ++ x ++ z).count s + v.count s + y.count s = p := fun s => by
    have h1 : (makeString_anbncndn p).count s = p := count_makeString_anbncndn p s
    rw [hw] at h1
    simp only [List.count_append] at h1 ⊢
    omega
  -- the two diagonal equalities transfer from `u ++ x ++ z` to the deleted window
  have hac_vy : v.count .a + y.count .a = v.count .c + y.count .c := by
    have ha := hrel .a; have hc := hrel .c
    rw [hm] at ha hc; simp only [count_a_makeString_ambncmdn,
      count_c_makeString_ambncmdn] at ha hc; omega
  have hbd_vy : v.count .b + y.count .b = v.count .d + y.count .d := by
    have hb := hrel .b; have hd := hrel .d
    rw [hm] at hb hd; simp only [count_b_makeString_ambncmdn,
      count_d_makeString_ambncmdn] at hb hd; omega
  -- the window is too short to meet both blocks of either diagonal pair, so both are empty
  have ha_zero : v.count .a + y.count .a = 0 := by
    by_cases ha : FourSymbol.a ∈ v ++ x ++ y
    · have hc : FourSymbol.c ∉ v ++ x ++ y := fun hc => hac ⟨ha, hc⟩
      have hcv : v.count .c = 0 := List.count_eq_zero.mpr fun h =>
        hc (List.mem_append_left _ (List.mem_append_left _ h))
      have hcy : y.count .c = 0 := List.count_eq_zero.mpr fun h => hc (List.mem_append_right _ h)
      omega
    · have hav : v.count .a = 0 := List.count_eq_zero.mpr fun h =>
        ha (List.mem_append_left _ (List.mem_append_left _ h))
      have hay : y.count .a = 0 := List.count_eq_zero.mpr fun h => ha (List.mem_append_right _ h)
      omega
  have hb_zero : v.count .b + y.count .b = 0 := by
    by_cases hb : FourSymbol.b ∈ v ++ x ++ y
    · have hd : FourSymbol.d ∉ v ++ x ++ y := fun hd => hbd ⟨hb, hd⟩
      have hdv : v.count .d = 0 := List.count_eq_zero.mpr fun h =>
        hd (List.mem_append_left _ (List.mem_append_left _ h))
      have hdy : y.count .d = 0 := List.count_eq_zero.mpr fun h => hd (List.mem_append_right _ h)
      omega
    · have hbv : v.count .b = 0 := List.count_eq_zero.mpr fun h =>
        hb (List.mem_append_left _ (List.mem_append_left _ h))
      have hby : y.count .b = 0 := List.count_eq_zero.mpr fun h => hb (List.mem_append_right _ h)
      omega
  -- all four counts vanish in `v` and `y`, so the deleted window was empty
  have hv := fourSymbol_count_total v
  have hy := fourSymbol_count_total y
  omega

/-- `{aᵐbⁿcᵐdⁿ}` does not have the CFL pumping property. -/
theorem ambncmdn_not_pumpable : ¬ HasCFLPumpingProperty ambncmdn := by
  rintro ⟨p, hp, hpump⟩
  obtain ⟨u, v, x, y, z, hw, hvxy, hvy, hall⟩ :=
    hpump _ (makeString_anbncndn_in_ambncmdn p) (by rw [length_makeString_anbncndn]; omega)
  obtain ⟨i, hbreak⟩ := pump_breaks_ambncmdn p hp u v x y z hw hvxy hvy
  exact hbreak (hall i)

/-- `{aᵐbⁿcᵐdⁿ}` is not context-free — the two-parameter relaxation that [shieber-1985]'s
Swiss German argument requires. -/
theorem ambncmdn_not_contextFree : ¬ Language.IsContextFree ambncmdn :=
  not_isContextFree_of_not_pumpable ambncmdn ambncmdn_not_pumpable
