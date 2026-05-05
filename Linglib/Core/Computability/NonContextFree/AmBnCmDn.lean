import Linglib.Core.Computability.NonContextFree.AnBnCnDn

/-!
# {aᵐbⁿcᵐdⁿ}: two-parameter four-symbol non-context-free witness

The two-parameter relaxation of `anbncndn`: case-sorted strings with
`a-count = c-count` and `b-count = d-count` (the diagonal pairs only —
not all four counts equal). Strict superset of `anbncndn`; this is the
language @cite{shieber-1985}'s argument that Swiss German is not weakly
context-free actually requires.

## Pumping

The witness is the **diagonal `makeString_anbncndn p`** (which lies in
`ambncmdn`, since equal-all-four implies the diagonal pairs match).
Pumping breaks one of the two diagonal equalities rather than all four
— hence the substantive content of this file beyond `AnBnCnDn`.

The proof uses the shared adjacency lemmas (`not_a_and_c_in_vxy`,
`not_b_and_d_in_vxy`) and filter machinery (`filter_count`,
`filter_eq_nil_of_not_mem`, `fourSymbol_filter_total`) re-exported from
`AnBnCnDn`.
-/

/-- The language `{aᵐbⁿcᵐdⁿ | m, n ≥ 0}`: case-sorted strings with
    `a-count = c-count` and `b-count = d-count`. Membership requires
    the case-sorted shape AND the two diagonal-count equalities. -/
def isInLanguage_ambncmdn (w : FourString) : Bool :=
  match w with
  | [] => true
  | _ =>
    let na := w.filter (· == .a) |>.length
    let nb := w.filter (· == .b) |>.length
    let nc := w.filter (· == .c) |>.length
    let nd := w.filter (· == .d) |>.length
    na == nc && nb == nd &&
    w == List.replicate na .a ++ List.replicate nb .b ++
         List.replicate nc .c ++ List.replicate nd .d

/-- Generate `aᵐbⁿcᵐdⁿ`. -/
def makeString_ambncmdn (m n : Nat) : FourString :=
  List.replicate m .a ++ List.replicate n .b ++
  List.replicate m .c ++ List.replicate n .d

#guard isInLanguage_ambncmdn []
#guard isInLanguage_ambncmdn (makeString_ambncmdn 0 0)
#guard isInLanguage_ambncmdn (makeString_ambncmdn 1 1)
#guard isInLanguage_ambncmdn (makeString_ambncmdn 2 3)
#guard isInLanguage_ambncmdn (makeString_ambncmdn 3 1)
#guard !isInLanguage_ambncmdn [.a, .b, .c]
#guard !isInLanguage_ambncmdn [.a, .a, .b, .c, .c, .d, .d]

/-- The language `{aᵐbⁿcᵐdⁿ}` as a mathlib `Language`. -/
def ambncmdn : Language FourSymbol := {w | isInLanguage_ambncmdn w = true}

/-- Unfold `isInLanguage_ambncmdn` on a nonempty string. -/
private theorem isInLang_ambncmdn_nonempty (w : FourString) (h : w ≠ []) :
    isInLanguage_ambncmdn w = (
      let na := (w.filter (· == .a)).length
      let nb := (w.filter (· == .b)).length
      let nc := (w.filter (· == .c)).length
      let nd := (w.filter (· == .d)).length
      na == nc && nb == nd &&
      w == List.replicate na .a ++ List.replicate nb .b ++
           List.replicate nc .c ++ List.replicate nd .d) := by
  unfold isInLanguage_ambncmdn
  match w, h with
  | _ :: _, _ => rfl

/-- Diagonal-count equalities extracted from ambncmdn membership. -/
private theorem counts_ambncmdn_of_inLanguage (w : FourString) (hne : w ≠ [])
    (hin : isInLanguage_ambncmdn w = true) :
    (w.filter (· == .a)).length = (w.filter (· == .c)).length ∧
    (w.filter (· == .b)).length = (w.filter (· == .d)).length := by
  unfold isInLanguage_ambncmdn at hin
  match w, hne with
  | _ :: _, _ =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hin
    exact ⟨hin.1.1, hin.1.2⟩

/-- The diagonal witness `makeString_anbncndn n` lies in `ambncmdn` (since
    `na = nb = nc = nd = n` satisfies the weaker `na = nc ∧ nb = nd`). -/
theorem makeString_anbncndn_in_ambncmdn (n : Nat) :
    makeString_anbncndn n ∈ ambncmdn := by
  show isInLanguage_ambncmdn (makeString_anbncndn n) = true
  cases n with
  | zero => rfl
  | succ k =>
    have hne : makeString_anbncndn (k + 1) ≠ [] := by
      simp [makeString_anbncndn, List.replicate_succ]
    rw [isInLang_ambncmdn_nonempty _ hne]
    simp only [filter_count, beq_self_eq_true, Bool.and_self, Bool.true_and]
    change (makeString_anbncndn (k + 1) == makeString_anbncndn (k + 1)) = true
    exact beq_self_eq_true _

/-- Asymmetric witness `makeString_ambncmdn m n` lies in `ambncmdn`. -/
theorem makeString_ambncmdn_in_language (m n : Nat) :
    makeString_ambncmdn m n ∈ ambncmdn := by
  show isInLanguage_ambncmdn (makeString_ambncmdn m n) = true
  by_cases hempty : makeString_ambncmdn m n = []
  · rw [hempty]; rfl
  · rw [isInLang_ambncmdn_nonempty _ hempty]
    have hca : ((makeString_ambncmdn m n).filter (· == .a)).length = m := by
      simp only [makeString_ambncmdn, List.filter_append, List.filter_replicate,
                 List.length_append, List.length_nil]
      simp (config := { decide := true })
    have hcb : ((makeString_ambncmdn m n).filter (· == .b)).length = n := by
      simp only [makeString_ambncmdn, List.filter_append, List.filter_replicate,
                 List.length_append, List.length_nil]
      simp (config := { decide := true })
    have hcc : ((makeString_ambncmdn m n).filter (· == .c)).length = m := by
      simp only [makeString_ambncmdn, List.filter_append, List.filter_replicate,
                 List.length_append, List.length_nil]
      simp (config := { decide := true })
    have hcd : ((makeString_ambncmdn m n).filter (· == .d)).length = n := by
      simp only [makeString_ambncmdn, List.filter_append, List.filter_replicate,
                 List.length_append, List.length_nil]
      simp (config := { decide := true })
    simp only [hca, hcb, hcc, hcd, beq_self_eq_true, Bool.and_self, Bool.true_and]
    show (makeString_ambncmdn m n == makeString_ambncmdn m n) = true
    exact beq_self_eq_true _

/-- Membership characterization: every string in `ambncmdn` equals
    `makeString_ambncmdn m n` for some `m, n`. -/
theorem mem_ambncmdn_iff (w : FourString) :
    w ∈ ambncmdn ↔ ∃ m n, w = makeString_ambncmdn m n := by
  constructor
  · intro hw
    by_cases hempty : w = []
    · exact ⟨0, 0, by rw [hempty]; rfl⟩
    · have heq := isInLang_ambncmdn_nonempty w hempty
      have hw' : isInLanguage_ambncmdn w = true := hw
      rw [heq] at hw'
      simp only [Bool.and_eq_true, beq_iff_eq] at hw'
      obtain ⟨⟨h_ac, h_bd⟩, h_eq⟩ := hw'
      refine ⟨(w.filter (· == .a)).length, (w.filter (· == .b)).length, ?_⟩
      have hc_eq : (w.filter (· == .c)).length = (w.filter (· == .a)).length := h_ac.symm
      have hd_eq : (w.filter (· == .d)).length = (w.filter (· == .b)).length := h_bd.symm
      calc w
          = List.replicate (w.filter (· == .a)).length .a ++
              List.replicate (w.filter (· == .b)).length .b ++
              List.replicate (w.filter (· == .c)).length .c ++
              List.replicate (w.filter (· == .d)).length .d := h_eq
        _ = List.replicate (w.filter (· == .a)).length .a ++
              List.replicate (w.filter (· == .b)).length .b ++
              List.replicate (w.filter (· == .a)).length .c ++
              List.replicate (w.filter (· == .b)).length .d := by
              rw [hc_eq, hd_eq]
        _ = makeString_ambncmdn (w.filter (· == .a)).length
              (w.filter (· == .b)).length := rfl
  · rintro ⟨m, n, rfl⟩
    exact makeString_ambncmdn_in_language m n

set_option maxHeartbeats 800000 in
/-- Pumping breaks ambncmdn membership. The witness is the diagonal
    `makeString_anbncndn p`. Deleting v and y must break either the
    `a-count = c-count` equality or the `b-count = d-count` equality,
    depending on which two adjacent blocks vxy intersects. -/
theorem pump_breaks_ambncmdn (p : Nat) (_hp : p > 0) :
    let w := makeString_anbncndn p
    ∀ u v x y z : FourString,
      w = u ++ v ++ x ++ y ++ z →
      (v ++ x ++ y).length ≤ p →
      (v.length + y.length) ≥ 1 →
      ∃ i : Nat, (u ++ List.flatten (List.replicate i v) ++ x ++
                   List.flatten (List.replicate i y) ++ z) ∉ ambncmdn := by
  intro w u v x y z hw hvxy_len hvy_len
  use 0
  simp only [List.replicate_zero, List.flatten_nil, List.append_nil]
  have hw' : makeString_anbncndn p = u ++ (v ++ x ++ y) ++ z := by
    have : w = u ++ v ++ x ++ y ++ z := hw
    simp only [List.append_assoc] at this ⊢; exact this
  have hac := not_a_and_c_in_vxy p u (v ++ x ++ y) z hw' hvxy_len
  have hbd := not_b_and_d_in_vxy p u (v ++ x ++ y) z hw' hvxy_len
  show ¬ (isInLanguage_ambncmdn (u ++ x ++ z) = true)
  intro hin
  have huxz_ne : u ++ x ++ z ≠ [] := by
    intro h
    have huxz0 : u.length + x.length + z.length = 0 := by
      have := congr_arg List.length h
      simp only [List.length_append, List.length_nil] at this; omega
    have hlen : u.length + v.length + x.length + y.length + z.length = 4 * p := by
      have := congr_arg List.length hw'.symm
      simp only [makeString_anbncndn, List.length_append, List.length_replicate] at this; omega
    have hvxy_len' : v.length + x.length + y.length ≤ p := by
      simp only [List.length_append] at hvxy_len; omega
    omega
  obtain ⟨h_ac, h_bd⟩ := counts_ambncmdn_of_inLanguage _ huxz_ne hin
  -- For each symbol, count(uxz, s) + count(vy, s) = p
  have hrel : ∀ s : FourSymbol,
      ((u ++ x ++ z).filter (· == s)).length +
      (v.filter (· == s)).length + (y.filter (· == s)).length = p := by
    intro s
    have h1 := filter_count p s; rw [hw'] at h1
    simp only [List.filter_append, List.length_append] at h1 ⊢; omega
  -- count(vy, a) = count(vy, c) and count(vy, b) = count(vy, d)
  have hac_vy : (v.filter (· == .a)).length + (y.filter (· == .a)).length =
                (v.filter (· == .c)).length + (y.filter (· == .c)).length := by
    have h_a := hrel .a; have h_c := hrel .c; omega
  have hbd_vy : (v.filter (· == .b)).length + (y.filter (· == .b)).length =
                (v.filter (· == .d)).length + (y.filter (· == .d)).length := by
    have h_b := hrel .b; have h_d := hrel .d; omega
  -- Show all four counts in vy are 0, contradicting |vy| ≥ 1
  have ha_vy_zero : (v.filter (· == .a)).length + (y.filter (· == .a)).length = 0 := by
    by_cases ha : FourSymbol.a ∈ v ++ x ++ y
    · have hc_notin : FourSymbol.c ∉ v ++ x ++ y := fun hc => hac ⟨ha, hc⟩
      have hcv : FourSymbol.c ∉ v :=
        fun h => hc_notin (List.mem_append_left _ (List.mem_append_left _ h))
      have hcy : FourSymbol.c ∉ y :=
        fun h => hc_notin (List.mem_append_right _ h)
      rw [filter_eq_nil_of_not_mem v .c hcv, filter_eq_nil_of_not_mem y .c hcy] at hac_vy
      simp only [List.length_nil, Nat.add_zero] at hac_vy; omega
    · have hav : FourSymbol.a ∉ v :=
        fun h => ha (List.mem_append_left _ (List.mem_append_left _ h))
      have hay : FourSymbol.a ∉ y :=
        fun h => ha (List.mem_append_right _ h)
      rw [filter_eq_nil_of_not_mem v .a hav, filter_eq_nil_of_not_mem y .a hay]
      simp only [List.length_nil, Nat.add_zero]
  have hb_vy_zero : (v.filter (· == .b)).length + (y.filter (· == .b)).length = 0 := by
    by_cases hb : FourSymbol.b ∈ v ++ x ++ y
    · have hd_notin : FourSymbol.d ∉ v ++ x ++ y := fun hd => hbd ⟨hb, hd⟩
      have hdv : FourSymbol.d ∉ v :=
        fun h => hd_notin (List.mem_append_left _ (List.mem_append_left _ h))
      have hdy : FourSymbol.d ∉ y :=
        fun h => hd_notin (List.mem_append_right _ h)
      rw [filter_eq_nil_of_not_mem v .d hdv, filter_eq_nil_of_not_mem y .d hdy] at hbd_vy
      simp only [List.length_nil, Nat.add_zero] at hbd_vy; omega
    · have hbv : FourSymbol.b ∉ v :=
        fun h => hb (List.mem_append_left _ (List.mem_append_left _ h))
      have hby : FourSymbol.b ∉ y :=
        fun h => hb (List.mem_append_right _ h)
      rw [filter_eq_nil_of_not_mem v .b hbv, filter_eq_nil_of_not_mem y .b hby]
      simp only [List.length_nil, Nat.add_zero]
  have hc_vy_zero : (v.filter (· == .c)).length + (y.filter (· == .c)).length = 0 := by
    omega
  have hd_vy_zero : (v.filter (· == .d)).length + (y.filter (· == .d)).length = 0 := by
    omega
  have hv_total := fourSymbol_filter_total v
  have hy_total := fourSymbol_filter_total y
  omega

/-- `{aᵐbⁿcᵐdⁿ}` does NOT have the CFL pumping property. -/
theorem ambncmdn_not_pumpable :
    ¬ HasCFLPumpingProperty ambncmdn := by
  intro ⟨p, hp, hpump⟩
  have hw_in := makeString_anbncndn_in_ambncmdn p
  have hw_len : (makeString_anbncndn p).length ≥ p := by
    simp only [makeString_anbncndn, List.length_append, List.length_replicate]; omega
  obtain ⟨u, v, x, y, z, hw, hvxy, hvy, hall⟩ := hpump _ hw_in hw_len
  obtain ⟨i, hbreak⟩ := pump_breaks_ambncmdn p hp u v x y z hw hvxy hvy
  exact hbreak (hall i)

/-- {aᵐbⁿcᵐdⁿ} is not context-free. The two-parameter relaxation that
    @cite{shieber-1985}'s Swiss German argument actually requires. -/
theorem ambncmdn_not_contextFree : ¬ Language.IsContextFree ambncmdn :=
  not_isContextFree_of_not_pumpable ambncmdn ambncmdn_not_pumpable
