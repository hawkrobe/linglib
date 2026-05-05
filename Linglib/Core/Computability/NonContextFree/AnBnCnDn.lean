import Linglib.Core.Computability.ContextFreeGrammar.Pumping
import Linglib.Core.Computability.NonContextFree.BlockWitness

/-!
# {aⁿbⁿcⁿdⁿ}: a four-symbol non-context-free witness language

The single-parameter four-symbol witness `anbncndn = {aⁿbⁿcⁿdⁿ | n ≥ 0}`,
proven non-context-free via the CFL pumping lemma + the unified adjacency
lemma in `BlockWitness`.

Membership requires `na = nb = nc = nd` (all four counts equal) **and** the
sorted shape `aⁿbⁿcⁿdⁿ`. Pumping breaks at least one count equality.

This file also hosts the **shared `FourSymbol` substrate** consumed by the
two-parameter relaxation in `NonContextFree.AmBnCmDn`:

* The alphabet (`FourSymbol`, `FourString`, `LawfulBEq`).
* Witness-form bridges (`makeString_anbncndn_eq_blockwitness`).
* Three adjacency consequences via `BlockWitness.not_both_in_vxy`
  (`not_a_and_d_in_vxy`, `not_a_and_c_in_vxy`, `not_b_and_d_in_vxy`).
* Filter-count machinery (`filter_count`, `filter_eq_nil_of_not_mem`,
  `fourSymbol_filter_total`).

Closure properties for `IsContextFree` (homomorphism, regular intersection)
live in `Linglib.Core.Computability.ContextFreeGrammar.Closure`.
-/

/-- Alphabet for cross-serial dependency patterns. -/
inductive FourSymbol where
  | a | b | c | d
  deriving DecidableEq, Repr

instance : LawfulBEq FourSymbol where
  eq_of_beq {x y} h := by cases x <;> cases y <;> first | rfl | exact absurd h (by decide)
  rfl {x} := by cases x <;> decide

abbrev FourString := List FourSymbol

/-- The language {aⁿbⁿcⁿdⁿ | n ≥ 0}, modeling Dutch cross-serial dependencies. -/
def isInLanguage_anbncndn (w : FourString) : Bool :=
  match w with
  | [] => true
  | _ =>
    let na := w.filter (· == .a) |>.length
    let nb := w.filter (· == .b) |>.length
    let nc := w.filter (· == .c) |>.length
    let nd := w.filter (· == .d) |>.length
    na == nb && nb == nc && nc == nd &&
    w == List.replicate na .a ++ List.replicate nb .b ++
         List.replicate nc .c ++ List.replicate nd .d

/-- Generate aⁿbⁿcⁿdⁿ. -/
def makeString_anbncndn (n : Nat) : FourString :=
  List.replicate n .a ++ List.replicate n .b ++
  List.replicate n .c ++ List.replicate n .d

#guard isInLanguage_anbncndn []
#guard isInLanguage_anbncndn (makeString_anbncndn 0)
#guard isInLanguage_anbncndn (makeString_anbncndn 1)
#guard isInLanguage_anbncndn (makeString_anbncndn 2)
#guard isInLanguage_anbncndn (makeString_anbncndn 3)
#guard !isInLanguage_anbncndn [.a, .b, .c]
#guard !isInLanguage_anbncndn [.a, .a, .b, .c, .c, .d]

/-- The language {aⁿbⁿcⁿdⁿ | n ≥ 0} as a mathlib `Language`. -/
def anbncndn : Language FourSymbol := {w | isInLanguage_anbncndn w = true}

/-- Unfold `isInLanguage_anbncndn` on a nonempty string. -/
private theorem isInLang_nonempty (w : FourString) (h : w ≠ []) :
    isInLanguage_anbncndn w = (
      let na := (w.filter (· == .a)).length
      let nb := (w.filter (· == .b)).length
      let nc := (w.filter (· == .c)).length
      let nd := (w.filter (· == .d)).length
      na == nb && nb == nc && nc == nd &&
      w == List.replicate na .a ++ List.replicate nb .b ++
           List.replicate nc .c ++ List.replicate nd .d) := by
  unfold isInLanguage_anbncndn
  match w, h with
  | _ :: _, _ => rfl

-- ============================================================================
-- Shared FourSymbol substrate (consumed by AmBnCmDn for the diagonal witness)
-- ============================================================================

/-- Each symbol's filter count in `makeString_anbncndn n` equals `n`. Shared
    with `AmBnCmDn` (which pumps over the same diagonal witness). -/
theorem filter_count (n : Nat) (s : FourSymbol) :
    ((makeString_anbncndn n).filter (· == s)).length = n := by
  simp only [makeString_anbncndn, List.filter_append, List.filter_replicate, List.length_append]
  cases s <;> simp (config := { decide := true })

/-- The four-symbol witness is structurally `BlockWitness [a, b, c, d] n`. -/
theorem makeString_anbncndn_eq_blockwitness (n : Nat) :
    makeString_anbncndn n =
      BlockWitness ([FourSymbol.a, .b, .c, .d] : List FourSymbol) n := by
  simp [makeString_anbncndn, BlockWitness, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc]

/-- Adjacency in the FourSymbol witness via the unified `BlockWitness.not_both_in_vxy`.
    Each instance is a one-line invocation parameterized by symbol indices. -/
private theorem not_both_in_vxy_FourSymbol {s t : FourSymbol} {i j : Nat}
    (hi : ([FourSymbol.a, .b, .c, .d] : List FourSymbol)[i]? = some s)
    (hj : ([FourSymbol.a, .b, .c, .d] : List FourSymbol)[j]? = some t)
    (hij : j ≥ i + 2) (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬ (s ∈ vxy ∧ t ∈ vxy) :=
  BlockWitness.not_both_in_vxy
    (by decide : ([FourSymbol.a, .b, .c, .d] : List FourSymbol).Nodup)
    hi hj hij (makeString_anbncndn_eq_blockwitness p ▸ hw) hvxy

theorem not_a_and_d_in_vxy (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(FourSymbol.a ∈ vxy ∧ FourSymbol.d ∈ vxy) :=
  not_both_in_vxy_FourSymbol (i := 0) (j := 3) rfl rfl (by decide) p u vxy z hw hvxy

theorem not_a_and_c_in_vxy (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(FourSymbol.a ∈ vxy ∧ FourSymbol.c ∈ vxy) :=
  not_both_in_vxy_FourSymbol (i := 0) (j := 2) rfl rfl (by decide) p u vxy z hw hvxy

theorem not_b_and_d_in_vxy (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(FourSymbol.b ∈ vxy ∧ FourSymbol.d ∈ vxy) :=
  not_both_in_vxy_FourSymbol (i := 1) (j := 3) rfl rfl (by decide) p u vxy z hw hvxy

theorem filter_eq_nil_of_not_mem (l : FourString) (s : FourSymbol) (h : s ∉ l) :
    l.filter (· == s) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx heq; exact h (beq_iff_eq.mp heq ▸ hx)

theorem fourSymbol_filter_total (l : FourString) :
    (l.filter (· == .a)).length + (l.filter (· == .b)).length +
    (l.filter (· == .c)).length + (l.filter (· == .d)).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.filter_cons, List.length_cons]
    cases h <;> simp <;> omega

private theorem counts_eq_of_inLanguage (w : FourString) (hne : w ≠ [])
    (hin : isInLanguage_anbncndn w = true) :
    (w.filter (· == .a)).length = (w.filter (· == .b)).length ∧
    (w.filter (· == .b)).length = (w.filter (· == .c)).length ∧
    (w.filter (· == .c)).length = (w.filter (· == .d)).length := by
  unfold isInLanguage_anbncndn at hin
  match w, hne with
  | _ :: _, _ =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hin
    exact ⟨hin.1.1.1, hin.1.1.2, hin.1.2⟩

-- ============================================================================
-- Membership characterizations
-- ============================================================================

/-- makeString_anbncndn n is always in {aⁿbⁿcⁿdⁿ}. -/
theorem makeString_in_language (n : Nat) :
    makeString_anbncndn n ∈ anbncndn := by
  show isInLanguage_anbncndn (makeString_anbncndn n) = true
  cases n with
  | zero => rfl
  | succ k =>
    have hne : makeString_anbncndn (k + 1) ≠ [] := by
      simp [makeString_anbncndn, List.replicate_succ]
    rw [isInLang_nonempty _ hne]
    simp only [filter_count, beq_self_eq_true, Bool.and_self, Bool.true_and]
    change (makeString_anbncndn (k + 1) == makeString_anbncndn (k + 1)) = true
    exact beq_self_eq_true _

/-- Membership characterization: every string in `anbncndn` is `makeString_anbncndn n`
    for some `n`. The converse to `makeString_in_language`. -/
theorem mem_anbncndn_iff (w : FourString) :
    w ∈ anbncndn ↔ ∃ n, w = makeString_anbncndn n := by
  constructor
  · intro hw
    by_cases hempty : w = []
    · exact ⟨0, by rw [hempty]; rfl⟩
    · have heq := isInLang_nonempty w hempty
      have hw' : isInLanguage_anbncndn w = true := hw
      rw [heq] at hw'
      simp only [Bool.and_eq_true, beq_iff_eq] at hw'
      obtain ⟨⟨⟨h_ab, h_bc⟩, h_cd⟩, h_eq⟩ := hw'
      refine ⟨(w.filter (· == .a)).length, ?_⟩
      have hb_eq : (w.filter (· == .b)).length = (w.filter (· == .a)).length := h_ab.symm
      have hc_eq : (w.filter (· == .c)).length = (w.filter (· == .a)).length :=
        h_bc.symm.trans h_ab.symm
      have hd_eq : (w.filter (· == .d)).length = (w.filter (· == .a)).length :=
        h_cd.symm.trans (h_bc.symm.trans h_ab.symm)
      calc w
          = List.replicate (w.filter (· == .a)).length .a ++
              List.replicate (w.filter (· == .b)).length .b ++
              List.replicate (w.filter (· == .c)).length .c ++
              List.replicate (w.filter (· == .d)).length .d := h_eq
        _ = List.replicate (w.filter (· == .a)).length .a ++
              List.replicate (w.filter (· == .a)).length .b ++
              List.replicate (w.filter (· == .a)).length .c ++
              List.replicate (w.filter (· == .a)).length .d := by
              rw [hb_eq, hc_eq, hd_eq]
        _ = makeString_anbncndn (w.filter (· == .a)).length := rfl
  · rintro ⟨n, rfl⟩
    exact makeString_in_language n

-- ============================================================================
-- Pumping fails for {aⁿbⁿcⁿdⁿ}
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- Pumping breaks membership in {aⁿbⁿcⁿdⁿ}. -/
theorem pump_breaks_anbncndn (p : Nat) (_hp : p > 0) :
    let w := makeString_anbncndn p
    ∀ u v x y z : FourString,
      w = u ++ v ++ x ++ y ++ z →
      (v ++ x ++ y).length ≤ p →
      (v.length + y.length) ≥ 1 →
      ∃ i : Nat, (u ++ List.flatten (List.replicate i v) ++ x ++
                   List.flatten (List.replicate i y) ++ z) ∉ anbncndn := by
  intro w u v x y z hw hvxy_len hvy_len
  use 0
  simp only [List.replicate_zero, List.flatten_nil, List.append_nil]
  have hw' : makeString_anbncndn p = u ++ (v ++ x ++ y) ++ z := by
    have : w = u ++ v ++ x ++ y ++ z := hw
    simp only [List.append_assoc] at this ⊢; exact this
  have hcontig := not_a_and_d_in_vxy p u (v ++ x ++ y) z hw' hvxy_len
  have hvxy_len' : v.length + x.length + y.length ≤ p := by
    simp only [List.length_append] at hvxy_len; omega
  show ¬ (isInLanguage_anbncndn (u ++ x ++ z) = true)
  intro hin
  have huxz_ne : u ++ x ++ z ≠ [] := by
    intro h
    have huxz0 : u.length + x.length + z.length = 0 := by
      have := congr_arg List.length h; simp only [List.length_append, List.length_nil] at this; omega
    have hlen : u.length + v.length + x.length + y.length + z.length = 4 * p := by
      have := congr_arg List.length hw'.symm
      simp only [makeString_anbncndn, List.length_append, List.length_replicate] at this; omega
    omega
  obtain ⟨hab, hbc, hcd⟩ := counts_eq_of_inLanguage _ huxz_ne hin
  have hrel : ∀ s : FourSymbol,
      ((u ++ x ++ z).filter (· == s)).length +
      (v.filter (· == s)).length + (y.filter (· == s)).length = p := by
    intro s
    have h1 := filter_count p s; rw [hw'] at h1
    simp only [List.filter_append, List.length_append] at h1 ⊢; omega
  have h4k : 4 * ((u ++ x ++ z).filter (· == .a)).length = (u ++ x ++ z).length := by
    have := fourSymbol_filter_total (u ++ x ++ z); omega
  have hlen_uxz : (u ++ x ++ z).length + (v.length + y.length) = 4 * p := by
    have hlen : (makeString_anbncndn p).length = 4 * p := by
      simp [makeString_anbncndn, List.length_append, List.length_replicate]; omega
    rw [hw'] at hlen; simp only [List.length_append] at hlen ⊢; omega
  have hk_eq_p : ((u ++ x ++ z).filter (· == .a)).length = p := by
    by_cases ha : FourSymbol.a ∈ (v ++ x ++ y)
    · have hd : FourSymbol.d ∉ (v ++ x ++ y) := fun hd => hcontig ⟨ha, hd⟩
      have hdv : FourSymbol.d ∉ v :=
        fun h => hd (List.mem_append_left _ (List.mem_append_left _ h))
      have hdy : FourSymbol.d ∉ y :=
        fun h => hd (List.mem_append_right _ h)
      have hrd := hrel .d
      rw [filter_eq_nil_of_not_mem v .d hdv, filter_eq_nil_of_not_mem y .d hdy] at hrd
      simp only [List.length_nil, Nat.add_zero] at hrd; omega
    · have hav : FourSymbol.a ∉ v :=
        fun h => ha (List.mem_append_left _ (List.mem_append_left _ h))
      have hay : FourSymbol.a ∉ y :=
        fun h => ha (List.mem_append_right _ h)
      have hra := hrel .a
      rw [filter_eq_nil_of_not_mem v .a hav, filter_eq_nil_of_not_mem y .a hay] at hra
      simp only [List.length_nil, Nat.add_zero] at hra; exact hra
  omega

/-- {aⁿbⁿcⁿdⁿ} does NOT have the CFL pumping property. -/
theorem anbncndn_not_pumpable :
    ¬ HasCFLPumpingProperty anbncndn := by
  intro ⟨p, hp, hpump⟩
  have hw_in := makeString_in_language p
  have hw_len : (makeString_anbncndn p).length ≥ p := by
    simp only [makeString_anbncndn, List.length_append, List.length_replicate]; omega
  obtain ⟨u, v, x, y, z, hw, hvxy, hvy, hall⟩ := hpump _ hw_in hw_len
  obtain ⟨i, hbreak⟩ := pump_breaks_anbncndn p hp u v x y z hw hvxy hvy
  exact hbreak (hall i)

/-- {aⁿbⁿcⁿdⁿ} is not context-free. -/
theorem anbncndn_not_contextFree : ¬ Language.IsContextFree anbncndn :=
  not_isContextFree_of_not_pumpable anbncndn anbncndn_not_pumpable
