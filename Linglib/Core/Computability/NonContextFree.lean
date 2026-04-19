import Linglib.Core.Computability.PumpingLemma

/-!
# Non-Context-Free Witness Languages

Two witness languages that fail the CFL pumping property:

- `anbncndn : Language FourSymbol` — {aⁿbⁿcⁿdⁿ | n ≥ 0}, modeling Dutch cross-serial
  dependencies
- `anbnc : Language ThreeSymbol` — {aⁿbⁿcⁿ | n ≥ 0}

## Key Results

- `anbncndn_not_pumpable` / `anbnc_not_pumpable` — pumping failure, fully proved
- `anbncndn_not_contextFree` / `anbnc_not_contextFree` — non-context-freeness
  via `not_isContextFree_of_not_pumpable`

## Consumers

- `Theories.Syntax.CCG.Formal.GenerativeCapacity` — proving CCG > CFG
- `Shieber1985` — proving Swiss German ∉ CFL
- `PullumGazdar1982` — CF vs non-CF distinction

## String Homomorphisms

`StringHom` and `Language.stringMap` provide basic closure-under-homomorphism
infrastructure used by the Shieber 1985 reduction.
-/

-- ============================================================================
-- {aⁿbⁿcⁿdⁿ}
-- ============================================================================

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

/-- Each symbol's filter count in makeString equals n. -/
private theorem filter_count (n : Nat) (s : FourSymbol) :
    ((makeString_anbncndn n).filter (· == s)).length = n := by
  simp only [makeString_anbncndn, List.filter_append, List.filter_replicate, List.length_append]
  cases s <;> simp (config := { decide := true })

/--.a cannot appear in the suffix of aᵖbᵖcᵖdᵖ past position p. -/
private theorem a_not_in_vxy_of_u_ge_p (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hu : u.length ≥ p) :
    FourSymbol.a ∉ vxy := by
  intro ha
  have hsuffix : vxy ++ z = (makeString_anbncndn p).drop u.length := by
    have : u ++ (vxy ++ z) = makeString_anbncndn p := by rw [hw, List.append_assoc]
    rw [← this, List.drop_left]
  have hx : FourSymbol.a ∈ (makeString_anbncndn p).drop u.length :=
    hsuffix ▸ List.mem_append_left z ha
  rw [show makeString_anbncndn p =
    List.replicate p FourSymbol.a ++ (List.replicate p FourSymbol.b ++
    List.replicate p FourSymbol.c ++ List.replicate p FourSymbol.d) by
    simp [makeString_anbncndn, List.append_assoc]] at hx
  rw [List.drop_append] at hx
  simp only [List.mem_append, List.drop_replicate, List.mem_replicate,
             List.length_replicate] at hx
  rcases hx with ⟨h, _⟩ | h
  · omega
  · have := List.mem_of_mem_drop h
    simp only [List.mem_append, List.mem_replicate] at this
    obtain (⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩ := this <;> exact absurd h (by decide)

/--.d cannot appear in the prefix of aᵖbᵖcᵖdᵖ up to position 3p. -/
private theorem d_not_in_vxy_of_end_le_3p (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hend : u.length + vxy.length ≤ 3 * p) :
    FourSymbol.d ∉ vxy := by
  intro hd
  have hpre : u ++ vxy = (makeString_anbncndn p).take (u.length + vxy.length) := by
    have heq : (u ++ vxy) ++ z = makeString_anbncndn p := by rw [hw, List.append_assoc]
    rw [show u.length + vxy.length = (u ++ vxy).length from by simp]
    rw [← heq, List.take_left]
  have hd_pre : FourSymbol.d ∈ u ++ vxy := List.mem_append_right _ hd
  rw [hpre] at hd_pre
  rw [show (makeString_anbncndn p).take (u.length + vxy.length) =
    ((makeString_anbncndn p).take (3 * p)).take (u.length + vxy.length) by
    rw [List.take_take]; congr 1; omega] at hd_pre
  have hd_3p := List.mem_of_mem_take hd_pre
  have htake3p : (makeString_anbncndn p).take (3 * p) =
      List.replicate p .a ++ List.replicate p .b ++ List.replicate p .c := by
    unfold makeString_anbncndn
    conv_lhs => rw [show List.replicate p FourSymbol.a ++ List.replicate p FourSymbol.b ++
        List.replicate p FourSymbol.c ++ List.replicate p FourSymbol.d =
        (List.replicate p FourSymbol.a ++ List.replicate p FourSymbol.b ++
        List.replicate p FourSymbol.c) ++ List.replicate p FourSymbol.d from
      by simp [List.append_assoc]]
    have hlen : (List.replicate p FourSymbol.a ++ List.replicate p FourSymbol.b ++
        List.replicate p FourSymbol.c).length = 3 * p := by
      simp [List.length_append, List.length_replicate]; omega
    rw [← hlen, List.take_left]
  rw [htake3p] at hd_3p
  simp only [List.mem_append, List.mem_replicate] at hd_3p
  obtain (⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩ := hd_3p <;> exact absurd h (by decide)

private theorem not_a_and_d_in_vxy (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(FourSymbol.a ∈ vxy ∧ FourSymbol.d ∈ vxy) := by
  intro ⟨ha, hd⟩
  have hu : u.length < p := by
    by_contra h; push Not at h
    exact a_not_in_vxy_of_u_ge_p p u vxy z hw h ha
  exact d_not_in_vxy_of_end_le_3p p u vxy z hw (by omega) hd

private theorem filter_eq_nil_of_not_mem (l : FourString) (s : FourSymbol) (h : s ∉ l) :
    l.filter (· == s) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx heq; exact h (beq_iff_eq.mp heq ▸ hx)

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

private theorem fourSymbol_filter_total (l : FourString) :
    (l.filter (· == .a)).length + (l.filter (· == .b)).length +
    (l.filter (· == .c)).length + (l.filter (· == .d)).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.filter_cons, List.length_cons]
    cases h <;> simp <;> omega

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

-- ============================================================================
-- {aⁿbⁿcⁿ}
-- ============================================================================

/-- Alphabet for {aⁿbⁿcⁿ}. -/
inductive ThreeSymbol where
  | a | b | c
  deriving DecidableEq, Repr

instance : LawfulBEq ThreeSymbol where
  eq_of_beq {x y} h := by cases x <;> cases y <;> first | rfl | exact absurd h (by decide)
  rfl {x} := by cases x <;> decide

/-- The language {aⁿbⁿcⁿ | n ≥ 0}. -/
def isInLanguage_anbnc (w : List ThreeSymbol) : Bool :=
  match w with
  | [] => true
  | _ =>
    let na := w.filter (· == .a) |>.length
    let nb := w.filter (· == .b) |>.length
    let nc := w.filter (· == .c) |>.length
    na == nb && nb == nc &&
    w == List.replicate na .a ++ List.replicate nb .b ++ List.replicate nc .c

/-- Generate aⁿbⁿcⁿ. -/
def makeString_anbnc (n : Nat) : List ThreeSymbol :=
  List.replicate n .a ++ List.replicate n .b ++ List.replicate n .c

#guard isInLanguage_anbnc (makeString_anbnc 3)

/-- The language {aⁿbⁿcⁿ | n ≥ 0} as a mathlib `Language`. -/
def anbnc : Language ThreeSymbol := {w | isInLanguage_anbnc w = true}

private theorem a_not_in_vxy3 (p : Nat) (u vxy z : List ThreeSymbol)
    (hw : makeString_anbnc p = u ++ vxy ++ z) (hu : u.length ≥ p) :
    ThreeSymbol.a ∉ vxy := by
  intro ha
  have hsuffix : vxy ++ z = (makeString_anbnc p).drop u.length := by
    have : u ++ (vxy ++ z) = makeString_anbnc p := by rw [hw, List.append_assoc]
    rw [← this, List.drop_left]
  have hx : ThreeSymbol.a ∈ (makeString_anbnc p).drop u.length :=
    hsuffix ▸ List.mem_append_left z ha
  rw [show makeString_anbnc p =
    List.replicate p ThreeSymbol.a ++ (List.replicate p ThreeSymbol.b ++
    List.replicate p ThreeSymbol.c) by
    simp [makeString_anbnc, List.append_assoc]] at hx
  rw [List.drop_append] at hx
  simp only [List.mem_append, List.drop_replicate, List.mem_replicate,
             List.length_replicate] at hx
  rcases hx with ⟨h, _⟩ | h
  · omega
  · have := List.mem_of_mem_drop h
    simp only [List.mem_append, List.mem_replicate] at this
    obtain ⟨_, h⟩ | ⟨_, h⟩ := this <;> exact absurd h (by decide)

private theorem c_not_in_vxy3 (p : Nat) (u vxy z : List ThreeSymbol)
    (hw : makeString_anbnc p = u ++ vxy ++ z) (hend : u.length + vxy.length ≤ 2 * p) :
    ThreeSymbol.c ∉ vxy := by
  intro hc
  have hpre : u ++ vxy = (makeString_anbnc p).take (u.length + vxy.length) := by
    have heq : (u ++ vxy) ++ z = makeString_anbnc p := by rw [hw, List.append_assoc]
    rw [show u.length + vxy.length = (u ++ vxy).length from by simp]
    rw [← heq, List.take_left]
  have hc_pre : ThreeSymbol.c ∈ u ++ vxy := List.mem_append_right _ hc
  rw [hpre] at hc_pre
  rw [show (makeString_anbnc p).take (u.length + vxy.length) =
    ((makeString_anbnc p).take (2 * p)).take (u.length + vxy.length) by
    rw [List.take_take]; congr 1; omega] at hc_pre
  have hc_2p := List.mem_of_mem_take hc_pre
  have htake2p : (makeString_anbnc p).take (2 * p) =
      List.replicate p .a ++ List.replicate p .b := by
    unfold makeString_anbnc
    conv_lhs => rw [show List.replicate p ThreeSymbol.a ++ List.replicate p ThreeSymbol.b ++
        List.replicate p ThreeSymbol.c =
        (List.replicate p ThreeSymbol.a ++ List.replicate p ThreeSymbol.b) ++
        List.replicate p ThreeSymbol.c from by simp [List.append_assoc]]
    have hlen : (List.replicate p ThreeSymbol.a ++
        List.replicate p ThreeSymbol.b).length = 2 * p := by
      simp [List.length_append, List.length_replicate]; omega
    rw [← hlen, List.take_left]
  rw [htake2p] at hc_2p
  simp only [List.mem_append, List.mem_replicate] at hc_2p
  obtain ⟨_, h⟩ | ⟨_, h⟩ := hc_2p <;> exact absurd h (by decide)

private theorem not_a_and_c_in_vxy3 (p : Nat) (u vxy z : List ThreeSymbol)
    (hw : makeString_anbnc p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(ThreeSymbol.a ∈ vxy ∧ ThreeSymbol.c ∈ vxy) := by
  intro ⟨ha, hc⟩
  have hu : u.length < p := by
    by_contra h; push Not at h; exact a_not_in_vxy3 p u vxy z hw h ha
  exact c_not_in_vxy3 p u vxy z hw (by omega) hc

private theorem filter_count3 (n : Nat) (s : ThreeSymbol) :
    ((makeString_anbnc n).filter (· == s)).length = n := by
  simp only [makeString_anbnc, List.filter_append, List.filter_replicate, List.length_append]
  cases s <;> simp (config := { decide := true })

private theorem filter_eq_nil3 (l : List ThreeSymbol) (s : ThreeSymbol) (h : s ∉ l) :
    l.filter (· == s) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx heq; exact h (beq_iff_eq.mp heq ▸ hx)

private theorem counts_eq3 (w : List ThreeSymbol) (hne : w ≠ [])
    (hin : isInLanguage_anbnc w = true) :
    (w.filter (· == .a)).length = (w.filter (· == .b)).length ∧
    (w.filter (· == .b)).length = (w.filter (· == .c)).length := by
  unfold isInLanguage_anbnc at hin
  match w, hne with
  | _ :: _, _ =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hin
    exact ⟨hin.1.1, hin.1.2⟩

private theorem threeSymbol_filter_total (l : List ThreeSymbol) :
    (l.filter (· == .a)).length + (l.filter (· == .b)).length +
    (l.filter (· == .c)).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.filter_cons, List.length_cons]
    cases h <;> simp <;> omega

private theorem isInLang3_nonempty (w : List ThreeSymbol) (h : w ≠ []) :
    isInLanguage_anbnc w = (
      let na := (w.filter (· == .a)).length
      let nb := (w.filter (· == .b)).length
      let nc := (w.filter (· == .c)).length
      na == nb && nb == nc &&
      w == List.replicate na .a ++ List.replicate nb .b ++ List.replicate nc .c) := by
  unfold isInLanguage_anbnc; match w, h with | _ :: _, _ => rfl

private theorem makeString_anbnc_in_language (n : Nat) :
    makeString_anbnc n ∈ anbnc := by
  show isInLanguage_anbnc (makeString_anbnc n) = true
  cases n with
  | zero => rfl
  | succ k =>
    have hne : makeString_anbnc (k + 1) ≠ [] := by
      simp [makeString_anbnc, List.replicate_succ]
    rw [isInLang3_nonempty _ hne]
    simp only [filter_count3, beq_self_eq_true, Bool.and_self, Bool.true_and]
    change (makeString_anbnc (k + 1) == makeString_anbnc (k + 1)) = true
    exact beq_self_eq_true _

set_option maxHeartbeats 800000 in
/-- {aⁿbⁿcⁿ} does NOT have the CFL pumping property. -/
theorem anbnc_not_pumpable :
    ¬ HasCFLPumpingProperty anbnc := by
  intro ⟨p, hp, hpump⟩
  have hw_in := makeString_anbnc_in_language p
  have hw_len : (makeString_anbnc p).length ≥ p := by
    simp only [makeString_anbnc, List.length_append, List.length_replicate]; omega
  obtain ⟨u, v, x, y, z, hw, hvxy, hvy, hall⟩ := hpump _ hw_in hw_len
  have hw' : makeString_anbnc p = u ++ (v ++ x ++ y) ++ z := by
    have : _ = u ++ v ++ x ++ y ++ z := hw
    simp only [List.append_assoc] at this ⊢; exact this
  have hcontig := not_a_and_c_in_vxy3 p u (v ++ x ++ y) z hw' hvxy
  suffices ∃ i, (u ++ List.flatten (List.replicate i v) ++ x ++
      List.flatten (List.replicate i y) ++ z) ∉ anbnc by
    obtain ⟨i, hbreak⟩ := this
    exact hbreak (hall i)
  use 0
  simp only [List.replicate_zero, List.flatten_nil, List.append_nil]
  show ¬ (isInLanguage_anbnc (u ++ x ++ z) = true)
  intro hin
  have huxz_ne : u ++ x ++ z ≠ [] := by
    intro h
    have huxz0 : u.length + x.length + z.length = 0 := by
      have := congr_arg List.length h; simp only [List.length_append, List.length_nil] at this; omega
    have hlen : u.length + v.length + x.length + y.length + z.length = 3 * p := by
      have := congr_arg List.length hw'.symm
      simp only [makeString_anbnc, List.length_append, List.length_replicate] at this; omega
    have : v.length + x.length + y.length ≤ p := by
      simp only [List.length_append] at hvxy; omega
    omega
  obtain ⟨hab, hbc⟩ := counts_eq3 _ huxz_ne hin
  have hrel : ∀ s : ThreeSymbol,
      ((u ++ x ++ z).filter (· == s)).length +
      (v.filter (· == s)).length + (y.filter (· == s)).length = p := by
    intro s
    have h1 := filter_count3 p s; rw [hw'] at h1
    simp only [List.filter_append, List.length_append] at h1 ⊢; omega
  have h3k : 3 * ((u ++ x ++ z).filter (· == .a)).length = (u ++ x ++ z).length := by
    have := threeSymbol_filter_total (u ++ x ++ z); omega
  have hlen_uxz : (u ++ x ++ z).length + (v.length + y.length) = 3 * p := by
    have hlen : (makeString_anbnc p).length = 3 * p := by
      simp [makeString_anbnc, List.length_append, List.length_replicate]; omega
    rw [hw'] at hlen; simp only [List.length_append] at hlen ⊢; omega
  have hk_eq_p : ((u ++ x ++ z).filter (· == .a)).length = p := by
    by_cases ha : ThreeSymbol.a ∈ (v ++ x ++ y)
    · have hc : ThreeSymbol.c ∉ (v ++ x ++ y) := fun hc => hcontig ⟨ha, hc⟩
      have hcv : ThreeSymbol.c ∉ v :=
        fun h => hc (List.mem_append_left _ (List.mem_append_left _ h))
      have hcy : ThreeSymbol.c ∉ y :=
        fun h => hc (List.mem_append_right _ h)
      have hrc := hrel .c
      rw [filter_eq_nil3 v .c hcv, filter_eq_nil3 y .c hcy] at hrc
      simp only [List.length_nil, Nat.add_zero] at hrc; omega
    · have hav : ThreeSymbol.a ∉ v :=
        fun h => ha (List.mem_append_left _ (List.mem_append_left _ h))
      have hay : ThreeSymbol.a ∉ y :=
        fun h => ha (List.mem_append_right _ h)
      have hra := hrel .a
      rw [filter_eq_nil3 v .a hav, filter_eq_nil3 y .a hay] at hra
      simp only [List.length_nil, Nat.add_zero] at hra; exact hra
  omega

-- ============================================================================
-- String Homomorphisms
-- ============================================================================

/-- A string homomorphism: maps each source symbol to a target string. -/
abbrev StringHom (α β : Type) := α → List β

/-- Apply a string homomorphism to a string. -/
def StringHom.applyTo {α β : Type} (h : StringHom α β) : List α → List β
  | [] => []
  | a :: w => h a ++ applyTo h w

/-- A letter-to-letter homomorphism. -/
def StringHom.letterMap {α β : Type} (f : α → β) : StringHom α β :=
  fun a => [f a]

theorem StringHom.applyTo_letterMap {α β : Type} (f : α → β) (w : List α) :
    (StringHom.letterMap f).applyTo w = w.map f := by
  induction w with
  | nil => rfl
  | cons _ _ ih => simp [applyTo, letterMap, ih]

/-- Apply a general string homomorphism to a mathlib `Language`. -/
def Language.stringMap {α β : Type} (h : StringHom α β) (L : Language α) : Language β :=
  {w | ∃ v ∈ L, StringHom.applyTo h v = w}

-- ============================================================================
-- Non-Context-Freeness Results
-- ============================================================================

/-- {aⁿbⁿcⁿdⁿ} is not context-free. -/
theorem anbncndn_not_contextFree : ¬ Language.IsContextFree anbncndn :=
  not_isContextFree_of_not_pumpable anbncndn anbncndn_not_pumpable

/-- {aⁿbⁿcⁿ} is not context-free. -/
theorem anbnc_not_contextFree : ¬ Language.IsContextFree anbnc :=
  not_isContextFree_of_not_pumpable anbnc anbnc_not_pumpable
