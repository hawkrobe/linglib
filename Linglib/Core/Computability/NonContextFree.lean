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

String-homomorphism and regular-intersection closure properties live in
`Linglib.Core.Computability.CFLClosure` (re-using `Core.StringHom`).
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

/--.b cannot appear past position 2p of aᵖbᵖcᵖdᵖ. -/
private theorem b_not_in_vxy_of_u_ge_2p (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hu : u.length ≥ 2 * p) :
    FourSymbol.b ∉ vxy := by
  intro hb
  have hsuffix : vxy ++ z = (makeString_anbncndn p).drop u.length := by
    have : u ++ (vxy ++ z) = makeString_anbncndn p := by rw [hw, List.append_assoc]
    rw [← this, List.drop_left]
  have hx : FourSymbol.b ∈ (makeString_anbncndn p).drop u.length :=
    hsuffix ▸ List.mem_append_left z hb
  -- Decompose witness as (a-block ++ b-block) ++ (c-block ++ d-block)
  rw [show makeString_anbncndn p =
    (List.replicate p FourSymbol.a ++ List.replicate p FourSymbol.b) ++
    (List.replicate p FourSymbol.c ++ List.replicate p FourSymbol.d) by
    simp [makeString_anbncndn, List.append_assoc]] at hx
  rw [List.drop_append] at hx
  simp only [List.mem_append] at hx
  rcases hx with h | h
  · -- b in drop u.length (a-block ++ b-block) — but u.length ≥ 2p = length, so drop is []
    have hlen : (List.replicate p FourSymbol.a ++ List.replicate p FourSymbol.b).length ≤ u.length := by
      simp [List.length_append, List.length_replicate]; omega
    rw [List.drop_eq_nil_of_le hlen] at h
    exact List.not_mem_nil h
  · -- b in drop _ (c-block ++ d-block) — impossible since b ∉ c-block ++ d-block
    have := List.mem_of_mem_drop h
    simp only [List.mem_append, List.mem_replicate] at this
    obtain ⟨_, h⟩ | ⟨_, h⟩ := this <;> exact absurd h (by decide)

/--.c cannot appear in the prefix up to position 2p of aᵖbᵖcᵖdᵖ. -/
private theorem c_not_in_vxy_of_end_le_2p (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hend : u.length + vxy.length ≤ 2 * p) :
    FourSymbol.c ∉ vxy := by
  intro hc
  have hpre : u ++ vxy = (makeString_anbncndn p).take (u.length + vxy.length) := by
    have heq : (u ++ vxy) ++ z = makeString_anbncndn p := by rw [hw, List.append_assoc]
    rw [show u.length + vxy.length = (u ++ vxy).length from by simp]
    rw [← heq, List.take_left]
  have hc_pre : FourSymbol.c ∈ u ++ vxy := List.mem_append_right _ hc
  rw [hpre] at hc_pre
  rw [show (makeString_anbncndn p).take (u.length + vxy.length) =
    ((makeString_anbncndn p).take (2 * p)).take (u.length + vxy.length) by
    rw [List.take_take]; congr 1; omega] at hc_pre
  have hc_2p := List.mem_of_mem_take hc_pre
  have htake2p : (makeString_anbncndn p).take (2 * p) =
      List.replicate p .a ++ List.replicate p .b := by
    unfold makeString_anbncndn
    conv_lhs => rw [show List.replicate p FourSymbol.a ++ List.replicate p FourSymbol.b ++
        List.replicate p FourSymbol.c ++ List.replicate p FourSymbol.d =
        (List.replicate p FourSymbol.a ++ List.replicate p FourSymbol.b) ++
        (List.replicate p FourSymbol.c ++ List.replicate p FourSymbol.d) from
      by simp [List.append_assoc]]
    have hlen : (List.replicate p FourSymbol.a ++ List.replicate p FourSymbol.b).length = 2 * p := by
      simp [List.length_append, List.length_replicate]; omega
    rw [← hlen, List.take_left]
  rw [htake2p] at hc_2p
  simp only [List.mem_append, List.mem_replicate] at hc_2p
  obtain ⟨_, h⟩ | ⟨_, h⟩ := hc_2p <;> exact absurd h (by decide)

/-- Adjacency: a and c are 2 blocks apart, so vxy of length ≤ p can't contain both. -/
private theorem not_a_and_c_in_vxy (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(FourSymbol.a ∈ vxy ∧ FourSymbol.c ∈ vxy) := by
  intro ⟨ha, hc⟩
  have hu : u.length < p := by
    by_contra h; push Not at h
    exact a_not_in_vxy_of_u_ge_p p u vxy z hw h ha
  exact c_not_in_vxy_of_end_le_2p p u vxy z hw (by omega) hc

/-- Adjacency: b and d are 2 blocks apart. -/
private theorem not_b_and_d_in_vxy (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(FourSymbol.b ∈ vxy ∧ FourSymbol.d ∈ vxy) := by
  intro ⟨hb, hd⟩
  have hu : u.length < 2 * p := by
    by_contra h; push Not at h
    exact b_not_in_vxy_of_u_ge_2p p u vxy z hw h hb
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
-- {aᵐbⁿcᵐdⁿ}: the two-parameter relaxation of {aⁿbⁿcⁿdⁿ}
-- ============================================================================

/-- The language `{aᵐbⁿcᵐdⁿ | m, n ≥ 0}`: case-sorted strings with `a-count = c-count`
    and `b-count = d-count` (the diagonal pairs). Strict superset of `anbncndn`,
    used by @cite{shieber-1985}'s argument that Swiss German is not weakly
    context-free.

    Membership requires the case-sorted shape AND the two diagonal-count
    equalities. The pumping witness is the same diagonal `makeString_anbncndn p`
    (which lies in `ambncmdn`), but pumping breaks one of the diagonal
    equalities rather than all four. -/
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
#guard !isInLanguage_ambncmdn [.a, .a, .b, .c, .c, .d, .d]  -- na=2≠nd=2 ok, but nb=1≠nd=2

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
    -- Compute filter counts on the asymmetric witness
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
    `makeString_ambncmdn m n` for some `m, n`. The converse to
    `makeString_ambncmdn_in_language`. -/
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
    · -- a ∈ vxy ⇒ c ∉ vxy ⇒ c ∉ v, c ∉ y ⇒ count(vy, c) = 0 ⇒ count(vy, a) = 0
      have hc_notin : FourSymbol.c ∉ v ++ x ++ y := fun hc => hac ⟨ha, hc⟩
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
      simp
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
      simp
  have hc_vy_zero : (v.filter (· == .c)).length + (y.filter (· == .c)).length = 0 := by
    omega
  have hd_vy_zero : (v.filter (· == .d)).length + (y.filter (· == .d)).length = 0 := by
    omega
  -- Sum of all four counts in v + in y = |v| + |y|, but each is 0, contradicts |vy| ≥ 1
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
-- Non-Context-Freeness Results
-- ============================================================================

/-- {aⁿbⁿcⁿdⁿ} is not context-free. -/
theorem anbncndn_not_contextFree : ¬ Language.IsContextFree anbncndn :=
  not_isContextFree_of_not_pumpable anbncndn anbncndn_not_pumpable

/-- {aᵐbⁿcᵐdⁿ} is not context-free. The two-parameter relaxation that
    @cite{shieber-1985}'s Swiss German argument actually requires. -/
theorem ambncmdn_not_contextFree : ¬ Language.IsContextFree ambncmdn :=
  not_isContextFree_of_not_pumpable ambncmdn ambncmdn_not_pumpable

/-- {aⁿbⁿcⁿ} is not context-free. -/
theorem anbnc_not_contextFree : ¬ Language.IsContextFree anbnc :=
  not_isContextFree_of_not_pumpable anbnc anbnc_not_pumpable
