import Mathlib.Computability.ContextFreeGrammar

/-!
# Pumping Lemma for Context-Free Languages

The CFL pumping property (`HasCFLPumpingProperty`) is defined over mathlib's
`Language α` (= `Set (List α)`). Two non-context-free witness languages are
constructed:

- `anbncndn : Language FourSymbol` — {aⁿbⁿcⁿdⁿ | n ≥ 0}
- `anbnc : Language ThreeSymbol`   — {aⁿbⁿcⁿ | n ≥ 0}

## Key Results

- `anbncndn_not_pumpable : ¬ HasCFLPumpingProperty anbncndn` — fully proved
- `anbnc_not_pumpable : ¬ HasCFLPumpingProperty anbnc` — fully proved
- `cfl_pumping_lemma : L.IsContextFree → HasCFLPumpingProperty L` —
  proof structure complete, pending three lemmas (see below)
- `anbncndn_not_contextFree : ¬ Language.IsContextFree anbncndn`
- `anbnc_not_contextFree : ¬ Language.IsContextFree anbnc`

## CFL Pumping Lemma Proof Structure

The proof follows the standard textbook argument via derivation trees:

1. **`exists_valid_tree`** ✓: every word in a CFL has a valid `CFGTree`
   rooted at the start symbol. Proved via `forest_exists` (induction on
   `Relation.ReflTransGen` using `head_induction_on`, with `Derives.append_split`
   to split derivations at production sites).
2. **`yield_length_le_of_height`** ✓: a valid tree of height h has
   ≤ b^h leaves. Proved by well-founded recursion on tree size.
3. **`pumping_from_tall_tree`** (sorry): a tall tree (height > #rules) has a
   repeated nonterminal, yielding the uvxyz decomposition. Requires
   tree-path infrastructure + pigeonhole + subtree replacement.

The main theorem `cfl_pumping_lemma` combines these three lemmas; its proof
body is complete modulo the remaining lemma.

## Consumers

- `Theories.Syntax.CCG.Formal.GenerativeCapacity` — proving CCG > CFG
- `Phenomena.WordOrder.Studies.Shieber1985` — proving Swiss German ∉ CFL
- `Phenomena.WordOrder.Studies.PullumGazdar1982` — CF vs non-CF distinction
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

/-- The CFL pumping property for a language.

    Every context-free language satisfies this property — the pumping lemma
    for CFLs. Showing a language lacks it proves it is not context-free. -/
def HasCFLPumpingProperty {α : Type} (L : Language α) : Prop :=
    ∃ p : Nat, p > 0 ∧
    ∀ w : List α, w ∈ L → w.length ≥ p →
      ∃ u v x y z : List α,
        w = u ++ v ++ x ++ y ++ z ∧
        (v ++ x ++ y).length ≤ p ∧
        (v.length + y.length) ≥ 1 ∧
        ∀ i : Nat, (u ++ List.flatten (List.replicate i v) ++ x ++
                    List.flatten (List.replicate i y) ++ z) ∈ L

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

/-- A contiguous substring of aᵖbᵖcᵖdᵖ of length ≤ p cannot contain both.a and.d,
    since they are separated by 2p positions. -/
private theorem not_a_and_d_in_vxy (p : Nat) (u vxy z : FourString)
    (hw : makeString_anbncndn p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(FourSymbol.a ∈ vxy ∧ FourSymbol.d ∈ vxy) := by
  intro ⟨ha, hd⟩
  have hu : u.length < p := by
    by_contra h; push Not at h
    exact a_not_in_vxy_of_u_ge_p p u vxy z hw h ha
  exact d_not_in_vxy_of_end_le_3p p u vxy z hw (by omega) hd

/-- If s ∉ l, then filtering for s yields []. -/
private theorem filter_eq_nil_of_not_mem (l : FourString) (s : FourSymbol) (h : s ∉ l) :
    l.filter (· == s) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx heq; exact h (beq_iff_eq.mp heq ▸ hx)

/-- If isInLanguage = true and w ≠ [], all four filter counts are equal. -/
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

/-- Sum of filter counts over all four symbols equals list length. -/
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
/-- Pumping breaks membership in {aⁿbⁿcⁿdⁿ}: for any decomposition of aᵖbᵖcᵖdᵖ
    into uvxyz with |vxy| ≤ p and |vy| ≥ 1, pumping at i=0 breaks membership.

    Key insight: |vxy| ≤ p means vxy can't contain both .a and .d (they're
    separated by 2p positions). Pumping down (i=0) preserves one count at p
    while reducing the total, making counts unequal. -/
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

/-- {aⁿbⁿcⁿdⁿ} does NOT have the CFL pumping property, hence is not context-free.

    Proof: for any pumping constant p, the word aᵖbᵖcᵖdᵖ ∈ L witnesses failure.
    By `pump_breaks_anbncndn`, every valid decomposition can be pumped down (i=0)
    to break membership, contradicting the pumping property's ∀ i guarantee. -/
theorem anbncndn_not_pumpable :
    ¬ HasCFLPumpingProperty anbncndn := by
  intro ⟨p, hp, hpump⟩
  have hw_in := makeString_in_language p
  have hw_len : (makeString_anbncndn p).length ≥ p := by
    simp only [makeString_anbncndn, List.length_append, List.length_replicate]; omega
  obtain ⟨u, v, x, y, z, hw, hvxy, hvy, hall⟩ := hpump _ hw_in hw_len
  obtain ⟨i, hbreak⟩ := pump_breaks_anbncndn p hp u v x y z hw hvxy hvy
  exact hbreak (hall i)

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
/-- {aⁿbⁿcⁿ} does NOT have the CFL pumping property, hence is not context-free.
    Same structure as the four-symbol case: contiguity forces either .a or .c
    absent from vxy, preserving one count at p while the total decreases. -/
theorem anbnc_not_pumpable :
    ¬ HasCFLPumpingProperty anbnc := by
  intro ⟨p, hp, hpump⟩
  have hw_in := makeString_anbnc_in_language p
  have hw_len : (makeString_anbnc p).length ≥ p := by
    simp only [makeString_anbnc, List.length_append, List.length_replicate]; omega
  obtain ⟨u, v, x, y, z, hw, hvxy, hvy, hall⟩ := hpump _ hw_in hw_len
  -- Pump down (i=0) to break membership
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

/-- A string homomorphism: maps each source symbol to a target string.
    Extends to strings by concatenation: h(ε) = ε, h(a·w) = h(a) ++ h(w). -/
abbrev StringHom (α β : Type) := α → List β

/-- Apply a string homomorphism to a string. -/
def StringHom.applyTo {α β : Type} (h : StringHom α β) : List α → List β
  | [] => []
  | a :: w => h a ++ applyTo h w

/-- A letter-to-letter homomorphism: each source symbol maps to exactly one
    target symbol. This is the case used by @cite{shieber-1985}. -/
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
-- Derivation Trees for Context-Free Grammars
-- ============================================================================

/-- A derivation tree for a context-free grammar.
    Leaves hold terminal symbols; internal nodes hold a nonterminal
    and a list of children (matching a production rule's RHS). -/
inductive CFGTree (T N : Type) where
  | leaf (t : T) : CFGTree T N
  | node (nt : N) (children : List (CFGTree T N)) : CFGTree T N

namespace CFGTree

variable {T N : Type}

/-- The root symbol of a subtree. -/
def rootSymbol : CFGTree T N → Symbol T N
  | .leaf t => .terminal t
  | .node nt _ => .nonterminal nt

mutual
/-- The terminal frontier (yield) of a derivation tree, read left to right. -/
def yield : CFGTree T N → List T
  | .leaf t => [t]
  | .node _ children => yieldList children

/-- Concatenate yields of a list of subtrees. -/
def yieldList : List (CFGTree T N) → List T
  | [] => []
  | t :: ts => t.yield ++ yieldList ts
end

mutual
/-- The height: 0 for leaves, 1 + max child height for nodes. -/
def height : CFGTree T N → Nat
  | .leaf _ => 0
  | .node _ children => 1 + heightMax children

/-- Maximum height among a list of subtrees. -/
def heightMax : List (CFGTree T N) → Nat
  | [] => 0
  | t :: ts => max t.height (heightMax ts)
end

/-- A derivation tree is valid for a CFG if every internal node (A, children)
    corresponds to a rule A → [rootSymbol c₁, ..., rootSymbol cₖ], and all
    children are themselves valid. -/
inductive ValidFor (g : ContextFreeGrammar T) : CFGTree T g.NT → Prop where
  | leaf (t : T) : ValidFor g (.leaf t)
  | node (nt : g.NT) (children : List (CFGTree T g.NT))
    (hrule : ⟨nt, children.map rootSymbol⟩ ∈ g.rules)
    (hchildren : ∀ c ∈ children, ValidFor g c) :
    ValidFor g (.node nt children)

end CFGTree

-- ============================================================================
-- CFL Pumping Lemma — Helper Lemmas
-- ============================================================================

private theorem CFGTree.height_le_heightMax {T N : Type}
    {t : CFGTree T N} {ts : List (CFGTree T N)}
    (ht : t ∈ ts) : t.height ≤ CFGTree.heightMax ts := by
  induction ts with
  | nil => simp at ht
  | cons s ss ih =>
    simp only [CFGTree.heightMax]
    rcases List.mem_cons.mp ht with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

private theorem le_foldl_max_init (l : List Nat) (init : Nat) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact le_refl _
  | cons a as ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left init a) (ih _)

private theorem le_foldl_max_of_mem (l : List Nat) (x : Nat) (init : Nat) (hx : x ∈ l) :
    x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_trans (le_max_right init x) (le_foldl_max_init as _)
    · exact ih _ h

-- ============================================================================
-- CFL Pumping Lemma — Grammar Properties
-- ============================================================================

/-- Maximum rule RHS length in a grammar (at least 2).

    We take the max over all rules' output lengths, floored at 2 to ensure
    the branching factor is nontrivial (a tree of branching ≥ 2 and height h
    has at most b^h leaves). -/
noncomputable def ContextFreeGrammar.maxBranch {T : Type}
    (g : ContextFreeGrammar T) : Nat :=
  max 2 (g.rules.val.toList.map (·.output.length) |>.foldl max 0)

/-- The pumping constant for a CFG: b^(k+1) where b = maxBranch ≥ 2
    and k = number of rules (upper bound on distinct nonterminals). -/
noncomputable def ContextFreeGrammar.pumpingConstant {T : Type}
    (g : ContextFreeGrammar T) : Nat :=
  g.maxBranch ^ (g.rules.card + 1)

/-- maxBranch is at least 2. -/
theorem ContextFreeGrammar.maxBranch_ge_two {T : Type}
    (g : ContextFreeGrammar T) : g.maxBranch ≥ 2 := le_max_left _ _

/-- The pumping constant is positive (b ≥ 2 so b^(k+1) ≥ 2). -/
theorem ContextFreeGrammar.pumpingConstant_pos {T : Type}
    (g : ContextFreeGrammar T) : g.pumpingConstant > 0 :=
  Nat.pos_of_ne_zero (by
    unfold pumpingConstant
    exact ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one
      (Nat.one_le_pow _ _ (by have := g.maxBranch_ge_two; omega))))

/-- Any rule's RHS length is at most `maxBranch`. -/
private theorem ContextFreeGrammar.maxBranch_ge_output {T : Type} (g : ContextFreeGrammar T)
    (r : ContextFreeRule T g.NT) (hr : r ∈ g.rules) :
    r.output.length ≤ g.maxBranch := by
  unfold maxBranch
  apply le_trans _ (le_max_right _ _)
  apply le_foldl_max_of_mem
  exact List.mem_map.mpr
    ⟨r, Multiset.mem_toList.mpr (Finset.mem_val.mpr hr), rfl⟩

/-- Sum of children's yields is at most `|children| * b ^ heightMax`. -/
private theorem CFGTree.yieldList_le {T N : Type} (b : Nat) (_hb : b ≥ 2)
    (ts : List (CFGTree T N))
    (hbound : ∀ c ∈ ts, c.yield.length ≤ b ^ c.height) :
    (CFGTree.yieldList ts).length ≤ ts.length * b ^ CFGTree.heightMax ts := by
  induction ts with
  | nil => simp [CFGTree.yieldList, CFGTree.heightMax]
  | cons t rest ih =>
    simp only [CFGTree.yieldList, List.length_append, List.length_cons, CFGTree.heightMax]
    have ht := hbound t (List.mem_cons_self ..)
    have hrest := ih (fun c hc => hbound c (List.mem_cons_of_mem t hc))
    have hle_t : b ^ t.height ≤ b ^ (max t.height (CFGTree.heightMax rest)) :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hle_rest : b ^ (CFGTree.heightMax rest) ≤
        b ^ (max t.height (CFGTree.heightMax rest)) :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    set p := b ^ (max t.height (CFGTree.heightMax rest))
    have h1 : t.yield.length ≤ p := le_trans ht hle_t
    have h2 : (CFGTree.yieldList rest).length ≤ rest.length * p :=
      le_trans hrest (Nat.mul_le_mul_left _ hle_rest)
    have h3 : (rest.length + 1) * p = p + rest.length * p := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    omega

-- ============================================================================
-- Tree Existence — Helper Lemmas
-- ============================================================================

namespace ContextFreeGrammar

variable {T : Type} {g : ContextFreeGrammar T}

/-- A rewriting step at any position: applying a rule's RHS in place. -/
private theorem Rewrites.at_position {r : ContextFreeRule T g.NT}
    (p q : List (Symbol T g.NT)) :
    r.Rewrites (p ++ [Symbol.nonterminal r.input] ++ q) (p ++ r.output ++ q) := by
  induction p with
  | nil =>
    simp only [List.nil_append]
    exact .head q
  | cons x xs ih =>
    have h1 : (x :: xs) ++ [Symbol.nonterminal r.input] ++ q =
              x :: (xs ++ [Symbol.nonterminal r.input] ++ q) := by simp
    have h2 : (x :: xs) ++ r.output ++ q = x :: (xs ++ r.output ++ q) := by simp
    rw [h1, h2]
    exact .cons x ih

set_option maxHeartbeats 400000 in
/-- A `Rewrites` step on a concatenated list happens in one of the two halves. -/
private theorem Rewrites.append_split {r : ContextFreeRule T g.NT}
    {u₁ u₂ v : List (Symbol T g.NT)} (h : r.Rewrites (u₁ ++ u₂) v) :
    (∃ v₁, v = v₁ ++ u₂ ∧ r.Rewrites u₁ v₁) ∨
    (∃ v₂, v = u₁ ++ v₂ ∧ r.Rewrites u₂ v₂) := by
  obtain ⟨p, q, hpq, hv⟩ := h.exists_parts
  rw [List.append_assoc] at hpq
  rcases List.append_eq_append_iff.mp hpq with ⟨e, hp_eq, hu₂⟩ | ⟨e, hu₁, hrest⟩
  · -- nonterminal in u₂
    right
    have hu₂' : u₂ = e ++ [Symbol.nonterminal r.input] ++ q := by
      rw [hu₂]; simp [List.append_assoc]
    refine ⟨e ++ r.output ++ q, ?_, ?_⟩
    · subst hp_eq; rw [hv]; simp [List.append_assoc]
    · rw [hu₂']; exact Rewrites.at_position e q
  · rcases e with _ | ⟨e_head, e_tail⟩
    · -- u₁ = p, nonterminal at start of u₂
      simp at hu₁
      simp only [List.nil_append] at hrest
      right
      refine ⟨r.output ++ q, ?_, ?_⟩
      · subst hu₁; rw [hv]; simp [List.append_assoc]
      · rw [← hrest]
        simp only [List.singleton_append]
        exact .head q
    · -- nonterminal in u₁
      simp only [List.nil_append, List.cons_append] at hrest
      rw [List.cons_eq_cons] at hrest
      obtain ⟨he_head, h_tail⟩ := hrest
      left
      refine ⟨p ++ r.output ++ e_tail, ?_, ?_⟩
      · rw [hv, h_tail]; simp [List.append_assoc]
      · rw [hu₁]
        rw [show p ++ e_head :: e_tail = p ++ [e_head] ++ e_tail by simp]
        rw [he_head.symm]
        exact Rewrites.at_position p e_tail

/-- A `Produces` step on a concatenated list happens in one of the two halves. -/
private theorem Produces.append_split {u₁ u₂ v : List (Symbol T g.NT)}
    (h : g.Produces (u₁ ++ u₂) v) :
    (∃ v₁, v = v₁ ++ u₂ ∧ g.Produces u₁ v₁) ∨
    (∃ v₂, v = u₁ ++ v₂ ∧ g.Produces u₂ v₂) := by
  obtain ⟨r, hr, hrew⟩ := h
  rcases Rewrites.append_split hrew with ⟨v₁, hv, hpr⟩ | ⟨v₂, hv, hpr⟩
  · exact .inl ⟨v₁, hv, r, hr, hpr⟩
  · exact .inr ⟨v₂, hv, r, hr, hpr⟩

/-- A `Derives` chain on a concatenated list decomposes into chains for each half. -/
private theorem Derives.append_split {u₁ u₂ v : List (Symbol T g.NT)}
    (h : g.Derives (u₁ ++ u₂) v) :
    ∃ v₁ v₂, v = v₁ ++ v₂ ∧ g.Derives u₁ v₁ ∧ g.Derives u₂ v₂ := by
  induction h with
  | refl => exact ⟨u₁, u₂, rfl, .refl _, .refl _⟩
  | tail _ h_step ih =>
    obtain ⟨m₁, m₂, hmid, hd₁, hd₂⟩ := ih
    rw [hmid] at h_step
    rcases Produces.append_split h_step with ⟨v₁, hv, hp⟩ | ⟨v₂, hv, hp⟩
    · exact ⟨v₁, m₂, hv, hd₁.trans_produces hp, hd₂⟩
    · exact ⟨m₁, v₂, hv, hd₁, hd₂.trans_produces hp⟩

/-- A terminal symbol can never be rewritten (productions only replace nonterminals). -/
private theorem Derives.of_terminal {t : T} {v : List (Symbol T g.NT)}
    (h : g.Derives [Symbol.terminal t] v) : v = [Symbol.terminal t] := by
  induction h with
  | refl => rfl
  | tail _ h_step ih =>
    rw [ih] at h_step
    obtain ⟨r, _, hrew⟩ := h_step
    obtain ⟨p, q, hpq, _⟩ := hrew.exists_parts
    have hmem : (Symbol.nonterminal r.input : Symbol T g.NT) ∈
        ([Symbol.terminal t] : List _) := by
      rw [hpq]; simp
    simp at hmem

/-- The yield of a list of leaves is the original list of terminals. -/
private theorem yieldList_leaves (w : List T) :
    CFGTree.yieldList (w.map (CFGTree.leaf : T → CFGTree T g.NT)) = w := by
  induction w with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, CFGTree.yieldList, CFGTree.yield, List.singleton_append, ih]

/-- `yieldList` distributes over list concatenation. -/
private theorem yieldList_append {N : Type} (xs ys : List (CFGTree T N)) :
    CFGTree.yieldList (xs ++ ys) = CFGTree.yieldList xs ++ CFGTree.yieldList ys := by
  induction xs with
  | nil => simp [CFGTree.yieldList]
  | cons x xs ih =>
    simp only [List.cons_append, CFGTree.yieldList, ih, List.append_assoc]

set_option maxHeartbeats 800000 in
/-- **Forest existence.** For any sentential form `sf` deriving a terminal string `w`,
    there exists a list of trees whose roots match `sf`, are all valid, and whose
    concatenated yields equal `w`. -/
private theorem forest_exists {sf : List (Symbol T g.NT)} {w : List T}
    (h : g.Derives sf (w.map Symbol.terminal)) :
    ∃ trees : List (CFGTree T g.NT),
      trees.map CFGTree.rootSymbol = sf ∧
      (∀ t ∈ trees, t.ValidFor g) ∧
      CFGTree.yieldList trees = w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨w.map (CFGTree.leaf : T → CFGTree T g.NT), ?_, ?_, ?_⟩
    · simp [List.map_map, Function.comp_def, CFGTree.rootSymbol]
    · intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨_, _, rfl⟩ := ht
      exact .leaf _
    · exact yieldList_leaves w
  | head h_step _ ih =>
    obtain ⟨forest_c, hroot, hvalid, hyield⟩ := ih
    obtain ⟨r, hr, hrew⟩ := h_step
    obtain ⟨p, q, hsf, hc⟩ := hrew.exists_parts
    let pLen := p.length
    let outLen := r.output.length
    let prefix' := forest_c.take pLen
    let middle := (forest_c.drop pLen).take outLen
    let suffix := forest_c.drop (pLen + outLen)
    let new_node : CFGTree T g.NT := .node r.input middle
    let new_forest := prefix' ++ [new_node] ++ suffix
    have hprefix_root : prefix'.map CFGTree.rootSymbol = p := by
      have h1 : (forest_c.take pLen).map CFGTree.rootSymbol =
          (forest_c.map CFGTree.rootSymbol).take pLen := by rw [List.map_take]
      rw [show prefix' = forest_c.take pLen from rfl, h1, hroot, hc]
      simp [pLen]
    have hmiddle_root : middle.map CFGTree.rootSymbol = r.output := by
      have h1 : ((forest_c.drop pLen).take outLen).map CFGTree.rootSymbol =
          ((forest_c.map CFGTree.rootSymbol).drop pLen).take outLen := by
        rw [List.map_take, List.map_drop]
      rw [show middle = (forest_c.drop pLen).take outLen from rfl, h1, hroot, hc]
      simp [pLen, outLen, List.append_assoc]
    have hsuffix_root : suffix.map CFGTree.rootSymbol = q := by
      have h1 : (forest_c.drop (pLen + outLen)).map CFGTree.rootSymbol =
          (forest_c.map CFGTree.rootSymbol).drop (pLen + outLen) := by
        rw [List.map_drop]
      rw [show suffix = forest_c.drop (pLen + outLen) from rfl, h1, hroot, hc]
      simp [pLen, outLen, List.append_assoc]
    refine ⟨new_forest, ?_, ?_, ?_⟩
    · rw [hsf]
      show (prefix' ++ [new_node] ++ suffix).map CFGTree.rootSymbol =
           p ++ [Symbol.nonterminal r.input] ++ q
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [hprefix_root, hsuffix_root]
      show p ++ [new_node.rootSymbol] ++ q = p ++ [Symbol.nonterminal r.input] ++ q
      rfl
    · intro t ht
      simp only [new_forest, List.mem_append, List.mem_singleton] at ht
      rcases ht with (ht | ht) | ht
      · exact hvalid t (List.mem_of_mem_take ht)
      · subst ht
        refine .node r.input middle ?_ ?_
        · rw [hmiddle_root]; exact hr
        · intro c hc
          have : c ∈ forest_c := by
            have := List.mem_of_mem_take hc
            exact List.mem_of_mem_drop this
          exact hvalid c this
      · exact hvalid t (List.mem_of_mem_drop ht)
    · show CFGTree.yieldList new_forest = w
      have h_decomp : forest_c = prefix' ++ middle ++ suffix := by
        show forest_c = forest_c.take pLen ++ (forest_c.drop pLen).take outLen ++
                        forest_c.drop (pLen + outLen)
        conv_lhs => rw [← List.take_append_drop pLen forest_c,
                        ← List.take_append_drop outLen (forest_c.drop pLen),
                        List.drop_drop]
        rw [List.append_assoc]
      have hy_orig : CFGTree.yieldList (prefix' ++ middle ++ suffix) = w := by
        rw [← h_decomp]; exact hyield
      rw [yieldList_append, yieldList_append] at hy_orig
      show CFGTree.yieldList (prefix' ++ [new_node] ++ suffix) = w
      rw [yieldList_append, yieldList_append]
      have h_node_yield : CFGTree.yieldList [new_node] = CFGTree.yieldList middle := by
        show CFGTree.yieldList [new_node] = CFGTree.yieldList middle
        simp [CFGTree.yieldList, CFGTree.yield, new_node]
      rw [h_node_yield]
      exact hy_orig

end ContextFreeGrammar

/-- **Tree existence.** Every word in a CFG's language has a valid derivation
    tree rooted at the start symbol.

    Proof: applies `forest_exists` to the start nonterminal `[g.initial]`,
    which yields a singleton forest containing the desired tree. The
    `forest_exists` lemma generalizes to all sentential forms by induction
    on the derivation, with each `Produces` step "folding" the children of
    the rewritten nonterminal back into a single node tree. -/
theorem exists_valid_tree {T : Type} (g : ContextFreeGrammar T)
    (w : List T) (hw : w ∈ g.language) :
    ∃ t : CFGTree T g.NT,
      t.ValidFor g ∧ t.yield = w ∧ t.rootSymbol = .nonterminal g.initial := by
  have hd : g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := hw
  obtain ⟨trees, hroot, hvalid, hyield⟩ := ContextFreeGrammar.forest_exists hd
  have hlen : trees.length = 1 := by
    have := congr_arg List.length hroot
    simp at this; exact this
  match trees, hlen with
  | [t], _ =>
    refine ⟨t, ?_, ?_, ?_⟩
    · exact hvalid t (List.mem_singleton.mpr rfl)
    · have hy : CFGTree.yieldList [t] = w := hyield
      simp only [CFGTree.yieldList, List.append_nil] at hy
      exact hy
    · have hr : [t].map CFGTree.rootSymbol = [Symbol.nonterminal g.initial] := hroot
      simp at hr; exact hr

set_option maxHeartbeats 400000 in
/-- **Height–yield bound.** A valid derivation tree of height h has at most
    b^h terminal leaves, where b is the max branching factor.

    Proof: well-founded recursion on tree size. A leaf has height 0 and
    1 = b⁰ leaves. A node with children c₁...cₖ (k ≤ b) has
    |yield| = Σᵢ |yield(cᵢ)| ≤ k · b^(max heights) ≤ b · b^(h-1) = b^h. -/
theorem yield_length_le_of_height {T : Type} (g : ContextFreeGrammar T)
    (t : CFGTree T g.NT) (ht : t.ValidFor g) :
    t.yield.length ≤ g.maxBranch ^ t.height := by
  match t, ht with
  | .leaf _, _ => simp [CFGTree.yield, CFGTree.height]
  | .node nt children, .node _ _ hrule hvalid =>
    simp only [CFGTree.yield, CFGTree.height]
    have hchildren_bound : ∀ c ∈ children, c.yield.length ≤ g.maxBranch ^ c.height :=
      fun c hc => yield_length_le_of_height g c (hvalid c hc)
    have hlist := CFGTree.yieldList_le g.maxBranch g.maxBranch_ge_two children hchildren_bound
    have hlen : children.length ≤ g.maxBranch := by
      have heq : children.length = (children.map CFGTree.rootSymbol).length := by simp
      rw [heq]
      show (children.map CFGTree.rootSymbol).length ≤ g.maxBranch
      have : (children.map CFGTree.rootSymbol).length =
          (ContextFreeRule.mk nt (children.map CFGTree.rootSymbol)).output.length := rfl
      rw [this]
      exact g.maxBranch_ge_output ⟨nt, children.map CFGTree.rootSymbol⟩ hrule
    set b := g.maxBranch
    set hm := CFGTree.heightMax children
    have h1 : children.length * b ^ hm ≤ b * b ^ hm := Nat.mul_le_mul_right _ hlen
    have h2 : b * b ^ hm = b ^ (1 + hm) := by
      rw [show 1 + hm = hm + 1 from by omega, Nat.pow_succ']
    omega
termination_by sizeOf t

-- ============================================================================
-- Pumping — Spine Infrastructure
-- ============================================================================

namespace CFGTree

variable {T N : Type}

/-- A spine is a list of subtrees where each next tree is a child of the previous. -/
def IsSpine : List (CFGTree T N) → Prop
  | [] => True
  | [_] => True
  | parent :: child :: rest =>
    (∃ children nt, parent = .node nt children ∧ child ∈ children) ∧
    IsSpine (child :: rest)

/-- A spine's length is bounded by the head's height + 1. -/
private theorem spine_length_le_height_succ (ts : List (CFGTree T N)) (hs : IsSpine ts)
    (h : ts ≠ []) : ts.length ≤ (ts.head h).height + 1 := by
  induction ts with
  | nil => exact absurd rfl h
  | cons t rest ih =>
    cases rest with
    | nil => simp
    | cons child rest' =>
      simp only [List.length_cons, List.head_cons]
      obtain ⟨⟨children, nt, hparent, hchild⟩, hrest⟩ := hs
      have ih' := ih hrest (by simp)
      simp only [List.head_cons] at ih'
      have h1 : child.height ≤ heightMax children := height_le_heightMax hchild
      subst hparent
      simp only [height]
      have hlen : (child :: rest').length = rest'.length + 1 := by simp
      have : (child :: rest').length ≤ child.height + 1 := ih'
      omega

/-- Among a nonempty list of trees, there is one with maximum height. -/
private theorem exists_max_height (c : CFGTree T N) (cs : List (CFGTree T N)) :
    ∃ c_max ∈ (c :: cs : List (CFGTree T N)),
      ∀ c' ∈ (c :: cs : List (CFGTree T N)), c'.height ≤ c_max.height := by
  induction cs generalizing c with
  | nil =>
    refine ⟨c, List.mem_singleton.mpr rfl, ?_⟩
    intro c' hc'
    rw [List.mem_singleton.mp hc']
  | cons d ds ih =>
    obtain ⟨m, hm_mem, hm_max⟩ := ih c
    by_cases hgt : d.height > m.height
    · refine ⟨d, by simp, ?_⟩
      intro c' hc'
      simp only [List.mem_cons] at hc'
      rcases hc' with hcc | hcd | hcds
      · subst hcc
        have := hm_max c' (List.mem_cons_self ..)
        omega
      · subst hcd; exact le_refl _
      · have := hm_max c' (by simp [hcds]); omega
    · refine ⟨m, ?_, ?_⟩
      · simp only [List.mem_cons] at hm_mem ⊢
        rcases hm_mem with hmc | hmds
        · left; exact hmc
        · right; right; exact hmds
      · intro c' hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with hcc | hcd | hcds
        · subst hcc; exact hm_max c' (List.mem_cons_self ..)
        · subst hcd; push Not at hgt; exact hgt
        · exact hm_max c' (by simp [hcds])

end CFGTree

/-- **Pumping decomposition.** If a valid derivation tree is taller than the
    number of rules, then the yield decomposes as u·v·x·y·z satisfying the
    CFL pumping conditions, and all pumped strings remain in the language.

    Proof outline (still TODO — requires substantial tree-surgery infrastructure):

    1. **Spine extraction**: Use `exists_max_height` recursively to build a
       spine `[t = s₀, s₁, ..., s_h]` of length h + 1 = t.height + 1, where each
       sᵢ₊₁ is a child of sᵢ. Spine is then > g.rules.card + 1 long.

    2. **Pigeonhole on nonterminals**: Internal nodes of the spine (excluding
       leaf) carry nonterminal labels. With > g.rules.card such labels, two
       sᵢ, sⱼ (i < j) must share the same root nonterminal A. Pick the LATEST
       such pair to ensure sᵢ.height ≤ g.rules.card + 1, hence |yield(sᵢ)| ≤
       b^(g.rules.card + 1) = g.pumpingConstant.

    3. **Yield decomposition**: With sᵢ contained in t (at some path P) and
       sⱼ contained in sᵢ (at some path Q within sᵢ):
       - u = yield of t before P
       - v = yield of sᵢ before Q (within sᵢ)
       - x = yield of sⱼ
       - y = yield of sᵢ after Q (within sᵢ)
       - z = yield of t after P
       So t.yield = u ++ v ++ x ++ y ++ z and sᵢ.yield = v ++ x ++ y.
       |vxy| = |sᵢ.yield| ≤ g.pumpingConstant by step 2.

    4. **|vy| ≥ 1**: Since sᵢ ≠ sⱼ (distinct spine positions) and sⱼ is a
       PROPER subtree of sᵢ, sᵢ.yield is strictly longer than sⱼ.yield.

    5. **Pumping**: Define a "tree replacement" operation. Replace sⱼ in sᵢ
       with sᵢ itself (gives 2 v/y copies). Iterate i times, then graft into t
       at position P. Each replacement preserves validity (same root nonterminal A). -/
theorem pumping_from_tall_tree {T : Type} (g : ContextFreeGrammar T)
    (t : CFGTree T g.NT) (ht : t.ValidFor g)
    (hroot : t.rootSymbol = .nonterminal g.initial)
    (htall : t.height > g.rules.card) :
    ∃ u v x y z : List T,
      t.yield = u ++ v ++ x ++ y ++ z ∧
      (v ++ x ++ y).length ≤ g.pumpingConstant ∧
      (v.length + y.length) ≥ 1 ∧
      ∀ i : Nat, (u ++ List.flatten (List.replicate i v) ++ x ++
                  List.flatten (List.replicate i y) ++ z) ∈ g.language := by
  sorry

/-- **The CFL pumping lemma.** Every context-free language satisfies
    `HasCFLPumpingProperty`.

    Proof: given a CFG g generating L, set p = g.pumpingConstant.
    For any w ∈ L with |w| ≥ p:
    1. `exists_valid_tree`: w has a valid derivation tree t.
    2. `yield_length_le_of_height` (contrapositive): |w| ≥ p = b^(k+1)
       forces t.height > k = g.rules.card.
    3. `pumping_from_tall_tree`: the tall tree yields the decomposition. -/
theorem cfl_pumping_lemma {T : Type} (L : Language T)
    (hcf : L.IsContextFree) : HasCFLPumpingProperty L := by
  obtain ⟨g, rfl⟩ := hcf
  refine ⟨g.pumpingConstant, g.pumpingConstant_pos, ?_⟩
  intro w hw hlen
  obtain ⟨t, hvalid, hyield, hroot⟩ := exists_valid_tree g w hw
  have htall : t.height > g.rules.card := by
    by_contra hle
    simp only [not_lt] at hle
    have hbound := yield_length_le_of_height g t hvalid
    rw [hyield] at hbound
    unfold ContextFreeGrammar.pumpingConstant at hlen
    have h1 : g.maxBranch ^ t.height ≤ g.maxBranch ^ g.rules.card :=
      Nat.pow_le_pow_right (by have := g.maxBranch_ge_two; omega) hle
    have h2 : g.maxBranch ^ g.rules.card < g.maxBranch ^ (g.rules.card + 1) :=
      Nat.pow_lt_pow_right (by have := g.maxBranch_ge_two; omega) (by omega)
    -- hbound : w.length ≤ g.maxBranch ^ t.height
    -- h1 : ... ≤ g.maxBranch ^ g.rules.card
    -- h2 : ... < g.maxBranch ^ (g.rules.card + 1)
    -- hlen : w.length ≥ g.maxBranch ^ (g.rules.card + 1)
    omega
  obtain ⟨u, v, x, y, z, hdecomp, hvxy, hvy, hpump⟩ :=
    pumping_from_tall_tree g t hvalid hroot htall
  exact ⟨u, v, x, y, z, hyield ▸ hdecomp, hvxy, hvy, hpump⟩

/-- Contrapositive of the CFL pumping lemma: if a language lacks the pumping
    property, it is not context-free. -/
theorem not_isContextFree_of_not_pumpable {T : Type} (L : Language T)
    (h : ¬ HasCFLPumpingProperty L) : ¬ L.IsContextFree :=
  fun hcf => h (cfl_pumping_lemma L hcf)

-- ============================================================================
-- Non-Context-Freeness Results
-- ============================================================================

/-- {aⁿbⁿcⁿdⁿ} is not context-free.

    Proof via `not_isContextFree_of_not_pumpable`: the pumping failure is
    fully verified in `anbncndn_not_pumpable`; the connection to
    `Language.IsContextFree` goes through the CFL pumping lemma (sorry). -/
theorem anbncndn_not_contextFree : ¬ Language.IsContextFree anbncndn :=
  not_isContextFree_of_not_pumpable anbncndn anbncndn_not_pumpable

/-- {aⁿbⁿcⁿ} is not context-free. -/
theorem anbnc_not_contextFree : ¬ Language.IsContextFree anbnc :=
  not_isContextFree_of_not_pumpable anbnc anbnc_not_pumpable

