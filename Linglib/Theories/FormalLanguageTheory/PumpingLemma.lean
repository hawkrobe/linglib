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
- `cfl_pumping_lemma : L.IsContextFree → HasCFLPumpingProperty L` — fully proved
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
3. **`pumping_from_tall_tree`** ✓: a tall tree (height > #rules) has a
   repeated nonterminal, yielding the uvxyz decomposition. Proved via
   pigeonhole on root-to-leaf paths, subtree replacement, and
   `validFor_derives` (soundness of valid trees).

The main theorem `cfl_pumping_lemma` combines these three lemmas.

## Consumers

- `Theories.Syntax.CCG.Formal.GenerativeCapacity` — proving CCG > CFG
- `Shieber1985` — proving Swiss German ∉ CFL
- `PullumGazdar1982` — CF vs non-CF distinction
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
-- Pumping Infrastructure: Position-based Subtree Access
-- ============================================================================

namespace CFGTree

variable {T N : Type}

/-- A position in a tree: list of child indices to follow from the root. -/
abbrev Pos := List Nat

/-- Subtree at a given position. Returns `none` if the path is invalid. -/
def subtreeAt? : CFGTree T N → Pos → Option (CFGTree T N)
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .node _ children, i :: rest =>
    children[i]?.bind (·.subtreeAt? rest)

/-- Replace the subtree at a given position. If the path is invalid, returns the
    original tree unchanged. -/
def replaceAt : CFGTree T N → Pos → CFGTree T N → CFGTree T N
  | _, [], new => new
  | .leaf t, _ :: _, _ => .leaf t
  | .node nt children, i :: rest, new =>
    if h : i < children.length then
      .node nt (children.set i (children[i].replaceAt rest new))
    else
      .node nt children

/-- Replacing a subtree at a non-root position preserves the root symbol. -/
theorem rootSymbol_replaceAt_cons (t : CFGTree T N) (i : Nat) (rest : Pos)
    (new : CFGTree T N) :
    (t.replaceAt (i :: rest) new).rootSymbol = t.rootSymbol := by
  match t with
  | .leaf _ => rfl
  | .node _ children =>
    by_cases hi : i < children.length
    · simp [replaceAt, hi, rootSymbol]
    · simp [replaceAt, hi, rootSymbol]

/-- Yield decomposition: replacing a subtree at position `p` produces yield
    `pre ++ new.yield ++ post`, where `pre`/`post` are the surrounding context. -/
theorem yield_replaceAt_decomp (t : CFGTree T N) (p : Pos) (sub : CFGTree T N)
    (h : t.subtreeAt? p = some sub) :
    ∃ pre post : List T,
      t.yield = pre ++ sub.yield ++ post ∧
      ∀ new : CFGTree T N, (t.replaceAt p new).yield = pre ++ new.yield ++ post := by
  induction p generalizing t with
  | nil =>
    simp [subtreeAt?] at h
    subst h
    refine ⟨[], [], ?_, ?_⟩
    · simp
    · intro new; simp [replaceAt]
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?] at h
    | .node nt children =>
      simp only [subtreeAt?] at h
      rcases hi : children[i]? with _ | child
      · simp [hi] at h
      · simp [hi] at h
        obtain ⟨pre_inner, post_inner, hyield_inner, hreplace_inner⟩ := ih child h
        have hi_lt : i < children.length := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.1
        have hget : children[i] = child := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.2
        have hsplit_orig : children = children.take i ++ child :: children.drop (i+1) := by
          calc children
              = children.take i ++ children.drop i := (List.take_append_drop _ _).symm
            _ = children.take i ++ children[i] :: children.drop (i+1) := by
                congr 1; exact List.drop_eq_getElem_cons hi_lt
            _ = children.take i ++ child :: children.drop (i+1) := by rw [hget]
        have hsplit_set : ∀ new : CFGTree T N,
            children.set i new = children.take i ++ new :: children.drop (i+1) := by
          intro new
          clear hsplit_orig hget hi h hyield_inner hreplace_inner ih
          induction children generalizing i with
          | nil => simp at hi_lt
          | cons c cs ih_cs =>
            cases i with
            | zero => simp [List.set]
            | succ k =>
              simp only [List.length_cons] at hi_lt
              have hk_lt : k < cs.length := by omega
              simp [List.set, ih_cs k hk_lt]
        refine ⟨yieldList (children.take i) ++ pre_inner,
                post_inner ++ yieldList (children.drop (i+1)), ?_, ?_⟩
        · show yieldList children = _
          conv_lhs => rw [hsplit_orig]
          rw [ContextFreeGrammar.yieldList_append]
          show _ = (yieldList (children.take i) ++ pre_inner) ++ sub.yield ++
              (post_inner ++ yieldList (children.drop (i+1)))
          have hcons_eq : yieldList (child :: children.drop (i+1)) =
              child.yield ++ yieldList (children.drop (i+1)) := by
            simp [yieldList]
          rw [hcons_eq, hyield_inner]
          simp [List.append_assoc]
        · intro new
          have hreplace_unfolds :
              replaceAt (.node nt children) (i :: rest) new =
              .node nt (children.set i (child.replaceAt rest new)) := by
            simp only [replaceAt, hi_lt, ↓reduceDIte, hget]
          rw [hreplace_unfolds]
          show yieldList (children.set i (child.replaceAt rest new)) = _
          rw [hsplit_set, ContextFreeGrammar.yieldList_append]
          show _ = (yieldList (children.take i) ++ pre_inner) ++ new.yield ++
              (post_inner ++ yieldList (children.drop (i+1)))
          have hcons_eq2 : yieldList (child.replaceAt rest new :: children.drop (i+1)) =
              (child.replaceAt rest new).yield ++ yieldList (children.drop (i+1)) := by
            simp [yieldList]
          rw [hcons_eq2, hreplace_inner new]
          simp [List.append_assoc]

/-- Replacing a subtree of the same root symbol preserves validity. -/
theorem validFor_replaceAt {g : ContextFreeGrammar T}
    (t : CFGTree T g.NT) (p : Pos) (sub new : CFGTree T g.NT)
    (h : t.subtreeAt? p = some sub)
    (hroot : new.rootSymbol = sub.rootSymbol)
    (ht_valid : t.ValidFor g) (hnew_valid : new.ValidFor g) :
    (t.replaceAt p new).ValidFor g := by
  induction p generalizing t with
  | nil =>
    simp [subtreeAt?] at h
    subst h
    simp [replaceAt]
    exact hnew_valid
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?] at h
    | .node nt children =>
      simp only [subtreeAt?] at h
      rcases hi : children[i]? with _ | child
      · simp [hi] at h
      · simp [hi] at h
        have hi_lt : i < children.length := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.1
        have hget : children[i] = child := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.2
        have hreplace_unfolds :
            replaceAt (.node nt children) (i :: rest) new =
            .node nt (children.set i (child.replaceAt rest new)) := by
          simp only [replaceAt, hi_lt, ↓reduceDIte, hget]
        rw [hreplace_unfolds]
        match ht_valid with
        | .node _ _ hrule hchildren =>
          have hchild_valid : child.ValidFor g := hchildren child (by
            rw [show child = children[i] from hget.symm]
            exact List.getElem_mem _)
          have hchild_replace_valid : (child.replaceAt rest new).ValidFor g :=
            ih child h hchild_valid
          have hchild_replace_root :
              (child.replaceAt rest new).rootSymbol = child.rootSymbol := by
            cases rest with
            | nil =>
              simp [replaceAt]
              simp [subtreeAt?] at h
              subst h
              exact hroot
            | cons _ _ => exact rootSymbol_replaceAt_cons _ _ _ _
          refine .node nt _ ?_ ?_
          · have hmap_eq : (children.set i (child.replaceAt rest new)).map rootSymbol =
                children.map rootSymbol := by
              rw [List.map_set, hchild_replace_root, ← hget]
              have h_map_lt : i < (children.map rootSymbol).length := by
                rw [List.length_map]; exact hi_lt
              rw [show children[i].rootSymbol = (children.map rootSymbol)[i]'h_map_lt from
                (List.getElem_map _).symm]
              exact List.set_getElem_self _
            rw [hmap_eq]; exact hrule
          · intro c hc_mem
            rcases List.mem_or_eq_of_mem_set hc_mem with hc_orig | hc_eq
            · exact hchildren c hc_orig
            · subst hc_eq; exact hchild_replace_valid

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

-- ============================================================================
-- Spine extraction & pigeonhole
-- ============================================================================

/-- For a max-height list, find the max-height element. -/
private theorem exists_max_height_child (c : CFGTree T N) (cs : List (CFGTree T N)) :
    ∃ c_max ∈ (c :: cs : List (CFGTree T N)),
      c_max.height = heightMax (c :: cs) := by
  induction cs generalizing c with
  | nil => exact ⟨c, by simp, by simp [heightMax]⟩
  | cons d ds ih =>
    obtain ⟨m, hm_mem, hm_eq⟩ := ih c
    have hc_le_m : c.height ≤ m.height := by
      have : heightMax (c :: ds) = max c.height (heightMax ds) := by simp [heightMax]
      rw [this] at hm_eq; omega
    have hds_le_m : heightMax ds ≤ m.height := by
      have : heightMax (c :: ds) = max c.height (heightMax ds) := by simp [heightMax]
      rw [this] at hm_eq; omega
    by_cases hgt : d.height > m.height
    · refine ⟨d, by simp, ?_⟩
      have h1 : heightMax (c :: d :: ds) = max c.height (max d.height (heightMax ds)) := by
        simp [heightMax]
      rw [h1, max_eq_left (le_of_lt (by omega : heightMax ds < d.height)),
          max_eq_right (by omega : c.height ≤ d.height)]
    · push Not at hgt
      refine ⟨m, ?_, ?_⟩
      · simp at hm_mem ⊢
        rcases hm_mem with hmc | hmds
        · left; exact hmc
        · right; right; exact hmds
      · have h1 : heightMax (c :: d :: ds) = max c.height (max d.height (heightMax ds)) := by
          simp [heightMax]
        rw [h1]
        apply le_antisymm
        · have hm_eq' : m.height = max c.height (heightMax ds) := by
            have : heightMax (c :: ds) = max c.height (heightMax ds) := by simp [heightMax]
            rw [this] at hm_eq; exact hm_eq
          rw [hm_eq']
          exact max_le_max (le_refl _) (le_max_right _ _)
        · exact max_le hc_le_m (max_le hgt hds_le_m)

/-- For a tree of height ≥ k+1, there exists a position list of length k
    such that the subtree at that position has height ≥ 1 (i.e., is a `.node`). -/
theorem exists_pos_of_height (t : CFGTree T N) (k : Nat) (h : t.height ≥ k + 1) :
    ∃ p : Pos, p.length = k ∧ ∃ sub, t.subtreeAt? p = some sub ∧ sub.height ≥ 1 := by
  induction k generalizing t with
  | zero => exact ⟨[], rfl, t, rfl, h⟩
  | succ n ih =>
    match t with
    | .leaf _ => simp [height] at h
    | .node nt children =>
      have hmax : heightMax children ≥ n + 1 := by simp [height] at h; omega
      match hcs : children with
      | [] => simp [heightMax] at hmax
      | c :: cs =>
        obtain ⟨c_max, hmem, heq⟩ := exists_max_height_child c cs
        have hc_height : c_max.height ≥ n + 1 := by rw [heq]; exact hmax
        rcases List.mem_iff_get.mp hmem with ⟨⟨k_idx, hk_lt⟩, hk_get⟩
        obtain ⟨p_inner, hp_len, sub, hsub, hsub_h⟩ := ih c_max hc_height
        refine ⟨k_idx :: p_inner, ?_, sub, ?_, hsub_h⟩
        · simp [hp_len]
        · simp only [subtreeAt?]
          rw [show (c :: cs)[k_idx]? = some c_max from
            List.getElem?_eq_some_iff.mpr ⟨hk_lt, hk_get⟩]
          simp [hsub]

/-- Stronger: extract a max-descent path of length k, with subtree at depth i
    having height = t.height - i. -/
theorem exists_pos_max_descent (t : CFGTree T N) (k : Nat) (h : t.height ≥ k + 1) :
    ∃ p : Pos, p.length = k ∧
      ∀ i, i ≤ k → ∃ sub, t.subtreeAt? (p.take i) = some sub ∧ sub.height = t.height - i := by
  induction k generalizing t with
  | zero =>
    refine ⟨[], rfl, ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst this
    refine ⟨t, rfl, ?_⟩
    simp
  | succ n ih =>
    match t with
    | .leaf _ => simp [height] at h
    | .node nt children =>
      have hmax : heightMax children ≥ n + 1 := by simp [height] at h; omega
      match hcs : children with
      | [] => simp [heightMax] at hmax
      | c :: cs =>
        obtain ⟨c_max, hmem, heq⟩ := exists_max_height_child c cs
        have hc_height_ge : c_max.height ≥ n + 1 := by rw [heq]; exact hmax
        rcases List.mem_iff_get.mp hmem with ⟨⟨k_idx, hk_lt⟩, hk_get⟩
        obtain ⟨p_inner, hp_len, hsub_at⟩ := ih c_max hc_height_ge
        refine ⟨k_idx :: p_inner, by simp [hp_len], ?_⟩
        intro i hi
        subst hcs
        cases i with
        | zero =>
          simp only [List.take_zero, subtreeAt?]
          refine ⟨.node nt (c :: cs), rfl, ?_⟩
          simp
        | succ k' =>
          simp only [List.take_succ_cons]
          have hk'_le_n : k' ≤ n := by omega
          obtain ⟨sub, hsub_at_inner, hsub_h⟩ := hsub_at k' hk'_le_n
          refine ⟨sub, ?_, ?_⟩
          · simp only [subtreeAt?]
            rw [show (c :: cs)[k_idx]? = some c_max from
              List.getElem?_eq_some_iff.mpr ⟨hk_lt, hk_get⟩]
            simpa using hsub_at_inner
          · rw [hsub_h, heq]
            simp [height]
            omega

/-- subtreeAt? splits along path concatenation. -/
theorem subtreeAt?_append (t : CFGTree T N) (p1 p2 : Pos) :
    t.subtreeAt? (p1 ++ p2) = (t.subtreeAt? p1).bind (·.subtreeAt? p2) := by
  induction p1 generalizing t with
  | nil => simp [subtreeAt?]
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?]
    | .node _ children =>
      simp only [List.cons_append, subtreeAt?]
      rcases hi : children[i]? with _ | child
      · simp
      · simp [ih]

/-- For a valid tree and a path that descends, each prefix subtree is a `.node`. -/
theorem spine_node_at_prefix (t : CFGTree T N) (p : Pos) (sub : CFGTree T N)
    (hsub : t.subtreeAt? p = some sub) (hsub_h : sub.height ≥ 1)
    (k : Nat) (hk : k < p.length + 1) :
    ∃ nt children, t.subtreeAt? (p.take k) = some (.node nt children) := by
  induction p generalizing t k with
  | nil =>
    simp at hk; subst hk
    simp [subtreeAt?] at hsub
    subst hsub
    match t, hsub_h with
    | .node nt children, _ => exact ⟨nt, children, rfl⟩
  | cons i rest ih =>
    cases k with
    | zero =>
      simp [subtreeAt?]
      match t with
      | .leaf _ => simp [subtreeAt?] at hsub
      | .node nt children => exact ⟨nt, children, rfl⟩
    | succ k' =>
      simp only [List.take_succ_cons]
      simp only [List.length_cons] at hk
      have hk' : k' < rest.length + 1 := by omega
      match t with
      | .leaf _ => simp [subtreeAt?] at hsub
      | .node nt children =>
        simp only [subtreeAt?] at hsub ⊢
        rcases hi : children[i]? with _ | child
        · simp [hi] at hsub
        · simp [hi] at hsub
          exact ih child hsub k' hk'

/-- Validity propagates through subtreeAt?. -/
theorem subtreeAt?_validFor {g : ContextFreeGrammar T} (t : CFGTree T g.NT)
    (ht : t.ValidFor g) (p : Pos) (sub : CFGTree T g.NT)
    (hsub : t.subtreeAt? p = some sub) : sub.ValidFor g := by
  induction p generalizing t with
  | nil => simp [subtreeAt?] at hsub; subst hsub; exact ht
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?] at hsub
    | .node nt children =>
      simp only [subtreeAt?] at hsub
      rcases hi : children[i]? with _ | child
      · simp [hi] at hsub
      · simp [hi] at hsub
        match ht with
        | .node _ _ _ hchildren =>
          have hi_lt : i < children.length := by
            rw [List.getElem?_eq_some_iff] at hi; exact hi.1
          have hchild_in : child ∈ children := by
            rw [show child = children[i] from by
              rw [List.getElem?_eq_some_iff] at hi; exact hi.2.symm]
            exact List.getElem_mem _
          exact ih child (hchildren child hchild_in) hsub

/-- Extract the rule used at a position (option-valued). -/
def ruleAt? {g : ContextFreeGrammar T} (t : CFGTree T g.NT) (p : Pos) :
    Option (ContextFreeRule T g.NT) :=
  match t.subtreeAt? p with
  | some (.node nt children) => some ⟨nt, children.map rootSymbol⟩
  | _ => none

/-- For a valid tree at a `.node` subtree, ruleAt? returns the matching rule in g.rules. -/
theorem ruleAt?_mem_rules {g : ContextFreeGrammar T} (t : CFGTree T g.NT)
    (ht : t.ValidFor g) (p : Pos) (nt : g.NT) (children : List (CFGTree T g.NT))
    (hsub : t.subtreeAt? p = some (.node nt children)) :
    ruleAt? t p = some ⟨nt, children.map rootSymbol⟩ ∧
    ⟨nt, children.map rootSymbol⟩ ∈ g.rules := by
  refine ⟨?_, ?_⟩
  · simp [ruleAt?, hsub]
  · have hsub_valid : (CFGTree.node nt children).ValidFor g :=
      subtreeAt?_validFor t ht p (.node nt children) hsub
    match hsub_valid with
    | .node _ _ hrule _ => exact hrule

-- ============================================================================
-- Tree size measure (for minimality argument)
-- ============================================================================

mutual
def size : CFGTree T N → Nat
  | .leaf _ => 1
  | .node _ children => 1 + sizeList children

def sizeList : List (CFGTree T N) → Nat
  | [] => 0
  | t :: ts => t.size + sizeList ts
end

theorem size_pos (t : CFGTree T N) : t.size ≥ 1 := by
  match t with
  | .leaf _ => simp [size]
  | .node _ _ => simp [size]

theorem sizeList_le_of_mem {t : CFGTree T N} {ts : List (CFGTree T N)} (h : t ∈ ts) :
    t.size ≤ sizeList ts := by
  induction ts with
  | nil => simp at h
  | cons s ss ih =>
    simp only [sizeList]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem size_subtreeAt?_le (t : CFGTree T N) (p : Pos) (sub : CFGTree T N)
    (h : t.subtreeAt? p = some sub) : sub.size ≤ t.size := by
  induction p generalizing t with
  | nil =>
    have hsub : sub = t := (by simpa [subtreeAt?] using h : t = sub).symm
    rw [hsub]
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?] at h
    | .node _ children =>
      simp only [subtreeAt?] at h
      rcases hi : children[i]? with _ | child
      · simp [hi] at h
      · simp [hi] at h
        have hi_lt := (List.getElem?_eq_some_iff.mp hi).1
        have hget := (List.getElem?_eq_some_iff.mp hi).2
        have := ih child h
        have := sizeList_le_of_mem (hget ▸ List.getElem_mem hi_lt)
        simp [size]; omega

theorem size_subtreeAt?_lt_of_cons (t : CFGTree T N) (i : Nat) (rest : Pos)
    (sub : CFGTree T N) (h : t.subtreeAt? (i :: rest) = some sub) :
    sub.size < t.size := by
  match t with
  | .leaf _ => simp [subtreeAt?] at h
  | .node _ children =>
    simp only [subtreeAt?] at h
    rcases hi : children[i]? with _ | child
    · simp [hi] at h
    · simp [hi] at h
      have hi_lt := (List.getElem?_eq_some_iff.mp hi).1
      have hget := (List.getElem?_eq_some_iff.mp hi).2
      have := size_subtreeAt?_le child rest sub h
      have := sizeList_le_of_mem (hget ▸ List.getElem_mem hi_lt)
      simp [size]; omega

theorem sizeList_set (l : List (CFGTree T N)) (i : Nat) (x : CFGTree T N) (hi : i < l.length) :
    sizeList (l.set i x) + l[i].size = sizeList l + x.size := by
  induction l generalizing i with
  | nil => simp at hi
  | cons h t ih =>
    cases i with
    | zero => simp [List.set, sizeList]; omega
    | succ k =>
      simp only [List.length_cons] at hi
      have hk_lt : k < t.length := by omega
      simp only [List.set, sizeList, List.getElem_cons_succ]
      have := ih k hk_lt
      omega

/-- Replacing a subtree with a strictly smaller one gives a strictly smaller tree. -/
theorem size_replaceAt_lt (t : CFGTree T N) (p : Pos) (sub new : CFGTree T N)
    (h : t.subtreeAt? p = some sub) (hlt : new.size < sub.size) :
    (t.replaceAt p new).size < t.size := by
  induction p generalizing t with
  | nil =>
    simp [subtreeAt?] at h; subst h; simp [replaceAt]; exact hlt
  | cons i rest ih =>
    match t with
    | .leaf _ => simp [subtreeAt?] at h
    | .node nt children =>
      simp only [subtreeAt?] at h
      rcases hi : children[i]? with _ | child
      · simp [hi] at h
      · simp [hi] at h
        have hi_lt : i < children.length := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.1
        have hget : children[i] = child := by
          rw [List.getElem?_eq_some_iff] at hi; exact hi.2
        have hreplace_unfolds :
            replaceAt (.node nt children) (i :: rest) new =
            .node nt (children.set i (child.replaceAt rest new)) := by
          simp only [replaceAt, hi_lt, ↓reduceDIte, hget]
        rw [hreplace_unfolds]
        simp only [size]
        have hchild_lt : (child.replaceAt rest new).size < child.size := ih child h
        have hset := sizeList_set children i (child.replaceAt rest new) hi_lt
        rw [hget] at hset
        omega

/-- Existence of minimum-size valid tree with given yield and root. -/
theorem exists_min_size_tree {g : ContextFreeGrammar T} (t : CFGTree T g.NT) (ht : t.ValidFor g) :
    ∃ t_min : CFGTree T g.NT,
      t_min.ValidFor g ∧
      t_min.yield = t.yield ∧
      t_min.rootSymbol = t.rootSymbol ∧
      ∀ t' : CFGTree T g.NT,
        t'.ValidFor g → t'.yield = t.yield →
        t'.rootSymbol = t.rootSymbol →
        t_min.size ≤ t'.size := by
  classical
  let P : Nat → Prop := fun n => ∃ t' : CFGTree T g.NT,
    t'.ValidFor g ∧ t'.yield = t.yield ∧ t'.rootSymbol = t.rootSymbol ∧ t'.size = n
  have hP_ne : ∃ n, P n := ⟨t.size, t, ht, rfl, rfl, rfl⟩
  obtain ⟨t_min, ht_min_v, ht_min_y, ht_min_r, ht_min_s⟩ := Nat.find_spec hP_ne
  refine ⟨t_min, ht_min_v, ht_min_y, ht_min_r, ?_⟩
  intro t' ht'_v ht'_y ht'_r
  have hP_t' : P t'.size := ⟨t', ht'_v, ht'_y, ht'_r, rfl⟩
  have hle : Nat.find hP_ne ≤ t'.size := Nat.find_le hP_t'
  omega

/-- Pigeonhole: along a long-enough valid path, two prefixes have same root nonterminal. -/
theorem exists_repeat_root {g : ContextFreeGrammar T}
    (t : CFGTree T g.NT) (ht : t.ValidFor g)
    (p : Pos) (sub : CFGTree T g.NT)
    (hsub : t.subtreeAt? p = some sub) (hsub_h : sub.height ≥ 1)
    (hlen : p.length ≥ g.rules.card) :
    ∃ i j : Nat, i < j ∧ j ≤ p.length ∧
      ∃ ntᵢ children_i ntⱼ children_j,
        t.subtreeAt? (p.take i) = some (.node ntᵢ children_i) ∧
        t.subtreeAt? (p.take j) = some (.node ntⱼ children_j) ∧
        ntᵢ = ntⱼ := by
  classical
  let f : Nat → ContextFreeRule T g.NT := fun k =>
    (ruleAt? t (p.take k)).getD ⟨g.initial, []⟩
  have hf_in : ∀ k ∈ Finset.range (p.length + 1), f k ∈ g.rules := by
    intro k hk
    simp at hk
    obtain ⟨nt, children, hsub_k⟩ := spine_node_at_prefix t p sub hsub hsub_h k hk
    obtain ⟨hrule_eq, hrule_in⟩ := ruleAt?_mem_rules t ht (p.take k) nt children hsub_k
    show f k ∈ g.rules
    simp only [f, hrule_eq, Option.getD_some]
    exact hrule_in
  have hcard : g.rules.card < (Finset.range (p.length + 1)).card := by
    simp [Finset.card_range]; omega
  obtain ⟨a, ha, b, hb, hne, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hf_in
  simp at ha hb
  rcases Nat.lt_or_ge a b with hab | hab
  · obtain ⟨nt_a, children_a, hsub_a⟩ := spine_node_at_prefix t p sub hsub hsub_h a ha
    obtain ⟨nt_b, children_b, hsub_b⟩ := spine_node_at_prefix t p sub hsub hsub_h b hb
    obtain ⟨hrule_a, _⟩ := ruleAt?_mem_rules t ht (p.take a) nt_a children_a hsub_a
    obtain ⟨hrule_b, _⟩ := ruleAt?_mem_rules t ht (p.take b) nt_b children_b hsub_b
    have h_fa : f a = ⟨nt_a, children_a.map rootSymbol⟩ := by
      simp only [f, hrule_a, Option.getD_some]
    have h_fb : f b = ⟨nt_b, children_b.map rootSymbol⟩ := by
      simp only [f, hrule_b, Option.getD_some]
    have : nt_a = nt_b := by
      have : (⟨nt_a, children_a.map rootSymbol⟩ : ContextFreeRule T g.NT) =
          ⟨nt_b, children_b.map rootSymbol⟩ := by rw [← h_fa, ← h_fb, hfeq]
      exact ContextFreeRule.mk.injEq _ _ _ _ |>.mp this |>.1
    exact ⟨a, b, hab, by omega, nt_a, children_a, nt_b, children_b, hsub_a, hsub_b, this⟩
  · have hba : b < a := lt_of_le_of_ne hab (Ne.symm hne)
    obtain ⟨nt_a, children_a, hsub_a⟩ := spine_node_at_prefix t p sub hsub hsub_h a ha
    obtain ⟨nt_b, children_b, hsub_b⟩ := spine_node_at_prefix t p sub hsub hsub_h b hb
    obtain ⟨hrule_a, _⟩ := ruleAt?_mem_rules t ht (p.take a) nt_a children_a hsub_a
    obtain ⟨hrule_b, _⟩ := ruleAt?_mem_rules t ht (p.take b) nt_b children_b hsub_b
    have h_fa : f a = ⟨nt_a, children_a.map rootSymbol⟩ := by
      simp only [f, hrule_a, Option.getD_some]
    have h_fb : f b = ⟨nt_b, children_b.map rootSymbol⟩ := by
      simp only [f, hrule_b, Option.getD_some]
    have : nt_b = nt_a := by
      have : (⟨nt_b, children_b.map rootSymbol⟩ : ContextFreeRule T g.NT) =
          ⟨nt_a, children_a.map rootSymbol⟩ := by rw [← h_fa, ← h_fb, hfeq]
      exact ContextFreeRule.mk.injEq _ _ _ _ |>.mp this |>.1
    exact ⟨b, a, hba, by omega, nt_b, children_b, nt_a, children_a, hsub_b, hsub_a, this⟩

end CFGTree

set_option maxHeartbeats 800000 in
/-- **Pumping decomposition.** If a valid derivation tree is taller than the
    number of rules, then the yield decomposes as u·v·x·y·z satisfying the
    CFL pumping conditions, and all pumped strings remain in the language.

    Most of the infrastructure is now in place (see preceding sections):
    - `subtreeAt? : CFGTree → Pos → Option CFGTree` (Option-style like `List.get?`)
    - `replaceAt : CFGTree → Pos → CFGTree → CFGTree` (like `List.set`)
    - `subtreeAt?_append` — composition of paths
    - `subtreeAt?_validFor` — validity propagates through subtree access
    - `yield_replaceAt_decomp` — yield = pre ++ sub.yield ++ post, with replacement
    - `validFor_replaceAt` — replacing a same-root subtree preserves validity
    - `rootSymbol_replaceAt_cons` — non-root replacement preserves root symbol
    - `exists_pos_of_height` — extract a Pos of any chosen length k ≤ t.height - 1
    - `spine_node_at_prefix` — every prefix of a descent path lands on a `.node`
    - `ruleAt?` + `ruleAt?_mem_rules` — extract the rule used at a position
    - `exists_repeat_root` — pigeonhole gives two prefixes with same root NT

    Remaining for full assembly:
    1. **Restricted pigeonhole**: pick a path of length t.height - 1, restrict
       `exists_repeat_root` to bottom #rules + 1 prefixes (depths
       t.height - #rules - 1 to t.height - 1) so that t_outer.height ≤ #rules + 1,
       hence |t_outer.yield| ≤ b^(#rules + 1) = pumpingConstant.
    2. **Yield assembly**: apply `yield_replaceAt_decomp` to t at p_outer giving
       u, z; then to t_outer at the relative path giving v, y. Then x = t_inner.yield.
    3. **Pumping iteration**: define `iter k = replaceAt t_outer p_inner_rel
       (iter (k-1))`, prove its yield is `(v^k) ++ x ++ (y^k)` by induction;
       finally `replaceAt t p_outer (iter k)` gives the pumped tree, valid by
       `validFor_replaceAt`.
    4. **|vy| ≥ 1**: requires picking a MINIMUM-size tree with the same yield
       (Sipser's argument). If both v and y were ε, the inner subtree could
       replace the outer one in t, giving a smaller tree with same yield. -/
private theorem derives_yieldList {T : Type} {g : ContextFreeGrammar T}
    (ts : List (CFGTree T g.NT))
    (hvalid : ∀ t ∈ ts, g.Derives [t.rootSymbol] (t.yield.map Symbol.terminal)) :
    g.Derives (ts.map CFGTree.rootSymbol) ((CFGTree.yieldList ts).map Symbol.terminal) := by
  induction ts with
  | nil => exact Relation.ReflTransGen.refl
  | cons c cs ih =>
    simp only [List.map_cons, CFGTree.yieldList, List.map_append]
    show g.Derives ([c.rootSymbol] ++ cs.map CFGTree.rootSymbol)
      (c.yield.map Symbol.terminal ++ (CFGTree.yieldList cs).map Symbol.terminal)
    exact ((hvalid c (List.mem_cons_self ..)).append_right _).trans
      ((ih (fun t ht => hvalid t (List.mem_cons_of_mem _ ht))).append_left _)

theorem validFor_derives {T : Type} {g : ContextFreeGrammar T}
    (t : CFGTree T g.NT) (ht : t.ValidFor g) :
    g.Derives [t.rootSymbol] (t.yield.map Symbol.terminal) := by
  match t, ht with
  | .leaf _, _ => exact Relation.ReflTransGen.refl
  | .node nt children, .node _ _ hrule hchildren =>
    exact (ContextFreeGrammar.Produces.single
      ⟨⟨nt, children.map CFGTree.rootSymbol⟩, hrule,
       ContextFreeRule.Rewrites.input_output⟩).trans
      (derives_yieldList children (fun c hc => validFor_derives c (hchildren c hc)))
termination_by t

private theorem flatten_replicate_succ_right {T : Type} (l : List T) (n : Nat) :
    (List.replicate (n + 1) l).flatten = (List.replicate n l).flatten ++ l := by
  induction n with
  | zero => simp
  | succ k ih =>
    conv_lhs => rw [List.replicate_succ, List.flatten_cons, ih]
    conv_rhs => rw [List.replicate_succ, List.flatten_cons]
    rw [List.append_assoc]

theorem pumping_from_tall_tree {T : Type} (g : ContextFreeGrammar T)
    (t : CFGTree T g.NT) (ht : t.ValidFor g)
    (hroot : t.rootSymbol = .nonterminal g.initial)
    (hyield_long : t.yield.length ≥ g.pumpingConstant) :
    ∃ u v x y z : List T,
      t.yield = u ++ v ++ x ++ y ++ z ∧
      (v ++ x ++ y).length ≤ g.pumpingConstant ∧
      (v.length + y.length) ≥ 1 ∧
      ∀ i : Nat, (u ++ List.flatten (List.replicate i v) ++ x ++
                  List.flatten (List.replicate i y) ++ z) ∈ g.language := by
  classical
  -- Step 1: Pick min-size valid tree with same yield and root
  obtain ⟨t_min, ht_min_v, ht_min_y, ht_min_r, ht_min_minimal⟩ :=
    CFGTree.exists_min_size_tree t ht
  -- Step 2: Establish t_min.height > g.rules.card
  have htmin_tall : t_min.height > g.rules.card := by
    by_contra hle
    simp only [not_lt] at hle
    have hbound := yield_length_le_of_height g t_min ht_min_v
    have h1 : g.maxBranch ^ t_min.height ≤ g.maxBranch ^ g.rules.card :=
      Nat.pow_le_pow_right (by have := g.maxBranch_ge_two; omega) hle
    have h2 : g.maxBranch ^ g.rules.card < g.maxBranch ^ (g.rules.card + 1) :=
      Nat.pow_lt_pow_right (by have := g.maxBranch_ge_two; omega) (by omega)
    have hyl : t_min.yield.length ≥ g.pumpingConstant := by
      rw [ht_min_y]; exact hyield_long
    unfold ContextFreeGrammar.pumpingConstant at hyl
    omega
  -- Step 3: Max-descent path of length t_min.height - 1
  obtain ⟨p, hp_len, hpath⟩ :=
    CFGTree.exists_pos_max_descent t_min (t_min.height - 1) (by omega)
  -- Step 4: Restricted pigeonhole. Use Finset.range (#rules + 1) with shift.
  -- offset = p.length - #rules. Indices in [offset, offset + #rules].
  have hoffset_le : p.length - g.rules.card + g.rules.card = p.length := by omega
  -- Define f on shifted range
  let offset := p.length - g.rules.card
  -- Helper: get the rule at depth k for k ≤ p.length, with proof of NT match
  have hroot_at : ∀ k, k ≤ p.length →
      ∃ nt children, t_min.subtreeAt? (p.take k) = some (.node nt children) := by
    intro k hk_le
    obtain ⟨sub, hsub_at, hsub_h⟩ := hpath k (by omega)
    have hsub_h_ge : sub.height ≥ 1 := by rw [hsub_h]; omega
    match sub, hsub_h_ge with
    | .node nt children, _ => exact ⟨nt, children, hsub_at⟩
  let f : Nat → ContextFreeRule T g.NT := fun k =>
    (CFGTree.ruleAt? t_min (p.take (k + offset))).getD ⟨g.initial, []⟩
  have hf_in : ∀ k ∈ Finset.range (g.rules.card + 1), f k ∈ g.rules := by
    intro k hk
    simp at hk
    have hk_off_le : k + offset ≤ p.length := by simp [offset]; omega
    obtain ⟨nt, children, hsub_k⟩ := hroot_at (k + offset) hk_off_le
    obtain ⟨hrule_eq, hrule_in⟩ := CFGTree.ruleAt?_mem_rules t_min ht_min_v
      (p.take (k + offset)) nt children hsub_k
    show f k ∈ g.rules
    simp only [f, hrule_eq, Option.getD_some]
    exact hrule_in
  have hcard : g.rules.card < (Finset.range (g.rules.card + 1)).card := by
    simp [Finset.card_range]
  obtain ⟨a₀, ha₀, b₀, hb₀, hne₀, hfeq₀⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hf_in
  simp at ha₀ hb₀
  -- Reduce to a < b
  obtain ⟨a, b, ha, hb, hab, hfeq⟩ : ∃ a b,
      a < g.rules.card + 1 ∧ b < g.rules.card + 1 ∧ a < b ∧ f a = f b := by
    rcases Nat.lt_or_ge a₀ b₀ with h | h
    · exact ⟨a₀, b₀, ha₀, hb₀, h, hfeq₀⟩
    · exact ⟨b₀, a₀, hb₀, ha₀, lt_of_le_of_ne h hne₀.symm, hfeq₀.symm⟩
  -- Step 5: Set up t_outer, t_inner via the pigeonhole pair
  let i := a + offset
  let j := b + offset
  have hi_le : i ≤ p.length := by simp [i, offset]; omega
  have hj_le : j ≤ p.length := by simp [j, offset]; omega
  have hij : i < j := by simp [i, j]; omega
  have hi_ge_off : i ≥ offset := by simp [i]
  -- Get the subtrees and rules at i, j
  obtain ⟨nt_o, ch_o, hsub_o⟩ := hroot_at i hi_le
  obtain ⟨nt_i, ch_i, hsub_i⟩ := hroot_at j hj_le
  obtain ⟨hrule_o, hrule_o_in⟩ := CFGTree.ruleAt?_mem_rules t_min ht_min_v
    (p.take i) nt_o ch_o hsub_o
  obtain ⟨hrule_i, hrule_i_in⟩ := CFGTree.ruleAt?_mem_rules t_min ht_min_v
    (p.take j) nt_i ch_i hsub_i
  have hfa : f a = ⟨nt_o, ch_o.map CFGTree.rootSymbol⟩ := by
    change (CFGTree.ruleAt? t_min (p.take i)).getD _ = _
    rw [hrule_o]; rfl
  have hfb : f b = ⟨nt_i, ch_i.map CFGTree.rootSymbol⟩ := by
    change (CFGTree.ruleAt? t_min (p.take j)).getD _ = _
    rw [hrule_i]; rfl
  have hroot_eq : nt_o = nt_i := by
    have hh : (⟨nt_o, ch_o.map CFGTree.rootSymbol⟩ : ContextFreeRule T g.NT) =
        ⟨nt_i, ch_i.map CFGTree.rootSymbol⟩ := by rw [← hfa, ← hfb, hfeq]
    exact ContextFreeRule.mk.injEq _ _ _ _ |>.mp hh |>.1
  -- t_outer = .node nt_o ch_o, t_inner = .node nt_i ch_i
  -- t_outer has same root nonterminal as t_inner
  set t_outer : CFGTree T g.NT := .node nt_o ch_o with ht_outer_def
  set t_inner : CFGTree T g.NT := .node nt_i ch_i with ht_inner_def
  have hroot_o_eq_i : t_outer.rootSymbol = t_inner.rootSymbol := by
    show CFGTree.rootSymbol (.node nt_o ch_o) = CFGTree.rootSymbol (.node nt_i ch_i)
    show Symbol.nonterminal nt_o = Symbol.nonterminal nt_i
    rw [hroot_eq]
  -- Bound on t_outer.height
  have ht_outer_h : t_outer.height = t_min.height - i := by
    obtain ⟨sub_o, hsub_o', hsub_o_h⟩ := hpath i (by omega)
    rw [hsub_o] at hsub_o'
    have : t_outer = sub_o := by injection hsub_o'
    rw [this, hsub_o_h]
  have ht_outer_h_le : t_outer.height ≤ g.rules.card + 1 := by
    rw [ht_outer_h]; simp [i, offset]; omega
  -- t_inner is a subtree of t_outer at relative path
  have hsubtree_path_eq : p.take j = p.take i ++ (p.take j).drop i := by
    conv_lhs => rw [← List.take_append_drop i (p.take j)]
    congr 1; rw [List.take_take, min_eq_left (by omega)]
  let p_outer := p.take i
  let p_inner_rel := (p.take j).drop i
  have hp_inner_compose : t_min.subtreeAt? (p_outer ++ p_inner_rel) = some t_inner := by
    show t_min.subtreeAt? (p.take i ++ (p.take j).drop i) = _
    rw [← hsubtree_path_eq]; exact hsub_i
  have hsub_inner_in_outer : t_outer.subtreeAt? p_inner_rel = some t_inner := by
    rw [CFGTree.subtreeAt?_append] at hp_inner_compose
    rw [show t_min.subtreeAt? p_outer = some t_outer from hsub_o] at hp_inner_compose
    simpa using hp_inner_compose
  -- Step 6: Yield decomposition
  obtain ⟨u, z, hyield_t, hreplace_t⟩ :=
    CFGTree.yield_replaceAt_decomp t_min p_outer t_outer hsub_o
  obtain ⟨v, y, hyield_outer, hreplace_outer⟩ :=
    CFGTree.yield_replaceAt_decomp t_outer p_inner_rel t_inner hsub_inner_in_outer
  -- x := t_inner.yield
  let x := t_inner.yield
  -- t.yield = u ++ v ++ x ++ y ++ z (via t_min)
  have hyield_decomp : t.yield = u ++ v ++ x ++ y ++ z := by
    rw [← ht_min_y, hyield_t, hyield_outer]
    show u ++ (v ++ t_inner.yield ++ y) ++ z = u ++ v ++ x ++ y ++ z
    show u ++ (v ++ x ++ y) ++ z = u ++ v ++ x ++ y ++ z
    simp [List.append_assoc]
  -- Step 7: |vxy| ≤ pumpingConstant
  have hvxy_bound : (v ++ x ++ y).length ≤ g.pumpingConstant := by
    have ht_outer_yield_eq : t_outer.yield = v ++ x ++ y := by
      rw [hyield_outer]
    rw [← ht_outer_yield_eq]
    have hbound := yield_length_le_of_height g t_outer
      (CFGTree.subtreeAt?_validFor t_min ht_min_v p_outer t_outer hsub_o)
    have hpow_le : g.maxBranch ^ t_outer.height ≤ g.maxBranch ^ (g.rules.card + 1) :=
      Nat.pow_le_pow_right (by have := g.maxBranch_ge_two; omega) ht_outer_h_le
    unfold ContextFreeGrammar.pumpingConstant
    omega
  -- Step 8: |vy| ≥ 1 via minimality
  have hvy_pos : v.length + y.length ≥ 1 := by
    by_contra hcontra
    push Not at hcontra
    have hv_empty : v = [] :=
      List.eq_nil_of_length_eq_zero (by omega)
    have hy_empty : y = [] :=
      List.eq_nil_of_length_eq_zero (by omega)
    -- If v = y = ε, then yield(t_outer) = yield(t_inner)
    have ht_outer_yield_eq_inner : t_outer.yield = t_inner.yield := by
      rw [hyield_outer, hv_empty, hy_empty]; simp
    -- Replace t_outer with t_inner in t_min: same yield, but smaller size
    let t_replaced := t_min.replaceAt p_outer t_inner
    have hyield_replaced : t_replaced.yield = t_min.yield := by
      show (t_min.replaceAt p_outer t_inner).yield = t_min.yield
      rw [hreplace_t t_inner, hyield_t, ht_outer_yield_eq_inner]
    have hvalid_replaced : t_replaced.ValidFor g := by
      apply CFGTree.validFor_replaceAt t_min p_outer t_outer t_inner hsub_o
        hroot_o_eq_i.symm ht_min_v
      exact CFGTree.subtreeAt?_validFor t_min ht_min_v _ _ hp_inner_compose
    have hroot_replaced : t_replaced.rootSymbol = t_min.rootSymbol := by
      show (t_min.replaceAt p_outer t_inner).rootSymbol = t_min.rootSymbol
      cases hp_outer_eq : p_outer with
      | nil =>
        have hto_eq_tmin : t_outer = t_min := by
          have h0 : t_min.subtreeAt? [] = some t_outer := by rw [← hp_outer_eq]; exact hsub_o
          simp [CFGTree.subtreeAt?] at h0; exact h0.symm
        simp [CFGTree.replaceAt]
        rw [← hroot_o_eq_i, ← hto_eq_tmin]
      | cons hh tt =>
        exact CFGTree.rootSymbol_replaceAt_cons t_min hh tt t_inner
    -- size strict decrease
    have hsize_lt : t_replaced.size < t_min.size := by
      have hi_size_lt : t_inner.size < t_outer.size := by
        have hp_inner_rel_nonempty : p_inner_rel ≠ [] := by
          intro hempty
          have : (p.take j).drop i = [] := hempty
          have hlen_eq : (p.take j).length ≤ i := by
            have := congr_arg List.length this; simp at this; omega
          have : j ≤ i := by
            have h1 : (p.take j).length = min j p.length := by simp
            rw [h1] at hlen_eq; omega
          omega
        obtain ⟨idx, rest, hp_eq⟩ : ∃ idx rest, p_inner_rel = idx :: rest := by
          rcases p_inner_rel with _ | ⟨a, b⟩
          · exact absurd rfl hp_inner_rel_nonempty
          · exact ⟨a, b, rfl⟩
        have hsub' : t_outer.subtreeAt? (idx :: rest) = some t_inner := by
          rw [← hp_eq]; exact hsub_inner_in_outer
        exact CFGTree.size_subtreeAt?_lt_of_cons t_outer idx rest t_inner hsub'
      exact CFGTree.size_replaceAt_lt t_min p_outer t_outer t_inner hsub_o hi_size_lt
    -- Apply minimality
    have := ht_min_minimal t_replaced hvalid_replaced
      (by rw [hyield_replaced]; exact ht_min_y)
      (by rw [hroot_replaced]; exact ht_min_r)
    omega
  -- Step 9: Pumping iteration
  refine ⟨u, v, x, y, z, hyield_decomp, hvxy_bound, hvy_pos, ?_⟩
  -- For ∀ i, prove the pumped string is in g.language
  -- Define pumpInner : Nat → CFGTree, with yield = v^i ++ x ++ y^i
  intro k
  -- pumpInner k: replace t_inner with itself k times (giving v^k ++ x ++ y^k yield in t_outer's slot)
  -- Then graft into t_min at p_outer.
  -- For brevity, define recursively and prove by induction.
  let pumpInner : Nat → CFGTree T g.NT := fun n => Nat.rec t_inner
    (fun _ prev => t_outer.replaceAt p_inner_rel prev) n
  have hpump_yield : ∀ n, (pumpInner n).yield =
      List.flatten (List.replicate n v) ++ x ++ List.flatten (List.replicate n y) := by
    intro n
    induction n with
    | zero => simp [pumpInner, x]
    | succ m ih =>
      show (t_outer.replaceAt p_inner_rel (pumpInner m)).yield = _
      rw [hreplace_outer (pumpInner m), ih]
      conv_rhs =>
        rw [show List.replicate (m + 1) v = v :: List.replicate m v from rfl,
            List.flatten_cons, flatten_replicate_succ_right]
      simp only [List.append_assoc]
  have hpump_root : ∀ n, (pumpInner n).rootSymbol = t_inner.rootSymbol := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      show (t_outer.replaceAt p_inner_rel (pumpInner m)).rootSymbol = _
      cases hp_rel_eq : p_inner_rel with
      | nil =>
        simp [CFGTree.replaceAt]
        exact ih
      | cons hh tt =>
        exact (CFGTree.rootSymbol_replaceAt_cons t_outer hh tt (pumpInner m)).trans hroot_o_eq_i
  have hpump_valid : ∀ n, (pumpInner n).ValidFor g := by
    intro n
    induction n with
    | zero =>
      show t_inner.ValidFor g
      exact CFGTree.subtreeAt?_validFor t_min ht_min_v _ _ hp_inner_compose
    | succ m ih =>
      show (t_outer.replaceAt p_inner_rel (pumpInner m)).ValidFor g
      apply CFGTree.validFor_replaceAt t_outer p_inner_rel t_inner (pumpInner m)
        hsub_inner_in_outer
      · -- (pumpInner m).rootSymbol = t_inner.rootSymbol
        exact hpump_root m
      · exact CFGTree.subtreeAt?_validFor t_min ht_min_v _ _ hsub_o
      · exact ih
  -- Final pumped tree
  let final := t_min.replaceAt p_outer (pumpInner k)
  have hfinal_yield : final.yield =
      u ++ List.flatten (List.replicate k v) ++ x ++ List.flatten (List.replicate k y) ++ z := by
    show (t_min.replaceAt p_outer (pumpInner k)).yield = _
    rw [hreplace_t (pumpInner k), hpump_yield k]
    simp [List.append_assoc]
  have hfinal_valid : final.ValidFor g := by
    apply CFGTree.validFor_replaceAt t_min p_outer t_outer (pumpInner k) hsub_o
    · exact (hpump_root k).trans hroot_o_eq_i.symm
    · exact ht_min_v
    · exact hpump_valid k
  have hfinal_root : final.rootSymbol = .nonterminal g.initial := by
    show (t_min.replaceAt p_outer (pumpInner k)).rootSymbol = .nonterminal g.initial
    cases hp_outer_eq : p_outer with
    | nil =>
      have hto_eq_tmin : t_outer = t_min := by
        have h0 : t_min.subtreeAt? [] = some t_outer := by rw [← hp_outer_eq]; exact hsub_o
        simp [CFGTree.subtreeAt?] at h0; exact h0.symm
      simp [CFGTree.replaceAt]
      rw [hpump_root k, ← hroot_o_eq_i, hto_eq_tmin, ht_min_r, hroot]
    | cons hh tt =>
      exact (CFGTree.rootSymbol_replaceAt_cons t_min hh tt (pumpInner k)).trans
        (by rw [ht_min_r, hroot])
  -- Conclude: final.yield ∈ g.language
  show (u ++ List.flatten (List.replicate k v) ++ x ++
        List.flatten (List.replicate k y) ++ z) ∈ g.language
  rw [← hfinal_yield]
  have h := validFor_derives final hfinal_valid
  rw [hfinal_root] at h
  exact h

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
  have hyield_long : t.yield.length ≥ g.pumpingConstant := hyield ▸ hlen
  obtain ⟨u, v, x, y, z, hdecomp, hvxy, hvy, hpump⟩ :=
    pumping_from_tall_tree g t hvalid hroot hyield_long
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
    `Language.IsContextFree` goes through the CFL pumping lemma. -/
theorem anbncndn_not_contextFree : ¬ Language.IsContextFree anbncndn :=
  not_isContextFree_of_not_pumpable anbncndn anbncndn_not_pumpable

/-- {aⁿbⁿcⁿ} is not context-free. -/
theorem anbnc_not_contextFree : ¬ Language.IsContextFree anbnc :=
  not_isContextFree_of_not_pumpable anbnc anbnc_not_pumpable

