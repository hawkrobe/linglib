import Linglib.Core.Computability.ContextFreeGrammar.Pumping
import Linglib.Core.Computability.NonContextFree.BlockWitness

/-!
# {aⁿbⁿcⁿ}: a three-symbol non-context-free witness language

The classical three-symbol non-context-free witness `anbnc = {aⁿbⁿcⁿ | n ≥ 0}`,
proven non-context-free via the CFL pumping lemma + the unified adjacency
lemma in `BlockWitness`.

Independent of `AnBnCnDn` and `AmBnCmDn` — uses its own `ThreeSymbol`
alphabet and parallel filter-count machinery.
-/

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

/-- The three-symbol witness is structurally `BlockWitness [a, b, c] n`. -/
private theorem makeString_anbnc_eq_blockwitness (n : Nat) :
    makeString_anbnc n =
      BlockWitness ([ThreeSymbol.a, .b, .c] : List ThreeSymbol) n := by
  simp [makeString_anbnc, BlockWitness, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc]

/-- Adjacency in the ThreeSymbol witness via the unified `BlockWitness.not_both_in_vxy`. -/
private theorem not_a_and_c_in_vxy3 (p : Nat) (u vxy z : List ThreeSymbol)
    (hw : makeString_anbnc p = u ++ vxy ++ z) (hvxy : vxy.length ≤ p) :
    ¬(ThreeSymbol.a ∈ vxy ∧ ThreeSymbol.c ∈ vxy) :=
  BlockWitness.not_both_in_vxy
    (by decide : ([ThreeSymbol.a, .b, .c] : List ThreeSymbol).Nodup)
    (i := 0) (j := 2) rfl rfl (by decide)
    (makeString_anbnc_eq_blockwitness p ▸ hw) hvxy

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

/-- Membership characterization: every string in `anbnc` is `makeString_anbnc n`
    for some `n`. Mirror of `mem_anbncndn_iff`; consumed by the homomorphic
    reduction aⁿbⁿcⁿdⁿ → aⁿbⁿcⁿ in `AnBnCnDn`. -/
theorem mem_anbnc_iff (w : List ThreeSymbol) :
    w ∈ anbnc ↔ ∃ n, w = makeString_anbnc n := by
  constructor
  · intro hw
    by_cases hempty : w = []
    · exact ⟨0, by rw [hempty]; rfl⟩
    · have heq := isInLang3_nonempty w hempty
      have hw' : isInLanguage_anbnc w = true := hw
      rw [heq] at hw'
      simp only [Bool.and_eq_true, beq_iff_eq] at hw'
      obtain ⟨⟨h_ab, h_bc⟩, h_eq⟩ := hw'
      refine ⟨(w.filter (· == .a)).length, ?_⟩
      have hb_eq : (w.filter (· == .b)).length = (w.filter (· == .a)).length := h_ab.symm
      have hc_eq : (w.filter (· == .c)).length = (w.filter (· == .a)).length :=
        h_bc.symm.trans h_ab.symm
      calc w
          = List.replicate (w.filter (· == .a)).length .a ++
              List.replicate (w.filter (· == .b)).length .b ++
              List.replicate (w.filter (· == .c)).length .c := h_eq
        _ = List.replicate (w.filter (· == .a)).length .a ++
              List.replicate (w.filter (· == .a)).length .b ++
              List.replicate (w.filter (· == .a)).length .c := by rw [hb_eq, hc_eq]
        _ = makeString_anbnc (w.filter (· == .a)).length := rfl
  · rintro ⟨n, rfl⟩
    exact makeString_anbnc_in_language n

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

/-- {aⁿbⁿcⁿ} is not context-free. -/
theorem anbnc_not_contextFree : ¬ Language.IsContextFree anbnc :=
  not_isContextFree_of_not_pumpable anbnc anbnc_not_pumpable
