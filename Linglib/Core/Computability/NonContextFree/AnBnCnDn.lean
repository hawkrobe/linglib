import Linglib.Core.Computability.NonContextFree.BlockWitness
import Linglib.Core.Computability.NonContextFree.AnBnCn
import Linglib.Core.Computability.ContextFreeGrammar.Closure

/-!
# {aⁿbⁿcⁿdⁿ}: a four-symbol non-context-free witness language

The single-parameter four-symbol witness `anbncndn = {aⁿbⁿcⁿdⁿ | n ≥ 0}`.
Membership requires `na = nb = nc = nd` (all four counts equal) **and** the
sorted shape `aⁿbⁿcⁿdⁿ`.

Non-context-freeness is **derived by closure, not re-proved by pumping**: the
erasing homomorphism `dropD : d ↦ ε` maps `anbncndn` exactly onto the irreducible
counting core `anbnc = {aⁿbⁿcⁿ}` (`AnBnCn`), so `anbncndn_not_contextFree`
follows from `anbnc_not_contextFree` through `Language.IsContextFree.stringMap`
(the hom-closure root in `Map`, run contrapositively via `Closure`). aⁿbⁿcⁿdⁿ is
the *nested-counting* case; the genuinely *crossing* witness that [shieber-1985]'s
Swiss-German argument requires is the two-parameter `ambncmdn` sibling, which does
not reduce by single-symbol erasure.

This file also hosts the **shared `FourSymbol` substrate** consumed by the
two-parameter relaxation in `NonContextFree.AmBnCmDn`:

* The alphabet (`FourSymbol`, `FourString`, `LawfulBEq`).
* Witness-form bridges (`makeString_anbncndn_eq_blockwitness`).
* Adjacency consequences via `BlockWitness.not_both_in_vxy`
  (`not_a_and_c_in_vxy`, `not_b_and_d_in_vxy`).
* Filter-count machinery (`filter_count`, `filter_eq_nil_of_not_mem`,
  `fourSymbol_filter_total`).
-/

/-- Alphabet for the four-symbol counting witness languages. -/
inductive FourSymbol where
  | a | b | c | d
  deriving DecidableEq, Repr

instance : LawfulBEq FourSymbol where
  eq_of_beq {x y} h := by cases x <;> cases y <;> first | rfl | exact absurd h (by decide)
  rfl {x} := by cases x <;> decide

abbrev FourString := List FourSymbol

/-- The language {aⁿbⁿcⁿdⁿ | n ≥ 0}: the pedagogical four-symbol counting language. The
    genuinely *crossing* witness that [shieber-1985]'s Swiss-German non-context-freeness
    argument requires is the two-parameter `ambncmdn` sibling; this single-parameter
    language is the nested-counting case (cf. [bresnan-etal-1982] on Dutch cross-serial
    word order, which is itself only weakly context-free). -/
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
-- Non-context-freeness by homomorphic reduction to {aⁿbⁿcⁿ}
-- ============================================================================

/-- The erasing homomorphism `d ↦ ε` (per-symbol map; the string action is
    `List.flatMap dropD`, the free-monoid lift), relabelling the surviving a/b/c into
    the `ThreeSymbol` alphabet. The witness for the reduction aⁿbⁿcⁿdⁿ → aⁿbⁿcⁿ. -/
def dropD : FourSymbol → List ThreeSymbol
  | FourSymbol.a => [ThreeSymbol.a]
  | FourSymbol.b => [ThreeSymbol.b]
  | FourSymbol.c => [ThreeSymbol.c]
  | FourSymbol.d => []

private theorem flatten_replicate_singleton {α : Type*} (n : Nat) (x : α) :
    (List.replicate n [x]).flatten = List.replicate n x := by
  induction n with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

private theorem flatten_replicate_nil {α : Type*} (n : Nat) :
    (List.replicate n ([] : List α)).flatten = [] := by
  induction n with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

private theorem dropD_replicate (n : Nat) (s : FourSymbol) :
    List.flatMap dropD (List.replicate n s) =
      List.flatten (List.replicate n (dropD s)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, List.replicate_succ, List.flatten_cons]

/-- `dropD` erases the `dⁿ` block and relabels, sending the witness to `makeString_anbnc n`. -/
@[simp] theorem dropD_makeString (n : Nat) :
    List.flatMap dropD (makeString_anbncndn n) = makeString_anbnc n := by
  simp only [makeString_anbncndn, List.flatMap_append, dropD_replicate, dropD,
             flatten_replicate_singleton, flatten_replicate_nil, List.append_nil, makeString_anbnc]

/-- `dropD` maps `anbncndn` exactly onto the counting core `anbnc`. This image
    equality is what powers the closure reduction. -/
theorem stringMap_dropD_anbncndn : Language.stringMap dropD anbncndn = anbnc := by
  ext w
  rw [Language.mem_stringMap]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨n, rfl⟩ := (mem_anbncndn_iff v).mp hv
    rw [dropD_makeString]
    exact (mem_anbnc_iff _).mpr ⟨n, rfl⟩
  · intro hw
    obtain ⟨n, rfl⟩ := (mem_anbnc_iff w).mp hw
    exact ⟨makeString_anbncndn n, makeString_in_language n, dropD_makeString n⟩

/-- **{aⁿbⁿcⁿdⁿ} is not context-free** — derived by closure from the counting
    core `anbnc_not_contextFree` via the erasing homomorphism `dropD`, rather than
    re-proved by pumping. -/
theorem anbncndn_not_contextFree : ¬ Language.IsContextFree anbncndn :=
  Language.not_isContextFree_of_stringMap_not dropD
    (by rw [stringMap_dropD_anbncndn]; exact anbnc_not_contextFree)
