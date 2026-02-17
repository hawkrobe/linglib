import Linglib.Theories.Syntax.DependencyGrammar.Formal.DependencyLength

/-!
# Harmonic Word Order via Dependency Length Minimization

Gibson (2025, Ch. 5.3) argues that **dependency length minimization** (DLM)
explains the **head-direction generalization** (Greenberg 1963, Dryer 1992):
languages overwhelmingly prefer consistent head direction across construction
types. The argument:

1. In recursive structures, consistent direction (HH or FF) keeps spine
   dependencies local — each dependent is adjacent to its head.
2. Mixed direction (HF or FH) forces intervening subtree material between
   a head and its spine dependent, inflating dependency lengths.
3. For **single-word** dependents (leaves), direction is irrelevant to DLM
   because there is no subtree to intervene.

## Structure

- §1: **Chain TDL** — abstract theory over `List Nat` position sequences
- §2: **Intervening material** — connecting DLM to tree topology
- §3: **Single-word exception** — leaf dependents have no intervening material
- §4: **Direction change cost** — concrete DepTree examples (Gibson's pattern)
- §5: **DLM prediction** — harmonic order is cheaper

## References

- Gibson, E. (2025). Syntax: A cognitive approach. Ch. 5.3. MIT Press.
- Greenberg, J. (1963). Some universals of grammar.
- Dryer, M. (1992). The Greenbergian word order correlations. Language 68.
- Futrell, R., Levy, R. & Gibson, E. (2020). Dependency locality. Language 96(2).
-/

namespace DepGrammar.HarmonicOrder

open DepGrammar DependencyLength

-- ============================================================================
-- §1: Chain TDL — Abstract Theory
-- ============================================================================

/-! ### Chain Total Dependency Length

For a sequence of positions p[0], p[1], ..., p[k] representing a chain of
dependencies (head → dep₁ → dep₂ → ...), the total dependency length is
the sum of |p[i+1] - p[i]| for all consecutive pairs.

Key insight: monotone sequences (all ascending or all descending) achieve
the minimum TDL = span = max - min. Non-monotone sequences must exceed
the span because each direction reversal adds distance. -/

/-- Total dependency length of a chain of positions: sum of consecutive
    absolute differences |p[i+1] - p[i]|. -/
def chainTDL : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (max a b - min a b) + chainTDL (b :: rest)

/-- A list is monotone ascending. -/
def isAscending : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a ≤ b && isAscending (b :: rest)

/-- A list is monotone descending. -/
def isDescending : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a ≥ b && isDescending (b :: rest)

/-- A list is monotone if it is all ascending or all descending. -/
def isMonotone (l : List Nat) : Bool :=
  isAscending l || isDescending l

/-- The span of a list: max - min. For a chain of k+1 positions spanning
    k dependencies, this is the minimum possible TDL. -/
def listSpan (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | _ =>
    let mx := l.foldl max 0
    let mn := l.foldl min mx
    mx - mn

-- ============================================================================
-- §1a: foldl Helpers for listSpan Reasoning
-- ============================================================================

private theorem foldl_max_comm (l : List Nat) (a : Nat) :
    List.foldl max a l = max a (List.foldl max 0 l) := by
  induction l generalizing a with
  | nil => simp
  | cons b rest ih =>
    simp only [List.foldl]
    rw [show max 0 b = b by omega, ih (max a b), ih b]; omega

private theorem lmax_cons (a : Nat) (l : List Nat) :
    List.foldl max 0 (a :: l) = max a (List.foldl max 0 l) := by
  simp only [List.foldl]
  rw [show max 0 a = a by omega]; exact foldl_max_comm l a

private theorem head_le_lmax (b : Nat) (rest : List Nat) :
    b ≤ List.foldl max 0 (b :: rest) := by
  rw [lmax_cons]; omega

private theorem foldl_min_le_init (l : List Nat) (init : Nat) :
    List.foldl min init l ≤ init := by
  induction l generalizing init with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl]
    calc List.foldl min (min init a) rest
        ≤ min init a := ih (min init a)
      _ ≤ init := by omega

/-- Associativity of `min` through `foldl`: key lemma connecting
    `listSpan` of `a :: l` to `listSpan` of `l`. -/
private theorem foldl_min_assoc (l : List Nat) (a b : Nat) :
    List.foldl min (min a b) l = min a (List.foldl min b l) := by
  induction l generalizing a b with
  | nil => simp
  | cons c rest ih =>
    simp only [List.foldl]
    rw [show min (min a b) c = min a (min b c) by omega]
    exact ih a (min b c)

private theorem isAscending_cons2 (a b : Nat) (rest : List Nat)
    (h : isAscending (a :: b :: rest) = true) :
    a ≤ b ∧ isAscending (b :: rest) = true := by
  simp only [isAscending, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

private theorem ascending_all_ge_head (a : Nat) (l : List Nat)
    (h : isAscending (a :: l) = true) :
    ∀ x ∈ l, a ≤ x := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    intro x hx
    have ⟨hab, hrest⟩ := isAscending_cons2 a b rest h
    rcases List.mem_cons.mp hx with heq | hxr
    · omega
    · have : isAscending (a :: rest) = true := by
        cases rest with
        | nil => simp [isAscending]
        | cons c rs =>
          have ⟨hbc, hcrs⟩ := isAscending_cons2 b c rs hrest
          simp only [isAscending, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by omega, hcrs⟩
      exact ih this x hxr

private theorem foldl_min_of_le_all (l : List Nat) (a : Nat)
    (h : ∀ x ∈ l, a ≤ x) :
    List.foldl min a l = a := by
  induction l generalizing a with
  | nil => simp
  | cons b rest ih =>
    simp only [List.foldl]
    have hab : a ≤ b := h b (List.mem_cons.mpr (Or.inl rfl))
    rw [show min a b = a by omega]
    exact ih a (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

-- ============================================================================
-- §1b: Core Chain TDL Theorems
-- ============================================================================

/-- Triangle inequality for chains: total dep length ≥ span.
    By induction: `|a-b| + span(b::rest) ≥ span(a::b::rest)` reduces to
    arithmetic on `max`/`min` given `m ≤ b ≤ M` (head is between min and max
    of the tail). -/
theorem chain_tdl_ge_span (l : List Nat) :
    chainTDL l ≥ listSpan l := by
  induction l with
  | nil => simp [chainTDL, listSpan]
  | cons a rest ih =>
    match rest with
    | [] => simp [chainTDL, listSpan, List.foldl]
    | b :: rest' =>
      simp only [chainTDL]
      have ihval : chainTDL (b :: rest') ≥ listSpan (b :: rest') := ih
      suffices hsuff : max a b - min a b + listSpan (b :: rest') ≥
          listSpan (a :: b :: rest') by omega
      simp only [listSpan]
      set M' := List.foldl max 0 (b :: rest')
      rw [show List.foldl max 0 (a :: b :: rest') = max a M' from lmax_cons a (b :: rest')]
      have h_lmin_full : List.foldl min (max a M') (a :: b :: rest') =
          min a (List.foldl min b rest') := by
        simp only [List.foldl]
        rw [show min (max a M') a = a by omega]
        exact foldl_min_assoc rest' a b
      have h_lmin_tail : List.foldl min M' (b :: rest') =
          min M' (List.foldl min b rest') := by
        simp only [List.foldl]
        exact foldl_min_assoc rest' M' b
      rw [h_lmin_full, h_lmin_tail]
      set m := List.foldl min b rest'
      have hm_le_b : m ≤ b := foldl_min_le_init rest' b
      have hb_le_M : b ≤ M' := head_le_lmax b rest'
      rw [show min M' m = m by omega]
      omega

/-- Monotone (ascending) chain achieves TDL = span.
    For ascending lists, each step contributes exactly `b - a` and the
    span decomposes as `(b - a) + span(tail)`. -/
theorem monotone_ascending_achieves_span (l : List Nat) (h : isAscending l = true) :
    chainTDL l = listSpan l := by
  induction l with
  | nil => simp [chainTDL, listSpan]
  | cons a rest ih =>
    match rest, h with
    | [], _ => simp [chainTDL, listSpan, List.foldl]
    | b :: rest', h =>
      have ⟨hab, hrest⟩ := isAscending_cons2 a b rest' h
      simp only [chainTDL]
      rw [show max a b - min a b = b - a by omega, ih hrest]
      simp only [listSpan]
      set M' := List.foldl max 0 (b :: rest')
      rw [show List.foldl max 0 (a :: b :: rest') = max a M' from lmax_cons a (b :: rest')]
      have hMb : M' ≥ b := head_le_lmax b rest'
      rw [show max a M' = M' by omega]
      have hall : ∀ x ∈ b :: rest', a ≤ x := ascending_all_ge_head a (b :: rest') h
      have hball : ∀ x ∈ rest', b ≤ x :=
        fun x hx => ascending_all_ge_head b rest' hrest x hx
      have h_lmin_abr : List.foldl min M' (a :: b :: rest') = a := by
        simp only [List.foldl]
        rw [show min M' a = a by omega]
        exact foldl_min_of_le_all (b :: rest') a hall
      have h_lmin_br : List.foldl min M' (b :: rest') = b := by
        simp only [List.foldl]
        rw [show min M' b = b by omega]
        exact foldl_min_of_le_all rest' b hball
      rw [h_lmin_abr, h_lmin_br]
      omega

private theorem chainTDL_range' (s n : Nat) :
    chainTDL (List.range' s (n + 1)) = n := by
  induction n generalizing s with
  | zero => simp [List.range', chainTDL]
  | succ k ih =>
    show chainTDL (s :: List.range' (s + 1) (k + 1)) = k + 1
    show chainTDL (s :: (s + 1) :: List.range' (s + 1 + 1) k) = k + 1
    simp only [chainTDL]
    rw [show max s (s + 1) - min s (s + 1) = 1 by omega]
    rw [show (s + 1) :: List.range' (s + 1 + 1) k = List.range' (s + 1) (k + 1) from rfl]
    rw [ih (s + 1)]; omega

/-- The consecutive sequence [0, 1, ..., k] has chainTDL = k. -/
theorem consecutive_tdl (k : Nat) :
    chainTDL (List.range (k + 1)) = k := by
  rw [List.range_eq_range']
  exact chainTDL_range' 0 k

-- Concrete verifications for small k
example : chainTDL [0, 1, 2] = 2 := by native_decide
example : chainTDL [0, 1, 2, 3] = 3 := by native_decide
example : chainTDL [0, 1, 2, 3, 4] = 4 := by native_decide
example : chainTDL [4, 3, 2, 1, 0] = 4 := by native_decide

/-- Non-monotone sequence has strictly higher TDL than monotone with same span. -/
example : chainTDL [0, 2, 1, 3] > chainTDL [0, 1, 2, 3] := by native_decide
example : chainTDL [0, 3, 1, 4, 2] > chainTDL [0, 1, 2, 3, 4] := by native_decide

/-- Monotone ascending and descending have equal TDL (direction doesn't matter). -/
example : chainTDL [0, 1, 2, 3] = chainTDL [3, 2, 1, 0] := by native_decide
example : chainTDL [0, 1, 2, 3, 4] = chainTDL [4, 3, 2, 1, 0] := by native_decide

-- ============================================================================
-- §2: Intervening Material in Projective Trees
-- ============================================================================

/-! ### Intervening Material

The structural heart of Gibson's argument: dependency length between a head h
and dependent d equals 1 + the number of subtree members of d that fall
between h and d in linear order. In a projective tree, all subtree members
of d are on the same side of h as d, so they may intervene.

When direction is consistent (harmonic), recursive spine dependents are
adjacent to their heads. When direction is mixed (disharmonic), subtree
material from one dependent intervenes between the next spine dependent
and its head. -/

/-- Collect all transitive descendants of a node (excluding the node itself).
    Uses `projection` from Core/Basic.lean. -/
def subtreeMembers (t : DepTree) (idx : Nat) : List Nat :=
  (projection t.deps idx).filter (· != idx)

/-- Count nodes from subtree(d) that fall between positions h and d
    in linear order. These are the "intervening" nodes that inflate
    dependency length beyond 1. -/
def interveningSubtreeNodes (t : DepTree) (headPos depPos : Nat) : Nat :=
  let lo := min headPos depPos
  let hi := max headPos depPos
  let members := subtreeMembers t depPos
  members.filter (λ m => lo < m && m < hi) |>.length

/-- Dependency length ≥ 1 + intervening subtree nodes.

    `depLength` counts ALL positions between head and dependent (= |h − d|).
    `interveningSubtreeNodes` counts only dep's subtree members in that interval.
    The gap is filled by siblings' subtrees placed between h and d.

    The original equality `depLength = 1 + interveningSubtreeNodes` (Gibson 2025,
    Ch. 5.3) holds only when d's subtree is the SOLE occupant of the interval
    (h, d) — i.e., no sibling subtrees intervene. That special case is exactly
    the harmonic-order scenario demonstrated concretely in §4 below. -/
theorem dep_length_ge_one_plus_intervening (t : DepTree) (d : Dependency)
    (hd : d ∈ t.deps)
    (hne : d.headIdx ≠ d.depIdx) :
    depLength d ≥ 1 + interveningSubtreeNodes t d.headIdx d.depIdx := by
  -- depLength = |h - d| ≥ 1 (since h ≠ d).
  -- interveningSubtreeNodes counts a subset of the |h - d| - 1 positions
  -- strictly between h and d, so interveningSubtreeNodes ≤ |h - d| - 1,
  -- giving |h - d| ≥ 1 + interveningSubtreeNodes.
  sorry

-- ============================================================================
-- §3: Single-Word Exception
-- ============================================================================

/-! ### Single-Word (Leaf) Exception

When a dependent is a leaf (no children), its subtree is empty, so there
are no intervening nodes regardless of direction. This is why single-word
dependents (adjectives, demonstratives, intensifiers, negation markers)
can freely violate the head-direction generalization without DLM cost. -/

/-- A node is a leaf if it has no dependents. -/
def isLeaf (t : DepTree) (idx : Nat) : Bool :=
  t.deps.all (·.headIdx != idx)

/-- If no dependency has headIdx = root, then projection returns [root].
    BFS from root visits only root (no outgoing edges).
    Delegates to `projection_of_no_children` from Core.Basic. -/
private theorem projection_of_leaf (deps : List Dependency) (root : Nat)
    (h : deps.all (fun d => !(d.headIdx == root)) = true) :
    projection deps root = [root] := by
  apply projection_of_no_children
  induction deps with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.filter_cons]
    have hne : (d.headIdx == root) = false := by
      simp only [Bool.not_eq_true'] at h; exact h.1
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact ih h.2

/-- A leaf has no subtree members. -/
theorem leaf_no_subtree_members (t : DepTree) (idx : Nat)
    (h : isLeaf t idx = true) :
    subtreeMembers t idx = [] := by
  unfold subtreeMembers
  rw [projection_of_leaf t.deps idx h]
  simp [List.filter, bne, beq_self_eq_true]

/-- A leaf has 0 intervening nodes for any head position.

    Since leaves have no subtree, no subtree members can intervene.
    Direction of a leaf dependent is irrelevant to DLM. -/
theorem leaf_no_intervening (t : DepTree) (headPos depPos : Nat)
    (h : isLeaf t depPos = true) :
    interveningSubtreeNodes t headPos depPos = 0 := by
  unfold interveningSubtreeNodes
  rw [leaf_no_subtree_members t depPos h]
  simp

/-- Bridge to `single_dep_direction_irrelevant` from DependencyLength.lean:
    a single (leaf) dependency has the same length regardless of direction.
    This is the formal basis for Gibson's Table 4 exceptions. -/
theorem leaf_direction_irrelevant_bridge (h d : Nat) :
    depLength ⟨h, d, .amod⟩ = depLength ⟨d, h, .amod⟩ :=
  single_dep_direction_irrelevant h d

-- ============================================================================
-- §4: Direction Change Cost — Concrete Examples
-- ============================================================================

/-! ### Harmonic vs Disharmonic Trees

Gibson (2025, examples 122–123) pattern: a recursive embedding where
the verb takes a clausal complement. With 3 levels of embedding:

    V₁ — S₁ — V₂ — S₂ — V₃ — O₃

In head-initial (HH): V₁ S₁ V₂ S₂ V₃ O₃ — each V is adjacent to its S
In head-final (FF): O₃ V₃ S₂ V₂ S₁ V₁ — same TDL, mirror image
In mixed (HF): V₁ S₁ S₂ V₃ O₃ V₂ — V₂ separated from V₁ by intervening material
In mixed (FH): S₁ V₁ V₂ O₃ V₃ S₂ — similar inflation

We build concrete DepTrees for each and verify TDL. -/

/-- Consistent head-initial (HH) tree: V₁(0) S₁(1) V₂(2) S₂(3) V₃(4) O₃(5)
    Dependencies: V₁→S₁ (nsubj, 1), V₁→V₂ (ccomp, 2), V₂→S₂ (nsubj, 1),
                  V₂→V₃ (ccomp, 2), V₃→O₃ (obj, 1) -/
def harmonicHI : DepTree :=
  { words := [ Word.mk' "thinks" .VERB, Word.mk' "John" .PROPN
             , Word.mk' "knows" .VERB, Word.mk' "Mary" .PROPN
             , Word.mk' "likes" .VERB, Word.mk' "cats" .NOUN ]
    deps := [ ⟨0, 1, .nsubj⟩    -- thinks ← John, len 1
            , ⟨0, 2, .ccomp⟩    -- thinks → knows, len 2
            , ⟨2, 3, .nsubj⟩    -- knows ← Mary, len 1
            , ⟨2, 4, .ccomp⟩    -- knows → likes, len 2
            , ⟨4, 5, .obj⟩      -- likes → cats, len 1
            ]
    rootIdx := 0 }

/-- Consistent head-final (FF) tree: O₃(0) V₃(1) S₂(2) V₂(3) S₁(4) V₁(5)
    Mirror image of HH. Same TDL. -/
def harmonicHF : DepTree :=
  { words := [ Word.mk' "cats" .NOUN, Word.mk' "likes" .VERB
             , Word.mk' "Mary" .PROPN, Word.mk' "knows" .VERB
             , Word.mk' "John" .PROPN, Word.mk' "thinks" .VERB ]
    deps := [ ⟨1, 0, .obj⟩      -- likes ← cats, len 1
            , ⟨3, 1, .ccomp⟩    -- knows ← likes, len 2
            , ⟨3, 2, .nsubj⟩    -- knows ← Mary, len 1
            , ⟨5, 3, .ccomp⟩    -- thinks ← knows, len 2
            , ⟨5, 4, .nsubj⟩    -- thinks ← John, len 1
            ]
    rootIdx := 5 }

/-- Disharmonic HF tree: verb-initial main clause but verb-final embedding.
    V₁(0) S₁(1) S₂(2) O₃(3) V₃(4) V₂(5)
    The ccomp V₁→V₂ now spans the entire sentence (length 5). -/
def disharmonicHF : DepTree :=
  { words := [ Word.mk' "thinks" .VERB, Word.mk' "John" .PROPN
             , Word.mk' "Mary" .PROPN, Word.mk' "cats" .NOUN
             , Word.mk' "likes" .VERB, Word.mk' "knows" .VERB ]
    deps := [ ⟨0, 1, .nsubj⟩    -- thinks ← John, len 1
            , ⟨0, 5, .ccomp⟩    -- thinks → knows, len 5
            , ⟨5, 2, .nsubj⟩    -- knows ← Mary, len 3
            , ⟨5, 4, .ccomp⟩    -- knows ← likes, len 1
            , ⟨4, 3, .obj⟩      -- likes ← cats, len 1
            ]
    rootIdx := 0 }

/-- Disharmonic FH tree: verb-final main clause but verb-initial embedding.
    S₁(0) V₂(1) S₂(2) V₃(3) O₃(4) V₁(5)
    The ccomp V₁→V₂ again spans far. -/
def disharmonicFH : DepTree :=
  { words := [ Word.mk' "John" .PROPN, Word.mk' "knows" .VERB
             , Word.mk' "Mary" .PROPN, Word.mk' "likes" .VERB
             , Word.mk' "cats" .NOUN, Word.mk' "thinks" .VERB ]
    deps := [ ⟨5, 0, .nsubj⟩    -- thinks ← John, len 5
            , ⟨5, 1, .ccomp⟩    -- thinks ← knows, len 4
            , ⟨1, 2, .nsubj⟩    -- knows → Mary, len 1
            , ⟨1, 3, .ccomp⟩    -- knows → likes, len 2
            , ⟨3, 4, .obj⟩      -- likes → cats, len 1
            ]
    rootIdx := 5 }

-- TDL computations
/-- HH total dep length = 1+2+1+2+1 = 7 -/
example : totalDepLength harmonicHI = 7 := by native_decide

/-- FF total dep length = 1+2+1+2+1 = 7 -/
example : totalDepLength harmonicHF = 7 := by native_decide

/-- HF (disharmonic) total dep length = 1+5+3+1+1 = 11 -/
example : totalDepLength disharmonicHF = 11 := by native_decide

/-- FH (disharmonic) total dep length = 5+4+1+2+1 = 13 -/
example : totalDepLength disharmonicFH = 13 := by native_decide

/-- Core DLM prediction: HH < HF (harmonic beats disharmonic). -/
theorem harmonic_hi_beats_disharmonic_hf :
    totalDepLength harmonicHI < totalDepLength disharmonicHF := by native_decide

/-- Core DLM prediction: FF < FH (harmonic beats disharmonic). -/
theorem harmonic_hf_beats_disharmonic_fh :
    totalDepLength harmonicHF < totalDepLength disharmonicFH := by native_decide

/-- Direction itself doesn't matter, only consistency: HH = FF. -/
theorem direction_irrelevant_consistency_matters :
    totalDepLength harmonicHI = totalDepLength harmonicHF := by native_decide

/-- Both harmonic orders beat both disharmonic orders. -/
theorem harmonic_always_shorter :
    totalDepLength harmonicHI < totalDepLength disharmonicHF ∧
    totalDepLength harmonicHI < totalDepLength disharmonicFH ∧
    totalDepLength harmonicHF < totalDepLength disharmonicHF ∧
    totalDepLength harmonicHF < totalDepLength disharmonicFH :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- §5: DLM Prediction
-- ============================================================================

/-- DLM predicts harmonic order is cheaper. -/
def dlmPredictsHarmonicCheaper : Bool :=
  totalDepLength harmonicHI < totalDepLength disharmonicHF &&
  totalDepLength harmonicHF < totalDepLength disharmonicFH

end DepGrammar.HarmonicOrder
