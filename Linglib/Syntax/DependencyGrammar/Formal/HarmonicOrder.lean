import Linglib.Syntax.DependencyGrammar.Formal.DependencyLength

open Morphology (Word)

/-!
# Harmonic Word Order via Dependency Length Minimization
[dryer-1992] [futrell-gibson-2020] [gibson-2025] [greenberg-1963]

[gibson-2025] argues that dependency length minimization (DLM) explains
the head-direction generalization: consistent head direction (HH or FF) keeps
spine dependencies local, while mixed direction (HF or FH) forces intervening
subtree material between a head and its spine dependent. For single-word
(leaf) dependents the direction is irrelevant because there is no subtree to
intervene.

## Main declarations

* `chainTDL`, `listSpan` — abstract chain total dependency length on
  `List Nat` position sequences, with `chain_tdl_ge_span` (triangle
  inequality) and `monotone_ascending_achieves_span` (monotone chains hit
  the lower bound).
* `interveningSubtreeNodes`, `dep_length_ge_one_plus_intervening` — the
  structural bridge from chain TDL to projective tree topology.
* `isLeaf`, `leaf_no_intervening` — the leaf exception that licenses
  free direction for single-word dependents.
* `harmonicHI`, `harmonicHF`, `disharmonicHF`, `disharmonicFH` — concrete
  trees instantiating [gibson-2025]'s recursive-embedding pattern.
* `harmonic_always_shorter`, `dlmPredictsHarmonicCheaper` — the DLM
  prediction in the worked-example set.

## Implementation notes

* Predicate-shape definitions inherit the substrate-wide `Bool` convention
  from `DependencyGrammar.Basic` (`isLeaf`, `dlmPredictsHarmonicCheaper`);
  migrating these to `Prop` is a directory-wide refactor.
* The `foldl_*` helpers in `### Chain TDL substrate` are private bookkeeping
  for the two main chain theorems; they exist because `listSpan` is defined
  via `foldl max`/`foldl min` rather than mathlib's `List.maximum?`.
-/

namespace DepGrammar.HarmonicOrder


open DepGrammar DependencyLength

/-! ### Chain total dependency length

For a sequence of positions `p[0], p[1], …, p[k]` representing a chain of
dependencies (head → dep₁ → dep₂ → …), the total dependency length is the
sum of `|p[i+1] - p[i]|`. Monotone sequences achieve the lower bound
`span = max - min`; non-monotone sequences strictly exceed it. -/

/-- Total dependency length of a chain of positions: sum of consecutive
absolute differences `|p[i+1] - p[i]|`. -/
def chainTDL : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (max a b - min a b) + chainTDL (b :: rest)

/-- A list is monotone ascending. -/
def isAscending : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≤ b ∧ isAscending (b :: rest)

instance : DecidablePred isAscending := fun l => by
  induction l with
  | nil => unfold isAscending; infer_instance
  | cons a rest ih =>
    cases rest with
    | nil => unfold isAscending; infer_instance
    | cons b rest' =>
      unfold isAscending
      exact @instDecidableAnd _ _ (Nat.decLe a b) ih

/-- The span of a list: `max - min`. For a chain of `k+1` positions this is
the minimum possible `chainTDL`. -/
def listSpan (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | _ =>
    let mx := l.foldl max 0
    let mn := l.foldl min mx
    mx - mn

/-! ### Chain TDL substrate (foldl helpers) -/

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

private theorem foldl_min_assoc (l : List Nat) (a b : Nat) :
    List.foldl min (min a b) l = min a (List.foldl min b l) := by
  induction l generalizing a b with
  | nil => simp
  | cons c rest ih =>
    simp only [List.foldl]
    rw [show min (min a b) c = min a (min b c) by omega]
    exact ih a (min b c)

private theorem isAscending_cons2 (a b : Nat) (rest : List Nat)
    (h : isAscending (a :: b :: rest)) :
    a ≤ b ∧ isAscending (b :: rest) := by
  simp only [isAscending] at h
  exact h

private theorem ascending_all_ge_head (a : Nat) (l : List Nat)
    (h : isAscending (a :: l)) :
    ∀ x ∈ l, a ≤ x := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    intro x hx
    have ⟨hab, hrest⟩ := isAscending_cons2 a b rest h
    rcases List.mem_cons.mp hx with heq | hxr
    · omega
    · have : isAscending (a :: rest) := by
        cases rest with
        | nil => simp [isAscending]
        | cons c rs =>
          have ⟨hbc, _⟩ := isAscending_cons2 b c rs hrest
          simp only [isAscending]
          exact ⟨by omega, hrest.2⟩
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

/-! ### Core chain TDL theorems -/

/-- Triangle inequality for chains: `chainTDL l ≥ listSpan l`. -/
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

/-- A monotone-ascending chain achieves `chainTDL = listSpan`. -/
theorem monotone_ascending_achieves_span (l : List Nat) (h : isAscending l) :
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

/-! ### Intervening material in projective trees

The structural heart of [gibson-2025]'s argument: dependency length
between head `h` and dependent `d` is bounded below by `1` plus the number
of `d`'s subtree members that fall between `h` and `d` in linear order. -/

/-- All transitive descendants of `idx`, excluding `idx` itself. -/
def subtreeMembers (t : DepTree) (idx : Nat) : List Nat :=
  (projection t.deps idx).filter (· != idx)

/-- Number of nodes from `subtreeMembers t depPos` that fall strictly between
`headPos` and `depPos` in linear order. -/
def interveningSubtreeNodes (t : DepTree) (headPos depPos : Nat) : Nat :=
  let lo := min headPos depPos
  let hi := max headPos depPos
  let members := subtreeMembers t depPos
  members.filter (λ m => lo < m && m < hi) |>.length

/-- Dependency length is at least `1` plus the number of intervening subtree
nodes of the dependent. Strict equality holds when `d`'s subtree is the sole
occupant of `(h, d)` — the harmonic-order scenario in `### Harmonic vs
disharmonic trees`. -/
theorem dep_length_ge_one_plus_intervening (t : DepTree) (d : Dependency)
    (hd : d ∈ t.deps)
    (hne : d.headIdx ≠ d.depIdx) :
    depLength d ≥ 1 + interveningSubtreeNodes t d.headIdx d.depIdx := by
  simp only [depLength, interveningSubtreeNodes, subtreeMembers]
  set lo := min d.headIdx d.depIdx with lo_def
  set hi := max d.headIdx d.depIdx with hi_def
  set filtered := ((projection t.deps d.depIdx).filter (· != d.depIdx)).filter
    (λ m => lo < m && m < hi) with filtered_def
  have hlo_hi : lo < hi := by simp only [lo_def, hi_def]; omega
  have hchain_proj := projection_chain' t.deps d.depIdx
  have hpw_proj := List.isChain_iff_pairwise.mp hchain_proj
  have hpw_filtered : filtered.Pairwise (· < ·) :=
    (hpw_proj.filter _).filter _
  have hchain_filtered : filtered.IsChain (· < ·) :=
    List.isChain_iff_pairwise.mpr hpw_filtered
  have hbounds : ∀ x ∈ filtered, lo < x ∧ x < hi := by
    intro x hx
    simp only [filtered_def, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hx
    exact ⟨hx.2.1, hx.2.2⟩
  have hlen := chain_length_le_range filtered lo hi hchain_filtered hbounds
  omega

/-! ### Leaf (single-word) exception

A leaf dependent has no subtree, so no nodes can intervene regardless of
direction. This is the formal basis for [gibson-2025]'s exception for
single-word adjectives, demonstratives, intensifiers, and negation markers. -/

/-- A node is a leaf if it has no dependents. -/
def isLeaf (t : DepTree) (idx : Nat) : Bool :=
  t.deps.all (·.headIdx != idx)

private theorem projection_of_leaf (deps : List Dependency) (root : Nat)
    (h : deps.all (λ d => !(d.headIdx == root)) = true) :
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
  simp [List.filter, bne]

/-- A leaf contributes zero intervening nodes for any head position. -/
theorem leaf_no_intervening (t : DepTree) (headPos depPos : Nat)
    (h : isLeaf t depPos = true) :
    interveningSubtreeNodes t headPos depPos = 0 := by
  unfold interveningSubtreeNodes
  rw [leaf_no_subtree_members t depPos h]
  simp

/-- Bridge to `single_dep_direction_irrelevant`: a single leaf dependency
has the same length regardless of direction. -/
theorem leaf_direction_irrelevant_bridge (h d : Nat) :
    depLength ⟨h, d, .amod⟩ = depLength ⟨d, h, .amod⟩ :=
  single_dep_direction_irrelevant h d

/-! ### Harmonic vs disharmonic trees

[gibson-2025]'s recursive-embedding pattern: a verb takes a clausal
complement, embedded three levels deep. Head-initial (`HI`) and head-final
(`HF`) consistent orders share the same TDL; mixed orders inflate it. -/

/-- Consistent head-initial (HI) tree: V₁ S₁ V₂ S₂ V₃ O₃. -/
def harmonicHI : DepTree :=
  { words := [ Word.mk' "thinks" .VERB, Word.mk' "John" .PROPN
             , Word.mk' "knows" .VERB, Word.mk' "Mary" .PROPN
             , Word.mk' "likes" .VERB, Word.mk' "cats" .NOUN ]
    deps := [ ⟨0, 1, .nsubj⟩
            , ⟨0, 2, .ccomp⟩
            , ⟨2, 3, .nsubj⟩
            , ⟨2, 4, .ccomp⟩
            , ⟨4, 5, .obj⟩
            ]
    rootIdx := 0 }

/-- Consistent head-final (HF) tree: O₃ V₃ S₂ V₂ S₁ V₁ — mirror of `harmonicHI`. -/
def harmonicHF : DepTree :=
  { words := [ Word.mk' "cats" .NOUN, Word.mk' "likes" .VERB
             , Word.mk' "Mary" .PROPN, Word.mk' "knows" .VERB
             , Word.mk' "John" .PROPN, Word.mk' "thinks" .VERB ]
    deps := [ ⟨1, 0, .obj⟩
            , ⟨3, 1, .ccomp⟩
            , ⟨3, 2, .nsubj⟩
            , ⟨5, 3, .ccomp⟩
            , ⟨5, 4, .nsubj⟩
            ]
    rootIdx := 5 }

/-- Disharmonic HF tree: head-initial main clause, head-final embedding. -/
def disharmonicHF : DepTree :=
  { words := [ Word.mk' "thinks" .VERB, Word.mk' "John" .PROPN
             , Word.mk' "Mary" .PROPN, Word.mk' "cats" .NOUN
             , Word.mk' "likes" .VERB, Word.mk' "knows" .VERB ]
    deps := [ ⟨0, 1, .nsubj⟩
            , ⟨0, 5, .ccomp⟩
            , ⟨5, 2, .nsubj⟩
            , ⟨5, 4, .ccomp⟩
            , ⟨4, 3, .obj⟩
            ]
    rootIdx := 0 }

/-- Disharmonic FH tree: head-final main clause, head-initial embedding. -/
def disharmonicFH : DepTree :=
  { words := [ Word.mk' "John" .PROPN, Word.mk' "knows" .VERB
             , Word.mk' "Mary" .PROPN, Word.mk' "likes" .VERB
             , Word.mk' "cats" .NOUN, Word.mk' "thinks" .VERB ]
    deps := [ ⟨5, 0, .nsubj⟩
            , ⟨5, 1, .ccomp⟩
            , ⟨1, 2, .nsubj⟩
            , ⟨1, 3, .ccomp⟩
            , ⟨3, 4, .obj⟩
            ]
    rootIdx := 5 }

/-- Both harmonic orders beat both disharmonic orders. -/
theorem harmonic_always_shorter :
    totalDepLength harmonicHI < totalDepLength disharmonicHF ∧
    totalDepLength harmonicHI < totalDepLength disharmonicFH ∧
    totalDepLength harmonicHF < totalDepLength disharmonicHF ∧
    totalDepLength harmonicHF < totalDepLength disharmonicFH :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- DLM predicts harmonic order is cheaper. Consumed by `Studies/Gibson2025`
and `Studies/HahnDegenFutrell2021`. -/
def dlmPredictsHarmonicCheaper : Bool :=
  totalDepLength harmonicHI < totalDepLength disharmonicHF &&
  totalDepLength harmonicHF < totalDepLength disharmonicFH

end DepGrammar.HarmonicOrder
