import Linglib.Syntax.DependencyGrammar.Dominance

open Morphology (Word)

/-!
# Mildly non-projective dependency structures

Formalizes the structural theory of [kuhlmann-nivre-2006],
[kuhlmann-2013], [mueller-2013]: planarity, well-nestedness, and
the hierarchy

  projective ⊂ planar ⊂ well-nested ⊂ unrestricted.

The cross-serial / nested verb-cluster pair ([kuhlmann-2013] Figure 1)
witnesses the gap between projectivity and well-nestedness in attested
language data.

## Main declarations

* `depsCross`, `linked`, `disjoint`, `projectionsInterleave` — arc-crossing
  primitives.
* `DepTree.isPlanar`, `DepTree.isWellNested` — the two restrictiveness
  classes between projective and unrestricted.
* `projective_iff_gapDegree_zero`, `projective_iff_blockDegree_one`,
  `blockDegree_eq_gapDegree_succ` — equivalences in the hierarchy.
* `projective_implies_planar` — every well-formed projective tree is planar.
* `planar_implies_wellNested` — every well-formed planar tree is well-nested.
* `nonProjective_implies_gapDeg_ge1` — bridge to `Core/Basic.lean`'s
  `gapDegree`.
* `dutchCrossSerial`, `germanNested`, `nonProjectiveTree` — example trees
  used in `Discontinuity.lean`, `DependencyLength.lean`, and
  `Studies/Mueller2013.lean`.

## Implementation notes

* Predicate-shape definitions return `Bool`; this matches the substrate-wide
  DG convention and forces `... = true` in theorem statements. A Prop +
  `Decidable` refactor is tracked at the substrate level.
* The headline proof `planar_implies_wellNested` proceeds by contrapositive
  through `interleaving_not_planar`, a long chain of `private` infrastructure
  lemmas (`exists_spanning_edge`, `escape_gives_crossing`, the discrete
  intermediate-value lemmas `find_exit_step` / `find_entry_step`).
* `FillerGapDep` (a `{ tree, dep, inTree, nonProj }` wrapper formerly here)
  was dropped — no downstream consumer; the cross-framework "filler-gap" abstraction
  the prior docstring gestured at belongs in a shared substrate (the
  `LongDistance.lean` Todo articulates this), not as a thin subtype here.
-/

namespace DepGrammar


/-! ### Arc-crossing detection -/

/-- Two dependencies cross iff their spans overlap without containment.
    ([kuhlmann-nivre-2006], implicit in Definition 4) -/
def depsCross (d1 d2 : Dependency) : Bool :=
  if d1 == d2 then false
  else if d1.headIdx == d2.headIdx then false
  else
    let (min1, max1) := (min d1.headIdx d1.depIdx, max d1.headIdx d1.depIdx)
    let (min2, max2) := (min d2.headIdx d2.depIdx, max d2.headIdx d2.depIdx)
    ¬(max1 <= min2 || max2 <= min1 ||
      (min1 <= min2 && max2 <= max1) ||
      (min2 <= min1 && max1 <= max2))

/-- All non-projective (crossing) dependencies in a tree. -/
def nonProjectiveDeps (t : DepTree) : List Dependency :=
  t.deps.filter λ d1 => t.deps.any λ d2 => depsCross d1 d2

/-- Whether a tree has any non-projective dependencies. -/
def hasFillerGap (t : DepTree) : Bool :=
  (nonProjectiveDeps t).length > 0

/-! ### Planarity ([kuhlmann-nivre-2006], Definition 4) -/

/-- Whether two positions are linked by an edge (in either direction). -/
def linked (deps : List Dependency) (a b : Nat) : Bool :=
  deps.any λ d =>
    (d.headIdx == a && d.depIdx == b) || (d.headIdx == b && d.depIdx == a)

/-- A dependency tree is **planar** iff its edges can be drawn above the
    sentence without crossing: no nodes `a < b < c < d` with `linked a c`
    and `linked b d`. ([kuhlmann-nivre-2006], Definition 4) -/
def DepTree.isPlanar (t : DepTree) : Bool :=
  let deps := t.deps
  let n := t.words.length
  !(List.range n |>.any λ a =>
    List.range n |>.any λ b =>
      List.range n |>.any λ c =>
        List.range n |>.any λ d =>
          a < b && b < c && c < d && linked deps a c && linked deps b d)

/-! ### Well-nestedness ([kuhlmann-nivre-2006], Definition 8) -/

/-- Two projections **interleave** if there exist `l₁, r₁ ∈ p1` and
    `l₂, r₂ ∈ p2` with `l₁ < l₂ < r₁ < r₂`. -/
def projectionsInterleave (p1 p2 : List Nat) : Bool :=
  p1.any λ l1 => p2.any λ l2 => p1.any λ r1 => p2.any λ r2 =>
    l1 < l2 && l2 < r1 && r1 < r2

/-- Two nodes are **disjoint** if neither dominates the other. -/
def disjoint (deps : List Dependency) (u v : Nat) : Bool :=
  let pu := projection deps u
  let pv := projection deps v
  !(pu.contains v) && !(pv.contains u)

private theorem disjoint_symm {deps : List Dependency} {u v : Nat}
    (h : disjoint deps u v = true) : disjoint deps v u = true := by
  simp only [disjoint, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
  exact ⟨h.2, h.1⟩

/-- A dependency tree is **well-nested** if no two disjoint nodes have
    interleaving projections. ([kuhlmann-nivre-2006], Definition 8) -/
def DepTree.isWellNested (t : DepTree) : Bool :=
  let deps := t.deps
  let n := t.words.length
  !(List.range n |>.any λ u =>
    List.range n |>.any λ v =>
      u != v && disjoint deps u v &&
      projectionsInterleave (projection deps u) (projection deps v))

/-! ### Example trees

Cross-serial Dutch and nested German from [kuhlmann-2013] Figure 1 —
the canonical pair witnessing that mild non-projectivity (well-nested,
gap degree 1) covers attested data. -/

/-- Minimal crossing tree: arcs `0 → 2` and `1 → 3` cross. -/
def nonProjectiveTree : DepTree :=
  { words := [ { form :="A", cat := .NOUN, features := {}}, { form :="B", cat := .VERB, features := {}}, { form :="C", cat := .NOUN, features := {}}, { form :="D", cat := .VERB, features := {}} ]
    deps := [ ⟨0, 2, .obj⟩, ⟨1, 3, .obj⟩ ]
    rootIdx := 0 }

/-- Dutch cross-serial: "dat Jan Piet Marie zag helpen lezen".
    Dependencies `zag→Jan`, `helpen→Piet`, `lezen→Marie` cross. -/
def dutchCrossSerial : DepTree :=
  { words := [ Word.mk' "dat" .SCONJ, Word.mk' "Jan" .PROPN
             , Word.mk' "Piet" .PROPN, Word.mk' "Marie" .PROPN
             , Word.mk' "zag" .VERB, Word.mk' "helpen" .VERB
             , Word.mk' "lezen" .VERB ]
    deps := [ ⟨0, 4, .dep⟩, ⟨4, 1, .nsubj⟩, ⟨4, 5, .xcomp⟩
            , ⟨5, 2, .nsubj⟩, ⟨5, 6, .xcomp⟩, ⟨6, 3, .nsubj⟩ ]
    rootIdx := 0 }

/-- German nested: "dass Jan Piet Marie lesen helfen sah". Same dependencies
    as `dutchCrossSerial` but verbs in reverse order → projective. -/
def germanNested : DepTree :=
  { words := [ Word.mk' "dass" .SCONJ, Word.mk' "Jan" .PROPN
             , Word.mk' "Piet" .PROPN, Word.mk' "Marie" .PROPN
             , Word.mk' "lesen" .VERB, Word.mk' "helfen" .VERB
             , Word.mk' "sah" .VERB ]
    deps := [ ⟨0, 6, .dep⟩, ⟨6, 1, .nsubj⟩, ⟨6, 5, .xcomp⟩
            , ⟨5, 2, .nsubj⟩, ⟨5, 4, .xcomp⟩, ⟨4, 3, .nsubj⟩ ]
    rootIdx := 0 }

/-! ### Verified properties of the example trees -/

example : isProjective nonProjectiveTree = false := by decide
example : hasFillerGap nonProjectiveTree = true := by decide
example : isProjective dutchCrossSerial = false := by decide
example : isProjective germanNested = true := by decide

example : DepTree.gapDegree germanNested = 0 := by decide
example : DepTree.blockDegree germanNested = 1 := by decide
example : DepTree.gapDegree dutchCrossSerial = 1 := by decide
example : DepTree.blockDegree dutchCrossSerial = 2 := by decide
example : DepTree.gapDegree nonProjectiveTree = 1 := by decide
example : DepTree.blockDegree nonProjectiveTree = 2 := by decide

example : DepTree.isPlanar germanNested = true := by decide
example : DepTree.isPlanar dutchCrossSerial = false := by decide
example : DepTree.isPlanar nonProjectiveTree = false := by decide

example : DepTree.isWellNested germanNested = true := by decide
/-- Dutch cross-serial: well-nested despite being non-projective. -/
example : DepTree.isWellNested dutchCrossSerial = true := by decide
example : DepTree.isWellNested nonProjectiveTree = false := by decide

/-! ### Hierarchy theorems -/

/-- **Projective ⟺ gap degree 0**: a tree is projective iff no node's
    projection has any gaps.
    ([kuhlmann-nivre-2006], Definition 3 + Definition 7) -/
theorem projective_iff_gapDegree_zero (t : DepTree) :
    isProjective t = true ↔ t.gapDegree = 0 := by
  unfold isProjective DepTree.gapDegree
  constructor
  · intro hall
    rw [foldl_max_zero_iff]
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    unfold gapDegreeAt
    have hiv : isInterval (projection t.deps i) = true := by
      rw [List.all_eq_true] at hall
      exact hall i hi
    have := (isInterval_iff_gaps_nil _ (projection_chain' _ _)).mp hiv
    simp [this]
  · intro hzero
    rw [foldl_max_zero_iff] at hzero
    rw [List.all_eq_true]
    intro i hi
    rw [(isInterval_iff_gaps_nil _ (projection_chain' _ _))]
    have := hzero (gapDegreeAt t.deps i)
      (List.mem_map.mpr ⟨i, hi, rfl⟩)
    unfold gapDegreeAt at this
    exact List.eq_nil_of_length_eq_zero this

/-- **Projective ⟺ block-degree 1** for non-empty trees. -/
theorem projective_iff_blockDegree_one (t : DepTree)
    (hne_tree : t.words.length > 0) :
    isProjective t = true ↔ t.blockDegree = 1 := by
  rw [projective_iff_gapDegree_zero]
  unfold DepTree.gapDegree DepTree.blockDegree
  constructor
  · intro hgap
    have hall_gap : ∀ x ∈ (List.range t.words.length).map (gapDegreeAt t.deps), x = 0 :=
      (foldl_max_zero_iff _).mp hgap
    have hall_block : ∀ x ∈ (List.range t.words.length).map (blockDegreeAt t.deps), x = 1 := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have hgap_i : gapDegreeAt t.deps i = 0 :=
        hall_gap _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
      unfold blockDegreeAt gapDegreeAt at *
      rw [blocks_length_eq_gaps_length_succ _ (projection_nonempty t.deps i)
          (projection_chain' t.deps i)]
      omega
    have hne : (List.range t.words.length).map (blockDegreeAt t.deps) ≠ [] := by
      intro h
      have h1 : ((List.range t.words.length).map (blockDegreeAt t.deps)).length = 0 := by
        rw [h]; rfl
      simp only [List.length_map, List.length_range] at h1
      exact absurd h1 (by omega)
    exact foldl_max_const _ 1 hne hall_block
  · intro hblock
    rw [foldl_max_zero_iff]
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hblock_bound : blockDegreeAt t.deps i ≤ 1 := by
      have hmem : blockDegreeAt t.deps i ∈
          (List.range t.words.length).map (blockDegreeAt t.deps) :=
        List.mem_map.mpr ⟨i, hi, rfl⟩
      have hge := foldl_max_ge_mem _ 0 _ hmem
      omega
    unfold blockDegreeAt gapDegreeAt at *
    rw [blocks_length_eq_gaps_length_succ _ (projection_nonempty t.deps i)
        (projection_chain' t.deps i)] at hblock_bound
    omega

/-- **Block-degree = gap degree + 1** for non-empty projections.
    ([kuhlmann-2013], §7.1 footnote 2) -/
theorem blockDegree_eq_gapDegree_succ (deps : List Dependency) (root : Nat) :
    blockDegreeAt deps root = gapDegreeAt deps root + 1 := by
  unfold blockDegreeAt gapDegreeAt
  exact blocks_length_eq_gaps_length_succ
    (projection deps root) (projection_nonempty deps root)
    (projection_chain' deps root)

/-! ### Projective ⊂ planar

The forward direction of the hierarchy. The proof goes by contrapositive:
if planarity fails, the four witness nodes generate a dominance cycle via
`dominates_to_parent`, contradicting acyclicity. The `hasUniqueHeads`
precondition is essential — a multi-headed node can be projective yet
non-planar. -/

/-- Extract the witnessing edge and direction from `linked = true`. -/
private theorem linked_exists {deps : List Dependency} {a c : Nat}
    (h : linked deps a c = true) :
    ∃ e ∈ deps, (e.headIdx = a ∧ e.depIdx = c) ∨ (e.headIdx = c ∧ e.depIdx = a) := by
  simp only [linked, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true,
             beq_iff_eq] at h
  obtain ⟨e, he_mem, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := h
  · exact ⟨e, he_mem, Or.inl ⟨h1, h2⟩⟩
  · exact ⟨e, he_mem, Or.inr ⟨h1, h2⟩⟩

/-- From `isProjective = true`, every in-range projection is an interval. -/
private theorem projective_interval {t : DepTree} (hproj : isProjective t = true)
    (i : Nat) (hi : i < t.words.length) :
    isInterval (projection t.deps i) = true := by
  simp only [isProjective, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hproj
  exact hproj i hi

/-- Under `hasUniqueHeads`, all incoming edges of an in-range non-root node
    share the same head. -/
private theorem unique_parent_of_hasUniqueHeads {t : DepTree}
    (hwf : t.WF) {c : Nat} (hc : c < t.words.length)
    {e₁ e₂ : Dependency} (he₁ : e₁ ∈ t.deps) (he₂ : e₂ ∈ t.deps)
    (hd₁ : e₁.depIdx = c) (hd₂ : e₂.depIdx = c) :
    e₁.headIdx = e₂.headIdx := by
  have hf₁ : e₁ ∈ t.deps.filter (·.depIdx == c) :=
    List.mem_filter.mpr ⟨he₁, beq_iff_eq.mpr hd₁⟩
  have hf₂ : e₂ ∈ t.deps.filter (·.depIdx == c) :=
    List.mem_filter.mpr ⟨he₂, beq_iff_eq.mpr hd₂⟩
  have hspec : (if c = t.rootIdx then
      (t.deps.filter (·.depIdx == c)).length == 0
    else (t.deps.filter (·.depIdx == c)).length == 1) = true := by
    have hwf' := hwf.uniqueHeads
    unfold hasUniqueHeads at hwf'
    have hmem : (c, (t.deps.filter (·.depIdx == c)).length) ∈
        (List.range ((List.range t.words.length |>.map fun i =>
          (t.deps.filter (·.depIdx == i)).length).length)).zip
          (List.range t.words.length |>.map fun i =>
            (t.deps.filter (·.depIdx == i)).length) := by
      rw [List.mem_iff_getElem]
      simp only [List.length_zip, List.length_range, List.length_map]
      exact ⟨c, by omega, by simp [List.getElem_zip, List.getElem_range, List.getElem_map]⟩
    have h := (List.all_eq_true.mp hwf') _ hmem
    simp only [beq_iff_eq] at h
    exact h
  have hroot : c ≠ t.rootIdx := by
    intro heq
    rw [if_pos heq, beq_iff_eq] at hspec
    exact absurd hspec (by have := List.length_pos_of_mem hf₁; omega)
  rw [if_neg hroot, beq_iff_eq] at hspec
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hspec
  rw [hx] at hf₁ hf₂
  rw [List.eq_of_mem_singleton hf₁, List.eq_of_mem_singleton hf₂]

/-- **Projective ⊂ planar** for well-formed trees.
    ([kuhlmann-nivre-2006], §3.5) -/
theorem projective_implies_planar (t : DepTree)
    (hwf : t.WF) (hacyc : isAcyclic t = true)
    (hproj : isProjective t = true) : t.isPlanar = true := by
  by_contra h_np
  simp only [DepTree.isPlanar] at h_np
  simp at h_np
  obtain ⟨a, ha_lt, b, hb_lt, c, hc_lt, d, hd_lt,
          hab, hbc, hcd, hlink_ac, hlink_bd⟩ := h_np
  obtain ⟨e₁, he₁_mem, he₁_dir⟩ := linked_exists hlink_ac
  obtain ⟨e₂, he₂_mem, he₂_dir⟩ := linked_exists hlink_bd
  have mk_parent : ∀ {node head : Nat}, node < t.words.length →
      ∀ (e_ref : Dependency), e_ref ∈ t.deps → e_ref.headIdx = head →
      e_ref.depIdx = node → ∀ dep ∈ t.deps, dep.depIdx = node → dep.headIdx = head :=
    fun hnode e_ref he_ref_mem hh_ref hd_ref dep hdep hdep_node =>
      (unique_parent_of_hasUniqueHeads hwf hnode he_ref_mem hdep hd_ref hdep_node).symm.trans hh_ref
  rcases he₁_dir with ⟨hh₁, hd₁⟩ | ⟨hh₁, hd₁⟩ <;>
  rcases he₂_dir with ⟨hh₂, hd₂⟩ | ⟨hh₂, hd₂⟩
  · have hc_in_a := child_mem_projection t.deps a c ⟨e₁, he₁_mem, hh₁, hd₁⟩
    have hd_in_b := child_mem_projection t.deps b d ⟨e₂, he₂_mem, hh₂, hd₂⟩
    have hint_a := projective_interval hproj a ha_lt
    have hint_b := projective_interval hproj b hb_lt
    have hb_in_a := interval_mem_between _ (projection_chain' t.deps a) hint_a
      a b c (root_mem_projection t.deps a) hc_in_a hab hbc
    have hc_in_b := interval_mem_between _ (projection_chain' t.deps b) hint_b
      b c d (root_mem_projection t.deps b) hd_in_b hbc hcd
    have h_a_dom_b := dominates_of_mem_projection hb_in_a
    have h_b_dom_c := dominates_of_mem_projection hc_in_b
    have h_c_parent := mk_parent hc_lt e₁ he₁_mem hh₁ hd₁
    have h_b_dom_a := dominates_to_parent h_b_dom_c (Nat.ne_of_lt hbc) h_c_parent
    exact absurd (dominates_antisymm t hwf hacyc a b h_a_dom_b h_b_dom_a) (Nat.ne_of_lt hab)
  · have hc_in_a := child_mem_projection t.deps a c ⟨e₁, he₁_mem, hh₁, hd₁⟩
    have hb_in_d := child_mem_projection t.deps d b ⟨e₂, he₂_mem, hh₂, hd₂⟩
    have hint_a := projective_interval hproj a ha_lt
    have hint_d := projective_interval hproj d hd_lt
    have hb_in_a := interval_mem_between _ (projection_chain' t.deps a) hint_a
      a b c (root_mem_projection t.deps a) hc_in_a hab hbc
    have hc_in_d := interval_mem_between _ (projection_chain' t.deps d) hint_d
      b c d hb_in_d (root_mem_projection t.deps d) hbc hcd
    have h_a_dom_b := dominates_of_mem_projection hb_in_a
    have h_d_dom_c := dominates_of_mem_projection hc_in_d
    have h_c_parent := mk_parent hc_lt e₁ he₁_mem hh₁ hd₁
    have h_b_parent : ∀ dep ∈ t.deps, dep.depIdx = b → dep.headIdx = d :=
      mk_parent hb_lt e₂ he₂_mem hh₂ hd₂
    have h_d_dom_a := dominates_to_parent h_d_dom_c (Nat.ne_of_lt hcd).symm h_c_parent
    have h_a_dom_d := dominates_to_parent h_a_dom_b (Nat.ne_of_lt hab) h_b_parent
    exact absurd (dominates_antisymm t hwf hacyc a d h_a_dom_d h_d_dom_a)
      (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_trans hab hbc) hcd))
  · have ha_in_c := child_mem_projection t.deps c a ⟨e₁, he₁_mem, hh₁, hd₁⟩
    have hd_in_b := child_mem_projection t.deps b d ⟨e₂, he₂_mem, hh₂, hd₂⟩
    have hint_c := projective_interval hproj c hc_lt
    have hint_b := projective_interval hproj b hb_lt
    have hb_in_c := interval_mem_between _ (projection_chain' t.deps c) hint_c
      a b c ha_in_c (root_mem_projection t.deps c) hab hbc
    have hc_in_b := interval_mem_between _ (projection_chain' t.deps b) hint_b
      b c d (root_mem_projection t.deps b) hd_in_b hbc hcd
    have h_c_dom_b := dominates_of_mem_projection hb_in_c
    have h_b_dom_c := dominates_of_mem_projection hc_in_b
    exact absurd (dominates_antisymm t hwf hacyc b c h_b_dom_c h_c_dom_b) (Nat.ne_of_lt hbc)
  · have ha_in_c := child_mem_projection t.deps c a ⟨e₁, he₁_mem, hh₁, hd₁⟩
    have hb_in_d := child_mem_projection t.deps d b ⟨e₂, he₂_mem, hh₂, hd₂⟩
    have hint_c := projective_interval hproj c hc_lt
    have hint_d := projective_interval hproj d hd_lt
    have hb_in_c := interval_mem_between _ (projection_chain' t.deps c) hint_c
      a b c ha_in_c (root_mem_projection t.deps c) hab hbc
    have hc_in_d := interval_mem_between _ (projection_chain' t.deps d) hint_d
      b c d hb_in_d (root_mem_projection t.deps d) hbc hcd
    have h_c_dom_b := dominates_of_mem_projection hb_in_c
    have h_d_dom_c := dominates_of_mem_projection hc_in_d
    have h_b_parent : ∀ dep ∈ t.deps, dep.depIdx = b → dep.headIdx = d :=
      mk_parent hb_lt e₂ he₂_mem hh₂ hd₂
    have h_c_dom_d := dominates_to_parent h_c_dom_b (Nat.ne_of_lt hbc).symm h_b_parent
    exact absurd (dominates_antisymm t hwf hacyc c d h_c_dom_d h_d_dom_c) (Nat.ne_of_lt hcd)

/-! ### Planar ⊂ well-nested

By contrapositive: an interleaving witness produces a spanning-edge crossing
that breaks planarity. The infrastructure below — dominance comparability
under unique heads, parent-chain extraction, the discrete IVT-style
exit/entry steps — feeds the core `interleaving_not_planar` lemma. -/

/-- Under unique heads, any two ancestors of the same node are comparable
    under dominance. -/
private theorem dominates_comparable (t : DepTree)
    (hwf : t.WF)
    {u v x : Nat} (hux : Dominates t.deps u x) (hvx : Dominates t.deps v x) :
    Dominates t.deps u v ∨ Dominates t.deps v u := by
  induction hvx using Dominates.head_induction_on with
  | refl => exact Or.inl hux
  | @step v' w hedge _ ih =>
    rcases ih with huw | hwu
    · by_cases huw_eq : u = w
      · subst huw_eq; exact Or.inr (Dominates.edge hedge)
      · obtain ⟨e, he_mem, he_head, he_dep⟩ := hedge
        have hw_lt : w < t.words.length := he_dep ▸ hwf.depIdx_lt e he_mem
        have hparent : ∀ d ∈ t.deps, d.depIdx = w → d.headIdx = v' := by
          intro d hd hd_dep_eq
          have h := unique_parent_of_hasUniqueHeads hwf hw_lt he_mem hd he_dep hd_dep_eq
          rw [he_head] at h; exact h.symm
        exact Or.inl (dominates_to_parent huw huw_eq hparent)
    · exact Or.inr (Dominates.step hedge hwu)

/-- Disjoint nodes have disjoint projections. -/
private theorem projection_disjoint_of_disjoint (t : DepTree)
    (hwf : t.WF)
    {u v : Nat} (hdisj : disjoint t.deps u v = true)
    {x : Nat} (hxu : x ∈ projection t.deps u) (hxv : x ∈ projection t.deps v) :
    False := by
  simp only [disjoint, Bool.and_eq_true] at hdisj
  rcases dominates_comparable t hwf
    (dominates_of_mem_projection hxu) (dominates_of_mem_projection hxv) with huv | hvu
  · have := mem_projection_of_dominates huv; simp_all
  · have := mem_projection_of_dominates hvu; simp_all

/-- If `root ≥ k` dominates `x < k`, there is a linked edge in `π(root)`
    crossing `k`. -/
private theorem exists_spanning_edge_down {deps : List Dependency}
    {root x : Nat} (hdom : Dominates deps root x) {k : Nat}
    (hroot : k ≤ root) (hx : x < k) :
    ∃ p c, linked deps p c = true ∧
      p ∈ projection deps root ∧ c ∈ projection deps root ∧
      p < k ∧ k ≤ c := by
  revert hroot hx
  induction hdom using Dominates.head_induction_on with
  | refl => intros; omega
  | @step r w hedg _ ih =>
    intro hroot hx
    have hw_mem := child_mem_projection deps r w hedg
    by_cases hw : w < k
    · obtain ⟨d, hd_mem, hd_head, hd_dep⟩ := hedg
      refine ⟨w, r, ?_, hw_mem, root_mem_projection deps r, hw, hroot⟩
      simp only [linked, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact ⟨d, hd_mem, Or.inr ⟨hd_head, hd_dep⟩⟩
    · have hw' : k ≤ w := by omega
      obtain ⟨p, c, hlinked, hp_mem, hc_mem, hp_lt, hc_ge⟩ := ih hw' hx
      exact ⟨p, c, hlinked,
        mem_projection_of_dominates (Dominates.step hedg
          (dominates_of_mem_projection hp_mem)),
        mem_projection_of_dominates (Dominates.step hedg
          (dominates_of_mem_projection hc_mem)),
        hp_lt, hc_ge⟩

/-- If `root < k` dominates `x ≥ k`, there is a linked edge in `π(root)`
    crossing `k`. -/
private theorem exists_spanning_edge_up {deps : List Dependency}
    {root x : Nat} (hdom : Dominates deps root x) {k : Nat}
    (hroot : root < k) (hx : k ≤ x) :
    ∃ p c, linked deps p c = true ∧
      p ∈ projection deps root ∧ c ∈ projection deps root ∧
      p < k ∧ k ≤ c := by
  revert hroot hx
  induction hdom using Dominates.head_induction_on with
  | refl => intros; omega
  | @step r w hedg _ ih =>
    intro hroot hx
    have hw_mem := child_mem_projection deps r w hedg
    by_cases hw : k ≤ w
    · obtain ⟨d, hd_mem, hd_head, hd_dep⟩ := hedg
      refine ⟨r, w, ?_, root_mem_projection deps r, hw_mem, hroot, hw⟩
      simp only [linked, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact ⟨d, hd_mem, Or.inl ⟨hd_head, hd_dep⟩⟩
    · have hw' : w < k := by omega
      obtain ⟨p, c, hlinked, hp_mem, hc_mem, hp_lt, hc_ge⟩ := ih hw' hx
      exact ⟨p, c, hlinked,
        mem_projection_of_dominates (Dominates.step hedg
          (dominates_of_mem_projection hp_mem)),
        mem_projection_of_dominates (Dominates.step hedg
          (dominates_of_mem_projection hc_mem)),
        hp_lt, hc_ge⟩

/-- If `u` dominates nodes on both sides of `k`, there is a linked edge in
    `π(u)` crossing `k`. -/
private theorem exists_spanning_edge {deps : List Dependency}
    {u a b k : Nat} (ha : a ∈ projection deps u) (hb : b ∈ projection deps u)
    (ha_lt : a < k) (hb_ge : k ≤ b) :
    ∃ p c, linked deps p c = true ∧
      p ∈ projection deps u ∧ c ∈ projection deps u ∧
      p < k ∧ k ≤ c := by
  by_cases hu : k ≤ u
  · exact exists_spanning_edge_down (dominates_of_mem_projection ha) hu ha_lt
  · have hu' : u < k := by omega
    exact exists_spanning_edge_up (dominates_of_mem_projection hb) hu' hb_ge

/-- Crossing edges witness non-planarity. -/
private theorem crossing_edges_not_planar (t : DepTree)
    (h_head_wf : ∀ d ∈ t.deps, d.headIdx < t.words.length)
    (h_dep_wf : ∀ d ∈ t.deps, d.depIdx < t.words.length)
    {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hac : linked t.deps a c = true) (hbd : linked t.deps b d = true) :
    t.isPlanar = false := by
  have ha : a < t.words.length := by
    obtain ⟨e, he, hdir⟩ := linked_exists hac
    rcases hdir with ⟨hh, _⟩ | ⟨_, hd⟩
    · exact hh ▸ h_head_wf e he
    · exact hd ▸ h_dep_wf e he
  have hdn : d < t.words.length := by
    obtain ⟨e, he, hdir⟩ := linked_exists hbd
    rcases hdir with ⟨_, hd⟩ | ⟨hh, _⟩
    · exact hd ▸ h_dep_wf e he
    · exact hh ▸ h_head_wf e he
  have hb : b < t.words.length := by omega
  have hc : c < t.words.length := by omega
  match hp : t.isPlanar with
  | false => rfl
  | true =>
    exfalso
    simp only [DepTree.isPlanar, Bool.not_eq_true'] at hp
    have hwitness : (List.range t.words.length |>.any λ a' =>
      List.range t.words.length |>.any λ b' =>
        List.range t.words.length |>.any λ c' =>
          List.range t.words.length |>.any λ d' =>
            a' < b' && b' < c' && c' < d' &&
            linked t.deps a' c' && linked t.deps b' d') = true := by
      rw [List.any_eq_true]
      refine ⟨a, List.mem_range.mpr ha, ?_⟩
      rw [List.any_eq_true]
      refine ⟨b, List.mem_range.mpr hb, ?_⟩
      rw [List.any_eq_true]
      refine ⟨c, List.mem_range.mpr hc, ?_⟩
      rw [List.any_eq_true]
      refine ⟨d, List.mem_range.mpr hdn, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨hab, hbc⟩, hcd⟩, hac⟩, hbd⟩
    simp [hwitness] at hp

/-- Discrete IVT: if `P` holds at `0` and fails at `k`, some step witnesses
    the transition. -/
private theorem find_exit_step {k : Nat} (hk : 0 < k)
    (P : Nat → Prop) [DecidablePred P]
    (h0 : P 0) (hk_neg : ¬P k) :
    ∃ i, i < k ∧ P i ∧ ¬P (i + 1) := by
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : P n
    · exact ⟨n, by omega, hn, hk_neg⟩
    · match n with
      | 0 => exact ⟨0, by omega, h0, hk_neg⟩
      | n' + 1 =>
        obtain ⟨i, hi, hpi, hnpi⟩ := ih (by omega) hn
        exact ⟨i, by omega, hpi, hnpi⟩

/-- Dual: if `P` fails at `0` and holds at `k`, some step witnesses entry. -/
private theorem find_entry_step {k : Nat} (hk : 0 < k)
    (P : Nat → Prop) [DecidablePred P]
    (h0 : ¬P 0) (hk_pos : P k) :
    ∃ i, i < k ∧ ¬P i ∧ P (i + 1) := by
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : P n
    · match n with
      | 0 => exact absurd hn h0
      | n' + 1 =>
        obtain ⟨i, hi, hni, hpi⟩ := ih (by omega) hn
        exact ⟨i, by omega, hni, hpi⟩
    · exact ⟨n, by omega, hn, hk_pos⟩

/-- `linked` is symmetric. -/
private theorem linked_symm_val {deps : List Dependency} {a b : Nat}
    (h : linked deps a b = true) : linked deps b a = true := by
  simp only [linked, List.any_eq_true, Bool.or_eq_true,
             Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨d, hd_mem, hd⟩ := h
  exact ⟨d, hd_mem, hd.symm⟩

/-- Every element of the `iterParent` chain from `w` to `u` belongs to `π(u)`. -/
private theorem iterParent_chain_mem_projection (t : DepTree)
    {u w : Nat} {k : Nat} (hiter : iterParent_uh t w k = u)
    (hchain : ∀ i, i < k → ∃ dep,
      t.deps.find? (fun d => d.depIdx == iterParent_uh t w i) = some dep ∧
      dep.headIdx = iterParent_uh t w (i + 1))
    (i : Nat) (hi : i ≤ k) :
    iterParent_uh t w i ∈ projection t.deps u := by
  suffices h : ∀ j, j ≤ k →
      iterParent_uh t w (k - j) ∈ projection t.deps u by
    have := h (k - i) (by omega)
    rwa [show k - (k - i) = i from by omega] at this
  intro j hj
  induction j with
  | zero => rw [Nat.sub_zero, hiter]; exact root_mem_projection t.deps u
  | succ n ih =>
    have hprev := ih (by omega)
    obtain ⟨dep, hdep_find, hdep_head⟩ := hchain (k - (n + 1)) (by omega)
    have hdep_mem := List.mem_of_find?_eq_some hdep_find
    have hdep_pred := List.find?_some hdep_find
    have hdep_dep : dep.depIdx = iterParent_uh t w (k - (n + 1)) :=
      beq_iff_eq.mp hdep_pred
    have h_shift : k - (n + 1) + 1 = k - n := by omega
    exact projection_closed_under_children t.deps u
      (iterParent_uh t w (k - n)) (iterParent_uh t w (k - (n + 1)))
      hprev ⟨dep, hdep_mem, h_shift ▸ hdep_head, hdep_dep⟩

/-- Consecutive elements of the `iterParent` chain are linked. -/
private theorem iterParent_chain_linked {t : DepTree}
    {w : Nat} {k : Nat}
    (hchain : ∀ i, i < k → ∃ dep,
      t.deps.find? (fun d => d.depIdx == iterParent_uh t w i) = some dep ∧
      dep.headIdx = iterParent_uh t w (i + 1))
    (i : Nat) (hi : i < k) :
    linked t.deps (iterParent_uh t w i) (iterParent_uh t w (i + 1)) = true := by
  obtain ⟨dep, hdep_find, hdep_head⟩ := hchain i hi
  have hdep_mem := List.mem_of_find?_eq_some hdep_find
  have hdep_pred := List.find?_some hdep_find
  have hdep_dep : dep.depIdx = iterParent_uh t w i :=
    beq_iff_eq.mp hdep_pred
  simp only [linked, List.any_eq_true, Bool.or_eq_true,
             Bool.and_eq_true, beq_iff_eq]
  exact ⟨dep, hdep_mem, Or.inr ⟨hdep_head, hdep_dep⟩⟩

/-- Walking out of an interval `(lo, hi)` along a parent chain forces a
    boundary-crossing edge, which crosses the disjoint `linked lo hi`. -/
private theorem escape_gives_crossing (t : DepTree)
    (hwf : t.WF)
    {u v : Nat} (hdisj : disjoint t.deps u v = true)
    {lo hi : Nat} (hlo_hi : lo < hi)
    (hlink_v : linked t.deps lo hi = true)
    (hlo_mem : lo ∈ projection t.deps v) (hhi_mem : hi ∈ projection t.deps v)
    {x : Nat} (hx_mem : x ∈ projection t.deps u)
    (hx_lo : lo < x) (hx_hi : x < hi)
    {z : Nat} (hz_mem : z ∈ projection t.deps u) (hz_out : z < lo ∨ hi < z) :
    t.isPlanar = false := by
  have ne_lo : ∀ w, w ∈ projection t.deps u → w ≠ lo := by
    intro w hw heq; subst heq
    exact projection_disjoint_of_disjoint t hwf hdisj hw hlo_mem
  have ne_hi : ∀ w, w ∈ projection t.deps u → w ≠ hi := by
    intro w hw heq; subst heq
    exact projection_disjoint_of_disjoint t hwf hdisj hw hhi_mem
  have boundary_crossing : ∀ a b : Nat,
      lo < a → a < hi → (b < lo ∨ hi < b) →
      linked t.deps a b = true → t.isPlanar = false := by
    intro a b ha_lo ha_hi hb_out hab
    rcases hb_out with hb | hb
    · exact crossing_edges_not_planar t hwf.headIdx_lt hwf.depIdx_lt hb ha_lo ha_hi
        (linked_symm_val hab) hlink_v
    · exact crossing_edges_not_planar t hwf.headIdx_lt hwf.depIdx_lt ha_lo ha_hi hb
        hlink_v hab
  let P (w : Nat) (i : Nat) : Prop :=
    lo < iterParent_uh t w i ∧ iterParent_uh t w i < hi
  have not_inside_is_outside : ∀ (w : Nat) (k : Nat) (hiter : iterParent_uh t w k = u)
      (hchain : ∀ i, i < k → ∃ dep,
        t.deps.find? (fun d => d.depIdx == iterParent_uh t w i) = some dep ∧
        dep.headIdx = iterParent_uh t w (i + 1))
      (i : Nat) (hik : i ≤ k) (hnp : ¬P w i),
      iterParent_uh t w i < lo ∨ hi < iterParent_uh t w i := by
    intro w k hiter hchain i hik hnp
    have hmem := iterParent_chain_mem_projection t hiter hchain i hik
    have hne_lo := ne_lo _ hmem
    have hne_hi := ne_hi _ hmem
    by_contra hc; push_neg at hc
    exact hnp ⟨by omega, by omega⟩
  by_cases hu_inside : lo < u ∧ u < hi
  · have hz_ne_u : z ≠ u := by
      intro h; subst h; rcases hz_out with h | h <;> omega
    obtain ⟨k, hk_pos, hiter_k, hchain_k⟩ :=
      dominates_iterParent_uh t hwf (dominates_of_mem_projection hz_mem) hz_ne_u.symm
    have h0_out : ¬P z 0 := by
      simp only [P, iterParent_uh]
      rcases hz_out with h | h <;> omega
    have hk_in : P z k := by
      simp only [P, hiter_k]; exact hu_inside
    obtain ⟨j, hj_lt, hj_out, hj1_in⟩ :=
      find_entry_step hk_pos (P z) h0_out hk_in
    simp only [P] at hj1_in
    have hj_out' := not_inside_is_outside z k hiter_k hchain_k j (by omega) hj_out
    exact boundary_crossing (iterParent_uh t z (j + 1)) (iterParent_uh t z j)
      hj1_in.1 hj1_in.2 hj_out' (linked_symm_val (iterParent_chain_linked hchain_k j hj_lt))
  · push_neg at hu_inside
    have hx_ne_u : x ≠ u := by
      intro h; subst h; exact absurd hx_hi (not_lt.mpr (hu_inside hx_lo))
    obtain ⟨k, hk_pos, hiter_k, hchain_k⟩ :=
      dominates_iterParent_uh t hwf (dominates_of_mem_projection hx_mem) hx_ne_u.symm
    have h0_in : P x 0 := by
      simp only [P, iterParent_uh]; exact ⟨hx_lo, hx_hi⟩
    have hk_out : ¬P x k := by
      simp only [P, hiter_k]; intro ⟨h1, h2⟩; exact absurd h2 (not_lt.mpr (hu_inside h1))
    obtain ⟨j, hj_lt, hj_in, hj1_out⟩ :=
      find_exit_step hk_pos (P x) h0_in hk_out
    simp only [P] at hj_in
    have hj1_out' := not_inside_is_outside x k hiter_k hchain_k (j + 1) (by omega) hj1_out
    exact boundary_crossing (iterParent_uh t x j) (iterParent_uh t x (j + 1))
      hj_in.1 hj_in.2 hj1_out' (iterParent_chain_linked hchain_k j hj_lt)

/-- Interleaving projections of disjoint subtrees witness non-planarity. -/
private theorem interleaving_not_planar (t : DepTree)
    (hwf : t.WF)
    {u v : Nat} (hdisj : disjoint t.deps u v = true)
    {l₁ l₂ r₁ r₂ : Nat}
    (hl₁ : l₁ ∈ projection t.deps u) (hr₁ : r₁ ∈ projection t.deps u)
    (hl₂ : l₂ ∈ projection t.deps v) (hr₂ : r₂ ∈ projection t.deps v)
    (hord : l₁ < l₂ ∧ l₂ < r₁ ∧ r₁ < r₂) :
    t.isPlanar = false := by
  obtain ⟨h12, h23, h34⟩ := hord
  obtain ⟨p₂, c₂, hlink₂, hp₂_mem, hc₂_mem, hp₂_lt, hc₂_ge⟩ :=
    exists_spanning_edge hl₂ hr₂ h23 (Nat.le_of_lt h34)
  have hc₂_gt : r₁ < c₂ := by
    rcases Nat.eq_or_lt_of_le hc₂_ge with heq | hlt
    · exfalso; rw [← heq] at hc₂_mem
      exact projection_disjoint_of_disjoint t hwf hdisj hr₁ hc₂_mem
    · exact hlt
  obtain ⟨p₁, c₁, hlink₁, hp₁_mem, hc₁_mem, hp₁_lt, hc₁_ge⟩ :=
    exists_spanning_edge hl₁ hr₁ (by omega : l₁ < l₂ + 1) (by omega : l₂ + 1 ≤ r₁)
  have hp₁_lt_l₂ : p₁ < l₂ := by
    have : p₁ ≤ l₂ := by omega
    rcases Nat.eq_or_lt_of_le this with heq | hlt
    · exfalso; rw [heq] at hp₁_mem
      exact projection_disjoint_of_disjoint t hwf hdisj hp₁_mem hl₂
    · exact hlt
  have hc₁_gt_l₂ : l₂ < c₁ := by omega
  by_cases hpc : p₂ < c₁
  · by_cases hac : p₁ < p₂
    · by_cases hbd : c₁ < c₂
      · exact crossing_edges_not_planar t hwf.headIdx_lt hwf.depIdx_lt hac hpc hbd hlink₁ hlink₂
      · have hc₁_ge_c₂ : c₂ ≤ c₁ := by omega
        have hc₂_ne : c₂ ≠ c₁ := by
          intro heq; rw [← heq] at hc₁_mem
          exact projection_disjoint_of_disjoint t hwf hdisj hc₁_mem hc₂_mem
        have hc₁_gt_c₂ : c₂ < c₁ := by omega
        exact escape_gives_crossing t hwf hdisj
          (by omega : p₂ < c₂) hlink₂ hp₂_mem hc₂_mem
          hr₁ hp₂_lt hc₂_gt hp₁_mem (Or.inl (by omega : p₁ < p₂))
    · have hp₂_lt_p₁ : p₂ < p₁ := by
        have : p₂ ≤ p₁ := by omega
        rcases Nat.eq_or_lt_of_le this with heq | hlt
        · exfalso; rw [heq] at hp₂_mem
          exact projection_disjoint_of_disjoint t hwf hdisj hp₁_mem hp₂_mem
        · exact hlt
      by_cases hbd : c₂ < c₁
      · have hp₁_lt_c₂ : p₁ < c₂ := by omega
        exact crossing_edges_not_planar t hwf.headIdx_lt hwf.depIdx_lt hp₂_lt_p₁ hp₁_lt_c₂ hbd hlink₂ hlink₁
      · have hc₂_ge_c₁ : c₁ ≤ c₂ := by omega
        exact escape_gives_crossing t hwf
          (disjoint_symm hdisj)
          (by omega : p₁ < c₁) hlink₁ hp₁_mem hc₁_mem
          hl₂ hp₁_lt_l₂ hc₁_gt_l₂ hp₂_mem (Or.inl hp₂_lt_p₁)
  · have hc₁_le_p₂ : c₁ ≤ p₂ := by omega
    have hc₁_lt_p₂ : c₁ < p₂ := by
      rcases Nat.eq_or_lt_of_le hc₁_le_p₂ with heq | hlt
      · exfalso; rw [← heq] at hp₂_mem
        exact projection_disjoint_of_disjoint t hwf hdisj hc₁_mem hp₂_mem
      · exact hlt
    exact escape_gives_crossing t hwf hdisj
      (by omega : p₂ < c₂) hlink₂ hp₂_mem hc₂_mem
      hr₁ hp₂_lt hc₂_gt hc₁_mem (Or.inl hc₁_lt_p₂)

/-- **Planar ⊂ well-nested** for well-formed trees.
    ([kuhlmann-nivre-2006], Theorem 1) -/
theorem planar_implies_wellNested (t : DepTree)
    (hwf : t.WF)
    (hplanar : t.isPlanar = true) : t.isWellNested = true := by
  by_contra h_nwn
  have h_false : t.isWellNested = false := by
    cases h : t.isWellNested with | true => exact absurd h h_nwn | false => rfl
  simp only [DepTree.isWellNested, Bool.not_eq_true'] at h_false
  have h_any : (List.range t.words.length |>.any fun u =>
    List.range t.words.length |>.any fun v =>
      u != v && disjoint t.deps u v &&
      projectionsInterleave (projection t.deps u) (projection t.deps v)) = true := by
    cases h : (List.range t.words.length |>.any _) with
    | true => rfl
    | false => simp [h] at h_false
  rw [List.any_eq_true] at h_any
  obtain ⟨u, _, h_u⟩ := h_any
  rw [List.any_eq_true] at h_u
  obtain ⟨v, _, h_uv⟩ := h_u
  simp only [Bool.and_eq_true] at h_uv
  obtain ⟨⟨_, hdisj⟩, hinterleave⟩ := h_uv
  simp only [projectionsInterleave] at hinterleave
  rw [List.any_eq_true] at hinterleave
  obtain ⟨l₁, hl₁, h_rest⟩ := hinterleave
  rw [List.any_eq_true] at h_rest
  obtain ⟨l₂, hl₂, h_rest2⟩ := h_rest
  rw [List.any_eq_true] at h_rest2
  obtain ⟨r₁, hr₁, h_rest3⟩ := h_rest2
  rw [List.any_eq_true] at h_rest3
  obtain ⟨r₂, hr₂, hords⟩ := h_rest3
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hords
  obtain ⟨⟨h1, h2⟩, h3⟩ := hords
  have h_not_planar := interleaving_not_planar t hwf
    hdisj hl₁ hr₁ hl₂ hr₂ ⟨h1, h2, h3⟩
  rw [hplanar] at h_not_planar; exact absurd h_not_planar (by decide)

/-! ### Bridge to `gapDegree` -/

/-- Non-projective ⇒ gap degree ≥ 1. Contrapositive of
    `projective_iff_gapDegree_zero`. -/
theorem nonProjective_implies_gapDeg_ge1 (t : DepTree)
    (h : isProjective t = false) : t.gapDegree ≥ 1 := by
  by_contra hlt
  have hzero : t.gapDegree = 0 := by omega
  have := (projective_iff_gapDegree_zero t).mpr hzero
  simp [this] at h

end DepGrammar
