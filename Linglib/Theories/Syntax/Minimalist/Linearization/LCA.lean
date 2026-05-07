import Linglib.Theories.Syntax.Minimalist.Basic
import Linglib.Theories.Syntax.Minimalist.HeadFunction

/-!
# Linear Correspondence Axiom
@cite{chomsky-1995} @cite{kayne-1994}

Formalizes the core of @cite{kayne-1994}'s *The Antisymmetry of Syntax*: the
Linear Correspondence Axiom (LCA), which derives linear (temporal)
precedence of terminal elements from asymmetric c-command in the
hierarchical structure.

## Key definitions

- `dominatedTerminals`: d(X) — the set of terminals dominated by X
  (alias for `terminalNodes` from `Basic.lean`). Noncomputable in
  Phase 1.0 because `terminalNodes` is.
- `lcaPrecedesIn`: the derived precedence relation on terminals
- `SatisfiesLCAIn`: the LCA as a well-formedness condition (strict total order)

## Main results

- **Outer precedes inner** (`outer_precedes_inner`): in `[x [y z]]` where
  all three are leaves, `x` precedes both `y` and `z`
- **Specifier precedes head and complement** (`spec_precedes_head_complement`):
  alias for `outer_precedes_inner`
- **Head precedes complement internals** (`head_precedes_complement`):
  alias for `outer_precedes_inner`
- **No right specifier** (`no_right_specifier`)
- **Adjunction is left-adjunction** (`adjunction_left_only`)
- **Sister terminals are unordered** (`sister_terminals_unordered`)

## Phase 1.0 status

This file uses `terminalNodes` and `linearize`, both of which became
noncomputable in the FreeCommMagma migration (planar order is not
preserved by the substrate's commutativity quotient). The LCA itself is
intrinsically planar, so this entire module's *concrete* computational
content (e.g., the Examples section) has been moved to `sorry` /
removed pending a Phase 2 LCA-based planarization. The theorems about
`lcaPrecedesIn` survive because they reduce to membership facts about
`subtrees` (now `Multiset`) and `immediatelyContains` / `cCommandsIn`,
which remain decidable.

-/

namespace Minimalist

open SyntacticObject

/-- Leaves are injective on `LIToken`. Phase 1.0 helper for proofs that
    previously used `injection` directly on the `.leaf` constructor —
    now that `.leaf` is an abbrev around `FreeCommMagma.of (.inl _)`,
    the `injection` tactic doesn't pierce the quotient. We extract via
    `getLIToken` instead. -/
private theorem leaf_inj {a b : LIToken}
    (h : (.leaf a : SyntacticObject) = .leaf b) : a = b := by
  have hgi : SyntacticObject.getLIToken (.leaf a) = SyntacticObject.getLIToken (.leaf b) :=
    congrArg _ h
  simp only [SyntacticObject.getLIToken_leaf] at hgi
  exact (Option.some.injEq _ _).mp hgi

-- ============================================================================
-- Part 1: Kayne's Formal Apparatus
-- ============================================================================

/-- d(X): the set of terminals dominated by (or equal to) X.
    Corresponds to Kayne's d function (p. 16). Noncomputable in Phase
    1.0 because `terminalNodes` lifts via `Quot.out`. The Phase 2
    parameterized variant is `dominatedTerminalsWith h` (below). -/
noncomputable def dominatedTerminals : SyntacticObject → List SyntacticObject :=
  terminalNodes

/-- Parameterized d(X) under head function `h`: the terminals of `h.externalize X`
    in left-to-right order. Computable when `h.externalize` is. Alias for
    `HeadFunction.terminalNodesWith`. -/
def dominatedTerminalsWith (h : HeadFunction) : SyntacticObject → List SyntacticObject :=
  HeadFunction.terminalNodesWith h

/-- Tree-relative LCA precedence.
    Terminal `a` precedes terminal `b` within `root` iff there exist
    subterms X, Y of `root` such that X asymmetrically c-commands Y
    (within `root`), `a ∈ d(X)`, and `b ∈ d(Y)`. -/
def lcaPrecedesIn (root a b : SyntacticObject) : Prop :=
  ∃ x y, x ∈ root.subtrees ∧ y ∈ root.subtrees ∧
    asymCCommandsIn root x y ∧
    a ∈ dominatedTerminals x ∧ b ∈ dominatedTerminals y

/-- The LCA holds for a tree `root` iff `lcaPrecedesIn root` is a strict
    total order on its terminal nodes: irreflexive, transitive, and
    total (every pair of distinct terminals is ordered). -/
structure SatisfiesLCAIn (root : SyntacticObject) : Prop where
  /-- No terminal precedes itself. -/
  irrefl : ∀ t, t ∈ terminalNodes root → ¬lcaPrecedesIn root t t
  /-- Precedence is transitive. -/
  trans : ∀ a b c, a ∈ terminalNodes root → b ∈ terminalNodes root →
    c ∈ terminalNodes root →
    lcaPrecedesIn root a b → lcaPrecedesIn root b c → lcaPrecedesIn root a c
  /-- Every pair of distinct terminals is ordered. -/
  total : ∀ a b, a ∈ terminalNodes root → b ∈ terminalNodes root →
    a ≠ b → lcaPrecedesIn root a b ∨ lcaPrecedesIn root b a

-- ============================================================================
-- Part 2: Core LCA Theorems
-- ============================================================================

/-- In `root = node x (node y z)`, `x` c-commands `y` within `root`.
    Works for arbitrary SOs, not just leaves. -/
theorem outer_cCommandsIn_inner_left (x y z : SyntacticObject)
    (hne : x ≠ .node y z) :
    cCommandsIn (.node x (.node y z)) x y := by
  -- cCommandsIn root x y := ∃ z ∈ root.subtrees, areSistersIn root x z ∧ containsOrEq z y
  refine ⟨.node y z, ?_, ⟨.node x (.node y z), self_mem_subtrees _,
    (immediatelyContains_mul _ _ _).mpr (Or.inl rfl),
    (immediatelyContains_mul _ _ _).mpr (Or.inr rfl), hne⟩,
    Or.inr (contains.imm _ _ ((immediatelyContains_mul _ _ _).mpr (Or.inl rfl)))⟩
  -- .node y z ∈ (.node x (.node y z)).subtrees
  have hyz : (.node y z : SyntacticObject) ∈ (.node y z : SyntacticObject).subtrees :=
    self_mem_subtrees _
  simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons, Multiset.mem_add]
  tauto


/-- In `root = node x (node y z)`, `x` c-commands `z` within `root`.
    Works for arbitrary SOs, not just leaves. -/
theorem outer_cCommandsIn_inner_right (x y z : SyntacticObject)
    (hne : x ≠ .node y z) :
    cCommandsIn (.node x (.node y z)) x z := by
  refine ⟨.node y z, ?_, ⟨.node x (.node y z), self_mem_subtrees _,
    (immediatelyContains_mul _ _ _).mpr (Or.inl rfl),
    (immediatelyContains_mul _ _ _).mpr (Or.inr rfl), hne⟩,
    Or.inr (contains.imm _ _ ((immediatelyContains_mul _ _ _).mpr (Or.inr rfl)))⟩
  have hyz : (.node y z : SyntacticObject) ∈ (.node y z : SyntacticObject).subtrees :=
    self_mem_subtrees _
  simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons, Multiset.mem_add]
  tauto

/-- An inner leaf does not c-command the outer leaf in a three-leaf tree.
    Unifies the four negative c-command proofs (head→spec, compl→spec,
    a→head, b→head) into one: the inner leaf's only sister is the other
    inner leaf, which neither equals nor contains the outer leaf. -/
private theorem inner_not_cCommandsIn_outer (s h c : LIToken)
    (hne_sh : s ≠ h) (hne_sc : s ≠ c) (hne_hc : h ≠ c)
    (inner : LIToken) (hinner : inner = h ∨ inner = c) :
    ¬cCommandsIn (.node (.leaf s) (.node (.leaf h) (.leaf c))) (.leaf inner) (.leaf s) := by
  intro ⟨z, _hz_mem, ⟨w, hw_mem, hw_inner, hw_z, hne_iz⟩, hz_s⟩
  -- Subtrees of `(.leaf s) * ((.leaf h) * (.leaf c))`:
  -- the root, .leaf s, (.leaf h) * (.leaf c), .leaf h, .leaf c
  simp only [SyntacticObject.subtrees_mul, SyntacticObject.subtrees_leaf,
    Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton] at hw_mem
  rcases hw_mem with rfl | (rfl | (rfl | (rfl | rfl)))
  · -- w = root: inner can't be a daughter of root
    rw [immediatelyContains_mul] at hw_inner
    rcases hw_inner with hinj | hinj
    · have hinj' : inner = s := leaf_inj hinj
      rcases hinner with rfl | rfl
      · exact hne_sh hinj'.symm
      · exact hne_sc hinj'.symm
    · -- hinj : .leaf inner = .node (.leaf h) (.leaf c) — impossible
      exact absurd (hinj ▸ (SyntacticObject.isLeaf_leaf inner).mpr trivial)
        (SyntacticObject.isLeaf_mul _ _)
  · exact immediatelyContains_leaf _ _ hw_inner -- w = .leaf s
  · -- w = .node (.leaf h) (.leaf c): z is the other daughter
    rw [immediatelyContains_mul] at hw_inner
    rcases hinner with rfl | rfl
    · -- inner = h
      rcases hw_inner with hh1 | hh2
      · -- .leaf h = .leaf h: hw_z says z = .leaf h or z = .leaf c
        rw [immediatelyContains_mul] at hw_z
        rcases hw_z with hzh | hzc
        · exact hne_iz hzh.symm
        · subst hzc
          rcases hz_s with hsz | hsz
          · have : c = s := leaf_inj hsz
            exact hne_sc this.symm
          · exact leaf_contains_nothing c _ hsz
      · -- .leaf h = .leaf c — contradicts hne_hc
        exact hne_hc (leaf_inj hh2)
    · -- inner = c
      rcases hw_inner with hh1 | hh2
      · -- .leaf c = .leaf h — contradicts hne_hc
        exact hne_hc (leaf_inj hh1).symm
      · -- .leaf c = .leaf c
        rw [immediatelyContains_mul] at hw_z
        rcases hw_z with hzh | hzc
        · subst hzh
          rcases hz_s with hsz | hsz
          · have : h = s := leaf_inj hsz
            exact hne_sh this.symm
          · exact leaf_contains_nothing h _ hsz
        · exact hne_iz hzc.symm
  · exact immediatelyContains_leaf _ _ hw_inner -- w = .leaf h
  · exact immediatelyContains_leaf _ _ hw_inner -- w = .leaf c

/-- A leaf is in its own dominated terminals (Phase 1.0: noncomputable). -/
private theorem leaf_mem_dominatedTerminals (tok : LIToken) :
    SyntacticObject.leaf tok ∈ dominatedTerminals (.leaf tok) := by
  show SyntacticObject.leaf tok ∈ terminalNodes (SyntacticObject.leaf tok)
  rw [terminalNodes_leaf]
  exact List.mem_singleton.mpr rfl

/-- **Outer precedes inner under the LCA.** For `root = node (leaf x) (node (leaf y) (leaf z))`
    where all three are distinct leaves, `x` precedes both `y` and `z`
    in `lcaPrecedesIn root`.

    This is Kayne's key result (1994, pp. 35-36): the outer daughter
    asymmetrically c-commands everything in its sister's projection,
    so all its terminals precede all terminals of the inner daughters.

    Subsumes both "specifier precedes head/complement" and
    "head precedes complement internals". -/
theorem outer_precedes_inner (x y z : LIToken)
    (hne_xy : x ≠ y) (hne_xz : x ≠ z) (hne_yz : y ≠ z) :
    let root := SyntacticObject.node (.leaf x) (.node (.leaf y) (.leaf z))
    lcaPrecedesIn root (.leaf x) (.leaf y) ∧ lcaPrecedesIn root (.leaf x) (.leaf z) := by
  refine ⟨⟨.leaf x, .leaf y, ?_, ?_, ?_, ?_, ?_⟩,
          ⟨.leaf x, .leaf z, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- x precedes y: membership in subterms (Multiset)
  · -- (.leaf x) ∈ root.subtrees where root = (.leaf x).node ((.leaf y).node (.leaf z))
    simp only [SyntacticObject.subtrees_mul, SyntacticObject.subtrees_leaf,
      Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton]
    -- root = .leaf x or .leaf x ∈ {.leaf x} or ...
    tauto
  · simp only [SyntacticObject.subtrees_mul, SyntacticObject.subtrees_leaf,
      Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton]
    tauto
  · refine ⟨outer_cCommandsIn_inner_left _ _ _ (fun h => ?_),
           inner_not_cCommandsIn_outer x y z hne_xy hne_xz hne_yz y (Or.inl rfl)⟩
    exact absurd (h ▸ (SyntacticObject.isLeaf_leaf x).mpr trivial)
      (SyntacticObject.isLeaf_mul _ _)
  · exact leaf_mem_dominatedTerminals x
  · exact leaf_mem_dominatedTerminals y
  -- x precedes z: membership in subterms (Multiset)
  · simp only [SyntacticObject.subtrees_mul, SyntacticObject.subtrees_leaf,
      Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton]
    tauto
  · simp only [SyntacticObject.subtrees_mul, SyntacticObject.subtrees_leaf,
      Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton]
    tauto
  · refine ⟨outer_cCommandsIn_inner_right _ _ _ (fun h => ?_),
           inner_not_cCommandsIn_outer x y z hne_xy hne_xz hne_yz z (Or.inr rfl)⟩
    exact absurd (h ▸ (SyntacticObject.isLeaf_leaf x).mpr trivial)
      (SyntacticObject.isLeaf_mul _ _)
  · exact leaf_mem_dominatedTerminals x
  · exact leaf_mem_dominatedTerminals z

/-- **Specifier precedes head and complement under the LCA.**
    Alias for `outer_precedes_inner` with conventional names. -/
theorem spec_precedes_head_complement (spec head compl : LIToken)
    (hne_sh : spec ≠ head) (hne_sc : spec ≠ compl) (hne_hc : head ≠ compl) :
    let root := SyntacticObject.node (.leaf spec) (.node (.leaf head) (.leaf compl))
    lcaPrecedesIn root (.leaf spec) (.leaf head) ∧
    lcaPrecedesIn root (.leaf spec) (.leaf compl) :=
  outer_precedes_inner spec head compl hne_sh hne_sc hne_hc

/-- **Head precedes complement internals.**
    Alias for `outer_precedes_inner` with conventional names. -/
theorem head_precedes_complement (head a b : LIToken)
    (hne_ha : head ≠ a) (hne_hb : head ≠ b) (hne_ab : a ≠ b) :
    let root := SyntacticObject.node (.leaf head) (.node (.leaf a) (.leaf b))
    lcaPrecedesIn root (.leaf head) (.leaf a) ∧
    lcaPrecedesIn root (.leaf head) (.leaf b) :=
  outer_precedes_inner head a b hne_ha hne_hb hne_ab

-- ============================================================================
-- Part 3: Structural Constraints Derived from the LCA
-- ============================================================================

-- 3a. No right specifier

/-- **Right specifiers are LCA-incompatible.** In `root = node (node head compl) spec`,
    `spec`'s sister is `node head compl`, which contains `head`. So `spec`
    c-commands `head`. But `head`'s sister (within the tree) is `compl`,
    which does not contain `spec` (spec is in the other branch).

    The LCA therefore orders spec's terminals BEFORE head's terminals.
    But the PF string has `head` before `spec` (right-specifier position).
    This contradiction means right specifiers are ruled out: the LCA
    forces specifiers to the left. -/
theorem no_right_specifier
    (head compl spec : SyntacticObject)
    (hne_hc_node : .node head compl ≠ spec) :
    let root := SyntacticObject.node (.node head compl) spec
    cCommandsIn root spec head := by
  refine ⟨.node head compl, ?_,
    ⟨.node (.node head compl) spec, self_mem_subtrees _,
     (immediatelyContains_mul _ _ _).mpr (Or.inr rfl),
     (immediatelyContains_mul _ _ _).mpr (Or.inl rfl),
     Ne.symm hne_hc_node⟩,
    Or.inr (contains.imm _ _ ((immediatelyContains_mul _ _ _).mpr (Or.inl rfl)))⟩
  -- .node head compl ∈ root.subtrees where root = .node (.node head compl) spec
  simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons, Multiset.mem_add]
  tauto

-- 3b. Adjunction asymmetry

/-- **Head-to-head adjunction must be left-adjunction (parameterized).**
    Under a head function `h` whose externalize section sends a node to the
    `*`-product of its children's externalizations, linearization concatenates
    in left-to-right order (mover then target).

    The hypothesis `h_ext_node : h.externalize (.node mover target) =
    h.externalize mover * h.externalize target` is the **local-magma-morphism
    property** at this specific node. MCB Lemma 1.13.1 rules out a *global*
    magma morphism `SO → SO^{nc}`, but a *particular* externalize choice can
    satisfy this property at any specific node — and consumers who supply a
    derivation-built externalize get this for free per construction.

    The unparameterized `adjunction_left_only` (currently sorry) cannot be
    proven without committing to an externalize: `Quot.out (.node mover target)`
    may pick either `mover.out * target.out` or `target.out * mover.out`. -/
theorem adjunction_left_only_with
    (h : HeadFunction) (mover target : SyntacticObject)
    (h_ext_node : h.externalize (.node mover target) =
      h.externalize mover * h.externalize target) :
    HeadFunction.linearizeWith h (.node mover target) =
    HeadFunction.linearizeWith h mover ++ HeadFunction.linearizeWith h target := by
  show linearizePlanar (h.externalize (.node mover target)) =
    linearizePlanar (h.externalize mover) ++ linearizePlanar (h.externalize target)
  rw [h_ext_node]
  rfl

/-- **Head-to-head adjunction must be left-adjunction (legacy unparameterized).**
    The Phase 1.0 statement on the bare `linearize` (= `linearizeWith leftSpine`).
    Cannot be proven without committing to an externalize choice — see
    `adjunction_left_only_with` for the principled parameterized version that
    requires a local-magma-morphism hypothesis on the externalize section. -/
theorem adjunction_left_only
    (mover target : SyntacticObject) :
    linearize (.node mover target) =
    linearize mover ++ linearize target := by
  -- Cannot be proven on the bare `linearize`: `Quot.out (.node mover target)`
  -- may pick either `mover.out * target.out` or `target.out * mover.out`,
  -- giving different concatenation orders. Use `adjunction_left_only_with`
  -- with a `HeadFunction` whose externalize respects the merge structure
  -- locally.
  sorry

-- ============================================================================
-- Part 4: Sister-Terminal Limitation
-- ============================================================================

/-- **Sister terminals are unordered by the LCA.** For `root = node (leaf a) (leaf b)`,
    `leaf a` and `leaf b` are sisters: each c-commands the other (via
    its sister). So neither asymmetrically c-commands the other, and
    `lcaPrecedesIn` does not order them.

    This is not a defect but a feature: in well-formed BPS, sister
    terminals don't arise. Complements are always phrases (nodes), and
    heads project, so the complement of a head is always `node X Y`, not
    a bare leaf. -/
theorem sister_terminals_unordered (a b : LIToken) (hne : a ≠ b) :
    ¬asymCCommandsIn (.node (.leaf a) (.leaf b)) (.leaf a) (.leaf b) := by
  intro ⟨_, hno⟩
  apply hno
  -- cCommandsIn root b a := ∃ z ∈ root.subtrees, areSistersIn root b z ∧ containsOrEq z a
  refine ⟨.leaf a, ?_, ?_, Or.inl rfl⟩
  · -- .leaf a ∈ root.subtrees
    simp only [SyntacticObject.subtrees_mul, SyntacticObject.subtrees_leaf,
      Multiset.mem_cons, Multiset.mem_add, Multiset.mem_singleton]
    tauto
  · -- areSistersIn root b a
    refine ⟨.node (.leaf a) (.leaf b), self_mem_subtrees _,
            (immediatelyContains_mul _ _ _).mpr (Or.inr rfl),
            (immediatelyContains_mul _ _ _).mpr (Or.inl rfl), ?_⟩
    intro h
    exact hne (leaf_inj h).symm

end Minimalist
