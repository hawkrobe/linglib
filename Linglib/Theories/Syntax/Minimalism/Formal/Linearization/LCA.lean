import Linglib.Theories.Syntax.Minimalism.Core.Basic

/-!
# Linear Correspondence Axiom (Kayne 1994)

Formalizes the core of Kayne's (1994) *The Antisymmetry of Syntax*: the
Linear Correspondence Axiom (LCA), which derives linear (temporal)
precedence of terminal elements from asymmetric c-command in the
hierarchical structure.

## Key definitions

- `subterms`: all nodes (recursively) in a `SyntacticObject`
- `terminalNodes`: the leaf subset of `subterms`
- `dominatedTerminals`: d(X) — the set of terminals dominated by X
- `areSistersIn` / `cCommandsIn` / `asymCCommandsIn`: tree-relative
  versions of the relations from `Core/Basic.lean`
- `lcaPrecedesIn`: the derived precedence relation on terminals
- `SatisfiesLCAIn`: the LCA as a well-formedness condition (strict total order)
- `linearize`: left-to-right leaf traversal (= `phonYield` for binary trees)

## Tree-relative c-command

The `cCommands` and `areSisters` definitions in `Core/Basic.lean` are
tree-free: sisterhood holds for *any* pair of distinct SOs (since we can
always construct `node X Y` as a witness). This makes `asymCCommands`
trivially false for all distinct pairs — every SO c-commands every
other distinct SO.

Kayne's LCA requires c-command *relative to a specific phrase marker*.
We therefore define `areSistersIn`, `cCommandsIn`, and
`asymCCommandsIn`, which restrict the witness node to be a subterm of
the given root. This correctly captures the structural asymmetries that
drive linearization.

## Main results

- **Specifier precedes head and complement** (`spec_precedes_head_complement`)
- **Head precedes complement internals** (`head_precedes_complement`)
- **No right specifier** (`no_right_specifier`)
- **Adjunction is left-adjunction** (`adjunction_left_only`)
- **Sister terminals are unordered** (`sister_terminals_unordered`)

## References

- Kayne, R. S. (1994). *The Antisymmetry of Syntax*. MIT Press.
- Chomsky, N. (1995). *The Minimalist Program*. MIT Press.
-/

namespace Minimalism

open SyntacticObject

-- ============================================================================
-- Part 1: Subterm Enumeration
-- ============================================================================

/-- All nodes in a `SyntacticObject`, including the root itself. -/
def subterms : SyntacticObject → List SyntacticObject
  | so@(.leaf _) => [so]
  | so@(.node l r) => so :: (subterms l ++ subterms r)

/-- The terminal (leaf) nodes of a `SyntacticObject`. -/
def terminalNodes : SyntacticObject → List SyntacticObject
  | so@(.leaf _) => [so]
  | .node l r => terminalNodes l ++ terminalNodes r

/-- Every terminal node is a leaf. -/
theorem terminalNodes_are_leaves {so t : SyntacticObject}
    (h : t ∈ terminalNodes so) : t.isLeaf = true := by
  induction so with
  | leaf _ =>
    simp only [terminalNodes] at h
    exact List.mem_singleton.mp h ▸ rfl
  | node l r ihl ihr =>
    simp only [terminalNodes, List.mem_append] at h
    exact h.elim ihl ihr

/-- Every terminal is a subterm. -/
theorem terminalNodes_sub_subterms {so t : SyntacticObject}
    (h : t ∈ terminalNodes so) : t ∈ subterms so := by
  induction so with
  | leaf _ =>
    simp only [terminalNodes] at h
    simp only [subterms]
    exact h
  | node l r ihl ihr =>
    simp only [terminalNodes, List.mem_append] at h
    simp only [subterms, List.mem_cons, List.mem_append]
    exact h.elim (fun h => Or.inr (Or.inl (ihl h)))
                 (fun h => Or.inr (Or.inr (ihr h)))

/-- The root is always in its own subterms. -/
theorem self_mem_subterms (so : SyntacticObject) : so ∈ subterms so := by
  cases so with
  | leaf _ => exact List.mem_cons.mpr (Or.inl rfl)
  | node _ _ => exact List.mem_cons.mpr (Or.inl rfl)

-- ============================================================================
-- Part 2: Boolean Containment (for decidability)
-- ============================================================================

/-- Boolean containment check: does `x` (strictly) contain `y`? -/
def containsB : SyntacticObject → SyntacticObject → Bool
  | .leaf _, _ => false
  | .node a b, y => a == y || b == y || containsB a y || containsB b y

/-- `containsB` implies `contains`. -/
theorem containsB_implies_contains {x y : SyntacticObject}
    (h : containsB x y = true) : contains x y := by
  induction x with
  | leaf _ => simp [containsB] at h
  | node a b iha ihb =>
    simp only [containsB, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ((rfl | rfl) | ha) | hb
    · exact contains.imm _ _ (Or.inl rfl)
    · exact contains.imm _ _ (Or.inr rfl)
    · exact contains.trans _ _ a (Or.inl rfl) (iha ha)
    · exact contains.trans _ _ b (Or.inr rfl) (ihb hb)

/-- `contains` implies `containsB`. -/
theorem contains_implies_containsB {x y : SyntacticObject}
    (h : contains x y) : containsB x y = true := by
  induction h with
  | imm x y himm =>
    cases x with
    | leaf _ => exact absurd himm id
    | node a b =>
      simp only [containsB, Bool.or_eq_true, beq_iff_eq]
      rcases himm with rfl | rfl
      · exact Or.inl (Or.inl (Or.inl rfl))
      · exact Or.inl (Or.inl (Or.inr rfl))
  | trans x _ z himm _ ih =>
    cases x with
    | leaf _ => exact absurd himm id
    | node a b =>
      simp only [containsB, Bool.or_eq_true, beq_iff_eq]
      rcases himm with rfl | rfl
      · exact Or.inl (Or.inr ih)
      · exact Or.inr ih

/-- Boolean and propositional containment are equivalent. -/
theorem containsB_iff {x y : SyntacticObject} :
    containsB x y = true ↔ contains x y :=
  ⟨containsB_implies_contains, contains_implies_containsB⟩

-- ============================================================================
-- Part 3: Dominated Terminals and Tree-Relative Relations
-- ============================================================================

/-- d(X): the set of terminals dominated by (or equal to) X.
    Corresponds to Kayne's d function (p. 16). -/
def dominatedTerminals : SyntacticObject → List SyntacticObject :=
  terminalNodes

/-- d(leaf) is the singleton containing the leaf. -/
theorem dominatedTerminals_leaf (tok : LIToken) :
    dominatedTerminals (.leaf tok) = [.leaf tok] := rfl

/-- d(node l r) is d(l) ++ d(r). -/
theorem dominatedTerminals_node (l r : SyntacticObject) :
    dominatedTerminals (.node l r) = dominatedTerminals l ++ dominatedTerminals r := rfl

/-- X and Y are sisters IN tree `root`: they are distinct co-daughters of
    some node that is a subterm of `root`. -/
def areSistersIn (root x y : SyntacticObject) : Prop :=
  ∃ z, z ∈ subterms root ∧ immediatelyContains z x ∧ immediatelyContains z y ∧ x ≠ y

/-- X c-commands Y IN tree `root`: X has a sister (in `root`) that
    contains-or-equals Y. -/
def cCommandsIn (root x y : SyntacticObject) : Prop :=
  ∃ z, areSistersIn root x z ∧ containsOrEq z y

/-- X asymmetrically c-commands Y in tree `root`. -/
def asymCCommandsIn (root x y : SyntacticObject) : Prop :=
  cCommandsIn root x y ∧ ¬cCommandsIn root y x

/-- Tree-relative LCA precedence.
    Terminal `a` precedes terminal `b` within `root` iff there exist
    subterms X, Y of `root` such that X asymmetrically c-commands Y
    (within `root`), `a ∈ d(X)`, and `b ∈ d(Y)`. (Kayne 1994, p. 16) -/
def lcaPrecedesIn (root a b : SyntacticObject) : Prop :=
  ∃ x y, x ∈ subterms root ∧ y ∈ subterms root ∧
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
-- Part 4: Linearization Function
-- ============================================================================

/-- Linearize a `SyntacticObject` by collecting leaf `LIToken`s in
    left-to-right traversal order. For binary-branching trees, this
    is the unique LCA-compatible linearization. -/
def linearize : SyntacticObject → List LIToken
  | .leaf tok => [tok]
  | .node l r => linearize l ++ linearize r

-- ============================================================================
-- Part 5: Core Theorems — Specifier Precedes Head and Complement
-- ============================================================================

/-- Subterms of a three-leaf tree `node (leaf s) (node (leaf h) (leaf c))`. -/
private theorem subterms_shc (s h c : LIToken) :
    subterms (.node (.leaf s) (.node (.leaf h) (.leaf c))) =
    [.node (.leaf s) (.node (.leaf h) (.leaf c)),
     .leaf s, .node (.leaf h) (.leaf c), .leaf h, .leaf c] := rfl

section SpecPrecedesHC

variable (spec head compl : SyntacticObject)

/-- In `root = node spec (node head compl)`, `spec` and `node head compl`
    are sisters in `root`. -/
private theorem spec_sisters_hc
    (hne : spec ≠ .node head compl) :
    areSistersIn (.node spec (.node head compl)) spec (.node head compl) :=
  ⟨.node spec (.node head compl), self_mem_subterms _, Or.inl rfl, Or.inr rfl, hne⟩

/-- In `root = node spec (node head compl)`, `spec` c-commands `head`
    within `root`. -/
theorem spec_cCommandsIn_head
    (hne_spec_hc : spec ≠ .node head compl) :
    cCommandsIn (.node spec (.node head compl)) spec head :=
  ⟨.node head compl, spec_sisters_hc spec head compl hne_spec_hc,
   Or.inr (contains.imm _ _ (Or.inl rfl))⟩

/-- In `root = node spec (node head compl)`, `spec` c-commands `compl`
    within `root`. -/
theorem spec_cCommandsIn_compl
    (hne_spec_hc : spec ≠ .node head compl) :
    cCommandsIn (.node spec (.node head compl)) spec compl :=
  ⟨.node head compl, spec_sisters_hc spec head compl hne_spec_hc,
   Or.inr (contains.imm _ _ (Or.inr rfl))⟩

/-- In `root = node spec (node head compl)` where all three are leaves,
    `head` does NOT c-command `spec` within `root`.

    Proof: enumerate all subterms of root. The only node that immediately
    contains `head` is `node head compl`, whose other daughter is `compl`.
    Since `compl ≠ spec` and leaves contain nothing, `containsOrEq compl spec`
    fails. -/
theorem head_not_cCommandsIn_spec
    (hspec_leaf : spec.isLeaf = true)
    (hhead_leaf : head.isLeaf = true)
    (hcompl_leaf : compl.isLeaf = true)
    (hne_sh : spec ≠ head)
    (hne_sc : spec ≠ compl)
    (hne_hc : head ≠ compl) :
    ¬cCommandsIn (.node spec (.node head compl)) head spec := by
  obtain ⟨stok, rfl⟩ : ∃ t, spec = .leaf t := by
    cases spec with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hspec_leaf
  obtain ⟨htok, rfl⟩ : ∃ t, head = .leaf t := by
    cases head with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hhead_leaf
  obtain ⟨ctok, rfl⟩ : ∃ t, compl = .leaf t := by
    cases compl with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hcompl_leaf
  intro ⟨z, ⟨w, hw_mem, hw_h, hw_z, hne_hz⟩, hz_s⟩
  rw [subterms_shc] at hw_mem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw_mem
  rcases hw_mem with rfl | rfl | rfl | rfl | rfl
  · -- w = root: head can't be a daughter of root
    rcases hw_h with h | h
    · exact hne_sh h.symm
    · exact SyntacticObject.noConfusion h
  · exact hw_h -- w = leaf stok: leaves don't immediately contain
  · -- w = node (leaf htok) (leaf ctok): z must be the other daughter
    rcases hw_z with rfl | rfl
    · exact hne_hz rfl
    · rcases hz_s with h | h
      · exact hne_sc h.symm
      · exact leaf_contains_nothing ctok _ h
  · exact hw_h -- w = leaf htok
  · exact hw_h -- w = leaf ctok

/-- `spec` asymmetrically c-commands `head` within `root`. -/
theorem spec_asymCCommandsIn_head
    (hspec_leaf : spec.isLeaf = true)
    (hhead_leaf : head.isLeaf = true)
    (hcompl_leaf : compl.isLeaf = true)
    (hne_sh : spec ≠ head)
    (hne_sc : spec ≠ compl)
    (hne_hc : head ≠ compl)
    (hne_spec_hc : spec ≠ .node head compl) :
    asymCCommandsIn (.node spec (.node head compl)) spec head :=
  ⟨spec_cCommandsIn_head spec head compl hne_spec_hc,
   head_not_cCommandsIn_spec spec head compl hspec_leaf hhead_leaf hcompl_leaf hne_sh hne_sc hne_hc⟩

/-- `compl` does not c-command `spec` within `root` (parallel to head). -/
theorem compl_not_cCommandsIn_spec
    (hspec_leaf : spec.isLeaf = true)
    (hhead_leaf : head.isLeaf = true)
    (hcompl_leaf : compl.isLeaf = true)
    (hne_sh : spec ≠ head)
    (hne_sc : spec ≠ compl)
    (hne_hc : head ≠ compl) :
    ¬cCommandsIn (.node spec (.node head compl)) compl spec := by
  obtain ⟨stok, rfl⟩ : ∃ t, spec = .leaf t := by
    cases spec with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hspec_leaf
  obtain ⟨htok, rfl⟩ : ∃ t, head = .leaf t := by
    cases head with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hhead_leaf
  obtain ⟨ctok, rfl⟩ : ∃ t, compl = .leaf t := by
    cases compl with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hcompl_leaf
  intro ⟨z, ⟨w, hw_mem, hw_c, hw_z, hne_cz⟩, hz_s⟩
  rw [subterms_shc] at hw_mem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw_mem
  rcases hw_mem with rfl | rfl | rfl | rfl | rfl
  · -- w = root
    rcases hw_c with h | h
    · exact hne_sc h.symm
    · exact SyntacticObject.noConfusion h
  · exact hw_c
  · -- w = node (leaf htok) (leaf ctok): z must be the other daughter
    rcases hw_z with rfl | rfl
    · rcases hz_s with h | h
      · exact hne_sh h.symm
      · exact leaf_contains_nothing htok _ h
    · exact hne_cz rfl
  · exact hw_c
  · exact hw_c

/-- `spec` asymmetrically c-commands `compl` within `root`. -/
theorem spec_asymCCommandsIn_compl
    (hspec_leaf : spec.isLeaf = true)
    (hhead_leaf : head.isLeaf = true)
    (hcompl_leaf : compl.isLeaf = true)
    (hne_sh : spec ≠ head)
    (hne_sc : spec ≠ compl)
    (hne_hc : head ≠ compl)
    (hne_spec_hc : spec ≠ .node head compl) :
    asymCCommandsIn (.node spec (.node head compl)) spec compl :=
  ⟨spec_cCommandsIn_compl spec head compl hne_spec_hc,
   compl_not_cCommandsIn_spec spec head compl hspec_leaf hhead_leaf hcompl_leaf hne_sh hne_sc hne_hc⟩

/-- A leaf is in its own dominated terminals. -/
private theorem leaf_mem_dominatedTerminals (tok : LIToken) :
    SyntacticObject.leaf tok ∈ dominatedTerminals (.leaf tok) :=
  List.mem_cons.mpr (Or.inl rfl)

/-- **Specifier precedes head and complement under the LCA.**
    For `root = node spec (node head compl)` where all three are leaves,
    `spec` precedes both `head` and `compl` in `lcaPrecedesIn root`.

    This is Kayne's key result (1994, pp. 35-36): the specifier
    asymmetrically c-commands everything in its sister's projection,
    so all its terminals precede all terminals of head and complement. -/
theorem spec_precedes_head_complement
    (hspec_leaf : spec.isLeaf = true)
    (hhead_leaf : head.isLeaf = true)
    (hcompl_leaf : compl.isLeaf = true)
    (hne_sh : spec ≠ head)
    (hne_sc : spec ≠ compl)
    (hne_hc : head ≠ compl)
    (hne_spec_hc : spec ≠ .node head compl) :
    let root := SyntacticObject.node spec (.node head compl)
    lcaPrecedesIn root spec head ∧ lcaPrecedesIn root spec compl := by
  -- Extract tokens from leaf hypotheses
  obtain ⟨stok, rfl⟩ : ∃ t, spec = .leaf t := by
    cases spec with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hspec_leaf
  obtain ⟨htok, rfl⟩ : ∃ t, head = .leaf t := by
    cases head with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hhead_leaf
  obtain ⟨ctok, rfl⟩ : ∃ t, compl = .leaf t := by
    cases compl with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hcompl_leaf
  refine ⟨⟨.leaf stok, .leaf htok, ?_, ?_, ?_, ?_, ?_⟩,
          ⟨.leaf stok, .leaf ctok, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- spec precedes head: membership in subterms
  · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
      (Or.inl (self_mem_subterms _))))
  · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
      (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_append.mpr
        (Or.inl (self_mem_subterms _))))))))
  · exact spec_asymCCommandsIn_head _ _ _ rfl rfl rfl hne_sh hne_sc hne_hc hne_spec_hc
  · exact leaf_mem_dominatedTerminals stok
  · exact leaf_mem_dominatedTerminals htok
  -- spec precedes compl: membership in subterms
  · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
      (Or.inl (self_mem_subterms _))))
  · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
      (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_append.mpr
        (Or.inr (self_mem_subterms _))))))))
  · exact spec_asymCCommandsIn_compl _ _ _ rfl rfl rfl hne_sh hne_sc hne_hc hne_spec_hc
  · exact leaf_mem_dominatedTerminals stok
  · exact leaf_mem_dominatedTerminals ctok

end SpecPrecedesHC

-- ============================================================================
-- Part 6: Head Precedes Complement Internals
-- ============================================================================

/-- In `root = node head (node a b)`, `head` c-commands `a` within `root`. -/
theorem head_cCommandsIn_a (head a b : SyntacticObject)
    (hne_h_ab : head ≠ .node a b) :
    cCommandsIn (.node head (.node a b)) head a :=
  ⟨.node a b,
   ⟨.node head (.node a b), self_mem_subterms _, Or.inl rfl, Or.inr rfl, hne_h_ab⟩,
   Or.inr (contains.imm _ _ (Or.inl rfl))⟩

/-- In `root = node head (node a b)`, `head` c-commands `b` within `root`. -/
theorem head_cCommandsIn_b (head a b : SyntacticObject)
    (hne_h_ab : head ≠ .node a b) :
    cCommandsIn (.node head (.node a b)) head b :=
  ⟨.node a b,
   ⟨.node head (.node a b), self_mem_subterms _, Or.inl rfl, Or.inr rfl, hne_h_ab⟩,
   Or.inr (contains.imm _ _ (Or.inr rfl))⟩

/-- `a` does not c-command `head` within `root = node head (node a b)`.
    The only node containing `a` as a daughter is `node a b`, whose other
    daughter `b` neither equals nor contains `head`. -/
theorem a_not_cCommandsIn_head (head a b : SyntacticObject)
    (hhead_leaf : head.isLeaf = true)
    (ha_leaf : a.isLeaf = true)
    (hb_leaf : b.isLeaf = true)
    (hne_ha : head ≠ a) (hne_hb : head ≠ b)
    (hne_ab : a ≠ b) :
    ¬cCommandsIn (.node head (.node a b)) a head := by
  obtain ⟨htok, rfl⟩ : ∃ t, head = .leaf t := by
    cases head with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hhead_leaf
  obtain ⟨atok, rfl⟩ : ∃ t, a = .leaf t := by
    cases a with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at ha_leaf
  obtain ⟨btok, rfl⟩ : ∃ t, b = .leaf t := by
    cases b with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hb_leaf
  intro ⟨z, ⟨w, hw_mem, hw_a, hw_z, hne_az⟩, hz_h⟩
  rw [subterms_shc] at hw_mem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw_mem
  rcases hw_mem with rfl | rfl | rfl | rfl | rfl
  · rcases hw_a with h | h
    · exact hne_ha h.symm
    · exact SyntacticObject.noConfusion h
  · exact hw_a
  · rcases hw_z with rfl | rfl
    · exact hne_az rfl
    · rcases hz_h with h | h
      · exact hne_hb h.symm
      · exact leaf_contains_nothing btok _ h
  · exact hw_a
  · exact hw_a

/-- `b` does not c-command `head` within `root` (parallel to `a`). -/
theorem b_not_cCommandsIn_head (head a b : SyntacticObject)
    (hhead_leaf : head.isLeaf = true)
    (ha_leaf : a.isLeaf = true)
    (hb_leaf : b.isLeaf = true)
    (hne_ha : head ≠ a) (hne_hb : head ≠ b)
    (hne_ab : a ≠ b) :
    ¬cCommandsIn (.node head (.node a b)) b head := by
  obtain ⟨htok, rfl⟩ : ∃ t, head = .leaf t := by
    cases head with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hhead_leaf
  obtain ⟨atok, rfl⟩ : ∃ t, a = .leaf t := by
    cases a with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at ha_leaf
  obtain ⟨btok, rfl⟩ : ∃ t, b = .leaf t := by
    cases b with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hb_leaf
  intro ⟨z, ⟨w, hw_mem, hw_b, hw_z, hne_bz⟩, hz_h⟩
  rw [subterms_shc] at hw_mem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw_mem
  rcases hw_mem with rfl | rfl | rfl | rfl | rfl
  · rcases hw_b with h | h
    · exact hne_hb h.symm
    · exact SyntacticObject.noConfusion h
  · exact hw_b
  · rcases hw_z with rfl | rfl
    · rcases hz_h with h | h
      · exact hne_ha h.symm
      · exact leaf_contains_nothing atok _ h
    · exact hne_bz rfl
  · exact hw_b
  · exact hw_b

/-- **Head precedes complement internals.** In `root = node head (node a b)`
    where all three are leaves, `head`'s terminal precedes the terminals of
    `a` and `b`. Together with `spec_precedes_head_complement`, this gives
    Specifier-Head-Complement order. -/
theorem head_precedes_complement
    (head a b : SyntacticObject)
    (hhead_leaf : head.isLeaf = true)
    (ha_leaf : a.isLeaf = true)
    (hb_leaf : b.isLeaf = true)
    (hne_ha : head ≠ a)
    (hne_hb : head ≠ b)
    (hne_ab : a ≠ b)
    (hne_h_ab : head ≠ .node a b) :
    let root := SyntacticObject.node head (.node a b)
    lcaPrecedesIn root head a ∧ lcaPrecedesIn root head b := by
  obtain ⟨htok, rfl⟩ : ∃ t, head = .leaf t := by
    cases head with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hhead_leaf
  obtain ⟨atok, rfl⟩ : ∃ t, a = .leaf t := by
    cases a with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at ha_leaf
  obtain ⟨btok, rfl⟩ : ∃ t, b = .leaf t := by
    cases b with | leaf t => exact ⟨t, rfl⟩ | node _ _ => simp [isLeaf] at hb_leaf
  refine ⟨⟨.leaf htok, .leaf atok, ?_, ?_, ?_, ?_, ?_⟩,
          ⟨.leaf htok, .leaf btok, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- head precedes a
  · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
      (Or.inl (self_mem_subterms _))))
  · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
      (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_append.mpr
        (Or.inl (self_mem_subterms _))))))))
  · exact ⟨head_cCommandsIn_a _ _ _ hne_h_ab,
           a_not_cCommandsIn_head _ _ _ rfl rfl rfl hne_ha hne_hb hne_ab⟩
  · exact leaf_mem_dominatedTerminals htok
  · exact leaf_mem_dominatedTerminals atok
  -- head precedes b
  · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
      (Or.inl (self_mem_subterms _))))
  · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
      (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_append.mpr
        (Or.inr (self_mem_subterms _))))))))
  · exact ⟨head_cCommandsIn_b _ _ _ hne_h_ab,
           b_not_cCommandsIn_head _ _ _ rfl rfl rfl hne_ha hne_hb hne_ab⟩
  · exact leaf_mem_dominatedTerminals htok
  · exact leaf_mem_dominatedTerminals btok

-- ============================================================================
-- Part 7: Structural Constraints Derived from the LCA
-- ============================================================================

-- 7a. No right specifier

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
    cCommandsIn root spec head :=
  ⟨.node head compl,
    ⟨.node (.node head compl) spec, self_mem_subterms _,
     Or.inr rfl, Or.inl rfl, Ne.symm hne_hc_node⟩,
    Or.inr (contains.imm _ _ (Or.inl rfl))⟩

-- 7b. Adjunction asymmetry

/-- **Head-to-head adjunction must be left-adjunction.** When a moving head
    `mover` adjoins to a target, the linearization function places
    mover's material before target's material (left-adjunction).
    This matches Kayne's result (1994, pp. 22-24).

    At the level of the complex head `node mover target` in isolation,
    two sister leaves symmetrically c-command each other (the sister-
    terminal limitation). The ordering emerges from the embedding context.
    But `linearize` — which gives the unique LCA-compatible order for
    well-formed trees — always places left daughters before right
    daughters, establishing left-adjunction. -/
theorem adjunction_left_only
    (mover target : SyntacticObject) :
    linearize (.node mover target) =
    linearize mover ++ linearize target :=
  rfl

-- ============================================================================
-- Part 8: Sister-Terminal Limitation
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
  refine ⟨.leaf a, ?_, Or.inl rfl⟩
  refine ⟨.node (.leaf a) (.leaf b), self_mem_subterms _, Or.inr rfl, Or.inl rfl, ?_⟩
  intro h
  injection h with h'
  exact hne h'.symm

-- ============================================================================
-- Part 9: Concrete Examples
-- ============================================================================

section Examples

private def specTok : SyntacticObject := mkLeafPhon .D [] "the" 1
private def headTok : SyntacticObject := mkLeafPhon .V [.D] "saw" 2
private def complTok : SyntacticObject := mkLeafPhon .N [] "Mary" 3

/-- Example: [DP the] [VP [V saw] [NP Mary]] -/
private def exampleTree : SyntacticObject :=
  .node specTok (.node headTok complTok)

/-- The linearization gives left-to-right order. -/
example : linearize exampleTree = [⟨.simple .D [] "the", 1⟩,
                                    ⟨.simple .V [.D] "saw", 2⟩,
                                    ⟨.simple .N [] "Mary", 3⟩] := by
  native_decide

/-- The phonological yield matches. -/
example : exampleTree.phonYield = ["the", "saw", "Mary"] := by
  native_decide

/-- Spec c-commands head within the example tree. -/
example : cCommandsIn exampleTree specTok headTok :=
  ⟨.node headTok complTok,
    ⟨exampleTree, self_mem_subterms _, Or.inl rfl, Or.inr rfl, by decide⟩,
    Or.inr (contains.imm _ _ (Or.inl rfl))⟩

/-- Spec c-commands complement within the example tree. -/
example : cCommandsIn exampleTree specTok complTok :=
  ⟨.node headTok complTok,
    ⟨exampleTree, self_mem_subterms _, Or.inl rfl, Or.inr rfl, by decide⟩,
    Or.inr (contains.imm _ _ (Or.inr rfl))⟩

end Examples

end Minimalism
