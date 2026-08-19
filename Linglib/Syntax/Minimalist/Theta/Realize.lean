import Linglib.Syntax.Minimalist.Theta.Basic
import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Colored Merge and realization

The bridge from the theta bud system to the syntactic-object carrier
([marcolli-larson-2025]'s reinterpretation of theta filtering as colored
structure formation). The compatibility relation on a colored binary
Merge — the root and children colors form a generator — is `ThetaLocal`,
and the colored Merge of derivable structures under a compatible root is
derivable (`derives_node_of_thetaLocal`, via the bottom-up
`Bud.System.Derives.node`): structure building through colored Merge
stays within the theta-lawful language. `realize` prunes the colors,
sending a colored tree to the `SyntacticObject` it builds — lexically
anchored leaves become lexical leaves, binary nodes become bare Merge
nodes, and the empty-tree marker is the magma unit, so a movement landing
site realizes to its host unchanged (`realize_node_emptyTree_right`).

## Main declarations

* `derives_node_of_thetaLocal` — colored Merge closure: joining derivable
  structures under a generator-compatible root color is derivable.
* `realize` — pruning to the `SyntacticObject` carrier, `none` playing the
  magma unit; intended on trees with terminal inputs, where `none` arises
  only from the empty-tree marker.
* `realize_node_emptyTree_right` — the unit law `M(T, 1) = T`: movement
  landing sites leave no mark on the realized object.
* `realize_isSome` — a tree with a lexically anchored input realizes.
-/

namespace Minimalist.Theta

variable {L : Type*} {hier : ThetaRole → ThetaRole → Prop}

/-- Colored Merge closure: joining two derivable structures under a root
    color that forms a generator with their output colors is derivable.
    Structure building by compatible colored Merge stays within the
    theta-lawful language. -/
theorem derives_node_of_thetaLocal {c : Color L}
    {S S' : Bud.Tree (Color L)} (hΞ : ThetaLocal hier c S.out S'.out)
    (hS : (system (L := L) hier).Derives S.out S)
    (hS' : (system (L := L) hier).Derives S'.out S') :
    (system (L := L) hier).Derives c (.node c S S') := by
  obtain ⟨g₀, rfl, hg⟩ := hΞ
  have hr : Bud.Tree.node (Color.free g₀) (.leaf S.out) (.leaf S'.out) ∈
      rules (L := L) hier := by
    rcases hg with hg | hg
    · exact ⟨g₀, _, _, hg, .inl rfl⟩
    · exact ⟨g₀, _, _, hg, .inr rfl⟩
  exact .node hr (by simp [system, Color.IsTerminal]) hS hS'

/-- Prune a colored tree to the syntactic object it builds: lexically
    anchored leaves become lexical leaves, nodes become bare Merge nodes,
    and `none` is the magma unit — contributed by the empty-tree marker
    (and, degenerately, by bare-grid leaves, which do not occur in trees
    with terminal inputs). -/
noncomputable def realize : Bud.Tree (Color LIToken) → Option SyntacticObject
  | .leaf (.lex tok _) => some (.lexLeaf tok)
  | .leaf _ => none
  | .node _ l r =>
      match realize l, realize r with
      | some L, some R => some (L.node R)
      | some L, none => some L
      | none, some R => some R
      | none, none => none

@[simp] theorem realize_leaf_lex (tok : LIToken) (g : List PolarizedRole) :
    realize (.leaf (.lex tok g)) = some (.lexLeaf tok) := rfl

@[simp] theorem realize_leaf_emptyTree :
    realize (.leaf .emptyTree) = none := rfl

@[simp] theorem realize_leaf_free (g : List PolarizedRole) :
    realize (.leaf (.free g)) = none := rfl

theorem realize_node_some_some {l r : Bud.Tree (Color LIToken)}
    {c : Color LIToken} {L R : SyntacticObject} (hl : realize l = some L)
    (hr : realize r = some R) :
    realize (.node c l r) = some (L.node R) := by
  simp [realize, hl, hr]

/-- The unit law `M(T, 1) = T`: a movement landing site realizes to its
    host unchanged — the empty-tree marker exists only for the coloring. -/
@[simp] theorem realize_node_emptyTree_right {x : Bud.Tree (Color LIToken)}
    {c : Color LIToken} :
    realize (.node c x (.leaf .emptyTree)) = realize x := by
  cases h : realize x <;> simp [realize, h]

/-- A tree with a lexically anchored input realizes to a syntactic
    object. -/
theorem realize_isSome {x : Bud.Tree (Color LIToken)}
    (h : ∃ tok g, Color.lex tok g ∈ x.inputs) : (realize x).isSome := by
  induction x with
  | leaf c =>
    obtain ⟨tok, g, hmem⟩ := h
    obtain rfl : Color.lex tok g = c := by simpa using hmem
    simp
  | node c l r ihl ihr =>
    obtain ⟨tok, g, hmem⟩ := h
    rcases List.mem_append.mp (by simpa using hmem) with hmem | hmem
    · have := ihl ⟨tok, g, hmem⟩
      obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp this
      cases hr : realize r <;> simp [realize, hL, hr]
    · have := ihr ⟨tok, g, hmem⟩
      obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp this
      cases hl : realize l <;> simp [realize, hl, hR]

end Minimalist.Theta
