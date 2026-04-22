import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Core.Order.Command

/-!
# M-Command @cite{newman-2024}

M-command (maximal-projection command) as defined in @cite{newman-2024}'s
*When Arguments Merge*. α m-commands β iff every maximal projection
dominating α dominates β.

M-command is weaker than c-command: c-command implies m-command, but not
vice versa. The difference matters for binding in ditransitives — in
@cite{newman-2024}'s structures where neither internal argument
c-commands the other (the "high IO" configuration), m-command correctly
predicts the binding asymmetries.

## Relation to Existing Binding

`Coreference.lean` uses c-command (`cCommandsInB` from `Basic.lean`).
M-command is an alternative structural relation for binding that makes
different predictions in multi-specifier configurations. Both are
available; empirical coverage determines which is appropriate for a
given phenomenon.

-/

namespace Minimalism

-- ============================================================================
-- § 1: Maximal Projections
-- ============================================================================

/-- A node in a tree is a maximal projection if it is not immediately
    contained by a node with the same label (i.e., it does not project
    further).

    Since `SyntacticObject` uses bare binary branching without explicit
    labels, we approximate: a node is a maximal projection if it is a
    non-leaf whose parent (in the given root tree) is either the root
    or has a different head. For label-free trees, we use a structural
    criterion: a node is maximal if it is not the head-child of its
    parent. -/
def isMaximalProjectionIn (root so : SyntacticObject) : Bool :=
  -- A node is a maximal projection if no node in the tree immediately
  -- contains it as a head (left daughter in our convention).
  -- Approximation: so is maximal if every parent of so in root
  -- contains so as a non-head daughter (right), or so is the root.
  decide (so = root) ||
  root.subtrees.all λ parent =>
    match parent with
    | .node a b =>
      if decide (b = so) then true       -- so is specifier/complement (right) → maximal
      else if decide (a = so) then false  -- so is head (left daughter) → not maximal
      else true                           -- parent doesn't contain so
    | .leaf _ => true

-- ============================================================================
-- § 2: Domination
-- ============================================================================

/-- α dominates β in tree root: α properly contains β. -/
def dominatesB (α β : SyntacticObject) : Bool :=
  containsB α β

-- ============================================================================
-- § 3: M-Command
-- ============================================================================

/-- α m-commands β in tree `root` iff every maximal projection in `root`
    that dominates α also dominates β.

    Formally: ∀ γ ∈ maximal projections of root,
      dominates(γ, α) → dominates(γ, β)

    This is weaker than c-command because c-command requires a *sister*
    that contains β, while m-command only requires that all maximal
    projections above α are also above β. -/
def mCommandsB (root α β : SyntacticObject) : Bool :=
  decide (α ≠ β) &&
  root.subtrees.all λ γ =>
    !(isMaximalProjectionIn root γ && dominatesB γ α && !dominatesB γ β)

/-- α asymmetrically m-commands β in tree `root`. -/
def asymMCommandsB (root α β : SyntacticObject) : Bool :=
  mCommandsB root α β && !mCommandsB root β α

-- ============================================================================
-- § 4: Binding via M-Command
-- ============================================================================

/-- Binding Principle A (m-command version): a reflexive/reciprocal must
    be m-commanded by its antecedent within a local domain. -/
def reflexiveLicensedMCmd (root antecedent anaphor : SyntacticObject) : Bool :=
  mCommandsB root antecedent anaphor

/-- Binding Principle B (m-command version): a pronoun must be free
    (not m-commanded by a coreferent) within a local domain. -/
def pronounFreeMCmd (root binder pronoun : SyntacticObject) : Bool :=
  !mCommandsB root binder pronoun

-- ============================================================================
-- § 5: C-Command Implies M-Command
-- ============================================================================

/-- C-command implies m-command: if α c-commands β in a tree, then α
    also m-commands β. The converse does not hold in general.

    This is a structural consequence: c-command requires α's sister to
    contain-or-equal β, which means every node dominating α also
    dominates α's sister and hence β. Since maximal projections are a
    subset of all dominating nodes, the m-command condition follows.

    We state this as a Boolean implication over `SyntacticObject`.
    The path-based companion `kCCommand_subset_mCCommand` (below) is
    *proved* via @cite{barker-pullum-1990}'s `command_antitone`; the
    Bool→Prop migration of `cCommandsInB` / `mCommandsB` would let
    this theorem be derived from the path-based version through the
    C6 bridge. -/
theorem cCommand_implies_mCommand_bool (root α β : SyntacticObject)
    (h : cCommandsInB root α β = true) :
    mCommandsB root α β = true := by
  sorry  -- TODO: prove from definitions; requires showing that
         -- c-command witnesses (sister containing β) ensure all
         -- maximal projections above α are above β

-- ============================================================================
-- § 6: Path-based M-Command via Barker-Pullum (mathlib-shape)
-- ============================================================================

/-! The path-based companion to value-based `mCommandsB`. Both definitions
    coexist: `mCommandsB` is decidable Bool for the existing ~10 consumers,
    `mCCommand` is `Set`-valued Prop for B&P-style algebraic reasoning.

    Definitionally, `mCCommand root` is just `commandRelation` applied to
    `maximalProjectionPaths`. The subset `kCCommand root ⊆ mCCommand root`
    — Reinhart's claim 49 in path form — is one line via
    `command_antitone`, with no induction on `SyntacticObject`. This is
    the design payoff motivating the C6 grounding in `commandRelation`. -/

/-- Maximal-projection paths in `root`. A `TreePath` is a max-projection
    iff (i) its last index is *not* 0 (it isn't a left-daughter / head;
    `getLast? = none` for the root automatically passes), and (ii) its
    subtree under the forgetful `FreeMagma.toTree` is a binary `.node`
    (a max projection must project — leaves don't qualify).

    Reflects the head-on-left convention of `isMaximalProjectionIn`:
    heads are left daughters, max projections are right daughters or
    the root. -/
def maximalProjectionPaths (root : SyntacticObject) : Set Core.Tree.TreePath :=
  {p | p.toList.getLast? ≠ some 0 ∧
       ∃ a b, root.toTree.subtreeAt p.toList = some (.node () [a, b])}

/-- Path-based m-command on `SyntacticObject`, recast as B&P
    @cite{barker-pullum-1990} `commandRelation` over the forgetful
    tree-order with `maximalProjectionPaths` as the generator.

    Use `mCCommand_def` to unfold to the underlying B&P apparatus when
    needed; otherwise treat as opaque. Sibling to `kCCommand` (in
    `Minimalism/Core/Basic.lean`); both inhabit the same B&P lattice. -/
def mCCommand (root : SyntacticObject) :
    Set (Core.Tree.TreePath × Core.Tree.TreePath) :=
  Core.Order.commandRelation root.toTree.toTreeOrder (maximalProjectionPaths root)

/-- Definitional unfolding of `mCCommand`. Use `rw [mCCommand_def]` only
    when the underlying `commandRelation` / `upperBounds` apparatus is
    needed; consumer code should treat `mCCommand` as opaque. -/
theorem mCCommand_def (root : SyntacticObject) :
    mCCommand root =
      Core.Order.commandRelation root.toTree.toTreeOrder
        (maximalProjectionPaths root) :=
  rfl

/-- Maximal-projection paths are a subset of branching paths: every
    max projection is, in particular, a binary node. -/
theorem maximalProjectionPaths_subset_branchingPaths (root : SyntacticObject) :
    maximalProjectionPaths root ⊆ branchingPaths root :=
  fun _ ⟨_, hb⟩ => hb

/-- **Reinhart's claim 49 (path form)**: c-command implies m-command.

    `kCCommand root ⊆ mCCommand root`. Proved in one line via B&P's
    `command_antitone` — no `SyntacticObject` induction, no path
    manipulation. The subset of generators
    (`maximalProjectionPaths ⊆ branchingPaths`) lifts antitonely into
    the *opposite* containment of command relations.

    This is the path-based analog of `cCommand_implies_mCommand_bool`
    (which awaits the C6 bridge proofs to be derivable from this
    via the value/path correspondence). -/
theorem kCCommand_subset_mCCommand (root : SyntacticObject) :
    kCCommand root ⊆ mCCommand root :=
  Core.Order.command_antitone root.toTree.toTreeOrder
    (maximalProjectionPaths root) (branchingPaths root)
    (maximalProjectionPaths_subset_branchingPaths root)

end Minimalism
