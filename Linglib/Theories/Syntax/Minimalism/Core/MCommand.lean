import Linglib.Theories.Syntax.Minimalism.Core.Basic

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
  so == root ||
  root.subtrees.all λ parent =>
    match parent with
    | .node a b =>
      if b == so then true       -- so is specifier/complement (right daughter) → maximal
      else if a == so then false  -- so is head (left daughter) → not maximal
      else true                   -- parent doesn't contain so
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
  α != β &&
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

    We state this as a Boolean implication over `SyntacticObject`. -/
theorem cCommand_implies_mCommand_bool (root α β : SyntacticObject)
    (h : cCommandsInB root α β = true) :
    mCommandsB root α β = true := by
  sorry  -- TODO: prove from definitions; requires showing that
         -- c-command witnesses (sister containing β) ensure all
         -- maximal projections above α are above β

end Minimalism
