import Linglib.Phenomena.Anaphora.Compare

/-!
# Reinhart (1976) @cite{reinhart-1976}

The Syntactic Domain of Anaphora. PhD dissertation, MIT.

## Key Contributions

1. **C-command** (def. 36, p. 32): replaces @cite{langacker-1969}'s S-node-based
   "command" with a **branching-node-based** relation
2. **C-command domain** (def. 38, p. 33): the subtree dominated by the first
   branching node dominating A — always a constituent
3. **Coreference restriction** (10b, p. 14): domain-based, dispensing with "precede"
4. **Claim (49)** (p. 40): c-command ⊆ command (= `kCommand ⊆ sCommand` in B&P)
5. **The irrelevance of precede** (§1.4): linear order is epiphenomenal for coreference

## Connection to @cite{barker-pullum-1990}

Reinhart's c-command is exactly B&P's **K-command** (parameterized by branching
nodes). @cite{langacker-1969}'s command is B&P's **S-command** (parameterized by
S-nodes). Theorem 49 follows from B&P's antitone map: since
`{S-nodes} ⊆ {branching nodes}`, we get `C_{branching} ⊆ C_{S}`.

## Connection to Address-Based `cCommand`

The address-based `cCommand` in `Compare.lean` computes K-command for binary
trees: in a binary tree every non-leaf node branches, so the "first branching
node dominating A" is A's parent, and A's parent dominates B iff A's sister
dominates B — which is exactly what `cCommand` tests.
-/

set_option autoImplicit false

namespace Reinhart1976

open Phenomena.Anaphora.Compare
open Set

-- ============================================================================
-- §1: Reinhart's Definitions
-- ============================================================================

/-! ### Definition 1 (p. 8) — Langacker's "command"

> A node A commands a node B if neither A nor B dominates the other and
> the S node most immediately dominating A also dominates B.

This is B&P's S-command, parameterized by S-nodes. Already formalized
as `sCommand` in `Compare.lean`. -/

/-! ### Definition 36 (p. 32) — C-command

> Node A c(onstituent)-commands node B if neither A nor B dominates the
> other and the first **branching node** which dominates A dominates B.

This is B&P's K-command, parameterized by branching nodes. Already
formalized as `kCommand` in `Compare.lean`.

Reinhart explicitly contrasts this with Langacker's command (p. 33):
"The difference between the relations of command and of c-command is
that while the first mentions **cyclic nodes** the second does not —
all **branching nodes** can be relevant." -/

/-! ### Definition 38 (p. 33) — C-command domain

> The domain of a node A consists of A together with all and only the
> nodes c-commanded by A. (OR: The domain of a node A is the subtree
> dominated by the first branching node which dominates A.)

A key observation (p. 34): c-command domains are always **constituents**
(subtrees), while precede-and-command domains may not be. -/

/-- The **c-command domain** of a node `a`: the set of nodes that `a`
    c-commands, plus `a` itself.

    In B&P terms: `{b | (a, b) ∈ kCommand T} ∪ {a}`. -/
def cCommandDomain {Node : Type} (T : AbstractTree Node) (a : Node) : Set Node :=
  {b | (a, b) ∈ kCommand T} ∪ {a}

-- ============================================================================
-- §2: Claim (49) — C-command ⊆ Command
-- ============================================================================

/-! ### Claim (49) (p. 40)

> A c-commands B ⟶ A commands B
> A does not command B ⟶ A does not c-command B

In B&P terms: `kCommand T ⊆ sCommand T`, provided every S-node is
also a branching node — a universally accepted structural assumption
(S-nodes always dominate both a subject and a predicate). -/

/-- **Claim (49)**: C-command implies command.

    Every S-node is a branching node (S-nodes dominate ≥2 children),
    so `{S-nodes} ⊆ {branching nodes}`, and by B&P's antitone map
    (`command_antitone`), `C_{branching} ⊆ C_{S}`. -/
theorem cCommand_implies_command {Node : Type} (T : LabeledTree Node)
    (h_S_branch : sNodes T ⊆ branchingNodes T.toAbstractTree) :
    kCommand T.toAbstractTree ⊆ sCommand T :=
  command_antitone T.toAbstractTree (sNodes T) (branchingNodes T.toAbstractTree) h_S_branch

-- ============================================================================
-- §3: The Coreference Restriction (10b)
-- ============================================================================

/-! ### Restriction 10b (p. 14)

> Two NP's in a non strict reflexive environment can be coreferential
> just in case **if either is in the domain of the other, the one in
> the domain is a pronoun**.

Reinhart argues (§1.4) that the earlier formulation using
precede-and-command is both empirically wrong (fails for preposed PPs)
and theoretically unnatural (c-command domains are constituents;
precede-and-command domains are not). -/

/-- Whether node `a` is a pronoun. -/
abbrev IsPronoun (Node : Type) := Node → Prop

/-- **Reinhart's Coreference Restriction (10b)**.

    Two nodes can corefer unless one is in the c-command domain of the
    other and is not a pronoun.

    `corefPermitted isPron T a b` holds iff:
    - neither is in the other's domain, OR
    - whichever is in the other's domain is a pronoun. -/
def corefPermitted {Node : Type} (isPron : IsPronoun Node)
    (T : AbstractTree Node) (a b : Node) : Prop :=
  (b ∈ cCommandDomain T a → isPron b) ∧
  (a ∈ cCommandDomain T b → isPron a)

-- ============================================================================
-- §4: The Irrelevance of Precede (§1.4)
-- ============================================================================

/-! ### The irrelevance of precede (§1.4, §1.5)

Reinhart's central argumentative contribution: the relation **precede** plays
no role in determining anaphora options. Two key observations:

1. **Preposed PPs** (§1.5.2): In "Near him, Dan saw a snake" (45),
   the pronoun *precedes* the antecedent yet coreference is fine —
   because "him" (PP-internal) does not c-command "Dan" (the subject).
   Meanwhile, "\*Near Dan, he saw a snake" (43a) is correctly blocked:
   "Dan" is in the c-command domain of "he" and is not a pronoun.

2. **VOS languages** (p. 41): In Malagasy, the pronoun precedes and
   commands the antecedent (by the precede-and-command definition)
   yet coreference is permitted — because the pronoun does not
   **c-command** the antecedent.

Both facts follow automatically from the c-command restriction (10b)
without mentioning linear order. -/

/-- **Precede is irrelevant**: c-command domains are symmetric with
    respect to linear order.

    In B&P terms: the command relation `C_P` is defined purely in terms
    of dominance (`upperBounds`, `dom`), with no reference to precedence.

    This is a structural fact about how `commandRelation` is defined —
    it uses only vertical (dominance) relations, never horizontal
    (precedence) relations. -/
theorem command_ignores_precedence {Node : Type} (T : AbstractTree Node) (P : Set Node) :
    ∀ a b, (a, b) ∈ commandRelation T P ↔
      ∀ x ∈ upperBounds T a P, T.dom x b :=
  λ _ _ => Iff.rfl

-- ============================================================================
-- §5: Concrete Verification
-- ============================================================================

/-! ### Preposed PP example (§1.5.2)

@cite{reinhart-1976}'s structures (41)/(42) are **ternary branching**
(S → PP NP₁ VP), but the key half of the argument is tree-shape-independent:

- NP₃ (PP-internal, e.g., "Dan" inside "near Dan") does NOT c-command
  NP₁ (the subject), because the first branching node dominating NP₃
  is PP, which does not dominate NP₁.

This is verified below in a binary encoding. It is the fact that the
precede-and-command approach fails to capture: the precede-and-command
rule incorrectly blocks backward pronominalization in
"Near him, Dan saw a snake" (45) — where "him" precedes and is
S-commanded by "Dan" — while the c-command restriction correctly
permits it (since "him" does not c-command "Dan").

**Binary tree limitation**: In @cite{reinhart-1976}'s ternary tree (41),
the subject NP₁ DOES c-command NP₃ (since the first branching node
above NP₁ is S, which dominates NP₃). Our binary encoding places NP₁
inside a VP shell, so the subject does NOT c-command into PP. This
changes the c-command facts for that direction but does not affect
the key structural observation that NP₃ cannot c-command NP₁. -/

/-- Preposed PP: the PP-internal NP does not c-command the subject.

    Binary encoding: `[S [PP [P near] [NP Dan]] [VP' [NP he] [VP ...]]]`
    NP_Dan at [L, R], NP_he at [R, L].

    This holds in both binary and n-ary trees: PP is the first
    branching node above Dan, and PP does not dominate the subject. -/
theorem preposed_pp_no_ccommand :
    cCommand [Dir.L, Dir.R] [Dir.R, Dir.L] = false := by native_decide

-- ============================================================================
-- §6: Bridge — Address-Based cCommand = B&P kCommand
-- ============================================================================

/-! ### Why address-based `cCommand` = B&P `kCommand`

In a **binary branching** tree, every non-leaf node has exactly two
children, so every non-leaf node is a **branching node**. Therefore:

- The "first branching node dominating A" = A's parent
- A's parent dominates B iff A's sister subtree contains B
- This is exactly what `cCommand a b` tests: `sister a` is a prefix of `b`

So for binary trees, address-based `cCommand` computes the same relation
as `commandRelation T (branchingNodes T)` = `kCommand T`.

We verify this on concrete examples below. -/

/-- In a binary tree, the subject [L] c-commands everything in [R, ...] -/
theorem subject_ccommands_into_vp :
    cCommand [Dir.L] [Dir.R] = true ∧
    cCommand [Dir.L] [Dir.R, Dir.L] = true ∧
    cCommand [Dir.L] [Dir.R, Dir.R] = true := by
  constructor
  · native_decide
  constructor <;> native_decide

/-- The object [R, R] does NOT c-command the subject [L] -/
theorem object_does_not_ccommand_subject :
    cCommand [Dir.R, Dir.R] [Dir.L] = false := by native_decide

/-- The object [R, R] c-commands the verb [R, L] (mutual c-command within VP) -/
theorem object_ccommands_verb :
    cCommand [Dir.R, Dir.R] [Dir.R, Dir.L] = true := by native_decide

/-- C-command is NOT symmetric in general: subject c-commands object
    but object does not c-command subject. -/
theorem ccommand_asymmetric_example :
    cCommand [Dir.L] [Dir.R, Dir.R] = true ∧
    cCommand [Dir.R, Dir.R] [Dir.L] = false := by
  constructor <;> native_decide

/-- Subject–object asymmetry for coreference (@cite{reinhart-1976}'s key prediction):
    - "She denied that Rosa met the Shah" — *she* c-commands *Rosa*, blocks coref
    - "The man who traveled with her denied that Rosa met the Shah" —
      *her* does NOT c-command *Rosa*, coref permitted

    In the second sentence, "her" is deeply embedded inside the subject NP
    (inside a relative clause PP). Any address under [L, ...] has a sister
    that also starts with [L, ...], so it can never c-command [R, ...]. -/
theorem subject_object_asymmetry :
    -- Subject [L] c-commands embedded subject [R, R, L]
    cCommand [Dir.L] [Dir.R, Dir.R, Dir.L] = true ∧
    -- NP deep inside subject [L, R, R, R, R] does NOT c-command embedded subject
    cCommand [Dir.L, Dir.R, Dir.R, Dir.R, Dir.R] [Dir.R, Dir.R, Dir.L] = false := by
  constructor <;> native_decide

-- ============================================================================
-- §7: End-to-End Verification — The (11) Paradigm (pp. 14-15)
-- ============================================================================

/-! ### Address-based coreference permission

A decidable version of `corefPermitted` for address-based binary trees.
Given two addresses and their pronoun status, tests whether coreference
is permitted under restriction (10b). -/

/-- **Address-based coreference permission** (decidable).

    Two NPs can corefer unless one c-commands the other and the
    c-commanded one is not a pronoun. Restriction (10b) applied to
    address-based `cCommand`.

    Note: like `corefPermitted`, this omits the "non strict reflexive
    environment" qualification — it governs non-reflexive coreference only. -/
def corefPermittedAddr (isPronA isPronB : Bool) (addrA addrB : Address) : Bool :=
  (if cCommand addrA addrB then isPronB else true) &&
  (if cCommand addrB addrA then isPronA else true)

/-! ### The (11) paradigm (pp. 14-15)

The key empirical test for restriction (10b). Given the structure:

    `[S NP₁ [VP denied [S' NP₂ [VP' has met the Shah]]]]`

with NP₁ at `[L]` and NP₂ at `[R, R, L]`, four sentences are generated
by varying the pronoun status of each NP:

- (11a) Rosa denied that Rosa has met the Shah.  — coref **blocked**
- (11b) She denied that Rosa has met the Shah.   — coref **blocked**
- (11c) Rosa denied that she has met the Shah.   — coref **permitted**
- (11d) She denied that she has met the Shah.    — coref **permitted**

The matrix subject c-commands the embedded subject (not vice versa),
so NP₂ is always in the c-command domain of NP₁. Therefore (10b) requires
NP₂ to be a pronoun for coreference to be permitted. -/

/-- Matrix subject c-commands embedded subject, not vice versa. -/
private theorem matrix_ccommands_embedded :
    cCommand [Dir.L] [Dir.R, Dir.R, Dir.L] = true ∧
    cCommand [Dir.R, Dir.R, Dir.L] [Dir.L] = false := by
  constructor <;> native_decide

/-- **(11a)** Rosa₁ denied that Rosa₂ has met the Shah: coref **blocked**.

    Rosa₂ is in the domain of Rosa₁ and is not a pronoun. -/
theorem paradigm_11a_blocked :
    corefPermittedAddr (isPronA := false) (isPronB := false)
      [Dir.L] [Dir.R, Dir.R, Dir.L] = false := by native_decide

/-- **(11b)** She₁ denied that Rosa₂ has met the Shah: coref **blocked**.

    Rosa₂ is in the domain of She₁ and is not a pronoun. -/
theorem paradigm_11b_blocked :
    corefPermittedAddr (isPronA := true) (isPronB := false)
      [Dir.L] [Dir.R, Dir.R, Dir.L] = false := by native_decide

/-- **(11c)** Rosa₁ denied that she₂ has met the Shah: coref **permitted**.

    she₂ is in the domain of Rosa₁ but IS a pronoun. -/
theorem paradigm_11c_permitted :
    corefPermittedAddr (isPronA := false) (isPronB := true)
      [Dir.L] [Dir.R, Dir.R, Dir.L] = true := by native_decide

/-- **(11d)** She₁ denied that she₂ has met the Shah: coref **permitted**.

    she₂ is in the domain of She₁ but IS a pronoun. -/
theorem paradigm_11d_permitted :
    corefPermittedAddr (isPronA := true) (isPronB := true)
      [Dir.L] [Dir.R, Dir.R, Dir.L] = true := by native_decide

-- ============================================================================
-- §8: (10a) vs (10b) — The Superiority of the Domain Formulation
-- ============================================================================

/-! ### Restriction (10a) — the pronoun-specific formulation (p. 14)

> Two NP's in a non strict reflexive environment can be coreferential
> just in case one is a pronoun, the other is not and the
> non-pronoun is not in the domain of the pronoun.

(10a) applies only to pairs consisting of a pronoun and a full NP.
It says nothing about pairs of two full NPs or two pronouns.

@cite{reinhart-1976} argues (pp. 14-17) that (10b) is strictly superior:
(10a) fails to block coreference between two full NPs when one is in
the domain of the other (the (11a) case). -/

/-- **Restriction (10a)**: applies only to pronoun–full NP pairs.

    When exactly one NP is a pronoun, the non-pronoun must not be in
    the c-command domain of the pronoun. When both are pronouns or
    both are full NPs, (10a) does not apply (returns `true`). -/
def corefPermitted_10a (isPronA isPronB : Bool) (addrA addrB : Address) : Bool :=
  if isPronA && !isPronB then
    -- A is pronoun, B is full NP: B must not be in domain of A
    !cCommand addrA addrB
  else if !isPronA && isPronB then
    -- B is pronoun, A is full NP: A must not be in domain of B
    !cCommand addrB addrA
  else
    -- Both pronouns or both full NPs: (10a) doesn't apply
    true

/-- **Non-equivalence of (10a) and (10b)**: (10a) fails on the (11a) case.

    (10a) cannot block coreference between two full NPs (Rosa₁ ... Rosa₂),
    because (10a) only applies to pronoun–full NP pairs.
    (10b) correctly blocks it because Rosa₂ is in the domain of Rosa₁
    and is not a pronoun. -/
theorem restriction_10a_vs_10b :
    -- (10a) INCORRECTLY permits (11a): Rosa₁ ... Rosa₂
    corefPermitted_10a false false [Dir.L] [Dir.R, Dir.R, Dir.L] = true ∧
    -- (10b) CORRECTLY blocks (11a)
    corefPermittedAddr false false [Dir.L] [Dir.R, Dir.R, Dir.L] = false := by
  constructor <;> native_decide

/-- **(10b) subsumes (10a)**: whenever (10a) blocks coreference, (10b) does too.

    The converse fails (as `restriction_10a_vs_10b` shows), so (10b) is
    strictly more restrictive than (10a). -/
theorem restriction_10b_subsumes_10a (isPronA isPronB : Bool) (addrA addrB : Address) :
    corefPermitted_10a isPronA isPronB addrA addrB = false →
    corefPermittedAddr isPronA isPronB addrA addrB = false := by
  simp only [corefPermitted_10a, corefPermittedAddr]
  cases isPronA <;> cases isPronB <;> simp_all

end Reinhart1976
