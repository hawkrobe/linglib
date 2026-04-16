/-!
# Post-Syntactic Operations (Distributed Morphology)
@cite{embick-noyer-2001} @cite{halle-marantz-1993}

Post-syntactic operations modify the output of the Syntax before
Vocabulary Insertion. Linglib already has Impoverishment (feature
deletion) and Fission (terminal splitting). This module adds the
remaining operations from the DM inventory:

- **Lowering**: a head adjoins downward to its complement head at PF
- **Local Dislocation**: linear adjacency is traded for affixation
- **Fusion**: two adjacent terminals merge into one
- **Dissociated Node Insertion**: a morphosyntactic node is inserted
  that has no source in the syntactic derivation

These operations apply after syntax and before Vocabulary Insertion,
in the **morphological structure** (MS) — a representation derived
from syntax that serves as input to VI.

@cite{kalin-bjorkman-etal-2026} §3.3.3, §4.2, §4.4, §4.5.2.
-/

namespace Morphology.DM.PostSyntactic

-- ============================================================================
-- §1: Lowering
-- ============================================================================

/-- Lowering (@cite{embick-noyer-2001}): a head X adjoins downward
    to the head Y of its complement, at PF.

    Precondition: X c-commands Y (X selects YP as complement).
    Effect: X affixes to Y, forming [Y X+Y] (or [Y Y+X]).

    Canonical example: English tense lowering — T lowers to V at PF,
    yielding V+T (*walk-ed*). When lowering is blocked (by an
    intervening element), do-support repairs the structure.

    Lowering is the PF counterpart of head raising: both produce
    complex heads, but lowering goes *down* (counter to the Head
    Movement Constraint). It is post-syntactic because the Syntax
    generates X above Y; the downward adjunction happens at PF. -/
structure LoweringRule (Head : Type) where
  /-- The head that lowers (e.g., T). -/
  source : Head
  /-- The head it lowers to (e.g., V). -/
  target : Head
  /-- Is the source head left-adjoined (prefix) or right-adjoined
      (suffix) to the target? -/
  leftAdjoin : Bool := false

/-- Apply lowering: merge source into target, producing a complex
    head. Returns the ordered pair of heads (left, right). -/
def LoweringRule.apply {Head : Type} (r : LoweringRule Head) :
    Head × Head :=
  if r.leftAdjoin then (r.source, r.target)
  else (r.target, r.source)

-- ============================================================================
-- §2: Local Dislocation
-- ============================================================================

/-- Local Dislocation (@cite{embick-noyer-2001}): takes two linearly
    adjacent elements X and Y (where X precedes Y), and adjoins X to Y
    (or vice versa), potentially reordering them.

    Unlike Lowering, Local Dislocation is sensitive to **linear**
    adjacency, not hierarchical structure. It cannot skip over
    intervening material.

    Notation from Embick & Noyer (2001):
    - Input:  `[X * [Y * Z]]`  (* = linear adjacency)
    - Output: `[[ Y+X ] * Z]`  (+ = morphological attachment)

    Canonical use: p-bound clitics that "tuck in" to a phrase they
    are linearly adjacent to, appearing to disrupt constituency. -/
structure LocalDislocationRule (Elem : Type) where
  /-- Does this element undergo dislocation? -/
  triggers : Elem → Bool
  /-- Does the dislocated element left-adjoin or right-adjoin
      to its host? -/
  leftAdjoin : Bool := false

-- ============================================================================
-- §3: Fusion
-- ============================================================================

/-- Fusion (@cite{halle-marantz-1993}): merges two adjacent terminal
    nodes into a single terminal before Vocabulary Insertion.

    The fused node bears the union of both terminals' features. A
    single Vocabulary Item then spells out the fused bundle, yielding
    a portmanteau.

    Canonical example: French *du* = Fusion of P[de] and D[le.MASC.SG].
    The fused node [P, D, MASC, SG] is spelled out by the VI *du*.

    Fusion is the DM mechanism for deriving portmanteaux from
    syntactically distinct heads. It applies between structurally
    adjacent terminals (typically head and complement head).

    @cite{kalin-bjorkman-etal-2026} §4.4. -/
structure FusionRule (Terminal : Type) where
  /-- First terminal (structurally higher). -/
  terminal1 : Terminal
  /-- Second terminal (structurally lower / complement head). -/
  terminal2 : Terminal

/-- The result of Fusion: a single terminal bearing features from
    both inputs. Parameterized over a feature-union operation. -/
def FusionRule.apply {Terminal Features : Type}
    (r : FusionRule Terminal)
    (getFeatures : Terminal → Features)
    (union : Features → Features → Features) : Features :=
  union (getFeatures r.terminal1) (getFeatures r.terminal2)

-- ============================================================================
-- §4: Dissociated Node Insertion
-- ============================================================================

/-- Dissociated Node Insertion (@cite{halle-marantz-1993};
    @cite{embick-noyer-2001} call this "node-sprouting"):
    insertion of a morphosyntactic terminal node that has no
    source in the narrow syntactic derivation.

    Dissociated nodes are introduced post-syntactically to provide
    positions for morphemes that are "ornamental" — present in the
    morphological structure but not required by the syntax.

    Canonical examples:
    - **Theme vowels** in Romance: the vowel between verb root and
      inflectional suffix (*cant-**a**-nt* 'singing') has no
      syntactic source but is required for well-formedness.
    - **Linkers** in compounds: Dutch *-s-* in *wetgeving-**s**-advies*
      'legislative advice'.
    - **Agreement nodes**: in some analyses, agreement morphemes are
      dissociated nodes inserted at PF, not present in syntax.

    @cite{kalin-bjorkman-etal-2026} §4.5.2. -/
structure DissociatedNode (Feature : Type) where
  /-- Features borne by the inserted node (may be empty for
      purely phonotactic elements like theme vowels). -/
  features : List Feature
  /-- Structural context: where is the node inserted?
      `true` = after the host terminal; `false` = before. -/
  insertAfter : Bool := true

end Morphology.DM.PostSyntactic
