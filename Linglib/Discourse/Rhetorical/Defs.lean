import Mathlib.Data.List.Basic
import Linglib.Discourse.Coherence

/-!
# Rhetorical-Structure Substrate (SDRT core)
@cite{asher-lascarides-2003}

The labelled discourse-structure record + SDRT-specific projections
(`kind`, `veridicality`) on top of the framework-neutral
`Discourse.Coherence.CoherenceRelation` enum. The Right Frontier
Constraint lives in the sibling `RightFrontier.lean`.
-/

namespace Discourse.Rhetorical

open Discourse.Coherence (CoherenceRelation)

/-- SDRT's rhetorical-relation type IS Core's coherence-relation enum.
    Provides paper-anchored vocabulary at the SDRT namespace level
    while keeping a single canonical enum. -/
abbrev RhetoricalRelation : Type := CoherenceRelation

-- ════════════════════════════════════════════════════════════════
-- § 1. Structural Kind: subordinating vs coordinating vs structural
-- ════════════════════════════════════════════════════════════════

/-- Three structural kinds for rhetorical relations
    (@cite{asher-lascarides-2003}, §4.7 p. 146):

    * `subordinating` — the second argument is "dominated by" the
      first (Elaboration, Explanation, the topic-relation ⇓).
    * `coordinating` — the two arguments are at the same hierarchical
      level (Narration, Result, Background, Continuation).
    * `structural` — imposes a propositional-structure constraint on
      the contents of its arguments (Parallel, Contrast, plus some
      of the Ch. 7 question-bearing relations).

    The kind matters for the Right Frontier Constraint
    (§4.7 Definition 14): only subordinating relations open new
    attachment points via condition (2b). -/
inductive RelationKind where
  | subordinating
  | coordinating
  | structural
  deriving DecidableEq, Repr, Inhabited

end Discourse.Rhetorical

namespace Discourse.Coherence

/-- SDRT's structural kind of a coherence relation
    (@cite{asher-lascarides-2003}, §4.6–§4.7). Defined on
    `CoherenceRelation` (the unified enum) so the dot-notation
    projection `R.sdrtKind` works for consumers anywhere in the
    codebase, including outside SDRT. -/
def CoherenceRelation.sdrtKind :
    CoherenceRelation → Discourse.Rhetorical.RelationKind
  | .elaboration  => .subordinating
  | .explanation  => .subordinating
  | .occasion     => .coordinating  -- = SDRT's Narration
  | .result       => .coordinating
  | .background   => .coordinating
  | .consequence  => .coordinating
  | .alternation  => .coordinating
  | .correction   => .coordinating
  | .contrast     => .structural
  | .parallel     => .structural

/-- Predicate: a coherence relation is subordinating in SDRT's sense
    (@cite{asher-lascarides-2003}, §4.7 p. 146). The RFC's
    condition (2b) gates on this predicate. -/
def CoherenceRelation.isSubordinating (R : CoherenceRelation) : Prop :=
  R.sdrtKind = .subordinating

instance : DecidablePred CoherenceRelation.isSubordinating :=
  fun R => inferInstanceAs (Decidable (R.sdrtKind = _))

end Discourse.Coherence

namespace Discourse.Rhetorical

open Discourse.Coherence (CoherenceRelation)

-- ════════════════════════════════════════════════════════════════
-- § 3. Veridicality
-- ════════════════════════════════════════════════════════════════

/-- Veridicality classification for rhetorical relations
    (@cite{asher-lascarides-2003}, preface "What's New", and
    Ch. 4 §4.8):

    * `veridical` — `R(α, β)` is true only if both `K_α` and `K_β`
      are true (Background, Narration, Explanation, Elaboration, Result).
    * `nonVeridical` — `R(α, β)` doesn't impose this condition
      (Alternation, Consequence).
    * `denialBearing` — the connection holds only if one argument
      is denied (Correction, Ch. 8).

    The classification matters for downstream truth-conditional
    semantics: veridical relations contribute their arguments'
    contents to the discourse update directly; denial-bearing
    relations introduce negation. -/
inductive Veridicality where
  | veridical
  | nonVeridical
  | denialBearing
  deriving DecidableEq, Repr, Inhabited

end Discourse.Rhetorical

namespace Discourse.Coherence

/-- Veridicality of each rhetorical relation per SDRT
    (@cite{asher-lascarides-2003}, preface "What's New" + §4.8). -/
def CoherenceRelation.veridicality :
    CoherenceRelation → Discourse.Rhetorical.Veridicality
  | .occasion     => .veridical    -- = SDRT's Narration
  | .elaboration  => .veridical
  | .explanation  => .veridical
  | .result       => .veridical
  | .background   => .veridical
  | .contrast     => .veridical
  | .parallel     => .veridical
  | .alternation  => .nonVeridical
  | .consequence  => .nonVeridical
  | .correction   => .denialBearing

end Discourse.Coherence

namespace Discourse.Rhetorical

open Discourse.Coherence (CoherenceRelation)

-- ════════════════════════════════════════════════════════════════
-- § 4. SDRS — Segmented Discourse Representation Structure
-- ════════════════════════════════════════════════════════════════

/-- A discourse-relation conjunct in an SDRS:
    `R(source, target)` is a conjunct in `F(container)`'s content
    (@cite{asher-lascarides-2003} Def 14 p. 148, condition 2a uses
    "in F(γ)" — γ is the container).

    The `container` field is essential for the i-outscopes relation:
    `iOutscopes(γ, α)` holds iff there's an edge with `container = γ`
    and either `source = α` or `target = α`. Without this field the
    outscoping relation collapses to a symmetric "endpoint of any
    edge" predicate, which is not what Def 14 says. -/
structure SDRSEdge (L : Type*) where
  /-- The constituent λ such that `R(source, target)` is a conjunct
      in `F(λ)`. -/
  container : L
  source : L
  target : L
  relation : RhetoricalRelation
  deriving Repr, DecidableEq

/-- A Segmented Discourse Representation Structure
    (@cite{asher-lascarides-2003}, Ch. 4 Def 13 p. 142, in the
    ⟨A, F⟩ form per p. 144).

    Polymorphic in:
    * `L` — label type (speech-act discourse referents `π₁, π₂, ...`).
    * `α` — content type (DRT DRSs, Set W, Prop, etc.). The substrate
      is content-agnostic per the book's "abstracting away from DRT"
      decision (preface, "What's New" § Discourse Structure).

    Fields:
    * `labels` — the set A of speech-act discourse referents.
    * `content` — the function F mapping each label to its content.
    * `edges` — the discourse-relation conjuncts. Multiple edges
      between the same pair are allowed (different relations).
    * `root` — the unique supremum π₀ guaranteed by Def 13 condition
      L4'.
    * `last` — the LAST attachment point used by Definition 14.

    @cite{asher-lascarides-2003} p. 144: Definition 13 condition L5
    ("every label has a unique parent") is **omitted** because "a
    given clause can make an illocutionary contribution to more than
    one part of the discourse structure." We follow the book's
    omission. -/
structure SDRS (L : Type*) (α : Type*) where
  labels : List L
  content : L → α
  edges : List (SDRSEdge L)
  root : L
  last : L

namespace SDRS

variable {L : Type*} {α : Type*}

/-- An empty SDRS with a single root label and no edges. The root
    serves as both the supremum (per Def 13 L4') and the LAST
    attachment point. -/
def initial (root : L) (rootContent : L → α) : SDRS L α where
  labels := [root]
  content := rootContent
  edges := []
  root := root
  last := root

/-- Add an edge to an SDRS. Does not add the labels — caller
    must ensure both `source` and `target` are already in `labels`. -/
def addEdge (s : SDRS L α) (e : SDRSEdge L) : SDRS L α :=
  { s with edges := e :: s.edges }

/-- Add a new labelled discourse unit, attaching it to a parent via
    a rhetorical relation whose conjunct lives in some container's
    content. The new unit becomes LAST.

    For top-level attachments (parent at root), the container is
    typically the root itself: `F(root)` accumulates the top-level
    relation conjuncts. For nested attachments, the container is the
    parent's container constituent. -/
def attach [DecidableEq L] (s : SDRS L α)
    (newLabel : L) (newContent : α)
    (container parent : L) (relation : RhetoricalRelation) : SDRS L α where
  labels := newLabel :: s.labels
  content := fun l => if l = newLabel then newContent else s.content l
  edges := ⟨container, parent, newLabel, relation⟩ :: s.edges
  root := s.root
  last := newLabel

end SDRS

-- ════════════════════════════════════════════════════════════════
-- § 5. Outscopes (i-outscopes from Def 14 condition 2a)
-- ════════════════════════════════════════════════════════════════

/-- `iOutscopes s γ α'` — γ immediately outscopes α' in SDRS s
    (@cite{asher-lascarides-2003}, §4.7 Def 14 condition 2a,
    p. 148): "R(δ, α) or R(α, δ) is a conjunct in F(γ) for some R
    and some δ".

    In our `container`-tagged edges, this is: there exists an edge
    with `container = γ` such that α' appears as either `source`
    or `target`. The relation is asymmetric in (γ, α') — γ is the
    bigger constituent, α' is the smaller one being mentioned in
    γ's content. -/
def iOutscopes {L : Type*} {α : Type*} [DecidableEq L]
    (s : SDRS L α) (γ α' : L) : Prop :=
  ∃ e ∈ s.edges, e.container = γ ∧ (e.source = α' ∨ e.target = α')

instance {L : Type*} {α : Type*} [DecidableEq L]
    (s : SDRS L α) (γ α' : L) :
    Decidable (iOutscopes s γ α') := by
  unfold iOutscopes
  exact List.decidableBEx _ _

end Discourse.Rhetorical
