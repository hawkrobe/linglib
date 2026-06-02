import Mathlib.Data.List.Basic
import Linglib.Discourse.Coherence
/-!
# Rhetorical-Structure Substrate (SDRT core)
[asher-lascarides-2003]
The labelled discourse-structure record + SDRT-specific projections
(`kind`, `veridicality`) on top of the framework-neutral
`Discourse.Coherence.CoherenceRelation` enum. The Right Frontier
Constraint lives in the sibling `RightFrontier.lean`.
-/
namespace Discourse.Rhetorical
open Discourse.Coherence (CoherenceRelation)
/-- SDRT vocabulary alias for the unified coherence-relation enum. -/
abbrev RhetoricalRelation : Type := CoherenceRelation
/-! ### Structural Kind: subordinating vs coordinating vs structural -/
/-- Structural kind of a rhetorical relation (Asher-Lascarides §4.7).
    The Right Frontier Constraint gates new attachment points on the
    `subordinating` case. -/
inductive RelationKind where
  | subordinating
  | coordinating
  | structural
  deriving DecidableEq, Repr, Inhabited
end Discourse.Rhetorical
namespace Discourse.Coherence
/-- SDRT structural kind of each coherence relation. -/
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
/-- The coherence relation is subordinating in SDRT's sense. -/
def CoherenceRelation.isSubordinating (R : CoherenceRelation) : Prop :=
  R.sdrtKind = .subordinating
instance : DecidablePred CoherenceRelation.isSubordinating :=
  fun R => inferInstanceAs (Decidable (R.sdrtKind = _))
end Discourse.Coherence
namespace Discourse.Rhetorical
open Discourse.Coherence (CoherenceRelation)
/-! ### Veridicality -/
/-- Veridicality classification for rhetorical relations
    (Asher-Lascarides §4.8). Determines whether `R(α, β)` requires
    both arguments' contents to be true, neither, or one denied. -/
inductive Veridicality where
  | veridical
  | nonVeridical
  | denialBearing
  deriving DecidableEq, Repr, Inhabited
end Discourse.Rhetorical
namespace Discourse.Coherence
/-- Veridicality of each rhetorical relation per SDRT
    ([asher-lascarides-2003], preface "What's New" + §4.8). -/
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
/-! ### SDRS — Segmented Discourse Representation Structure -/
/-- A discourse-relation conjunct in an SDRS: `R(source, target)` is
    a conjunct in `F(container)`'s content. The `container` field
    distinguishes i-outscopes from generic endpoint relations. -/
structure SDRSEdge (L : Type*) where
  container : L
  source : L
  target : L
  relation : RhetoricalRelation
  deriving Repr, DecidableEq
/-- A Segmented Discourse Representation Structure (Asher-Lascarides
    Def 13, ⟨A, F⟩ form). Polymorphic in label type `L` and content
    type `α`. Condition L5 ("unique parent") is intentionally omitted
    per the book p. 144. -/
structure SDRS (L : Type*) (α : Type*) where
  labels : List L
  content : L → α
  edges : List (SDRSEdge L)
  root : L
  last : L
namespace SDRS
variable {L : Type*} {α : Type*}
/-- An empty SDRS with one root label, no edges; root is also LAST. -/
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
/-- Attach a new labelled unit to `parent` via `relation`, recording
    the conjunct in `container`'s content. The new unit becomes LAST. -/
def attach [DecidableEq L] (s : SDRS L α)
    (newLabel : L) (newContent : α)
    (container parent : L) (relation : RhetoricalRelation) : SDRS L α where
  labels := newLabel :: s.labels
  content := fun l => if l = newLabel then newContent else s.content l
  edges := ⟨container, parent, newLabel, relation⟩ :: s.edges
  root := s.root
  last := newLabel
end SDRS
/-! ### Outscopes (i-outscopes from Def 14 condition 2a) -/
/-- `iOutscopes s γ α'` — γ immediately outscopes α': some edge with
    container γ mentions α' as source or target. -/
def iOutscopes {L : Type*} {α : Type*} [DecidableEq L]
    (s : SDRS L α) (γ α' : L) : Prop :=
  ∃ e ∈ s.edges, e.container = γ ∧ (e.source = α' ∨ e.target = α')
instance {L : Type*} {α : Type*} [DecidableEq L]
    (s : SDRS L α) (γ α' : L) :
    Decidable (iOutscopes s γ α') := by
  unfold iOutscopes
  exact List.decidableBEx _ _
end Discourse.Rhetorical
