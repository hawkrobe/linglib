import Mathlib.Data.List.Basic
import Linglib.Discourse.Coherence

/-!
# Asher & Lascarides 2003: SDRT Right Frontier Constraint worked example

[asher-lascarides-2003]

Example (21) from p. 149 — the discourse where the book explicitly
enumerates which attachment sites are available under the Right
Frontier Constraint, and which are excluded. We replicate it
against the SDRT substrate to verify that
`availableAttachmentPoints` returns exactly the book-predicted set.

## The example (21), p. 149

```
π₀:
  ├─ π₃, π₄
  │  ├─ π₃: K_π₃
  │  ├─ ⇓(π₃, π₄)              ← subordinating topic relation
  │  └─ π₄:
  │     ├─ π₁, π₂
  │     ├─ π₁: K_π₁
  │     ├─ π₂: K_π₂
  │     └─ Background(π₁, π₂)   ← coordinating
```

Reading the labelling F:
* F(π₀) ⊇ ⇓(π₃, π₄) — the topic relation lives at the top level
* F(π₄) ⊇ Background(π₁, π₂) — the coordinated pair lives inside π₄
* F(π₁), F(π₂), F(π₃) are atomic clausal contents K_πᵢ

## What the book asserts (p. 149)

> "assuming that π₂ in (21) is LAST, the available attachment sites
>  are π₂ (by condition 1), π₄ (by condition 2a), π₃ (by condition
>  2b and 3) and π₀ (by condition 3). But π₁ is *not* available."

## Why π₁ is not available

π₁ and π₂ are siblings under `Background`, which is **coordinating**
(not subordinating). After attaching to π₂ (LAST), the only way to
reach π₁ would be through a subordinating relation — but
`Background` doesn't qualify. Walking up via outscoping reaches π₄
(which contains both π₁ and π₂), and from π₄ we reach π₃ via the
subordinating ⇓ relation. But π₁ is on the wrong side of a
coordinating sibling boundary.

## Substrate note

[asher-lascarides-2003]'s ⇓ topic-relation is not in the
substrate's `RhetoricalRelation` enum (it's a structural relation
the book uses informally; the headline truth-conditional inventory
is Narration / Elaboration / Explanation / Result / Background /
Contrast / Parallel + Consequence / Alternation / Correction). We
encode ⇓ as `.elaboration` in the example below — both are
subordinating, and the RFC's condition 2b only sees the
`isSubordinating` projection. The example would behave identically
with a hypothetical `.topic` constructor.
-/

/-!### Rhetorical-Structure Substrate (SDRT core)
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


/-!### Right Frontier Constraint
[asher-lascarides-2003]
Available-attachment-points constraint restricting where new
discourse units attach in an SDRS. `α = LAST` is always available;
labels `γ` that outscope `α` structurally or are connected via a
subordinating relation are also available, transitively closed.
The central structural constraint on SDRT anaphora resolution.
-/

namespace Discourse.Rhetorical
variable {L : Type*} {α : Type*} [DecidableEq L]
/-! ### The single-step "<" relation (Def 14 conditions 2a + 2b) -/
/-- γ dominates α' in one step: γ outscopes α' (2a) or there is a
    subordinating-relation edge from γ to α' (2b). -/
def dominatesOneStep (s : SDRS L α) (α' γ : L) : Prop :=
  iOutscopes s γ α' ∨
  ∃ e ∈ s.edges, e.source = γ ∧ e.target = α' ∧
                 e.relation.isSubordinating
instance (s : SDRS L α) (α' γ : L) :
    Decidable (dominatesOneStep s α' γ) := by
  unfold dominatesOneStep
  exact instDecidableOr
/-! ### Available attachment points (Def 14, transitively closed) -/
/-- `availableViaChain s α γ n` — γ dominates α via a chain of
    length ≤ n of `dominatesOneStep` steps. Bounded because the
    transitive closure on a finite SDRS terminates. -/
def availableViaChain (s : SDRS L α) (α' γ : L) : Nat → Prop
  | 0 => α' = γ
  | n + 1 => availableViaChain s α' γ n ∨
             ∃ δ ∈ s.labels, dominatesOneStep s α' δ ∧
                              availableViaChain s δ γ n
instance (s : SDRS L α) (α' γ : L) (n : Nat) :
    Decidable (availableViaChain s α' γ n) := by
  induction n generalizing α' with
  | zero => exact inferInstanceAs (Decidable (_ = _))
  | succ n ih =>
    unfold availableViaChain
    exact instDecidableOr
/-- Labels available for new attachment from `s.last`: those reachable
    via `dominatesOneStep` within `s.labels.length` steps. -/
def availableAttachmentPoints (s : SDRS L α) : List L :=
  s.labels.filter
    (fun γ => decide (availableViaChain s s.last γ s.labels.length))
/-! ### Structural theorems -/
/-- LAST is always its own available attachment point (Def 14
    condition 1). Holds at chain length 0. -/
theorem last_self_available (s : SDRS L α) :
    availableViaChain s s.last s.last 0 := rfl
/-- The available-via-chain relation is monotone in the chain
    length: longer chains include shorter ones. -/
theorem availableViaChain_mono (s : SDRS L α) (α' γ : L) (n : Nat) :
    availableViaChain s α' γ n → availableViaChain s α' γ (n + 1) := by
  intro h
  unfold availableViaChain
  exact Or.inl h
/-- `α' < γ` (one-step domination) implies γ is available from α'
    at chain length 1. Headline corollary of Def 14 condition 2. -/
theorem oneStep_available (s : SDRS L α) (α' γ : L)
    (hγ : γ ∈ s.labels)
    (h : dominatesOneStep s α' γ) :
    availableViaChain s α' γ 1 := by
  unfold availableViaChain
  refine Or.inr ⟨γ, hγ, h, ?_⟩
  rfl
end Discourse.Rhetorical


namespace AsherLascarides2003

open Discourse.Rhetorical

-- ════════════════════════════════════════════════════════════════
-- § 1. The Example (21) SDRS
-- ════════════════════════════════════════════════════════════════

abbrev Label := Nat
abbrev Content := String

/-- Example (21) from [asher-lascarides-2003] p. 149, with
    LAST = π₂.

    Labels: 0 = π₀, 1 = π₁, 2 = π₂, 3 = π₃, 4 = π₄.

    Edges encode the labelled-discourse-structure conjuncts:
    * `⟨0, 3, 4, .elaboration⟩` represents `⇓(π₃, π₄) ∈ F(π₀)`
      (using `.elaboration` as a stand-in for ⇓; both subordinating).
    * `⟨4, 1, 2, .background⟩` represents `Background(π₁, π₂) ∈ F(π₄)`.

    Plus container-marking edges so that iOutscopes recovers the
    box-containment structure:
    * π₀ contains π₃ and π₄
    * π₄ contains π₁ and π₂

    These containment relations are conjuncts in the parent box's
    F-content (the book's "labels A and labelling F" representation
    — being a label inside a box IS a content fact about the parent).
    We encode them as additional outscoping conjuncts using the
    same edge structure.

    For Example (21) specifically, the ⇓(π₃, π₄) and
    Background(π₁, π₂) edges already encode the containment
    (since these relations have π₃, π₄, π₁, π₂ as arguments and
    the relations themselves live in F(π₀) and F(π₄)
    respectively). No additional outscoping edges needed. -/
def example21 : SDRS Label Content where
  labels := [0, 1, 2, 3, 4]
  content
    | 0 => "π₀ (root)"
    | 1 => "K_π₁"
    | 2 => "K_π₂"
    | 3 => "K_π₃"
    | 4 => "(complex constituent containing π₁, π₂)"
    | _ => "<unknown>"
  edges := [
    ⟨0, 3, 4, .elaboration⟩,   -- ⇓(π₃, π₄) ∈ F(π₀); ⇓ acts as subordinating
    ⟨4, 1, 2, .background⟩     -- Background(π₁, π₂) ∈ F(π₄); coordinating
  ]
  root := 0
  last := 2

-- ════════════════════════════════════════════════════════════════
-- § 2. RFC verification — book p. 149's predicted set
-- ════════════════════════════════════════════════════════════════

/-- π₂ (LAST) is itself available, by condition 1 of Def 14. -/
example : availableViaChain example21 example21.last 2 0 := rfl

/-- π₄ is available from π₂ via outscoping (condition 2a):
    `Background(π₁, π₂) ∈ F(π₄)` so iOutscopes(π₄, π₂) holds. -/
example : availableViaChain example21 2 4 1 := by decide

/-- π₃ is available from π₂ via condition 2b + 3 (transitive closure):
    π₂ → π₄ (outscoping) → π₃ (subordinating ⇓ encoded as .elaboration). -/
example : availableViaChain example21 2 3 2 := by decide

/-- π₀ is available from π₂ via condition 3 (transitive closure):
    π₂ → π₄ (outscoping) → π₀ (outscoping ⇓ which contains π₄). -/
example : availableViaChain example21 2 0 2 := by decide

-- ════════════════════════════════════════════════════════════════
-- § 3. The headline negative result: π₁ is NOT available
-- ════════════════════════════════════════════════════════════════

/-- **Book p. 149 headline claim**: π₁ is NOT in the available
    attachment set from π₂ (Example 21).

    The reason: π₁ and π₂ are siblings under `Background`, which is
    coordinating (not subordinating). RFC's condition 2b only opens
    up new attachment sites via subordinating relations, so the
    sibling-via-coordinating π₁ is unreachable from π₂'s right
    frontier. -/
theorem pi_1_not_available_from_pi_2 :
    1 ∉ availableAttachmentPoints example21 := by decide

/-- The full available set from π₂ matches the book's prediction:
    {π₀, π₂, π₃, π₄}. -/
theorem available_attachment_points_match :
    availableAttachmentPoints example21 = [0, 2, 3, 4] := by decide

end AsherLascarides2003
