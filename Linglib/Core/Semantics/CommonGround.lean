import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

/-!
# Common Ground

@cite{stalnaker-1974} @cite{stalnaker-2002}

Framework-agnostic context management following @cite{stalnaker-1974}:
context sets (`Set W`), common ground as proposition lists (`CG W`),
and the `HasContextSet` interface unifying both with the various
discourse-state representations across `Theories/`.

Multi-agent epistemic operators (knowledge, belief, common knowledge)
are in `Theories/Semantics/Modality/EpistemicLogic.lean`.
-/

namespace Core.CommonGround

/-- A context set is the set of worlds compatible with the common ground.

Just `Set W`. The namespace `ContextSet.*` provides discourse-meaningful
aliases (`entails`, `update`, `compatible`) backed by mathlib `Set` ops. -/
abbrev ContextSet (W : Type*) := Set W

namespace ContextSet

variable {W : Type*}

/-- The trivial context: all worlds possible. Alias for `Set.univ`. -/
abbrev trivial : ContextSet W := Set.univ

/-- Entailment: every world in the context satisfies the proposition.
Thin alias for `(· ⊆ ·)` so that the `⊧` notation reads naturally. -/
abbrev entails (c : ContextSet W) (p : Set W) : Prop := c ⊆ p

@[inherit_doc] notation:50 c " ⊧ " p => entails c p

/-- The context set has at least one world. Alias for `Set.Nonempty`. -/
abbrev nonEmpty (c : ContextSet W) : Prop := c.Nonempty

/-- Compatibility: some world in the context satisfies the proposition. -/
abbrev compatible (c : ContextSet W) (p : Set W) : Prop := (c ∩ p).Nonempty

/-- Update: keep only worlds where the proposition holds. Alias for `(· ∩ ·)`. -/
abbrev update (c : ContextSet W) (p : Set W) : ContextSet W := c ∩ p

@[inherit_doc] scoped notation:60 c " + " p => update c p

/-- Updated context entails the update proposition. -/
theorem update_entails (c : ContextSet W) (p : Set W) : (c + p) ⊧ p :=
  Set.inter_subset_right

/-- Updated context is contained in the original. -/
theorem update_restricts (c : ContextSet W) (p : Set W) : (c + p) ⊆ c :=
  Set.inter_subset_left

/-- Updating with what's already entailed doesn't change the context. -/
theorem update_entailed (c : ContextSet W) (p : Set W) (h : c ⊧ p) :
    (c + p) = c :=
  Set.inter_eq_left.mpr h

/-- Sequential updates are associative. -/
theorem update_assoc (c p q : Set W) :
    update (update c p) q = update c (update p q) :=
  Set.inter_assoc c p q

/-- Updating trivial context with `p` gives `p`. -/
theorem trivial_update (p : Set W) : (trivial + p) = p :=
  Set.univ_inter p

/-- Entailment is monotonic: a smaller context entails everything a larger one does. -/
theorem entails_mono {c₁ c₂ : ContextSet W} {p : Set W}
    (h_sub : c₁ ⊆ c₂) (h_ent : c₂ ⊧ p) : c₁ ⊧ p :=
  h_sub.trans h_ent

/-- Update is monotonic in the context. -/
theorem update_mono {c₁ c₂ : ContextSet W} (p : Set W) (h : c₁ ⊆ c₂) :
    update c₁ p ⊆ update c₂ p :=
  Set.inter_subset_inter_left p h

end ContextSet

/-- Common ground as a list of mutually believed propositions. -/
structure CG (W : Type*) where
  /-- The propositions in the common ground -/
  propositions : List (Set W)

namespace CG

variable {W : Type*}

/-- The context set determined by a common ground: intersection of its propositions. -/
def contextSet (cg : CG W) : ContextSet W :=
  cg.propositions.foldr (· ∩ ·) Set.univ

/-- Add a proposition to the common ground. -/
def add (cg : CG W) (p : Set W) : CG W :=
  { propositions := p :: cg.propositions }

/-- Empty common ground (no shared beliefs). -/
def empty : CG W := { propositions := [] }

instance : Inhabited (CG W) := ⟨CG.empty⟩

/-- Empty CG gives the trivial (universal) context set. -/
@[simp] theorem empty_contextSet : (empty : CG W).contextSet = ContextSet.trivial := rfl

/-- Adding a proposition intersects it into the context set. -/
@[simp] theorem contextSet_add (cg : CG W) (p : Set W) :
    (cg.add p).contextSet = p ∩ cg.contextSet := rfl

/-- Adding a proposition restricts the context set. -/
theorem add_restricts (cg : CG W) (p : Set W) :
    (cg.add p).contextSet ⊆ cg.contextSet :=
  Set.inter_subset_right

end CG

-- ════════════════════════════════════════════════════════════════
-- Unified Common Ground Interface
-- ════════════════════════════════════════════════════════════════

/-! ## HasContextSet: Uniform Access to Context Sets
@cite{ginzburg-2012} @cite{stalnaker-2002} @cite{krifka-2015}

Common ground appears in many guises across discourse theories:
`CG W` (@cite{stalnaker-2002}), `CommitmentSlate W` (@cite{krifka-2015}),
`CommitmentSpace W` (commitment trees), `DistributionalCG W` (probabilistic),
`DGB` (dialogue gameboard FACTS), and `InfoState` (TTR gameboard).
All of these induce a **context set** — the set of worlds compatible with
accumulated information.

`HasContextSet` provides uniform extraction, enabling framework-agnostic
discourse operations and bridge theorems connecting the representations. -/

/-- A discourse state from which a context set can be extracted.

Every discourse state representation (Stalnaker CG, Krifka commitment spaces,
Ginzburg DGB, distributional CG, TTR gameboard) projects to a context set:
the worlds compatible with the state's accumulated information. -/
class HasContextSet (S : Type*) (W : outParam Type*) where
  toContextSet : S → ContextSet W

namespace HasContextSet

variable {S W : Type*} [HasContextSet S W]

/-- A discourse state entails a proposition if its context set does. -/
abbrev entails (s : S) (p : Set W) : Prop := toContextSet s ⊆ p

/-- Updating a discourse state's context set with a proposition. -/
abbrev updateCS (s : S) (p : Set W) : ContextSet W := toContextSet s ∩ p

end HasContextSet

-- Canonical instances

instance {W : Type*} : HasContextSet (ContextSet W) W where
  toContextSet := id

instance {W : Type*} : HasContextSet (CG W) W where
  toContextSet := CG.contextSet

/-- The CG instance agrees with `CG.contextSet`. -/
theorem hasContextSet_CG_eq {W : Type*} (cg : CG W) :
    HasContextSet.toContextSet cg = cg.contextSet := rfl

/-- Adding to CG restricts the HasContextSet extraction. -/
theorem hasContextSet_add_restricts {W : Type*} (cg : CG W) (p : Set W) :
    HasContextSet.toContextSet (cg.add p) ⊆ HasContextSet.toContextSet cg :=
  CG.add_restricts cg p

end Core.CommonGround
