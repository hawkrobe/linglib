import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

/-!
# Common Ground

Framework-agnostic context management following [stalnaker-1974] and
[stalnaker-2002]: context sets, common ground as proposition lists, and
the `HasContextSet` interface unifying both with the various discourse-state
representations across the discourse layer.

## Main definitions

* `ContextSet W` — worlds compatible with the context (a synonym for `Set W`).
* `CommonGround W` — common ground as a list of propositions.
* `CommonGround.HasContextSet` — interface extracting a context set from an
  arbitrary discourse state.

## Implementation notes

`CommonGround` is the root-level type; its API (and `ContextSet` /
`HasContextSet`) lives in `namespace CommonGround`, mirroring mathlib's
`Finset`. Consumers `open CommonGround` for the API; the type itself is
visible unqualified.

Multi-agent epistemic operators (knowledge, belief, common knowledge) are in
`Semantics/Modality/EpistemicLogic.lean`.
-/

/-- Common ground as a list of mutually believed propositions. -/
structure CommonGround (W : Type*) where
  /-- The propositions in the common ground. -/
  propositions : List (Set W)

namespace CommonGround

variable {W : Type*}

/-- The set of worlds compatible with the common ground. -/
abbrev ContextSet (W : Type*) := Set W

namespace ContextSet

/-- The trivial context: all worlds possible. Alias for `Set.univ`. -/
abbrev trivial : ContextSet W := Set.univ

/-- Entailment: every world in the context satisfies the proposition. -/
abbrev entails (c : ContextSet W) (p : Set W) : Prop := c ⊆ p

/-- The context set has at least one world. Alias for `Set.Nonempty`. -/
abbrev nonEmpty (c : ContextSet W) : Prop := c.Nonempty

/-- Compatibility: some world in the context satisfies the proposition. -/
abbrev compatible (c : ContextSet W) (p : Set W) : Prop := (c ∩ p).Nonempty

/-- Update: keep only worlds where the proposition holds. Alias for `(· ∩ ·)`. -/
abbrev update (c : ContextSet W) (p : Set W) : ContextSet W := c ∩ p

/-- Updated context entails the update proposition. -/
theorem update_entails (c : ContextSet W) (p : Set W) : update c p ⊆ p :=
  Set.inter_subset_right

/-- Updated context is contained in the original. -/
theorem update_restricts (c : ContextSet W) (p : Set W) : update c p ⊆ c :=
  Set.inter_subset_left

/-- Updating with what's already entailed doesn't change the context. -/
theorem update_eq_self_of_entails (c : ContextSet W) (p : Set W) (h : c ⊆ p) :
    update c p = c :=
  Set.inter_eq_left.mpr h

/-- Sequential updates are associative. -/
theorem update_assoc (c p q : Set W) :
    update (update c p) q = update c (update p q) :=
  Set.inter_assoc c p q

/-- Successive updates commute: assertion order is irrelevant. -/
theorem update_comm (c p q : Set W) :
    update (update c p) q = update (update c q) p :=
  Set.inter_right_comm c p q

/-- Updating twice with the same proposition is updating once. -/
theorem update_idem (c p : Set W) : update (update c p) p = update c p := by
  simp [update, Set.inter_assoc]

/-- Updating the trivial context with `p` gives `p`. -/
theorem trivial_update (p : Set W) : update trivial p = p :=
  Set.univ_inter p

end ContextSet

/-- The context set determined by a common ground: intersection of its propositions. -/
def contextSet (cg : CommonGround W) : ContextSet W :=
  cg.propositions.foldr (· ∩ ·) Set.univ

/-- Add a proposition to the common ground. -/
def add (cg : CommonGround W) (p : Set W) : CommonGround W :=
  { propositions := p :: cg.propositions }

/-- Empty common ground (no shared beliefs). -/
def empty : CommonGround W := { propositions := [] }

instance : Inhabited (CommonGround W) := ⟨empty⟩

/-- Empty common ground gives the trivial (universal) context set. -/
@[simp] theorem empty_contextSet : (empty : CommonGround W).contextSet = Set.univ := rfl

/-- Adding a proposition intersects it into the context set. -/
@[simp] theorem contextSet_add (cg : CommonGround W) (p : Set W) :
    (cg.add p).contextSet = p ∩ cg.contextSet := rfl

/-- Adding a proposition restricts the context set. -/
theorem add_restricts (cg : CommonGround W) (p : Set W) :
    (cg.add p).contextSet ⊆ cg.contextSet :=
  Set.inter_subset_right

/-! ### Uniform context-set extraction -/

/-- A discourse state from which a context set can be extracted. -/
class HasContextSet (S : Type*) (W : outParam Type*) where
  toContextSet : S → ContextSet W

namespace HasContextSet

variable {S : Type*} [HasContextSet S W]

/-- A discourse state entails a proposition if its context set does. -/
abbrev entails (s : S) (p : Set W) : Prop := toContextSet s ⊆ p

/-- Updating a discourse state's context set with a proposition. -/
abbrev updateCS (s : S) (p : Set W) : ContextSet W := toContextSet s ∩ p

end HasContextSet

/-! ### Canonical instances -/

instance : HasContextSet (ContextSet W) W where
  toContextSet := id

instance : HasContextSet (CommonGround W) W where
  toContextSet := contextSet

/-- The `CommonGround` instance agrees with `CommonGround.contextSet`. -/
@[simp] theorem hasContextSet_commonGround_eq (cg : CommonGround W) :
    HasContextSet.toContextSet cg = cg.contextSet := rfl

/-- Adding to the common ground restricts the `HasContextSet` extraction. -/
theorem hasContextSet_add_restricts (cg : CommonGround W) (p : Set W) :
    HasContextSet.toContextSet (cg.add p) ⊆ HasContextSet.toContextSet cg :=
  add_restricts cg p

end CommonGround
