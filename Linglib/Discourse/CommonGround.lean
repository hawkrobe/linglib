import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Perm.Basic

/-!
# Common Ground

Stalnakerian context management ([stalnaker-1973], [stalnaker-1974],
[stalnaker-1978], [stalnaker-2002]): context sets and their update, common
ground as proposition lists, and the interfaces connecting discourse-state
representations to both.

## Main definitions

* `ContextSet W` — worlds compatible with the context (a synonym for
  `Set W`), with `ContextSet.update`.
* `CommonGround W` — common ground as a list of propositions.
* `CommonGround.HasContextSet` — extraction of a context set from a
  discourse state.
* `CommonGround.HasAssertion` — discourse states whose assertion operation
  projects onto `ContextSet.update` ([stalnaker-1973] p. 455); a played
  history lands on the free model (`toContextSet_play`) and its projection
  is permutation-invariant (`toContextSet_play_perm`).

Proposal-based ([farkas-bruce-2010]) and graded non-monotonic
([anderson-2021]) assertion models are deliberate non-instances; see
`FarkasBruce2010.assert_not_narrowing` and
`Anderson2021.graded_update_keeps_false_world`.
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

/-- Compatibility: some world in the context satisfies the proposition. -/
abbrev compatible (c : ContextSet W) (p : Set W) : Prop := (c ∩ p).Nonempty

/-- Update: keep only worlds where the proposition holds. Alias for `(· ∩ ·)`. -/
abbrev update (c : ContextSet W) (p : Set W) : ContextSet W := c ∩ p

/-- Updated context is contained in the original. -/
theorem update_restricts (c : ContextSet W) (p : Set W) : update c p ⊆ c :=
  Set.inter_subset_left

/-- Successive updates commute: assertion order is irrelevant. -/
theorem update_comm (c p q : Set W) :
    update (update c p) q = update (update c q) p :=
  Set.inter_right_comm c p q

/-- Updating twice with the same proposition is updating once. -/
theorem update_idem (c p : Set W) : update (update c p) p = update c p := by
  simp [update, Set.inter_assoc]

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

instance : LeftCommutative (α := Set W) (· ∩ ·) := ⟨Set.inter_left_comm⟩

/-- The context set is invariant under permutation of the propositions:
    the common ground is order-indifferent on its worlds-side projection. -/
theorem contextSet_perm {l₁ l₂ : List (Set W)} (p : l₁.Perm l₂) :
    contextSet ⟨l₁⟩ = contextSet ⟨l₂⟩ :=
  p.foldr_eq Set.univ

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

/-! ### Stalnakerian assertion -/

/-- A discourse state with a Stalnakerian `assert`: the projected context
    set updates by exactly the asserted proposition ([stalnaker-1978]). -/
class HasAssertion (S : Type*) (W : outParam Type*)
    extends HasContextSet S W where
  /-- The initial dialogue state. -/
  initial : S
  /-- Assert φ. -/
  assert : S → Set W → S
  /-- Nothing is presupposed initially: every world is live. -/
  toContextSet_initial : toContextSet initial = ContextSet.trivial
  /-- Assertion narrows the projected context set by exactly `φ`. -/
  toContextSet_assert : ∀ (s : S) (φ : Set W),
    toContextSet (assert s φ) = ContextSet.update (toContextSet s) φ

namespace HasAssertion

open HasContextSet (toContextSet)

variable {S : Type*} [HasAssertion S W] (s : S) (φ ψ : Set W)

/-- Contraction: assertion only removes worlds. -/
theorem assert_subset_prior :
    toContextSet (assert s φ) ⊆ toContextSet s :=
  toContextSet_assert s φ ▸ ContextSet.update_restricts _ φ

/-- Narrowing: every surviving world satisfies the asserted proposition. -/
theorem assert_narrows :
    toContextSet (assert s φ) ⊆ φ :=
  toContextSet_assert s φ ▸ Set.inter_subset_right

/-- Membership in the post-assertion context set, characterized. -/
theorem mem_assert {s : S} {φ : Set W} {w : W} :
    w ∈ toContextSet (assert s φ) ↔ w ∈ toContextSet s ∧ w ∈ φ := by
  rw [toContextSet_assert]; exact Set.mem_inter_iff ..

/-- Asserting φ in the initial context yields exactly φ. -/
@[simp] theorem assert_initial :
    toContextSet (assert (initial : S) φ) = φ := by
  rw [toContextSet_assert, toContextSet_initial]
  exact Set.univ_inter φ

/-- Assertion order is irrelevant on the projected context set. -/
theorem assert_comm :
    toContextSet (assert (assert s φ) ψ) =
      toContextSet (assert (assert s ψ) φ) := by
  simp only [toContextSet_assert]
  exact ContextSet.update_comm _ φ ψ

/-- Re-asserting φ does not change the projected context set. -/
theorem assert_idem :
    toContextSet (assert (assert s φ) φ) =
      toContextSet (assert s φ) := by
  simp only [toContextSet_assert]
  exact ContextSet.update_idem _ φ

/-- Asserting what the state already entails is a no-op on the projected
    context set ([stalnaker-1973] p. 454). -/
theorem assert_of_entails (h : toContextSet s ⊆ φ) :
    toContextSet (assert s φ) = toContextSet s := by
  rw [toContextSet_assert]
  exact Set.inter_eq_left.mpr h

/-- Two consecutive assertions narrow the context set by the conjunction. -/
theorem assert_twice :
    toContextSet (assert (assert s φ) ψ) =
      toContextSet s ∩ φ ∩ ψ := by
  rw [toContextSet_assert, toContextSet_assert]

/-- Two consecutive assertions land inside the conjunction. -/
theorem assert_twice_narrows :
    toContextSet (assert (assert s φ) ψ) ⊆ φ ∩ ψ := by
  rw [assert_twice]
  exact Set.subset_inter (Set.inter_subset_left.trans Set.inter_subset_right)
    Set.inter_subset_right

end HasAssertion

/-- The regular model: the context set itself, asserted-into by `update`.
    Every `HasAssertion` state projects onto this flow. -/
instance : HasAssertion (ContextSet W) W where
  initial := ContextSet.trivial
  assert := ContextSet.update
  toContextSet_initial := rfl
  toContextSet_assert _ _ := rfl

/-- The free model: proposition lists, asserted-into by `add`; the
    projection is `contextSet` ([stalnaker-1973] p. 450's duality map).
    `Discourse/Stalnaker.lean`'s framework rides this instance through the
    `StalnakerState W := CommonGround W` abbrev. -/
instance : HasAssertion (CommonGround W) W where
  initial := empty
  assert cg φ := cg.add φ
  toContextSet_initial := rfl
  toContextSet_assert _ φ := Set.inter_comm φ _

/-! ### Assertion histories -/

namespace HasAssertion

open HasContextSet (toContextSet)

variable {S : Type*} [HasAssertion S W]

/-- Play a history of assertions from a state. -/
def play (s : S) (h : List (Set W)) : S :=
  h.foldl assert s

@[simp] theorem play_nil (s : S) : play s [] = s := rfl

@[simp] theorem play_cons (s : S) (φ : Set W) (t : List (Set W)) :
    play s (φ :: t) = play (assert s φ) t := rfl

/-- The context set of a played history is the common ground of that
    history: `play` from `initial` lands on the free model
    ([stalnaker-1973] p. 450). -/
theorem toContextSet_play (h : List (Set W)) :
    toContextSet (play (initial : S) h) = contextSet ⟨h⟩ := by
  suffices key : ∀ s : S,
      toContextSet (play s h) = toContextSet s ∩ contextSet ⟨h⟩ by
    rw [key, toContextSet_initial]
    exact Set.univ_inter _
  induction h with
  | nil => intro s; exact (Set.inter_univ _).symm
  | cons φ t ih =>
    intro s
    rw [play_cons, ih, toContextSet_assert]
    exact Set.inter_assoc ..

/-- Assertion order is irrelevant: permuted histories project to the
    same context set. States may differ — frameworks can record order —
    but the projection cannot. -/
theorem toContextSet_play_perm {h₁ h₂ : List (Set W)} (p : h₁.Perm h₂) :
    toContextSet (play (initial : S) h₁) =
      toContextSet (play (initial : S) h₂) := by
  rw [toContextSet_play, toContextSet_play]
  exact contextSet_perm p

end HasAssertion

end CommonGround
