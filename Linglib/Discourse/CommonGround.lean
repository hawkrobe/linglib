import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Common Ground

Framework-agnostic context management following [stalnaker-1973],
[stalnaker-1974] and [stalnaker-2002]: context sets, common ground as
proposition lists, and the interfaces unifying both with the various
discourse-state representations across the discourse layer.

## Main definitions

* `ContextSet W` — worlds compatible with the context (a synonym for `Set W`).
* `CommonGround W` — common ground as a list of propositions.
* `CommonGround.HasContextSet` — interface extracting a context set from an
  arbitrary discourse state.
* `CommonGround.HasAssertion` — the Stalnakerian update law as an interface:
  discourse states whose assertion operation projects onto
  `ContextSet.update` ([stalnaker-1973] p. 455, [stalnaker-1978]).

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

/-! ### The meet monoid

`(ContextSet W, ∩, univ)` is a commutative idempotent monoid, and
`ContextSet.update` is its (right) regular action. The instance is scoped,
mirroring mathlib's `Pointwise` locale: `open CommonGround` activates it.
The same meet-monoid structure recurs one level up in inquisitive
semantics, where contexts are downward-closed sets of information states,
also updated by intersection ([ciardelli-groenendijk-roelofsen-2018]);
the classical picture formalized here is its declarative fragment, along
the Truth-Support Bridge `Question.declarativeHom` — an order-faithful
`InfTopHom` that does not preserve `⊔`
(`Semantics/Questions/Basic.lean`). -/

/-- Meet-monoid on context sets: `* = ∩`, `1 = univ`. Scoped, Pointwise-style. -/
scoped instance : CommMonoid (ContextSet W) where
  mul c p := c ∩ p
  one := ContextSet.trivial
  mul_assoc := Set.inter_assoc
  mul_comm := Set.inter_comm
  one_mul := Set.univ_inter
  mul_one := Set.inter_univ

theorem ContextSet.update_eq_mul (c : ContextSet W) (p : Set W) :
    ContextSet.update c p = c * p := rfl

theorem ContextSet.trivial_eq_one : (ContextSet.trivial : ContextSet W) = 1 := rfl

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

/-! ### Stalnakerian assertion: `HasAssertion`

A unifying interface over discourse-state types that admit a one-step
"speaker asserts φ" operation whose effect on the projected context set is
exactly Stalnaker's: the context set is updated to its intersection with φ
(`ContextSet.update`). The law is [stalnaker-1973]'s update principle —
"after some proposition has been asserted, then the speaker may reasonably
presuppose it in subsequent conversation" (p. 455) — projected through the
worlds-side characterization of the presupposition set (p. 450), and
[stalnaker-1978]'s essential effect of assertion.

Mathematically: `(Set W, ∩, univ)` is a commutative idempotent monoid `M`,
and `ContextSet.update` is its right regular action. A `HasAssertion`
structure is a raw pointed `M`-flow `(S, assert, initial)` together
with an equivariant pointed map into the regular act:
`toContextSet initial = univ` and
`toContextSet (assert s φ) = toContextSet s ∩ φ`. No act laws are
demanded of `S` itself — states may record commitment order, sources, or
credences — but every equation of `M` transports along the projection,
which is where the lemma kit (`assert_comm`, `_idem`, `_initial`,
...) comes from. Frameworks differ in the kernel of the projection (state
structure the context set cannot see); on states reachable from `initial`,
the projection is forced: the intersection of everything asserted.

The 1973 principle's own hedge — the asserted proposition stands "until it
is denied, challenged, retracted or forgotten" — marks the idealization
this interface bakes in: assertion takes effect immediately and
unchallenged. Frameworks that model the challenge stage explicitly, or
that update non-monotonically, do **not** instantiate it — informationally
important non-instances, not gaps:

* Proposal-based models — [farkas-bruce-2010], where assertion proposes
  via `dcS` and `table` without touching `cg` until uptake (witnessed by
  `FarkasBruce2010.assert_not_narrowing`).
* Graded models — [anderson-2021], whose distributional common ground is
  non-monotonic by design (excluded worlds can regain probability), so no
  sharp narrowing law holds
  (`Anderson2021.graded_update_keeps_false_world`).

Framework instances live with the framework types:
`Discourse/Stalnaker.lean` (via the `CommonGround` instance below),
`Discourse/CommitmentSpace.lean` ([krifka-2015] commitment spaces),
`Discourse/Gunlogson.lean` ([gunlogson-2004] source-marked commitments),
`Discourse/CredenceThreshold.lean` (credence-gated assertion).
-/

/-- A dialogue-state type that admits a Stalnakerian one-step assertion:
    `assert s φ` takes immediate effect on the projected context
    set, updating it by exactly `φ` — [stalnaker-1978]'s essential
    effect, under the idealization that assertion is not challenged. -/
class HasAssertion (S : Type*) (W : outParam Type*)
    extends HasContextSet S W where
  /-- The initial dialogue state. -/
  initial : S
  /-- Speaker commits to φ. -/
  assert : S → Set W → S
  /-- Nothing is presupposed initially: every world is live. -/
  toContextSet_initial : toContextSet initial = ContextSet.trivial (W := W)
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
  toContextSet_assert s φ ▸ ContextSet.update_entails _ φ

/-- Membership in the post-assertion context set, characterized. -/
theorem mem_assert {s : S} {φ : Set W} {w : W} :
    w ∈ toContextSet (assert s φ) ↔ w ∈ toContextSet s ∧ w ∈ φ := by
  rw [toContextSet_assert]; exact Set.mem_inter_iff ..

/-- Asserting φ in the initial context yields exactly φ. -/
@[simp] theorem assert_initial :
    toContextSet (assert (initial : S) φ) = φ := by
  rw [toContextSet_assert, toContextSet_initial, ContextSet.trivial_update]

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

/-- Asserting what the state already entails does not change the
    projected context set — the formal shadow of [stalnaker-1973]'s
    constraint that asserted content normally not already be
    presupposed (p. 454): such an assertion is a no-op. -/
theorem assert_of_entails (h : toContextSet s ⊆ φ) :
    toContextSet (assert s φ) = toContextSet s := by
  rw [toContextSet_assert]
  exact ContextSet.update_eq_self_of_entails _ φ h

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

/-! ### The assertion action and its equivariant projection

`HasAssertion` in mathlib vocabulary: propositions act on states by
assertion (a raw `SMul`), the meet monoid acts on itself regularly
(`Mul.toSMul`), and `toContextSet` is an equivariant map between the two
actions (a mathlib `MulActionHom`) sending `initial` to `1`. No action
laws are demanded of the state side — states may record commitment order,
sources, or credences — yet the projected dynamics inherits every monoid
equation, and on a played history the projection is the monoid product. -/

namespace HasAssertion

open HasContextSet (toContextSet)

variable {S : Type*} [HasAssertion S W]

/-- Propositions act on any `HasAssertion` state by assertion. Scoped. -/
scoped instance : SMul (Set W) S := ⟨fun φ s => assert s φ⟩

theorem smul_eq_assert (φ : Set W) (s : S) : φ • s = assert s φ := rfl

/-- `toContextSet` bundled as an equivariant map (`MulActionHom`) from the
    assertion action to the regular action of the meet monoid. -/
def toContextSetHom (S : Type*) [HasAssertion S W] :
    S →[Set W] ContextSet W where
  toFun := toContextSet
  map_smul' φ s := by
    show toContextSet (assert s φ) = φ * toContextSet s
    rw [toContextSet_assert]
    exact Set.inter_comm _ φ

/-- Play a history of assertions from a state. -/
def play (s : S) (h : List (Set W)) : S :=
  h.foldl assert s

/-- **Forced projection**: the context set of a played history is the
    monoid product — the intersection — of the history. [stalnaker-1973]
    p. 450's propositions-to-worlds duality as a hom equation. -/
theorem toContextSet_play (h : List (Set W)) :
    toContextSet (play (initial : S) h) = h.prod := by
  suffices key : ∀ (s : S), toContextSet (play s h) =
      toContextSet s * h.prod by
    rw [key, toContextSet_initial, ContextSet.trivial_eq_one, one_mul]
  induction h with
  | nil => intro s; simp [play]
  | cons φ t ih =>
    intro s
    rw [List.prod_cons, show play s (φ :: t) = play (assert s φ) t from rfl,
      ih, toContextSet_assert, ContextSet.update_eq_mul]
    exact mul_assoc _ _ _

end HasAssertion

end CommonGround
