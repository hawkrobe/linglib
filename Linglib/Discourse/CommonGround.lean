import Mathlib.Order.Filter.Ker

/-!
# Common ground

The common ground of a conversation is the **filter** of propositions the interlocutors
mutually accept ([stalnaker-1978], [stalnaker-2002]; independently
[karttunen-1974-presupposition]): acceptance is closed under entailment
and finite conjunction and contains the trivial proposition, which are exactly the filter
axioms (in modal-logic terms: "every augmented model is a filter", [chellas-1980] §7.3;
in belief-revision terms, a deductively closed belief set, [gardenfors-1988]). Stalnaker's
**context set** — the worlds compatible with everything accepted — is the kernel
`Filter.ker`, [chellas-1980]'s smallest proposition `⋂ Nα`, and a bare context set
`cs : Set W` is the principal common ground `𝓟 cs`, with acceptance `p ∈ 𝓟 cs ↔ cs ⊆ p`
(`Filter.mem_principal`); `Filter.giPrincipalKer` is the two-sidedness of this duality, and
the principal (augmented) case is exactly the Kripke case ([chellas-1980] Theorem 7.9).
**Assertion** of `φ` is `· ⊓ 𝓟 φ` ([stalnaker-1978]):
intersective update of the context set is `Filter.ker_inf`, and commutativity and
idempotence of assertion are lattice laws. A **consistent** context is a `Filter.NeBot`;
the absurd context is `⊥`.

`HasCommonGround` and `HasAssertion` connect richer discourse-state representations
(commitment slates, gameboards, probabilistic states) to this projection.

## Implementation notes

The filter axioms are the body-of-information view of the common ground ([geurts-2024]'s
survey) and deliberately carry no epistemology: whether what grounds them is iterated
common belief ([stalnaker-2002]), common acceptance as a primitive ([stalnaker-2014]), or
[lederman-2014]'s non-iterated minimal theory is stated separately, as `Filter.GroundedIn`
in `Logic/Modal/Epistemic.lean` — the epistemology, and in particular closure of acceptance
under conjunction (the filter's `inter_sets`, [lederman-2014] §2.C's contested axiom), is
the disputed idealization in that debate, not a commitment every consumer inherits.
Proposal-based ([farkas-bruce-2010]) and graded non-monotonic ([anderson-2021]) assertion
models are deliberate non-instances of `HasAssertion`; see
`FarkasBruce2010.assert_not_narrowing` and `Anderson2021.graded_update_keeps_false_world`.

## Main definitions

* `HasCommonGround`: discourse states projecting to a common ground `Filter W`, with the
  derived `contextSet`.
* `HasAssertion`: discourse states with a Stalnakerian `assert`, projecting to `· ⊓ 𝓟 φ`,
  and assertion histories `HasAssertion.play`.

## Main results

* `HasAssertion.contextSet_assert`: assertion intersects the context set by exactly the
  asserted proposition ([stalnaker-1973] p. 455).
* `HasAssertion.commonGround_play`: a played history lands on the principal filter of the
  history's intersection ([stalnaker-1973] p. 450's duality map), so the projection is
  permutation-invariant (`commonGround_play_perm`) — states may record assertion order,
  but the common ground cannot.
-/

open Filter Set

variable {W : Type*}

/-! ### Discourse states and their common ground -/

/-- A discourse state projecting to a common ground: the filter of propositions the
interlocutors mutually accept at that state. -/
class HasCommonGround (S : Type*) (W : outParam Type*) where
  /-- The common ground of the state. -/
  commonGround : S → Filter W

export HasCommonGround (commonGround)

/-- The context set of a discourse state: the worlds compatible with everything accepted. -/
def HasCommonGround.contextSet {S : Type*} [HasCommonGround S W] (s : S) : Set W :=
  (commonGround s).ker

/-- A filter is its own common ground. -/
instance : HasCommonGround (Filter W) W := ⟨id⟩

@[simp] theorem HasCommonGround.commonGround_filter (f : Filter W) : commonGround f = f := rfl

/-! ### Stalnakerian assertion -/

/-- A discourse state with a Stalnakerian `assert`: the projected common ground grows by
exactly the asserted proposition ([stalnaker-1978]). -/
class HasAssertion (S : Type*) (W : outParam Type*) extends HasCommonGround S W where
  /-- The initial dialogue state. -/
  initial : S
  /-- Assert `φ`. -/
  assert : S → Set W → S
  /-- Nothing is presupposed initially. -/
  commonGround_initial : commonGround initial = ⊤
  /-- Assertion adds exactly `φ` to the common ground. -/
  commonGround_assert : ∀ (s : S) (φ : Set W), commonGround (assert s φ) = commonGround s ⊓ 𝓟 φ

/-- The regular model: a common ground asserted-into by `· ⊓ 𝓟 φ`. Every `HasAssertion`
state projects onto this flow. -/
instance : HasAssertion (Filter W) W where
  initial := ⊤
  assert f φ := f ⊓ 𝓟 φ
  commonGround_initial := rfl
  commonGround_assert _ _ := rfl

namespace HasAssertion

open HasCommonGround (contextSet)

variable {S : Type*} [HasAssertion S W] (s : S) (φ ψ : Set W)

attribute [simp] commonGround_initial commonGround_assert

/-- The asserted proposition is accepted. -/
theorem mem_commonGround_assert : φ ∈ commonGround (assert s φ) := by
  simp [le_principal_iff.1 inf_le_right]

/-- Assertion strengthens the common ground. -/
theorem commonGround_assert_le : commonGround (assert s φ) ≤ commonGround s := by
  simp [inf_le_left]

/-- Assertion intersects the context set by exactly the asserted proposition
([stalnaker-1973] p. 455). -/
@[simp] theorem contextSet_assert : contextSet (assert s φ) = contextSet s ∩ φ := by
  simp [contextSet, HasCommonGround.contextSet]

/-- Asserting in the initial state yields the principal common ground. -/
@[simp] theorem commonGround_assert_initial :
    commonGround (assert (initial : S) φ) = 𝓟 φ := by simp

/-- Two consecutive assertions add the conjunction. -/
theorem commonGround_assert_assert :
    commonGround (assert (assert s φ) ψ) = commonGround s ⊓ 𝓟 (φ ∩ ψ) := by
  simp [inf_assoc, inf_principal]

/-- Assertion order is irrelevant on the common ground. -/
theorem commonGround_assert_comm :
    commonGround (assert (assert s φ) ψ) = commonGround (assert (assert s ψ) φ) := by
  simp only [commonGround_assert_assert, inter_comm]

/-- Re-assertion is a no-op on the common ground. -/
theorem commonGround_assert_idem :
    commonGround (assert (assert s φ) φ) = commonGround (assert s φ) := by
  simp

/-- Asserting what is already accepted is a no-op on the common ground
([stalnaker-1973] p. 454). -/
theorem commonGround_assert_of_mem (h : φ ∈ commonGround s) :
    commonGround (assert s φ) = commonGround s := by
  simp [inf_eq_left.2 (le_principal_iff.2 h)]

/-! ### Assertion histories -/

/-- Play a history of assertions from a state. -/
def play (s : S) (h : List (Set W)) : S :=
  h.foldl assert s

@[simp] theorem play_nil (s : S) : play s [] = s := rfl

@[simp] theorem play_cons (s : S) (φ : Set W) (t : List (Set W)) :
    play s (φ :: t) = play (assert s φ) t := rfl

/-- A played history adds the principal filter of the history's intersection. -/
theorem commonGround_play (h : List (Set W)) (s : S) :
    commonGround (play s h) = commonGround s ⊓ 𝓟 {w | ∀ p ∈ h, w ∈ p} := by
  induction h generalizing s with
  | nil => simp
  | cons φ t ih =>
    have h : φ ∩ {w | ∀ p ∈ t, w ∈ p} = {w | ∀ p ∈ φ :: t, w ∈ p} := by
      ext w
      simp
    rw [play_cons, ih, commonGround_assert, inf_assoc, inf_principal, h]

/-- From the initial state, a played history *is* its common ground: the free model of
Stalnakerian assertion ([stalnaker-1973] p. 450). -/
theorem commonGround_play_initial (h : List (Set W)) :
    commonGround (play (initial : S) h) = 𝓟 {w | ∀ p ∈ h, w ∈ p} := by
  simp [commonGround_play]

/-- Assertion order is irrelevant: permuted histories project to the same common ground.
States may differ — frameworks can record order — but the projection cannot. -/
theorem commonGround_play_perm {h₁ h₂ : List (Set W)} (p : h₁.Perm h₂) :
    commonGround (play (initial : S) h₁) = commonGround (play (initial : S) h₂) := by
  simp only [commonGround_play_initial]
  exact congrArg _ (Set.ext fun w => ⟨fun h q hq => h q (p.mem_iff.2 hq),
    fun h q hq => h q (p.mem_iff.1 hq)⟩)

end HasAssertion
