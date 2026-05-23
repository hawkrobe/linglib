import Linglib.Discourse.CommonGround
import Linglib.Discourse.Roles
import Linglib.Dialogue.Stalnaker
import Linglib.Dialogue.CommitmentSpace

/-!
# Assertable: a typeclass for commitment-tracking dialogue states

@cite{stalnaker-1978} @cite{krifka-2015} @cite{farkas-bruce-2010}
@cite{anderson-2021}

A unifying typeclass over discourse-state types that admit a one-step
"speaker asserts φ" operation whose effect on the projected context set
is to narrow it by φ (Stalnaker's classical assertion semantics, lifted
to be framework-generic).

The typeclass extends `HasContextSet S W` (re-using the existing
projection interface) and adds:

- `initial : S` — the empty / starting dialogue state.
- `speakerAssert : S → (W → Prop) → S` — record that the speaker has
  publicly committed to φ.
- `speakerAssert_monotone` — the typeclass law: every world surviving
  the asserted state was already in the prior context set AND
  satisfies the asserted proposition. This is the
  monotonicity-and-narrowing law in one shot, strong enough to prove
  compositional theorems (consecutive assertions, idempotence, etc.).

## What the typeclass is for

The point of `Assertable` is to make the **shape** of "Stalnakerian
narrowing" framework-generic. Every framework that admits an instance
satisfies the cross-framework theorems
(`speakerAssert_initial_subset`, `speakerAssert_twice_narrows`,
`speakerAssert_iter_subset_prior`) for free, lifted out of the
typeclass law. Any future framework-generic theorem about assertion
composition can be quantified over `[Assertable S W]` rather than
restated per framework.

## The structurally important non-instance

`Dialogue.FarkasBruce.DiscourseState` does **not** instantiate
`Assertable`. The reason is informationally important, not a gap to
fill: F&B's `assertDeclarative` writes to `dcS` and pushes an issue
onto the `table`, but does **not** write to `cg`. Their
`toContextSet` projects only `cg`. So the candidate "narrowing" law
`toContextSet (assertDeclarative ds φ) ⊆ φ` fails — the projection is
unchanged by the assertion.

This is not a bug in F&B; it's the F&B speaker/listener split made
visible. F&B requires a two-step `assertDeclarative ∘ acceptTop` to
produce a Stalnakerian narrowing, and that two-step composite has a
different type signature than `Assertable.speakerAssert`. The right
place to host F&B's narrowing operator is a sibling typeclass (e.g.,
`Proposable` separating *propose* from *settle*); this is left for a
future cross-framework refactor.

## Sibling notion: stability

Some frameworks have a "stability" predicate (no pending issues, no
open continuations). Stalnaker is always stable; Krifka is stable iff
`hasNoOpenContinuations`; F&B is stable iff `table.isEmpty`. The
predicate is genuine but is not a typeclass-required field — Stalnaker
provides only the trivially-True version, which is uninformative as a
hook for cross-framework theorems. We expose stability per-framework
via the existing `KrifkaState.hasNoOpenContinuations` and
`Stalnaker.isStable`.
-/

namespace Dialogue

open Discourse (DiscourseRole)
open Discourse.CommonGround (ContextSet HasContextSet)

-- ════════════════════════════════════════════════════════════════
-- § 1. The Assertable typeclass
-- ════════════════════════════════════════════════════════════════

/-- A dialogue-state type that admits a Stalnakerian one-step assertion.

    Instances satisfy two laws — `speakerAssert_subset_prior`
    (monotonicity: assertion never adds worlds) and
    `speakerAssert_narrows` (narrowing: every surviving world
    satisfies the asserted proposition). Their conjunction
    (`speakerAssert_monotone`, derived) is what compositional
    theorems consume.

    Frameworks whose "assertion" semantics differ structurally from
    Stalnaker's one-step narrowing — notably Farkas-Bruce 2010, where
    `assertDeclarative` proposes via `dcS` and `table` without
    touching `cg` — do **not** instantiate this typeclass. See the
    module docstring. -/
class Assertable (S : Type*) (W : outParam (Type*))
    extends HasContextSet S W where
  /-- The empty/initial dialogue state. -/
  initial : S
  /-- Speaker commits to φ. -/
  speakerAssert : S → (W → Prop) → S
  /-- **Monotonicity**: assertion never adds worlds — the surviving
      set is contained in the prior context set. -/
  speakerAssert_subset_prior : ∀ (s : S) (φ : W → Prop),
    toContextSet (speakerAssert s φ) ⊆ toContextSet s
  /-- **Narrowing**: every world surviving the asserted state
      satisfies the asserted proposition. The Stalnakerian half of
      the assertion law. -/
  speakerAssert_narrows : ∀ (s : S) (φ : W → Prop) (w : W),
    toContextSet (speakerAssert s φ) w → φ w

namespace Assertable

variable {S W : Type*} [Assertable S W]

/-- The conjoined narrowing-and-monotonicity law: every world
    surviving the asserted state was already in the prior context
    set AND satisfies the asserted proposition.

    Derived from the two typeclass fields. Useful when you need
    both halves of the post-assertion guarantee in a single
    hypothesis (e.g., for compositional theorems iterating the
    law across consecutive assertions). -/
theorem speakerAssert_monotone (s : S) (φ : W → Prop) (w : W)
    (h : HasContextSet.toContextSet (speakerAssert s φ) w) :
    HasContextSet.toContextSet s w ∧ φ w :=
  ⟨speakerAssert_subset_prior s φ h, speakerAssert_narrows s φ w h⟩

/-- The headline framework-generic theorem. Asserting φ from `initial`
    yields a context set entirely contained in `φ`. -/
theorem speakerAssert_initial_subset (φ : W → Prop) :
    HasContextSet.toContextSet (speakerAssert (initial : S) φ) ⊆ {w | φ w} :=
  fun w h => speakerAssert_narrows _ φ w h

/-- Two consecutive assertions narrow the context set by the
    conjunction of the two propositions.

    Lifted from the two laws: the outer narrowing gives `ψ w`; the
    monotonicity step from outer→inner pulls `w ∈ contextSet
    (speakerAssert s φ)`, and the inner narrowing then gives `φ w`. -/
theorem speakerAssert_twice_narrows (s : S) (φ ψ : W → Prop) :
    HasContextSet.toContextSet (speakerAssert (speakerAssert s φ) ψ) ⊆
      {w | φ w ∧ ψ w} := by
  intro w h
  refine ⟨?_, speakerAssert_narrows _ ψ w h⟩
  exact speakerAssert_narrows s φ w (speakerAssert_subset_prior _ ψ h)

/-- Iterated monotonicity: the chain of assertions stays within the
    initial context set. -/
theorem speakerAssert_twice_subset_prior (s : S) (φ ψ : W → Prop) :
    HasContextSet.toContextSet (speakerAssert (speakerAssert s φ) ψ) ⊆
      HasContextSet.toContextSet s :=
  Set.Subset.trans (speakerAssert_subset_prior _ ψ)
                   (speakerAssert_subset_prior s φ)

end Assertable

-- ════════════════════════════════════════════════════════════════
-- § 2. Stalnaker instance
-- ════════════════════════════════════════════════════════════════

/-- @cite{stalnaker-1978}'s common-ground-as-context-set instance.

    `speakerAssert s φ` is `s.add φ` (set intersection). The two laws
    follow from `Discourse.CommonGround.CG.contextSet` reducing the asserted
    CG to `φ ∩ s.contextSet`: monotonicity is the right conjunct of
    set-intersection membership, narrowing is the left. -/
instance instStalnaker {W : Type*} :
    Assertable (Dialogue.Stalnaker.StalnakerState W) W where
  initial := Stalnaker.initial
  speakerAssert s φ := Stalnaker.assert s φ
  -- (Stalnaker.assert s φ).contextSet = φ ∩ s.contextSet by `CG.contextSet_add`
  speakerAssert_subset_prior _ _ _ h := h.2
  speakerAssert_narrows _ _ _ h := h.1

-- ════════════════════════════════════════════════════════════════
-- § 3. Krifka (binary) instance
-- ════════════════════════════════════════════════════════════════

open Discourse.Commitment (IndexedWeightedCommitment IndexedCommitment
  CommitmentForce)

/-- @cite{krifka-2015}'s commitment-space instance, binary case.

    `speakerAssert s φ` is `s.assert φ` with default committer
    `.speaker` and default force `.doxastic`. `KrifkaState.assert`
    prepends `IndexedWeightedCommitment.commit .speaker .doxastic φ`
    to the space root; `KrifkaState.contextSet` requires every root
    commitment to project to True. At `G = Prop`, the new commit
    projects to `φ` itself (narrowing); the existing root commits
    project to the prior context set (monotonicity). -/
instance instKrifka {W : Type*} :
    Assertable (Dialogue.Krifka.KrifkaState W) W where
  initial := Krifka.KrifkaState.empty
  speakerAssert s φ := s.assert φ
  speakerAssert_subset_prior s φ w h := by
    intro ic hic
    have shifted : ic ∈ (s.assert φ).space.root := by
      simp only [Krifka.KrifkaState.assert,
                 Krifka.CommitmentSpace.assert, List.mem_cons]
      exact Or.inr hic
    exact h ic shifted
  speakerAssert_narrows s φ w h := by
    have head_mem :
        IndexedWeightedCommitment.commit (G := Prop) .speaker .doxastic φ ∈
          (s.assert φ).space.root := by
      simp only [Krifka.KrifkaState.assert,
                 Krifka.CommitmentSpace.assert, List.mem_cons, true_or]
    exact h _ head_mem

-- ════════════════════════════════════════════════════════════════
-- § 4. Smoke checks
-- ════════════════════════════════════════════════════════════════

/-- Sanity check: the cross-framework headline theorem applied at the
    Stalnaker instance reduces to a propositional fact about the
    asserted CG. -/
example {W : Type*} (φ : W → Prop) (w : W) :
    HasContextSet.toContextSet
      (Assertable.speakerAssert
        (Assertable.initial : Dialogue.Stalnaker.StalnakerState W) φ) w →
    φ w :=
  Assertable.speakerAssert_narrows _ φ w

/-- Sanity check: same theorem at the Krifka instance. -/
example {W : Type*} (φ : W → Prop) (w : W) :
    HasContextSet.toContextSet
      (Assertable.speakerAssert
        (Assertable.initial : Dialogue.Krifka.KrifkaState W) φ) w →
    φ w :=
  Assertable.speakerAssert_narrows _ φ w

/-- Sanity check: the twice-narrowing theorem at the Krifka instance. -/
example {W : Type*} (s : Dialogue.Krifka.KrifkaState W) (φ ψ : W → Prop) :
    HasContextSet.toContextSet
      (Assertable.speakerAssert
        (Assertable.speakerAssert s φ) ψ) ⊆ {w | φ w ∧ ψ w} :=
  Assertable.speakerAssert_twice_narrows s φ ψ

end Dialogue
