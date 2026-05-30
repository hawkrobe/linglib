import Linglib.Discourse.CommonGround

/-!
# Speech-Act Update: Stalnakerian narrowing as a typeclass
@cite{stalnaker-1978} @cite{krifka-2015} @cite{anderson-2021}

A unifying typeclass over discourse-state types that admit a one-step
"speaker asserts φ" operation whose effect on the projected context
set is to narrow it by φ (Stalnaker's classical assertion semantics,
lifted to be framework-generic).

Frameworks whose assertion semantics differ structurally from
Stalnaker's one-step narrowing — notably @cite{farkas-bruce-2010},
where assertion proposes via `dcS` and `table` without touching
`cg` — do **not** instantiate this typeclass. That's an
informationally important non-instance, not a gap.

## Main definitions

* `Assertable S W` — typeclass with `initial`, `speakerAssert`, and
  two laws (`speakerAssert_subset_prior`, `speakerAssert_narrows`).
* `speakerAssert_monotone` — derived conjunction of the two laws.
* `speakerAssert_initial_subset` — headline framework-generic theorem.
* `speakerAssert_twice_narrows` — composition lemma.

Instances live with the framework types (e.g. `Dialogue/Stalnaker.lean`,
`Dialogue/CommitmentSpace.lean`).
-/

namespace Discourse.SpeechAct

open CommonGround (HasContextSet)

/-- A dialogue-state type that admits a Stalnakerian one-step
    assertion: `speakerAssert s φ` is monotone (never adds worlds)
    and narrowing (every surviving world satisfies `φ`). -/
class Assertable (S : Type*) (W : outParam (Type*))
    extends HasContextSet S W where
  /-- The empty/initial dialogue state. -/
  initial : S
  /-- Speaker commits to φ. -/
  speakerAssert : S → (W → Prop) → S
  /-- Monotonicity: assertion never adds worlds. -/
  speakerAssert_subset_prior : ∀ (s : S) (φ : W → Prop),
    toContextSet (speakerAssert s φ) ⊆ toContextSet s
  /-- Narrowing: every surviving world satisfies the asserted proposition. -/
  speakerAssert_narrows : ∀ (s : S) (φ : W → Prop) (w : W),
    toContextSet (speakerAssert s φ) w → φ w

namespace Assertable

variable {S W : Type*} [Assertable S W]

/-- The conjoined narrowing-and-monotonicity law. -/
theorem speakerAssert_monotone (s : S) (φ : W → Prop) (w : W)
    (h : HasContextSet.toContextSet (speakerAssert s φ) w) :
    HasContextSet.toContextSet s w ∧ φ w :=
  ⟨speakerAssert_subset_prior s φ h, speakerAssert_narrows s φ w h⟩

/-- Asserting φ from `initial` yields a context set contained in φ. -/
theorem speakerAssert_initial_subset (φ : W → Prop) :
    HasContextSet.toContextSet (speakerAssert (initial : S) φ) ⊆ {w | φ w} :=
  fun w h => speakerAssert_narrows _ φ w h

/-- Two consecutive assertions narrow the context set by the conjunction. -/
theorem speakerAssert_twice_narrows (s : S) (φ ψ : W → Prop) :
    HasContextSet.toContextSet (speakerAssert (speakerAssert s φ) ψ) ⊆
      {w | φ w ∧ ψ w} := by
  intro w h
  refine ⟨?_, speakerAssert_narrows _ ψ w h⟩
  exact speakerAssert_narrows s φ w (speakerAssert_subset_prior _ ψ h)

/-- Iterated monotonicity. -/
theorem speakerAssert_twice_subset_prior (s : S) (φ ψ : W → Prop) :
    HasContextSet.toContextSet (speakerAssert (speakerAssert s φ) ψ) ⊆
      HasContextSet.toContextSet s :=
  Set.Subset.trans (speakerAssert_subset_prior _ ψ)
                   (speakerAssert_subset_prior s φ)

end Assertable

end Discourse.SpeechAct
