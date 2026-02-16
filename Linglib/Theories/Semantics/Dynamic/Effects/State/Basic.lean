import Linglib.Theories.Semantics.Dynamic.Core.Update

/-!
# State Effect: Assignment Threading

The state effect underlies anaphora resolution in dynamic semantics. It threads
variable assignments through interpretation, allowing one sentence to bind
variables that later sentences can access.

This module collects state-based semantic frameworks:
- **File Change Semantics** (Heim 1982, 1983): meanings as context change potentials
  over files (sets of world-assignment pairs)
- **Update Semantics** (Veltman 1996): propositional update with epistemic modals

Both are instances of the state effect: they differ in whether the state tracks
assignments (FCS) or just worlds (Update Semantics).
-/

/-!
## File Change Semantics (Heim 1982, 1983)

Heim's File Metaphor:
- The context is a "file" of information about discourse referents
- Each "file card" is a possibility: (world, assignment) pair
- Sentences update the file by adding/removing cards
- Indefinites "open" new file cards

⟦φ⟧ : File → File (sentences are context change potentials)

## References

- Heim, I. (1982). The Semantics of Definite and Indefinite Noun Phrases.
  PhD dissertation, University of Massachusetts.
- Heim, I. (1983). File Change Semantics and the Familiarity Theory of
  Definiteness. In Bäuerle et al. (eds.), Meaning, Use, and Interpretation.
-/

namespace DynamicSemantics.FileChangeSemantics

open DynamicSemantics.Core
open Classical

/--
A File is an information state: set of (world, assignment) pairs.

This is Heim's "file metaphor" - each pair is a "file card".
-/
abbrev File (W : Type*) (E : Type*) := InfoState W E

/--
A File Card is a single possibility: (world, assignment).
-/
abbrev FileCard (W : Type*) (E : Type*) := Possibility W E

/--
Variable x is NOVEL in file f iff f doesn't constrain x.

Indefinites require their variable to be novel - this prevents
the same variable being reused inappropriately.
-/
def File.novel {W E : Type*} (f : File W E) (x : Nat) : Prop :=
  f.novelAt x

/--
Variable x is FAMILIAR in file f iff f constrains x uniquely.

Definites require their variable to be familiar - the discourse
must have already established who "the X" refers to.
-/
def File.familiar {W E : Type*} (f : File W E) (x : Nat) : Prop :=
  f.definedAt x

/--
Update file with proposition: eliminate cards where φ fails.

f[φ] = { c ∈ f | φ(c.world) }
-/
def File.updateProp {W E : Type*} (f : File W E) (φ : W → Bool) : File W E :=
  f.update φ

/--
Introduce new discourse referent (indefinite).

f[x:=?] adds cards for each possible entity value of x.
Requires x to be NOVEL (precondition).
-/
def File.introduce {W E : Type*} (f : File W E) (x : Nat) (dom : Set E) : File W E :=
  f.randomAssign x dom

/--
File Change Potential (FCP): the semantic type for sentences in FCS.
-/
abbrev FCP (W : Type*) (E : Type*) := File W E → File W E

/--
Atomic predicate update.
-/
def FCP.atom {W E : Type*} (pred : W → Bool) : FCP W E :=
  λ f => f.updateProp pred

/--
Indefinite introduction: requires novelty.

This models "a man" - introduces a new discourse referent.
-/
def FCP.indefinite {W E : Type*} (x : Nat) (dom : Set E) (body : FCP W E) : FCP W E :=
  λ f => body (f.introduce x dom)

/--
Definite reference: requires familiarity.

This models "the man" - presupposes the referent is established.
-/
def FCP.definite {W E : Type*} (x : Nat) (body : FCP W E) : FCP W E :=
  λ f => if f.familiar x then body f else ∅

/--
Conjunction: sequential file update.

f[φ ∧ ψ] = f[φ][ψ]

Delegates to `Core.CCP.seq`.
-/
def FCP.conj {W E : Type*} (φ ψ : FCP W E) : FCP W E :=
  Core.CCP.seq φ ψ

/--
Negation: test-based (standard FCS).

f[¬φ] = f if f[φ] = ∅, else ∅

Note: This does NOT validate DNE.
Delegates to `Core.CCP.neg`.
-/
noncomputable def FCP.neg {W E : Type*} (φ : FCP W E) : FCP W E :=
  Core.CCP.neg φ

/--
Novelty precondition for indefinites.

Attempting to introduce a non-novel variable is undefined behavior
(typically modeled as returning ∅ or crash).
-/
def requiresNovelty {W E : Type*} (f : File W E) (x : Nat) : Prop :=
  f.novel x

/--
Familiarity precondition for definites.
-/
def requiresFamiliarity {W E : Type*} (f : File W E) (x : Nat) : Prop :=
  f.familiar x

/-!
### Relation to DynamicSemantics.Core.Basic

The `DynamicSemantics.Core.Basic` module provides the canonical infrastructure.
This module provides FCS-specific vocabulary as aliases:

| This Module | DynamicSemantics.Core |
|-------------|----------------------|
| File | InfoState |
| FileCard | Possibility |
| novel | novelAt |
| familiar | definedAt |
| introduce | randomAssign |
| updateProp | update |
-/

end DynamicSemantics.FileChangeSemantics


/-!
## Update Semantics (Veltman 1996)

In Update Semantics:
- Information states are sets of worlds (not assignments)
- Sentences update states by eliminating incompatible worlds
- "Might φ" is a TEST: passes if some φ-worlds remain
- No discourse referents (simpler than DRT/DPL)

⟦φ⟧ : State → State where State = Set World

## References

- Veltman, F. (1996). Defaults in Update Semantics. Journal of Philosophical Logic 25:221-261.
-/

namespace DynamicSemantics.UpdateSemantics

open Classical

/--
Update Semantics state: a set of possible worlds.

Unlike DPL/DRT, no assignment component - US focuses on propositional content.
-/
abbrev State (W : Type*) := Set W

/--
Update function: how a sentence modifies a state.
-/
def Update (W : Type*) := State W → State W

/--
Propositional update: eliminate worlds where φ fails.

⟦φ⟧(s) = { w ∈ s | φ(w) }
-/
def Update.prop {W : Type*} (φ : W → Bool) : Update W :=
  λ s => { w ∈ s | φ w }

/--
Conjunction: sequential update.

⟦φ ∧ ψ⟧ = ⟦ψ⟧ ∘ ⟦φ⟧

Delegates to `Core.CCP.seq`.
-/
def Update.conj {W : Type*} (φ ψ : Update W) : Update W :=
  Core.CCP.seq φ ψ

/--
Negation: test and possibly fail.

⟦¬φ⟧(s) = s if ⟦φ⟧(s) = ∅, else ∅

Delegates to `Core.CCP.neg`.
-/
noncomputable def Update.neg {W : Type*} (φ : Update W) : Update W :=
  Core.CCP.neg φ

/--
Epistemic "might": compatibility test.

⟦might φ⟧(s) = s if ⟦φ⟧(s) ≠ ∅, else ∅

Delegates to `Core.CCP.might`.
-/
noncomputable def Update.might {W : Type*} (φ : Update W) : Update W :=
  Core.CCP.might φ

/--
Epistemic "must": universal test.

⟦must φ⟧(s) = s if ⟦φ⟧(s) = s, else ∅

Delegates to `Core.CCP.must`.
-/
noncomputable def Update.must {W : Type*} (φ : Update W) : Update W :=
  Core.CCP.must φ

/--
Might is a TEST: it doesn't change the state (if it passes).
-/
theorem might_is_test {W : Type*} (φ : Update W) (s : State W)
    (h : (φ s).Nonempty) :
    Update.might φ s = s := by
  simp [Update.might, Core.CCP.might, h]

/--
Order matters for epistemic might.

"It's raining and it might not be raining" is contradictory:
after learning rain, the might-not-rain test fails (no ¬rain worlds remain).
But "it might not be raining and it's raining" can succeed:
the might test passes on the initial state, then learning eliminates ¬rain worlds.

TODO: Prove by exhibiting a state with both p-worlds and ¬p-worlds.
Requires `Nontrivial W`: for empty or singleton W, no state has both
p-worlds and ¬p-worlds, making the second conjunct unsatisfiable. -/
theorem might_order_matters {W : Type*} [Nontrivial W] :
    ∃ (p : W → Bool) (s : State W),
      Update.conj (Update.prop p) (Update.might (Update.prop λ w => !p w)) s = ∅ ∧
      (Update.conj (Update.might (Update.prop λ w => !p w)) (Update.prop p) s).Nonempty := by
  sorry

/--
State s supports φ iff updating with φ doesn't change s.

s ⊨ φ iff ⟦φ⟧(s) = s
-/
def supports {W : Type*} (s : State W) (φ : Update W) : Prop :=
  φ s = s

/--
State s accepts φ iff updating with φ yields a non-empty state.

s accepts φ iff ⟦φ⟧(s) ≠ ∅
-/
def accepts {W : Type*} (s : State W) (φ : Update W) : Prop :=
  (φ s).Nonempty

end DynamicSemantics.UpdateSemantics
