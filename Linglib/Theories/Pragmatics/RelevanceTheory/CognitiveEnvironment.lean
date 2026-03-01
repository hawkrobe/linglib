import Mathlib.Data.Rat.Defs

/-!
# Cognitive Environments — Sperber & Wilson (1986/95)

The cognitive environment of an individual is the set of all facts that are
manifest to them. Manifestness is graded: perceptually obvious facts are
highly manifest; distant inferences are weakly manifest.

| Definition | S&W Reference |
|------------|---------------|
| `CogEnv` | Ch. 1, §7: "A cognitive environment of an individual" |
| `isManifest` | Ch. 1, §7: "manifest to an individual" |
| `MutualCogEnv` | Ch. 1, §8: "mutual cognitive environments" |

## References

Sperber, D. & Wilson, D. (1986/95). Relevance: Communication and Cognition.
Blackwell. Ch. 1 §7-8.
-/

set_option autoImplicit false

namespace Theories.Pragmatics.RelevanceTheory

/-- A cognitive environment: assumptions manifest to an individual.

    - `W`: possible-worlds type
    - `A`: index type for assumptions (typically a finite inductive)

    Each assumption has propositional content and a degree of manifestness.
    Higher manifestness = more accessible, more salient, more readily
    represented.

    S&W (p. 39): "A fact is manifest to an individual at a given time if
    and only if he is capable at that time of representing it mentally and
    accepting its representation as true or probably true." -/
structure CogEnv (W : Type*) (A : Type*) where
  /-- Propositional content of each assumption -/
  content : A → W → Bool
  /-- Degree of manifestness (higher = more accessible) -/
  manifestness : A → ℕ

variable {W : Type*} {A : Type*}

/-- An assumption is manifest iff its degree is nonzero. -/
def CogEnv.isManifest (env : CogEnv W A) (a : A) : Prop :=
  0 < env.manifestness a

/-- Assumption `a` is more manifest than `b`. -/
def CogEnv.moreManifest (env : CogEnv W A) (a b : A) : Prop :=
  env.manifestness b < env.manifestness a

/-- `moreManifest` is transitive. -/
theorem CogEnv.moreManifest_trans (env : CogEnv W A) {a b c : A}
    (hab : env.moreManifest a b) (hbc : env.moreManifest b c) :
    env.moreManifest a c := by
  simp only [moreManifest] at *; omega

/-- A mutual cognitive environment: assumptions mutually manifest to all
    parties in a communicative exchange.

    S&W's shortcut: rather than requiring infinite mutual knowledge
    iteration, a shared physical environment suffices. If individuals share
    a perceptual environment and have similar cognitive abilities,
    perceptible facts are mutually manifest. -/
structure MutualCogEnv (W : Type*) (A : Type*) extends CogEnv W A

end Theories.Pragmatics.RelevanceTheory
