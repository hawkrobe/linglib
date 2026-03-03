import Mathlib.Data.Rat.Defs

/-!
# Cognitive Environments — @cite{sperber-wilson-1986}

The cognitive environment of an individual is the set of all facts that are
manifest to them. Manifestness is graded: perceptually obvious facts are
highly manifest; distant inferences are weakly manifest.

| Definition | S&W Reference |
|------------|---------------|
| `CogEnv` | Ch. 1, §7: "A cognitive environment of an individual" |
| `isManifest` | Ch. 1, §7: "manifest to an individual" |
| `SharedCogEnv` | Ch. 1, §9: "shared cognitive environment" (p. 42) |

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

/-- A shared cognitive environment: assumptions manifest to all parties,
    where the fact that they share the environment is itself manifest.

    S&W (p. 42) argue that mutual knowledge (an infinite regress of
    "A knows that B knows that A knows...") is unattainable. Their
    replacement is the SHARED cognitive environment: a cognitive environment
    that two people share, where it is manifest to both that they share it.

    This is NOT a weaker version of mutual knowledge — it's a fundamentally
    different notion. The sharing is grounded in perceptual co-presence
    and similar cognitive abilities, not in iterated belief attribution. -/
structure SharedCogEnv (W : Type*) (A : Type*) extends CogEnv W A where
  /-- Number of parties sharing this environment -/
  parties : ℕ
  /-- The sharing itself is manifest (reflexivity condition) -/
  sharingManifest : Prop

end Theories.Pragmatics.RelevanceTheory
