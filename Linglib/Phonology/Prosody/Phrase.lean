/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Word

/-!
# Phrase-level prosodic structure

The φ and ι layers sit above the prosodic word. A well-formed phrase is a φ-node licensed by
Layeredness, so a φ over prosodic words, recursive phrases, or stray feet and syllables, the
free-clitic site of Selkirk (1996); a well-formed utterance is an ι-node over phrases and
whatever Layeredness admits below them. Recursion and level skipping are admitted at both
levels, since Nonrecursivity and Exhaustivity are violable (Selkirk 1996; the recursive φ of
Match Theory, Selkirk 2011). `HeadUnique` is the culminativity of prominence, at most one head
child per node, the structural hook that Büring's (2015) metrical weak–strong calculus reads
(Büring 2016). The φ-constituents of an utterance are its maximal φ-projections
(`maximalProjections`); φ-edges are what demarcative focus reflexes (`Reflex.boundary`)
realize.

## References

* [selkirk-1996]
* [selkirk-2011]
* [ishihara-kalivoda-2022]
* [buring-2015]
* [buring-2016]
-/

@[expose] public section

namespace Prosody

/-- A well-formed phonological phrase is a licensed tree rooted in a φ-node: a φ over nodes of
level at most φ. -/
abbrev IsPhrase : Tree → Prop := IsConstituent .ph

/-- A well-formed intonational phrase, or utterance, is a licensed tree rooted in an ι-node. -/
abbrev IsUtterance : Tree → Prop := IsConstituent .iota

/-- Prominence is culminative when at most one child heads its parent. -/
def HeadUnique (t : Tree) : Prop :=
  (t.children.filter (fun c => c.value.isHead)).length ≤ 1

instance (t : Tree) : Decidable (HeadUnique t) :=
  inferInstanceAs (Decidable (_ ≤ _))

-- A φ over words, a recursive φ, and a φ over a stray syllable are all well-formed phrases; a
-- φ over an ι is not.
example : IsPhrase (.ph [.om [], .om []]) := by decide
example : IsPhrase (.ph [.ph [.om []], .om []]) := by decide
example : IsPhrase (.ph [.σ 1, .om []]) := by decide
example : ¬ IsPhrase (.ph [.node .iota []]) := by decide

end Prosody
