module

public import Linglib.Syntax.Category.Adjective.ClauseEmbedding
public import Linglib.Syntax.Category.Verb.Basic

/-!
# English copular predicates

This file defines the English predicates of the form *be* + adjective that embed a clause: the
emotive factive *annoyed (that p)* and the veridical non-factive *right (that p)*, which
entails its complement without presupposing it, both from Degen and Tonhauser's projection
experiments, and *able (to VP)*, which Karttunen classes as a necessary-condition predicate,
its negation entailing the negation of the complement while its affirmative does not entail the
complement, the actuality entailment arising from perfective aspect, as Nadathur shows, and not
from the lexicon. The adjectives are `ClauseEmbeddingAdjective` entries, and the copular verbs
are their realization with *be*.

## Main definitions

* `English.Verbs.Copular.annoyed`, `English.Verbs.Copular.right`: the adjectives.
* `English.Verbs.Copular.beAnnoyed`, `English.Verbs.Copular.beRight`,
  `English.Verbs.Copular.beAble`: the copular verbs.

## References

* [degen-tonhauser-2021]
* [degen-tonhauser-2022]
* [karttunen-1971]
* [nadathur-2023]
-/

@[expose] public section

namespace English.Verbs.Copular

open ArgumentStructure

/-- *annoyed (that p)*, an emotive factive adjective. -/
def annoyed : ClauseEmbeddingAdjective where
  form := "annoyed"
  factivity := some .full

/-- *right (that p)*, a veridical non-factive adjective, which entails its complement without
presupposing it. -/
def right : ClauseEmbeddingAdjective where
  form := "right"

/-- *be annoyed (that p)*. -/
def beAnnoyed : Verb := annoyed.toVerb "be"

/-- *be right (that p)*. -/
def beRight : Verb := right.toVerb "be"

/-- *be able (to VP)*, a subject-control predicate whose negation entails the negation of its
complement and whose affirmative entails the complement only under perfective aspect, so no
implicative entry. -/
def beAble : Verb where
  form := "be able"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]

end English.Verbs.Copular
