/-!
# Attitude predicates: the classification

This file is the root of the attitude API: the semantic classification a clause-embedding
predicate's lexical entry records, from which its combinatorial properties are derived. A
doxastic predicate is veridical or not, the [karttunen-1971] lineage of factive and non-factive
complement-taking verbs (`Doxastic.Veridicality`). A preferential predicate has an evaluative
valence, positive for *hope* and negative for *fear* (`Preferential.Valence`), and a
compositional strategy (`Preferential.Strategy`): the degree comparison of [villalta-2008],
whose question use is the existential over answers, or a relation to the question itself,
anxious uncertainty for *worry* ([anand-hacquard-2013]) or anticipation of resolution for
Mandarin *qidai* and relevance for *care* ([elliott-etal-2017]), which holds of no particular
answer. `Attitude` composes the two dimensions, and its projections are what verb entries and
the doxastic and preferential semantics of `Doxastic.lean` and `Preference.lean` read.

## Implementation notes

The binary cut between veridical and non-veridical is the classical default;
[giannakidou-1998]'s three-way veridical, nonveridical, and antiveridical taxonomy and finer
attitude typologies ([anand-hacquard-2013]) cut the space differently. The strategies are the
ones whose clausal distributivity [qing-uegaki-2025] contrast; relevance-based is not a
published label. Speech-act predicates are outside the classification.

## References

* [karttunen-1971]
* [villalta-2008]
* [anand-hacquard-2013]
* [elliott-etal-2017]
* [giannakidou-1998]
* [qing-uegaki-2025]
* [hintikka-1962]
-/

/-- Veridicality of a doxastic predicate: *know* and *discover* entail their complement,
*believe* and *think* do not. -/
inductive Doxastic.Veridicality
  | veridical
  | nonVeridical
  deriving DecidableEq, Repr

/-- Evaluative valence of a preferential predicate: positive for *hope* and *wish*, negative for
*fear* and *worry*. -/
inductive Preferential.Valence
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The compositional strategy of a preferential predicate, from which its clausal
distributivity is derived: a degree comparison's question use is the existential over answers
(`Preferential.mkDegreeComparison_isDistributive`), while a relation to the question holds of
no particular answer (`Preferential.PreferentialPredicate.not_isDistributive_of_forall_not`). -/
inductive Preferential.Strategy
  /-- Degree comparison ([villalta-2008]): ⟦x V p⟧ = μ(x, p) > θ. -/
  | degreeComparison (valence : Preferential.Valence)
  /-- Anxious uncertainty about the question (*worry*). -/
  | uncertaintyBased
  /-- Anticipation of the question's resolution (Mandarin *qidai*) or its relevance
  (*care*). -/
  | relevanceBased (valence : Preferential.Valence)
  deriving DecidableEq, Repr

namespace Preferential.Strategy

/-- The valence of a strategy; *worry* is negative. -/
def valence : Strategy → Valence
  | .degreeComparison v => v
  | .uncertaintyBased => .negative
  | .relevanceBased v => v

end Preferential.Strategy

/-- The semantic classification of an attitude predicate: doxastic, with an accessibility
semantics ([hintikka-1962]) and a veridicality, or preferential, with a degree semantics and a
strategy. -/
inductive Attitude
  | doxastic (veridicality : Doxastic.Veridicality)
  | preferential (strategy : Preferential.Strategy)
  deriving DecidableEq, Repr

namespace Attitude

/-- The veridicality of a predicate; preferential predicates are non-veridical. -/
def veridicality : Attitude → Doxastic.Veridicality
  | .doxastic v => v
  | .preferential _ => .nonVeridical

/-- Whether the predicate is doxastic, as a Boolean for lexicon filters. -/
def isDoxastic : Attitude → Bool
  | .doxastic _ => true
  | .preferential _ => false

/-- Whether the predicate is preferential, as a Boolean for lexicon filters. -/
def isPreferential : Attitude → Bool
  | .doxastic _ => false
  | .preferential _ => true

/-- The strategy of a preferential predicate. -/
def strategy? : Attitude → Option Preferential.Strategy
  | .doxastic _ => none
  | .preferential s => some s

/-- The valence of a preferential predicate. -/
def valence : Attitude → Option Preferential.Valence
  | .doxastic _ => none
  | .preferential s => some s.valence

end Attitude
