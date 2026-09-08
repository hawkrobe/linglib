import Linglib.Fragments.Adyghe.Clause
import Linglib.Fragments.Bulgarian.Clause
import Linglib.Fragments.Ndebele.Clause
import Linglib.Fragments.NezPerce.Clause
import Linglib.Fragments.Washo.Clause
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine

/-!
# Deal (2026): Clausal complementation as relativization, revisited

This file formalizes the typology of notional complement clauses of [deal-2026]. The relative
embeddings of Nez Perce, the complements whose edge obligatorily carries the relative pronoun
*yox̂* and the complementizer *ke*, are CPs containing an Ā-dependency launched above TP, not
DPs or PPs, so clausal complementation is not uniformly relativization ([kayne-2008],
[kayne-2014], [arsenijevic-2009]). Table (79) places each construction by its extended spine,
the heads projected from V up through any nominal or adpositional shell over C, and by whether
the CP contains an Ā-dependency, and every cell of the table is filled: the internal syntax of
a clause does not predict its external syntax. Factivity cross-cuts the Ā axis as well, table
(80): within Nez Perce every relative embedding is factive but *cuukwe* 'know' is factive and
simplex, and Adyghe uses the relative strategy for every tensed notional complement, factive
or not. The Nez Perce embedding strategy is derived from the Fragment's *yox̂ ke* edge
observable, the Adyghe and Bulgarian Ā flags from their Fragments' relativizer observables,
the shells from the spines, and the case half of the diagnostic (21) that *yox̂* is a D from
the Fragment's relative-pronoun paradigm.

## Implementation notes

The Ā column of (79) is a datum for English, Ndebele and Washo, whose Fragments carry no
relativizer observable, and the Washo V D CP structure of footnote 33 is a row beside the
table's six. Table (81), nominalization against factivity, needs Turkish *düşün-* 'think',
which has no Fragment.

## TODO

* *ke*-agreement (§2, after [deal-2015a-nels]): the φ-probe on C interacts with all
  φ-features, probing from the subject downward until [addr] satisfies it; needs
  value-sensitive satisfaction and ordered-goal probing.
* §6: relative embeddings block indexical shift and take matrix-matching tense as temporal de
  re, while simplex embeddings allow shift and relative tense; rests on [deal-2025]'s
  clause-type semantics.

## References

* [deal-2026]
* [kayne-2008]
* [kayne-2014]
* [arsenijevic-2009]
* [caponigro-polinsky-2011]
* [krapova-2010]
* [pietraszko-2019]
* [bochnak-hanink-2021]
* [hanink-bochnak-2017]
* [hankamer-mikkelsen-2021]
* [chomsky-1970]
* [deal-2025]
* [deal-2015a-nels]
-/

namespace Deal2026

open NezPerce.Clause Minimalist

/-! ### The embedding strategy -/

/-- The two embedding strategies: a relative embedding, whose complement obligatorily carries
the *yox̂ ke* edge and contains an Ā-dependency above TP, and a simplex embedding, a bare CP. -/
inductive EmbeddingStrategy where
  | relative
  | simplex
  deriving DecidableEq, Repr

/-- A predicate's strategy, from the Fragment's edge observable: relative when *yox̂ ke* is
obligatory on its complement, simplex when the complement may be bare. Both strategies select
a CP; the contrast is internal to the clause selected. -/
def strategy (v : NezPerceEmbedder) : EmbeddingStrategy :=
  if v.yoxKeEdge = .obligatory then .relative else .simplex

/-! ### Table (79): internal against external syntax -/

/-- A cell of table (79): the extended spine of a notional complement, the heads projected
from V up through any shell over C, and whether the CP contains an Ā-dependency. -/
structure Cell where
  spine : ClauseSpine
  internalAbar : Bool

/-- A Nez Perce cell: a bare CP whose Ā-dependency is the relative strategy. -/
def nezPerce (v : NezPerceEmbedder) : Cell := ⟨ClauseSpine.cP, strategy v == .relative⟩

/-- English simplex V complementation, *think*: a bare CP without an Ā-dependency. -/
def englishThink : Cell := ⟨ClauseSpine.cP, false⟩

/-- The Adyghe relative embedding of (43), V D N CP with an Ā-dependency, the flag from the
Fragment: 'think' requires the relativizer and the high applicative *ze-re-* on its tensed
complement ([caponigro-polinsky-2011]). -/
def adygheRelative : Cell :=
  ⟨ClauseSpine.cP.extend [.N, .D], Adyghe.Clause.gwepshesa.highApplicative == .required⟩

/-- English N complementation, *the fact that S*: V D N CP without an Ā-dependency, the DP
shell with an N co-argument of [hankamer-mikkelsen-2021]. -/
def englishNComplementation : Cell := ⟨ClauseSpine.cP.extend [.N, .D], false⟩

/-- The Bulgarian relative embedding of (49), V P D CP with an Ā-dependency, the flag from the
Fragment: *săžaljavam* 'regret' takes the *deto* complement [krapova-2010] analyzes as a hidden
relative. -/
def bulgarianRelative : Cell :=
  ⟨ClauseSpine.cP.extend [.D, .P], Bulgarian.Clause.sazhaljavam.deto == .alternating⟩

/-- The Ndebele embedding of (78), V P D CP without an Ā-dependency: the preposition *nga*
'about' over the class-15 augment [pietraszko-2019] takes as a D over *kuthi*. -/
def ndebeleEmbedding : Cell := ⟨ClauseSpine.cP.extend [.D, .P], false⟩

/-- The Washo factive of footnote 33, V D CP without an Ā-dependency or an N: a silent D over
the nominalized clause ([hanink-bochnak-2017], [bochnak-hanink-2021]). -/
def washoFactive : Cell := ⟨ClauseSpine.cP.extend [.D], false⟩

/-- The rows: the six cells of table (79), with the V CP cell without an Ā-dependency
witnessed twice, and the Washo structure. -/
def rows : List Cell :=
  [nezPerce liloy, nezPerce neki, englishThink, adygheRelative, englishNComplementation,
    bulgarianRelative, ndebeleEmbedding, washoFactive]

/-- Every cell of table (79) is filled: each of the three shells over C, none, D N and P D,
occurs with and without an Ā-dependency in the CP. The internal syntax of a clause does not
predict its external syntax, the category selected ranging over C, D and P for one CP-internal
syntax, and not all complementation is relativization. -/
theorem table79 :
    ∀ shell ∈ [([] : List Cat), [.N, .D], [.D, .P]], ∀ abar ∈ [true, false],
      ∃ c ∈ rows, c.spine.above .C = shell ∧ c.internalAbar = abar := by
  decide

/-! ### Table (80): factivity against the Ā axis -/

/-- Every cell of table (80) is filled: a factive relative embedding, *lilooy* 'be happy'; a
factive simplex embedding, *cuukwe* 'know'; a non-factive simplex embedding, *neki* 'think';
and a non-factive relative embedding, Adyghe 'think', which requires the relative strategy for
its tensed complement. Factivity and relative-embedding syntax vary independently. -/
theorem table80 :
    (∃ v ∈ allEmbedders, v.factive = true ∧ strategy v = .relative) ∧
      (∃ v ∈ allEmbedders, v.factive = true ∧ strategy v = .simplex) ∧
      (∃ v ∈ allEmbedders, v.factive = false ∧ strategy v = .simplex) ∧
      (∃ v ∈ Adyghe.Clause.relativeTakers, v.factive = some false) := by
  decide

/-! ### The D-inflection diagnostic (21) -/

/-- The relative pronoun *yox̂* ~ *ko* inflects for case: cells of the paradigm with distinct
cases share no forms. This is the case half of the diagnostic that *yox̂* ~ *ko* is a D while
the invariant *ke* is a C. -/
theorem paradigm_case_discriminates :
    ∀ p ∈ relativePronounParadigm, ∀ q ∈ relativePronounParadigm,
      p.case ≠ q.case → ∀ f ∈ p.forms, f ∉ q.forms := by
  decide

end Deal2026
