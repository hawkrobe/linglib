import Linglib.Fragments.Adyghe.Clause
import Linglib.Fragments.Bulgarian.Clause
import Linglib.Fragments.Ndebele.Clause
import Linglib.Fragments.NezPerce.Clause
import Linglib.Data.Examples.Deal2026
import Linglib.Data.Examples.Krapova2010
import Linglib.Studies.BochnakHanink2021
import Linglib.Syntax.Category.Verb.Complement.Takes
import Linglib.Semantics.Presupposition.Environment
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
or not. The Nez Perce embedding strategy is read off the paper's judgments, the rows of
`Data/Examples/Deal2026.json`: a predicate embeds relatively when a grammatical notional
complement of it carries the *yox̂ ke* edge (`RelativeEmbedding`). Every relative embedding
is factive (`relative_factive`), factivity being the Fragment entries' [karttunen-1971] class,
which the projection trials (33)–(36) and (68) confirm row by row (`projection_rows`). The
Adyghe Ā flag is that 'think' takes the Fragment's *ze-re-* typer, the Bulgarian one is
[krapova-2010]'s double requirement over the Fragment's frames (`DetoComplement`), checked
against her sentences (56)–(59) as rows of `Data/Examples/Krapova2010.json`, the shells
come from the spines, and the case half of the diagnostic (21) that *yox̂* is a D from the
Fragment's relative-pronoun paradigm.

## Implementation notes

The Ā column of (79) is a datum for English, Ndebele and Washo, whose Fragments carry no
relativizer observable, and the Washo V D CP structure of footnote 33, the complementation
spine of [bochnak-hanink-2021], is a row beside the table's six. Table (81), nominalization
against factivity, needs Turkish *düşün-* 'think', which has no Fragment.

## TODO

* *ke*-agreement (§2, after [deal-2015a-nels]): the φ-probe on C interacts with all
  φ-features, probing from the subject downward until [addr] satisfies it; needs
  value-sensitive satisfaction and ordered-goal probing.
* §6: relative embeddings block indexical shift and take matrix-matching tense as temporal de
  re, while simplex embeddings allow shift and relative tense; rests on [deal-2025b]'s
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
* [deal-2025b]
* [deal-2015a-nels]
* [karttunen-1971]
* [tonhauser-beaver-roberts-simons-2013]
-/

namespace Deal2026

open NezPerce Minimalist Data.Examples

/-! ### The embedding strategy -/

/-- The two embedding strategies: a relative embedding, whose complement obligatorily carries
the *yox̂ ke* edge and contains an Ā-dependency above TP, and a simplex embedding, a bare CP. -/
inductive EmbeddingStrategy where
  | relative
  | simplex
  deriving DecidableEq, Repr

/-- A predicate embeds relatively when some grammatical notional complement of it carries the
*yox̂ ke* edge ((27)–(28)); *cuukwe*'s (66b) is only marginal. -/
def RelativeEmbedding (v : NezPerce.Verb) : Prop :=
  ∃ row ∈ Examples.all, row.feature? "verb" = some v.form ∧
    row.feature? "edge" = some "yoxKe" ∧ row.judgment = .acceptable

instance (v : NezPerce.Verb) : Decidable (RelativeEmbedding v) :=
  inferInstanceAs (Decidable (∃ row ∈ Examples.all, _))

/-- A predicate's strategy is relative when it embeds relatively and simplex otherwise. Both
strategies select a CP; the contrast is internal to the clause selected. -/
def strategy (v : NezPerce.Verb) : EmbeddingStrategy :=
  if RelativeEmbedding v then .relative else .simplex

/-- The relative-embedding predicates take no noun-phrase object, (41). -/
theorem nominal_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "nominalComplement" →
      ∀ v ∈ verbs, row.feature? "verb" = some v.form →
        (row.judgment = .acceptable ↔ ∃ fr ∈ v.frames, fr.HasNominal) := by
  decide

/-- Every relative embedding is factive (§7). -/
theorem relative_factive :
    ∀ v ∈ verbs, strategy v = .relative → v.toVerb.factivePresup = true := by
  decide

/-- Consultants endorse the complement under negation, in a question or in a conditional
antecedent exactly for the factive predicates, the projection trials (33)–(36) and (68); no
trial is in the first person, so no semi-factive is cancelled ([karttunen-1971]). -/
theorem projection_rows :
    ∀ row ∈ Examples.all, ∀ f ∈ row.environment?, ∀ p ∈ row.person?,
      ∀ v ∈ verbs, row.feature? "verb" = some v.form →
        (row.projective? = some true ↔
          v.toVerb.factivePresup = true ∧ ∀ c ∈ v.factivity, ¬ c.Cancelled f p) := by
  decide

/-! ### Table (79): internal against external syntax -/

/-- A cell of table (79): the extended spine of a notional complement, the heads projected
from V up through any shell over C, and whether the CP contains an Ā-dependency. -/
structure Cell where
  spine : ClauseSpine
  internalAbar : Bool

/-- A Nez Perce cell: a bare CP whose Ā-dependency is the relative strategy. -/
def nezPerce (v : NezPerce.Verb) : Cell := ⟨ClauseSpine.cP, strategy v == .relative⟩

/-- English simplex V complementation, *think*: a bare CP without an Ā-dependency. -/
def englishThink : Cell := ⟨ClauseSpine.cP, false⟩

/-- The Adyghe relative embedding of (43), V D N CP with an Ā-dependency, the flag from the
Fragment: 'think' takes the relativizer *ze-* with the applicative *re-* on its tensed
complement ([caponigro-polinsky-2011]). -/
def adygheRelative : Cell :=
  ⟨ClauseSpine.cP.extend [.N, .D], decide (Adyghe.gwepshesa.toVerb.takes Adyghe.zeRe)⟩

/-- [krapova-2010]'s double requirement, reported at footnote 22: *deto* introduces the
complement of a predicate that is an emotive factive and takes a *za* phrase. -/
def DetoComplement (v : Bulgarian.Verb) : Prop :=
  v.factivity = some .emotive ∧ ∃ fr ∈ v.frames, Complement.Position.adpositional ∈ fr

instance (v : Bulgarian.Verb) : Decidable (DetoComplement v) :=
  inferInstanceAs (Decidable (_ ∧ ∃ fr ∈ v.frames, _))

/-- The double requirement picks out exactly the predicates Krapova lists as *deto*-takers, and
neither condition suffices: *văzmuštavam se* 'resent' is emotive without a *za* phrase, and
*razbiram* 'comprehend' is factive without being emotive. -/
theorem detoComplement_iff :
    (∀ v ∈ Bulgarian.verbs, DetoComplement v ↔ v.form ∈ Bulgarian.detoTakers.map (·.form)) ∧
      ¬ DetoComplement Bulgarian.vazmushtavamSe ∧ ¬ DetoComplement Bulgarian.razbiram := by
  decide

/-- Krapova's *deto* sentences (56) and (58) are grammatical exactly for the predicates that meet
the double requirement, and their *če* variants are always grammatical (fn. 46). -/
theorem deto_rows :
    ∀ row ∈ Krapova2010.Examples.all, row.feature? "diagnostic" = some "detoSelection" →
      ∀ v ∈ Bulgarian.verbs, row.feature? "verb" = some v.form →
        (row.judgment = .acceptable ↔ DetoComplement v) ∧
          ∀ a ∈ row.alternatives, a.2 = .acceptable := by
  decide

/-- The nominal paraphrases (59) take the preposition *za* and no other, the adpositional frame
of the Fragment's emotive factives. -/
theorem zaPhrase_rows :
    ∀ row ∈ Krapova2010.Examples.all, row.feature? "diagnostic" = some "zaPhrase" →
      ∀ v ∈ Bulgarian.verbs, row.feature? "verb" = some v.form →
        (row.judgment = .acceptable ↔ ∃ fr ∈ v.frames, Complement.Position.adpositional ∈ fr) ∧
          ∀ a ∈ row.alternatives, a.2 = .ungrammatical := by
  decide

/-- Krapova's factivity tests (57a–b): the complement survives negation and a question exactly
for the factive predicates, and the emotive factives are cancelled nowhere. -/
theorem krapova_projection_rows :
    ∀ row ∈ Krapova2010.Examples.all, ∀ f ∈ row.environment?, ∀ p ∈ row.person?,
      ∀ v ∈ Bulgarian.verbs, row.feature? "verb" = some v.form →
        (row.projective? = some true ↔
          v.toVerb.factivePresup = true ∧ ∀ c ∈ v.factivity, ¬ c.Cancelled f p) := by
  decide

/-- Krapova's contradiction tests (57c) and footnote 46: a continuation denying the complement
is unacceptable exactly under a factive predicate, under *deto* and *če* alike. -/
theorem krapova_contradiction_rows :
    ∀ row ∈ Krapova2010.Examples.all, row.feature? "diagnostic" = some "contradiction" →
      ∀ v ∈ Bulgarian.verbs, row.feature? "verb" = some v.form →
        ((∃ a ∈ row.alternatives, a.2 = .unacceptable) ↔ v.toVerb.factivePresup = true) := by
  decide

/-- English N complementation, *the fact that S*: V D N CP without an Ā-dependency, the DP
shell with an N co-argument of [hankamer-mikkelsen-2021]. -/
def englishNComplementation : Cell := ⟨ClauseSpine.cP.extend [.N, .D], false⟩

/-- The Bulgarian relative embedding of (49), V P D CP with an Ā-dependency, the flag from the
Fragment: *săžaljavam* 'regret' meets the double requirement, so it takes the *deto*
complement [krapova-2010] analyzes as a hidden relative. -/
def bulgarianRelative : Cell :=
  ⟨ClauseSpine.cP.extend [.D, .P], decide (DetoComplement Bulgarian.sazhaljavam)⟩

/-- The Ndebele embedding of (78), V P D CP without an Ā-dependency: the preposition *nga*
'about' over the class-15 augment [pietraszko-2019] takes as a D over *kuthi*. -/
def ndebeleEmbedding : Cell := ⟨ClauseSpine.cP.extend [.D, .P], false⟩

/-- The Washo factive of footnote 33, V D CP without an Ā-dependency or an N: a silent D over
the nominalized clause ([hanink-bochnak-2017], [bochnak-hanink-2021]), whose index binds without
movement ([hanink-2021]). -/
def washoFactive : Cell := ⟨BochnakHanink2021.complementSpine, false⟩

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
    (∃ v ∈ verbs, v.toVerb.factivePresup = true ∧ strategy v = .relative) ∧
      (∃ v ∈ verbs, v.toVerb.factivePresup = true ∧ strategy v = .simplex) ∧
      (∃ v ∈ verbs, v.toVerb.factivePresup = false ∧ strategy v = .simplex) ∧
      (∃ v ∈ Adyghe.verbs, v.toVerb.takes Adyghe.zeRe ∧ v.toVerb.factivePresup = false) := by
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
