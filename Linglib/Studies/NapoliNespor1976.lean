import Linglib.Fragments.Italian.PolarityItems
import Linglib.Semantics.Mood.Defs
import Linglib.Features.Acceptability

/-!
# Napoli & Nespor (1976): Negatives in Comparatives

This file formalizes [napoli-nespor-1976]'s account of the Italian *non* that appears in
comparative clauses without reversing truth conditions, *Maria è più intelligente di quanto non
sia Carlo* 'Maria is more intelligent than Carlo is'. Against [antinucci-puglielli-1971]'s
pleonastic element and [seuren-1969]'s underlyingly negative *than*-clause, the paper takes this
*non₂* to be real negation licensed by the discourse move: the speaker presupposes that the
assertion contradicts a belief inferred from the interlocutor's prior discourse, the move is an
assertion, the matrix clause is not negated, and the construction does not demand precise
knowledge of the compared degrees (`Move.Licensed`). The acceptability paradigm of dialogues
between Dario and Paolo, comparative constructions, and an indirect question records the facts
of each move with the reported judgment, and `paradigm_licensed_iff` shows the four conditions
reproduce every judgment. Six morphosyntactic diagnostics witness the underlying negation:
subjunctive mood and non-specific indefinites in the *than*-clause, the complementizer *che*, the
predicative clitic *lo*, *neanche*-conjunction, and the weak NPI *pur*, whose contrast with
*affatto* is read off the Italian Fragment's licensing registry (`pur_admissible`,
`affatto_blocked`).

## Implementation notes

The paper's own implementation, a Generative Semantics abstract higher clause hosting *non₂* and
optionally deleted, is not formalized; only the licensing conditions and their surface
diagnostics are. The paper's condition on precision splits into two facts of a move: whether the
contradicted belief was inferred or stated explicitly, and whether the construction, an equality
comparative or an explicit degree modifier, demands precise knowledge of the degrees.

## References

* [napoli-nespor-1976]
* [antinucci-puglielli-1971]
* [seuren-1969]

## TODO

The paradigm's moves are typed from the paper's descriptions of its contexts; the dialogues
themselves await the paper as `Data/Examples/NapoliNespor1976.json` rows.
-/

namespace NapoliNespor1976

open Italian.PolarityItems Polarity Mood Features

/-! ### The licensing condition -/

/-- The speaker's relation to the belief the assertion contradicts. -/
inductive PriorBelief where
  /-- The interlocutor's prior discourse implies a contrary belief. -/
  | inferred
  /-- The interlocutor stated the contrary belief explicitly. -/
  | explicit
  /-- No contrary belief is in play. -/
  | absent
  deriving DecidableEq, Repr

/-- The constructions hosting a *non₂* candidate. -/
inductive Construction where
  /-- *più … di quanto*. -/
  | piu
  /-- *meno … di quanto*. -/
  | meno
  /-- The equality comparative *tanto … quanto*. -/
  | equality
  /-- A comparative with an explicit degree modifier, *molto più*, *due metri più*. -/
  | explicitDegree
  /-- An indirect question, *chissà se*. -/
  | indirectQuestion
  deriving DecidableEq, Repr

/-- The construction demands precise knowledge of the compared degrees. -/
def Construction.Precise (c : Construction) : Prop := c = .equality ∨ c = .explicitDegree

instance (c : Construction) : Decidable c.Precise := inferInstanceAs (Decidable (_ ∨ _))

/-- The polarity of the matrix clause. -/
inductive Matrix where
  | affirmative
  | negated
  deriving DecidableEq, Repr

/-- A discourse move hosting a *non₂* candidate. -/
structure Move where
  priorBelief : PriorBelief
  force : Illocutionary
  matrix : Matrix
  construction : Construction
  deriving DecidableEq, Repr

/-- The licensing condition on *non₂*: the assertion contradicts a belief the speaker inferred
from the interlocutor's discourse, the move is an assertion, the matrix is affirmative, and the
construction does not demand precision. -/
def Move.Licensed (m : Move) : Prop :=
  m.priorBelief = .inferred ∧ m.force = .declarative ∧ m.matrix = .affirmative ∧
    ¬ m.construction.Precise

instance (m : Move) : Decidable m.Licensed := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-! ### The acceptability paradigm

Four dialogues between Dario and Paolo vary the speaker's epistemic state, comparative
constructions isolate the remaining conditions, with *meno*-comparatives as the positive control,
and an indirect question shows the condition is a property of the move rather than of comparative
syntax. -/

/-- A row of the paradigm: the move and the reported acceptability of *non₂*. -/
structure Row where
  move : Move
  judgment : Judgment
  deriving DecidableEq, Repr

/-- An assertion of *Maria è più intelligente di quanto non sia Carlo* against a prior belief of
the given status. -/
def assertion (b : PriorBelief) : Move := ⟨b, .declarative, .affirmative, .piu⟩

/-- Dario gives no opinion of Maria or Carlo; Paolo asserts that Maria is more intelligent. -/
def noOpinionContext : Row := ⟨assertion .absent, .unacceptable⟩

/-- Dario implies Carlo would beat Maria at chess; Paolo asserts that Maria is more
intelligent. -/
def chessContext : Row := ⟨assertion .inferred, .acceptable⟩

/-- Dario calls Maria stupid in so many words; Paolo disagrees. -/
def explicitCriticismContext : Row := ⟨assertion .explicit, .unacceptable⟩

/-- Dario's complaint implies he expects Maria cannot help; Paolo asserts she is smart enough
to ask. -/
def complaintContext : Row := ⟨assertion .inferred, .acceptable⟩

/-- *È più intelligente di quanto non sia Carlo?*: the move is a question. -/
def questionedComparative : Row :=
  ⟨⟨.inferred, .interrogative, .affirmative, .piu⟩, .unacceptable⟩

/-- *Maria non è più intelligente di quanto non sia Carlo*: the matrix is negated. -/
def matrixNegatedComparative : Row :=
  ⟨⟨.inferred, .declarative, .negated, .piu⟩, .unacceptable⟩

/-- *Maria è tanto intelligente quanto è Carlo*: an equality comparative demands precise
knowledge of the compared degrees. -/
def equalityComparative : Row :=
  ⟨⟨.inferred, .declarative, .affirmative, .equality⟩, .unacceptable⟩

/-- *Molto più intelligente*, *due metri più alta*: an explicit degree modifier demands precise
knowledge of the gap. -/
def precisionComparative : Row :=
  ⟨⟨.inferred, .declarative, .affirmative, .explicitDegree⟩, .unacceptable⟩

/-- *Maria è meno intelligente di quanto tu non creda*: a *meno*-comparative admits *non₂* under
the same conditions as *più*, while a negated equality comparative, semantically close to it,
rejects *non₂*, so the equality restriction cannot reduce to equality linking two similar things
(contra [seuren-1969] and [antinucci-puglielli-1971]). -/
def menoComparative : Row :=
  ⟨⟨.inferred, .declarative, .affirmative, .meno⟩, .acceptable⟩

/-- *Chissà se non vale la pena di comprarlo*: an indirect question whose negated proposition the
speaker presupposes to be contrary to expectation. -/
def chissaSeNon : Row :=
  ⟨⟨.inferred, .declarative, .affirmative, .indirectQuestion⟩, .acceptable⟩

/-- The paper's acceptability paradigm. -/
def paradigm : List Row :=
  [noOpinionContext, chessContext, explicitCriticismContext, complaintContext,
    questionedComparative, matrixNegatedComparative, equalityComparative, precisionComparative,
    menoComparative, chissaSeNon]

/-- The four conditions reproduce the paper's judgment on every row, each condition failing on
its own row. -/
theorem paradigm_licensed_iff : ∀ r ∈ paradigm, r.move.Licensed ↔ r.judgment = .acceptable := by
  decide

/-! ### Morphosyntactic diagnostics for underlying negation

Two diagnostics are forced choices in the *than*-clause, mood and the specificity of indefinites;
four are admissibility asymmetries, in which the marked alternant (the complementizer *che*, the
predicative clitic *lo*, *neanche*-conjunction, the weak NPI *pur*) is possible only under
licensed *non₂* while the default (*di quanto*, a repeated predicate, plain conjunction) remains
available throughout. -/

/-- Specificity of indefinites embedded in the *than*-clause. -/
inductive SpecificityProfile where
  /-- Both specific and non-specific readings are available. -/
  | unrestricted
  /-- Only the non-specific reading, under the scope of underlying negation. -/
  | nonspecificOnly
  deriving DecidableEq, Repr

/-- The Italian comparative complementizers. -/
inductive Complementizer where
  /-- The default *than*-complementizer. -/
  | diQuanto
  /-- The alternant admissible only under *non₂*. -/
  | che
  deriving DecidableEq, Repr

/-- Whether the predicative clitic *lo* substitutes for a repeated predicate adjective in the
*than*-clause. -/
inductive Clitic where
  | present
  | absent
  deriving DecidableEq, Repr

/-- Mood of the *than*-clause: subjunctive exactly under licensed *non₂*, the paper's optional
deletion of *non₂* deriving surface subjunctive without *non*; lexical mood control by *credere*
and its kin is abstracted away. -/
def predictedMood (m : Move) : Grammatical := if m.Licensed then .subjunctive else .indicative

/-- Embedded indefinites are restricted to the non-specific reading under licensed *non₂*. -/
def predictedSpecificity (m : Move) : SpecificityProfile :=
  if m.Licensed then .nonspecificOnly else .unrestricted

/-- *Di quanto* occurs with and without *non₂*; *che* only with it. -/
def complementizerAdmissible (m : Move) : Complementizer → Prop
  | .diQuanto => True
  | .che => m.Licensed

/-- A clitic-less comparative is always available; *lo* only under *non₂*, and optionally. -/
def cliticAdmissible (m : Move) : Clitic → Prop
  | .present => m.Licensed
  | .absent => True

/-- *Neanche*-conjunction is admissible iff its host clause is negated at some level, in a
comparative iff *non₂* is licensed; the negation requirement is the Fragment's registry entry
for *neanche*. -/
def neancheConjunctionAdmissible (m : Move) : Prop :=
  m.Licensed ∧ .negation ∈ neanche.licensingContexts

/-- A weak NPI is admissible in a *non₂*-comparative iff its registry lists the clausal
comparative slot and the move licenses *non₂*. -/
def weakNPIAdmissible (m : Move) (npi : Item) : Prop :=
  m.Licensed ∧ .clausalComparative ∈ npi.licensingContexts

/-- *Neanche*-conjunction is admissible in the chess dialogue. -/
theorem neanche_admissible : neancheConjunctionAdmissible chessContext.move :=
  ⟨by decide, by decide⟩

/-- *Pur* is admissible wherever *non₂* is licensed. -/
theorem pur_admissible {m : Move} (h : m.Licensed) : weakNPIAdmissible m pur :=
  ⟨h, pur_licensed_in_comparative⟩

/-- *Affatto* is inadmissible in *non₂*-comparatives whatever the move: it requires precise
knowledge of the contradicted belief, and the block is registered in its lexical entry. -/
theorem affatto_blocked (m : Move) : ¬ weakNPIAdmissible m affatto :=
  λ ⟨_, h⟩ => affatto_not_licensed_in_comparative h

end NapoliNespor1976
