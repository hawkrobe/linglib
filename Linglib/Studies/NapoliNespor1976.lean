import Linglib.Pragmatics.Bias
import Linglib.Fragments.Italian.PolarityItems
import Linglib.Semantics.Mood.Defs

/-!
# Napoli & Nespor (1976): Negatives in Comparatives

Italian *non* appears in some comparative clauses without truth-conditional
effect: *Maria è più intelligente di quanto non sia Carlo* 'Maria is more
intelligent than Carlo (is)'. Earlier accounts treated this *non₂* as a
pleonastic element ([antinucci-puglielli-1971]) or as surface evidence that
*than*-clauses are underlyingly negative ([seuren-1969]).
[napoli-nespor-1976] (*Language* 52(4), 811–838) reject both: *non₂* is real
negation, licensed by a discourse condition — the speaker presupposes that the
assertion contradicts a prior belief, the move is assertive, the matrix is
unnegated, and neither the contradicted belief nor the construction involves
precise knowledge. The licensing predicate is formalized once as
`Pragmatics.Bias.BiasLicensingProfile.licenses`; this file is its first
historical attestation, applied to the paper's Italian data. The paper's own
implementation — a Generative Semantics abstract higher clause hosting *non₂*,
optionally deleted — is historical; only the licensing predicate and its
surface diagnostics are preserved.

## Main declarations

* `noOpinionContext`, `chessContext`, `explicitCriticismContext`,
  `complaintContext`: the dialogue paradigm probing the contradicted-belief
  presupposition;
* `questionedComparative` … `menoComparative`: distributional environments,
  each isolating one licensing condition;
* `predictedMood`, `predictedSpecificity`, `complementizerAdmissible`,
  `cliticAdmissible`, `neancheConjunctionAdmissible`, `weakNPIAdmissible`:
  morphosyntactic diagnostics for underlying negation;
* `chissaSeNon`: the same profile licensing *non₂* in indirect questions.
-/

namespace NapoliNespor1976

open Pragmatics.Bias
open Italian.PolarityItems (pur affatto neanche
  pur_licensed_in_comparative affatto_not_licensed_in_comparative)
open Polarity (Item)

/-! ### The dialogue-context paradigm

Four dialogues between Dario and Paolo vary the speaker's epistemic state:
*non₂* is felicitous exactly when the assertion contradicts a belief
*inferred* from the interlocutor's prior discourse — infelicitous when there
is no prior belief to contradict, and when the contradicted belief was
explicitly stated rather than inferred. -/

/-- Dario gives no opinion of Maria or Carlo; Paolo asserts Maria > Carlo.
No prior belief to contradict, so *non₂* is infelicitous. -/
def noOpinionContext : BiasLicensingProfile := noContradictionProfile

/-- Dario implies Carlo would beat Maria at chess; Paolo asserts Maria is more
intelligent. The contradicted belief is inferred, so *non₂* may appear. -/
def chessContext : BiasLicensingProfile := licensedProfile

/-- Dario explicitly calls Maria stupid; Paolo disagrees. The contradicted
belief is explicitly stated rather than inferred, failing the
imprecise/inferred condition, so *non₂* is out. -/
def explicitCriticismContext : BiasLicensingProfile := preciseProfile

/-- Dario's complaint implies he expects Maria cannot help; Paolo asserts she
is smart enough to ask. The contradicted belief is inferred: *non₂* is used. -/
def complaintContext : BiasLicensingProfile := licensedProfile

theorem noOpinion_blocks : ¬ noOpinionContext.licenses := no_contradiction_blocks
theorem chess_licenses : chessContext.licenses := licensed_licenses
theorem explicitCriticism_blocks : ¬ explicitCriticismContext.licenses := precise_blocks
theorem complaint_licenses : complaintContext.licenses := licensed_licenses

/-! ### Distributional environments

Construction-level environments each isolate one licensing condition (the
contradicted-belief condition is contextual and is witnessed by the dialogue
paradigm above); equality and explicit-degree comparatives both fail the
precision condition. *Meno*-comparatives are the positive control. -/

/-- *È più intelligente di quanto non sia Carlo?* 'Is she more intelligent
than Carlo?': questioning is non-assertive, blocking *non₂*. -/
def questionedComparative : BiasLicensingProfile := questionedProfile

/-- *Maria non è più intelligente di quanto non sia Carlo*: a negated matrix
blocks *non₂*. -/
def matrixNegatedComparative : BiasLicensingProfile := matrixNegatedProfile

/-- Equality comparatives (*Maria è tanto intelligente quanto è Carlo*) demand
explicit, precise knowledge of the compared degrees, while *non₂* demands
inferred, imprecise knowledge — so the two are mutually exclusive. -/
def equalityComparative : BiasLicensingProfile := preciseProfile

/-- Explicit degree modifiers (*molto più intelligente*, *due metri più alta*)
require precise knowledge of the degree gap, failing the imprecise
condition. -/
def precisionComparative : BiasLicensingProfile := preciseProfile

/-- *Maria è meno intelligente di quanto tu non creda* 'Maria is less
intelligent than you think': *meno*-comparatives admit *non₂* under the same
contextual conditions as *più*. Negated equality comparatives are semantically
close to *meno*-comparatives yet reject *non₂*, so the equality restriction
cannot reduce to equality linking two similar things (contra [seuren-1969]
and [antinucci-puglielli-1971]); it follows from matrix negation and the
precision condition. -/
def menoComparative : BiasLicensingProfile := licensedProfile

theorem questioned_blocks_non2 : ¬ questionedComparative.licenses := questioned_blocks
theorem matrix_negated_blocks_non2 : ¬ matrixNegatedComparative.licenses := matrix_negated_blocks
theorem equality_blocks_non2 : ¬ equalityComparative.licenses := precise_blocks
theorem precision_blocks_non2 : ¬ precisionComparative.licenses := precise_blocks
theorem meno_licenses_non2 : menoComparative.licenses := licensed_licenses

/-! ### Morphosyntactic diagnostics for underlying negation

Six surface diagnostics witness underlying negation in the comparative
clause. Two are forced choices — mood morphology and indefinite specificity.
Four are admissibility asymmetries — complementizer *che*, predicative clitic
*lo*, the weak NPI *pur*, and *neanche*-conjunction: the bias-marked
alternant is possible only under licensed *non₂*, while the default
(*di quanto*, clitic-less repetition) remains available throughout. The NPI
diagnostics are derived from the Italian Fragment's `licensingContexts`
registry. -/

/-- Specificity of indefinites embedded in the *than*-clause. -/
inductive SpecificityProfile where
  /-- Both [+specific] and [−specific] readings available. -/
  | unrestricted
  /-- Restricted to [−specific] under the scope of underlying negation. -/
  | nonspecificOnly
  deriving DecidableEq, Repr

/-- The Italian comparative complementizers. -/
inductive ComplementizerChoice where
  /-- The default *than*-complementizer. -/
  | diQuanto
  /-- The alternant admissible only under *non₂*. -/
  | che
  deriving DecidableEq, Repr

/-- Presence of the predicative clitic *lo* substituting for a repeated
predicate adjective in the *than*-clause. -/
inductive CliticPresence where
  | present
  | absent
  deriving DecidableEq, Repr

/-- Mood of the *than*-clause: subjunctive exactly when *non₂* is underlyingly
present, indicative otherwise (lexical mood control by *credere* etc. is
abstracted away). Surface subjunctive without *non* is derived by the paper's
optional deletion of an underlying *non₂*. -/
def predictedMood (p : BiasLicensingProfile) : Mood.Grammatical :=
  if p.licenses then .subjunctive else .indicative

/-- Embedded indefinites are restricted to [−specific] under licensed *non₂*
and unrestricted otherwise. -/
def predictedSpecificity (p : BiasLicensingProfile) : SpecificityProfile :=
  if p.licenses then .nonspecificOnly else .unrestricted

/-- Complementizer admissibility: *di quanto* occurs in comparatives with and
without *non₂*; *che* only with it. -/
def complementizerAdmissible (p : BiasLicensingProfile) :
    ComplementizerChoice → Prop
  | .diQuanto => True
  | .che => p.licenses

/-- Clitic admissibility: clitic-less comparatives are always available; *lo*
is possible only under *non₂*, and optional there. -/
def cliticAdmissible (p : BiasLicensingProfile) : CliticPresence → Prop
  | .present => p.licenses
  | .absent => True

/-- *Neanche*-conjunction ('and not even …') is admissible iff its host
clause is negated at some underlying level — in a comparative, iff *non₂* is
licensed. The negation requirement is the Fragment registry fact that
*neanche* lists `.negation` among its licensing contexts. -/
def neancheConjunctionAdmissible (p : BiasLicensingProfile) : Prop :=
  p.licenses ∧ .negation ∈ neanche.licensingContexts

/-- The mood diagnostic tracks the licensing predicate: the *than*-clause is
subjunctive exactly on licensed profiles. -/
theorem predictedMood_eq_subjunctive_iff (p : BiasLicensingProfile) :
    predictedMood p = .subjunctive ↔ p.licenses := by
  by_cases h : p.licenses <;> simp [predictedMood, h]

/-- The specificity diagnostic tracks the licensing predicate. -/
theorem predictedSpecificity_eq_nonspecificOnly_iff (p : BiasLicensingProfile) :
    predictedSpecificity p = .nonspecificOnly ↔ p.licenses := by
  by_cases h : p.licenses <;> simp [predictedSpecificity, h]

/-- *Neanche*-conjunction is admissible under licensed *non₂*; the second
conjunct is the Fragment's registry datum. -/
theorem neanche_conjunction_with_non2 :
    neancheConjunctionAdmissible licensedProfile :=
  ⟨licensed_licenses, by decide⟩

/-! ### The pur / affatto contrast

The weak NPI *pur* is licensed in *non₂*-comparatives; the weak NPI *affatto*
is blocked, because *affatto* requires precise knowledge of the contradicted
belief — incompatible with the imprecise/inferred licensing condition (a
footnote observation of [napoli-nespor-1976]). The contrast is witnessed at
the lexical layer: `pur.licensingContexts` lists the clausal-comparative slot
`.comparativeS` while `affatto`'s does not, so the predictions below are
derived from the Fragment registry. -/

/-- A weak NPI is admissible in a bias-conditioned comparative iff its
registry lists the clausal-comparative slot `.comparativeS` (surface
NP-comparatives are not NPI environments) and the profile licenses *non₂*. -/
def weakNPIAdmissible (p : BiasLicensingProfile) (npi : Item) : Prop :=
  p.licenses ∧ .comparativeS ∈ npi.licensingContexts

/-- *Pur* is admissible wherever *non₂* is licensed; the registry conjunct is
the Fragment's `pur_licensed_in_comparative`. -/
theorem pur_admissible_with_non2 : weakNPIAdmissible licensedProfile pur :=
  ⟨licensed_licenses, pur_licensed_in_comparative⟩

/-- *Affatto* is inadmissible in *non₂*-comparatives whatever the bias
profile: the block is registered in the lexical entry itself. -/
theorem affatto_blocked_in_non2 (p : BiasLicensingProfile) :
    ¬ weakNPIAdmissible p affatto :=
  λ ⟨_, h⟩ => affatto_not_licensed_in_comparative h

/-! ### Beyond comparatives: indirect questions

The same *non₂* appears in indirect questions where the speaker presupposes
the negated proposition is contrary to expectation: *Chissà se non vale la
pena di comprarlo* 'Who knows if it's (not) worth buying it' suggests the
speaker expected it to be worth buying. The licensing condition is a property
of the discourse move, not of comparative syntax. -/

/-- *Chissà se non…*: indirect question with bias-conditioned negation, same
licensing profile as the licensed comparative contexts. -/
def chissaSeNon : BiasLicensingProfile := licensedProfile

theorem chissa_licenses_non2 : chissaSeNon.licenses := licensed_licenses

end NapoliNespor1976
