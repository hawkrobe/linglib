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

* `Non2Datum`, `paradigm`: the paper's acceptability paradigm — dialogue
  contexts, comparative environments, and indirect questions, each pairing a
  bias profile with the reported judgment for *non₂*;
* `paradigm_licenses_iff_non2Ok`: the licensing predicate reproduces every
  judgment in the paradigm;
* `predictedMood`, `predictedSpecificity`, `complementizerAdmissible`,
  `cliticAdmissible`, `neancheConjunctionAdmissible`, `weakNPIAdmissible`:
  morphosyntactic diagnostics for underlying negation.
-/

namespace NapoliNespor1976

open Pragmatics.Bias
open Italian.PolarityItems
open Polarity (Item)

/-! ### The acceptability paradigm

The licensing conditions are established through an acceptability paradigm.
Four dialogues between Dario and Paolo vary the speaker's epistemic state:
*non₂* is felicitous exactly when the assertion contradicts a belief
*inferred* from the interlocutor's prior discourse. Construction-level
environments then isolate the remaining conditions (equality and
explicit-degree comparatives both fail the precision condition;
*meno*-comparatives are the positive control), and indirect questions show
the condition is a property of the discourse move, not of comparative
syntax. -/

/-- One row of the acceptability paradigm: a dialogue context or
construction, its bias-licensing profile, and the reported acceptability of
*non₂*. -/
structure Non2Datum where
  profile : BiasLicensingProfile
  /-- Whether the paper reports *non₂* as felicitous. -/
  non2Ok : Bool
  deriving Repr

/-- Dario gives no opinion of Maria or Carlo; Paolo asserts Maria > Carlo:
no prior belief to contradict. -/
def noOpinionContext : Non2Datum :=
  { profile := noContradictionProfile, non2Ok := false }

/-- Dario implies Carlo would beat Maria at chess; Paolo asserts Maria is
more intelligent: the contradicted belief is inferred. -/
def chessContext : Non2Datum :=
  { profile := licensedProfile, non2Ok := true }

/-- Dario explicitly calls Maria stupid; Paolo disagrees: the contradicted
belief is explicitly stated rather than inferred, failing the
imprecise/inferred condition. -/
def explicitCriticismContext : Non2Datum :=
  { profile := preciseProfile, non2Ok := false }

/-- Dario's complaint implies he expects Maria cannot help; Paolo asserts
she is smart enough to ask: the contradicted belief is inferred. -/
def complaintContext : Non2Datum :=
  { profile := licensedProfile, non2Ok := true }

/-- *È più intelligente di quanto non sia Carlo?* 'Is she more intelligent
than Carlo?': questioning is non-assertive. -/
def questionedComparative : Non2Datum :=
  { profile := questionedProfile, non2Ok := false }

/-- *Maria non è più intelligente di quanto non sia Carlo*: the matrix is
negated. -/
def matrixNegatedComparative : Non2Datum :=
  { profile := matrixNegatedProfile, non2Ok := false }

/-- Equality comparatives (*Maria è tanto intelligente quanto è Carlo*)
demand explicit, precise knowledge of the compared degrees, while *non₂*
demands inferred, imprecise knowledge. -/
def equalityComparative : Non2Datum :=
  { profile := preciseProfile, non2Ok := false }

/-- Explicit degree modifiers (*molto più intelligente*, *due metri più
alta*) require precise knowledge of the degree gap. -/
def precisionComparative : Non2Datum :=
  { profile := preciseProfile, non2Ok := false }

/-- *Maria è meno intelligente di quanto tu non creda* 'Maria is less
intelligent than you think': *meno*-comparatives admit *non₂* under the same
contextual conditions as *più*. Negated equality comparatives are
semantically close to *meno*-comparatives yet reject *non₂*, so the equality
restriction cannot reduce to equality linking two similar things (contra
[seuren-1969] and [antinucci-puglielli-1971]); it follows from matrix
negation and the precision condition. -/
def menoComparative : Non2Datum :=
  { profile := licensedProfile, non2Ok := true }

/-- *Chissà se non vale la pena di comprarlo* 'Who knows if it's (not) worth
buying it': an indirect question whose negated proposition the speaker
presupposes to be contrary to expectation, licensed by the same profile as
the comparatives. -/
def chissaSeNon : Non2Datum :=
  { profile := licensedProfile, non2Ok := true }

/-- The paper's acceptability paradigm. -/
def paradigm : List Non2Datum :=
  [ noOpinionContext, chessContext, explicitCriticismContext, complaintContext
  , questionedComparative, matrixNegatedComparative, equalityComparative
  , precisionComparative, menoComparative, chissaSeNon ]

/-- The licensing predicate reproduces the paper's judgment on every row of
the paradigm. -/
theorem paradigm_licenses_iff_non2Ok :
    ∀ d ∈ paradigm, (d.profile.licenses ↔ d.non2Ok = true) := by decide

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
`.clausalComparative` while `affatto`'s does not, so the predictions below
are derived from the Fragment registry. -/

/-- A weak NPI is admissible in a bias-conditioned comparative iff its
registry lists the clausal-comparative slot (surface phrasal comparatives are
not NPI environments) and the profile licenses *non₂*. -/
def weakNPIAdmissible (p : BiasLicensingProfile) (npi : Item) : Prop :=
  p.licenses ∧ .clausalComparative ∈ npi.licensingContexts

/-- *Pur* is admissible wherever *non₂* is licensed; the registry conjunct is
the Fragment's `pur_licensed_in_comparative`. -/
theorem pur_admissible_with_non2 : weakNPIAdmissible licensedProfile pur :=
  ⟨licensed_licenses, pur_licensed_in_comparative⟩

/-- *Affatto* is inadmissible in *non₂*-comparatives whatever the bias
profile: the block is registered in the lexical entry itself. -/
theorem affatto_blocked_in_non2 (p : BiasLicensingProfile) :
    ¬ weakNPIAdmissible p affatto :=
  λ ⟨_, h⟩ => affatto_not_licensed_in_comparative h

end NapoliNespor1976
