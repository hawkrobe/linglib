import Linglib.Theories.Semantics.Questions.Probabilistic

/-!
# Thomas (2026): Probabilistic, question-based additivity
@cite{thomas-2026} @cite{ciardelli-groenendijk-roelofsen-2018} @cite{frank-goodman-2012}

Formalisation of @cite{thomas-2026} "A probabilistic, question-based
approach to additivity" (S&P 19:1). The paper unifies the canonical
additive use of *too* with a previously unstudied "argument-building
use" by formalising felicity in terms of Bayesian inquisitive
answerhood — Def 62 of the paper. The substrate primitives
(`Answers`, `IsResolutionEvidencedBy`, `evidencesResolutionMore`)
live in `Theories/Semantics/Questions/Probabilistic.lean`; this file
encodes Def 64 (TOO felicity) and the abstract consequences that
account for the empirical contrasts in §3 and §4.

## Def 64: TOO(π) felicity

`TOO(π)` is felicitous iff there exists a contextually relevant
question `RQ` and an antecedent fact `ANT` such that:

* **Antecedent**: `ANT` Answers `RQ`.
* **Conjunction**: `ANT ∩ ⟦π⟧` Answers `RQ`, and the resolution
  evidenced by `ANT ∩ ⟦π⟧` is evidenced more strongly by it than by
  `ANT` alone.
* **Prejacent (i)**: `⟦π⟧` does not entail the resolution evidenced
  by `ANT ∩ ⟦π⟧`.
* **Prejacent (ii)**: for every proper superset `S ⊋ ⟦π⟧`, the
  resolution is evidenced more strongly by `ANT ∩ ⟦π⟧` than by
  `ANT ∩ S`.

(i) prevents *too* from being felicitous when the prejacent already
entails the answer suggested by the conjunction (the
@cite{beaver-clark-2008} ecstatic case (29a)). (ii) prevents *too*
from being felicitous when a weaker prejacent would do (the
"some-instrument vs cello" case (30)).
-/

namespace Phenomena.AdditiveParticles.Thomas2026

open Core Core.Question Semantics.Questions.Probabilistic

variable {W : Type*} {μ : PMF W}
  {prejacent antecedent : Set W} {rq : Question W} {𝒜 : Set (Set W)}

/-! ### TOO felicity (@cite{thomas-2026} Def 64) -/

/-- `TOO(π)` felicity in the sense of @cite{thomas-2026} Def 64. The
    five conditions are bundled below as a `structure` so consumers
    can project them by name. -/
structure IsTooFelicitous (prejacent antecedent : Set W) (rq : Question W)
    (μ : PMF W) : Prop where
  /-- Def 64a: the antecedent answers the relevant question. -/
  antecedent_answers : Answers antecedent rq μ
  /-- Def 64b (first half): the conjunction answers the relevant question. -/
  conjunction_answers : Answers (antecedent ∩ prejacent) rq μ
  /-- Def 64b (second half): the conjunction evidences its resolution
      more strongly than the antecedent alone does. -/
  conjunction_stronger : ∃ 𝒜,
    IsResolutionEvidencedBy rq 𝒜 (antecedent ∩ prejacent) μ ∧
    evidencesResolutionMore μ 𝒜 (antecedent ∩ prejacent) antecedent
  /-- Def 64c.i: the prejacent does not by itself entail the resolution
      that the conjunction evidences. -/
  prejacent_not_entails : ∀ 𝒜,
    IsResolutionEvidencedBy rq 𝒜 (antecedent ∩ prejacent) μ →
    ¬ prejacent ⊆ ⋂₀ 𝒜
  /-- Def 64c.ii: no proper weakening `S ⊋ prejacent` would license the
      same resolution as well as the prejacent does. -/
  prejacent_minimal : ∀ S : Set W, prejacent ⊆ S → S ≠ prejacent →
    ∀ 𝒜, IsResolutionEvidencedBy rq 𝒜 (antecedent ∩ prejacent) μ →
      evidencesResolutionMore μ 𝒜 (antecedent ∩ prejacent) (antecedent ∩ S)

/-! ### Abstract consequences -/

/-- TOO felicity entails that the antecedent puts positive prior mass:
    a direct corollary of `Answers.probOfSet_pos` applied to the
    antecedent condition. -/
theorem IsTooFelicitous.antecedent_probOfSet_pos
    (h : IsTooFelicitous prejacent antecedent rq μ) :
    μ.probOfSet antecedent > 0 :=
  h.antecedent_answers.probOfSet_pos

/-- TOO felicity entails that the conjunction puts positive prior
    mass — same corollary applied to the conjunction condition. -/
theorem IsTooFelicitous.conjunction_probOfSet_pos
    (h : IsTooFelicitous prejacent antecedent rq μ) :
    μ.probOfSet (antecedent ∩ prejacent) > 0 :=
  h.conjunction_answers.probOfSet_pos

/-- TOO felicity entails that the conjunction is genuinely stronger
    evidence than the antecedent alone (the @cite{thomas-2026} §4.4
    intuition that *too* marks a strict improvement). The witness
    `𝒜` from the conjunction-stronger field exhibits this. -/
theorem IsTooFelicitous.exists_strict_improvement
    (h : IsTooFelicitous prejacent antecedent rq μ) :
    ∃ 𝒜, IsResolutionEvidencedBy rq 𝒜 (antecedent ∩ prejacent) μ ∧
      μ.condProbSet (antecedent ∩ prejacent) (⋂₀ 𝒜) >
      μ.condProbSet antecedent (⋂₀ 𝒜) := by
  obtain ⟨𝒜, hRes, hMore⟩ := h.conjunction_stronger
  exact ⟨𝒜, hRes, hMore⟩

/-! ### RQ vs CQ — the contextual-relevance layer (@cite{thomas-2026} §5.4.3, §5.5)

The RQ in `IsTooFelicitous` need not be a Current Question (CQ) in
the discourse tree — it only needs to be *relevant* to one (the DQ
or some other in-scope question). This generalization is what
licenses *too* in cases like (45c) [implicit RQ] and (71) [single
*wh*-answer to multiple-*wh* CQ]. The relevance check uses
`Probabilistic.IsRelevantTo` (Def 61). -/

/-- TOO licensed by an RQ that is in turn relevant to some discourse
    question DQ. This is the full felicity condition (@cite{thomas-2026}
    Def 64) — `IsTooFelicitous` itself only constrains `rq`, but the
    paper requires `rq` to be Relevant to *some* `dq` in the discourse
    tree. -/
def IsTooLicensedByDQ (prejacent antecedent : Set W)
    (rq dq : Question W) (μ : PMF W) : Prop :=
  IsTooFelicitous prejacent antecedent rq μ ∧ IsRelevantTo rq dq μ

/-! ### Predicted infelicity

If the RQ does not satisfy the felicity conditions for any candidate
in the discourse, *too* is predicted infelicitous. Two characteristic
infelicity patterns from §5.5: -/

/-- @cite{thomas-2026} §5.5 (ex 72): if no contextually relevant `rq`
    has the prejacent providing additional evidence beyond the
    antecedent, *too* is infelicitous. The infelicity is captured by
    the absence of any felicitous RQ for the given (prejacent, ant). -/
def IsTooInfelicitous (prejacent antecedent : Set W) (μ : PMF W) : Prop :=
  ∀ rq : Question W, ¬ IsTooFelicitous prejacent antecedent rq μ

/-- @cite{thomas-2026} §5.5.1 (ex 75): if a single *wh*-answer (e.g.,
    "Bailey ate spaghetti") is offered against a multiple-*wh* CQ
    (e.g., "Who ate what?") whose resolutions specify what every
    salient individual ate, no `rq` over alt(CQ) satisfies the
    Conjunction Condition because the antecedent alone (e.g., "Avery
    ate pizza") doesn't constrain Bailey. *Too* is infelicitous unless
    the CQ is reinterpreted (cf. ex 77, where multiple-*wh* admits a
    mention-some single-pair reading). -/
def IsTooInfelicitousAgainstCQ (prejacent antecedent : Set W)
    (cq : Question W) (μ : PMF W) : Prop :=
  ¬ IsTooFelicitous prejacent antecedent cq μ

/-! ### Empirical predictions catalog

The proposal accounts for the following data from the paper. Each
entry pairs a numbered example with the structural reason it is
licensed (✓) or predicted infelicitous (✗). Worked numerical
formalisations are deferred to per-example study artifacts.

#### Argument-building uses (§3, §5.3)

* (1a)/(14a)/(65) ✓ "*Good thing she did too*" — hotel-style RQ
  ("How much has Ernie helped Iree?"); ANT and ANT∩π each raise the
  probability of "Ernie helped Iree a great deal" but ANT∩π raises
  it more.

* (1b)/(14b) ✓ "*The fine is a hefty one too*" — RQ "How much should
  I worry about traffic enforcement?".

* (1c)/(14c)/(65) ✓ "*It looks kind of fancy too*" (hotel) — see
  Thomas §5.3 worked derivation.

#### Canonical additive uses (§5.4)

* (10)/(21) ✓ "*I like spaghetti, too*" (after "I like pizza") —
  the canonical case; ANT entails one alt of "What do you like?",
  ANT∩π entails another.

* (68) ✓ "*She invited Dana, too*" — single mention-some answer
  combined with prior partial answer.

* (69) ✓ "*I like spaghetti, too*" — antecedent doesn't entail an
  alternative but provides probabilistic evidence (§5.4.1).

* (70) ✓ "*She invited Ellis, too*" — mention-all RQ, Quantity
  implicature handles the "no other invitee" inference (§5.4.2).

* (71) ✓ "*She invited Cameron, too*" against multiple-*wh* "Who
  are some people Avery invited?" — implicit single-*wh* RQ "Who is
  someone that Avery invited?" satisfies the felicity conditions
  (§5.4.3).

#### Predicted infelicity (§5.5)

* (15a-c) ✗ Argument-reversal: "*It was a bad thing she did, #too*"
  — no RQ relevant to discourse goals such that ANT∩π evidences a
  resolution; the prejacent argues against the antecedent.

* (29a)/(73) ✗ "*Sam is happy. #He's ecstatic, too*" — Prejacent
  Condition (i) violated: ⟦π⟧ = ecstatic entails "Sam is happy" =
  resolution evidenced by ANT∩π.

* (29b) ✗ "*Sam stole the cookies, #too*" (after fingerprints) —
  same Prejacent (i) violation.

* (30)/(74) ✗ "*Bailey plays the cello, #too*" against "Who plays
  an instrument?" — Prejacent Condition (ii) violated: a weaker
  prejacent ("Bailey plays an instrument") would license the same
  resolution.

* (40)/(75) ✗ "*Bailey ate spaghetti, #too*" against multiple-*wh*
  "Who ate what?" with both individuals presupposed to have eaten —
  Conjunction Condition fails because ANT does not constrain Bailey.

* (72) ✗ "*Dogs are mammals, too*" — ANT∩π provides no information
  about the existing CQ alternatives.

#### Other distributional facts (§5.5.2)

* (78)/(79) ✓ Narrow scope under negation: *too* under negation
  scopes its prejacent to the positive proposition.

* (80) ✓ Subordinate-clause use: prejacent is the subordinate clause.

* (81) ✓ Polar-question scope.

* (82)–(85) ✓ Wh-question domain restriction (Theiler 2019); felicity
  requires the variable in the prejacent to be properly bound. -/

end Phenomena.AdditiveParticles.Thomas2026
