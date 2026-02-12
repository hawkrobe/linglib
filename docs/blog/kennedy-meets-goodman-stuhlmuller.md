# How Speaker Knowledge Shapes Numeral Meaning: Type-Shifting Resolves the Kennedy--Goodman & Stuhlmuller Puzzle

## 1. Introduction

Bare numerals present a persistent challenge at the semantics-pragmatics interface. Kennedy (2015) argues persuasively that the basic meaning of a bare numeral like *two* is exact --- *Two of the apples are red* is true if and only if the maximum number of red apples is exactly two. On this account, the weaker "at least" reading is derived through Partee's (1987) type-shifting operations, not encoded in the lexical semantics.

Independently, Goodman & Stuhlmuller (2013) demonstrate experimentally that numeral interpretation is sensitive to the speaker's epistemic state. When a speaker has full access to the relevant situation, listeners reliably assign an exact reading to bare numerals. But when the speaker's epistemic access is partial --- when she has observed only some of the relevant objects --- the exact reading weakens, and listeners allow that the true count may exceed the stated numeral.

These two results appear to be in tension. If *two* literally means "exactly two", then it is *false* when there are three red apples. A rational listener, hearing a speaker say *two* and knowing the speaker adheres to the Gricean maxim of Quality, should infer that the world contains exactly two red apples --- regardless of the speaker's epistemic access. The knowledge-sensitivity that Goodman & Stuhlmuller observe seems to require that the lower-bound reading be available as a genuine semantic option, not merely as a pragmatic weakening of an exact truth condition.

We show that this tension dissolves once Kennedy's own type-shifting analysis is taken seriously within a Rational Speech Acts (RSA) model. The resolution requires no modifications to either framework; it consists simply in recognizing that Kennedy's type-shifted lower-bound meaning constitutes an interpretation ambiguity that the RSA listener should marginalize over. We formalize the model in Lean 4 with exact rational arithmetic and prove several structural results, including a general criterion for when type-shifted meanings generate truth-conditionally distinct interpretations.

## 2. The Problem: Kennedy Exact Semantics Under Epistemic Uncertainty

Consider the standard RSA setup for the Goodman & Stuhlmuller paradigm: four world states s0 through s3 (representing 0--3 red apples), three utterances {*two*, *more than two*, *at least two*} (Kennedy's Class A/B alternative structure), and a speaker whose observations are determined by her level of epistemic access.

Under Kennedy's exact semantics, the truth conditions are:

- *two* is true only at s2
- *more than two* is true only at s3
- *at least two* is true at s2 and s3

The knowledge-state speaker model (G&S 2013, Eq. 2--3) scores utterances using log-utility: U(w; u) = ln P_L0(w | u). Since ln(0) = -infinity, any utterance that is false at some world the speaker considers possible receives utility negative infinity and is thus blocked. This is the *quality filter* --- the RSA implementation of the Gricean maxim of Quality.

The quality filter generates a stark prediction. A speaker who is uncertain between s2 and s3 cannot say *two* (false at s3) or *more than two* (false at s2). Only *at least two* survives. Under this analysis, bare *two* is predicted to be unspeakable under partial epistemic access.

But Goodman & Stuhlmuller's Experiment 2 shows precisely the opposite: speakers *do* use bare *two* under partial access, and listeners interpret it with a weakened, lower-bound-compatible reading. The naive implementation of Kennedy semantics within RSA does not merely make a wrong quantitative prediction --- it makes a categorical error, predicting zero probability for an utterance that speakers regularly produce.

## 3. The Resolution: Type-Shifting as Interpretation Ambiguity

The key observation is that Kennedy's own analysis already provides the necessary machinery. In Section 3.1, Kennedy shows that bare numerals are systematically ambiguous between two grammatically available meanings:

1. **The de-Fregean meaning (exact)**: max{d : D(d)} = n. This is the basic lexical entry --- a second-order property of degrees that introduces bilateral (two-sided) truth conditions.

2. **The type-lowered meaning (lower-bound)**: Via Partee's (1987) BE operation followed by iota and existential closure, the de-Fregean meaning can be lowered to a singular term, yielding the unilateral truth condition that there exist at least n objects satisfying the predicate.

Both meanings are grammatically legitimate. The de-Fregean meaning is basic; the type-lowered meaning is derived but not defective. The existence of two distinct, truth-conditionally divergent meanings constitutes a genuine interpretation ambiguity --- precisely the kind of latent variable that RSA models are designed to handle.

We treat interpretation as a latent variable following the approach of Scontras & Pearl (2021) for scope ambiguity. The pragmatic listener L1 marginalizes over interpretations:

> L1(w | u, access) is proportional to P(w) times the sum over interpretations i of P(i) times S1(u | w, access, i)

where S1(u | w, access, i) runs the full knowledge-state speaker model (with quality filter) under interpretation i separately.

## 4. How the Quality Filter Selects Interpretations

The central mechanism is straightforward: the quality filter interacts with the speaker's epistemic state to select the appropriate interpretation.

**Full access.** When the speaker knows the true world state, the exact interpretation is viable for bare *two* at s2 (it is true there). The exact interpretation is also more *informative* than the lower-bound interpretation, since it rules out s3. A rational speaker therefore prefers the exact interpretation. The listener, reasoning about this preference, assigns high posterior probability to s2 upon hearing *two*. The result is an exact reading.

**Partial access.** When the speaker is uncertain between s2 and s3, the exact interpretation is blocked by the quality filter: bare *two* is false at s3, and the speaker considers s3 possible. However, the lower-bound interpretation survives, since bare *two* under the lower-bound reading is true at both s2 and s3. The speaker can only produce *two* under the lower-bound interpretation. The listener, reasoning about this constraint, infers the lower-bound interpretation and assigns posterior mass to both s2 and s3. The result is a lower-bound reading.

This pattern reproduces the Goodman & Stuhlmuller finding: exact interpretation at full access, lower-bound interpretation at partial access. The quality filter is doing double duty: it enforces Gricean Quality in its standard role, and, as a direct consequence, it *selects* between available grammatical interpretations based on the speaker's epistemic state. This second function --- quality as interpretation selector --- is implicit in any RSA model with interpretation ambiguity, but it has not been explicitly characterized in the literature.

## 5. Formal Verification

We implemented this model in Lean 4 using exact rational arithmetic (no floating point). The predictions are:

| Access | Utterance | P(s2 \| u) | P(s3 \| u) | Interpretation |
|--------|-----------|------------|------------|----------------|
| Full   | bare *two* | 14/17     | 3/17       | Exact          |
| Partial | bare *two* | 1/4      | 3/4        | Lower-bound    |

At full access, the listener assigns the majority of probability mass to s2 (exactly two), consistent with an exact reading. At partial access, the posterior shifts decisively toward s3: the listener has inferred that the speaker's use of bare *two* under uncertainty signals the lower-bound interpretation, which is compatible with higher counts.

The interpretation marginals make the mechanism transparent:

| Access  | P(exact) | P(lower-bound) |
|---------|----------|----------------|
| Full    | 8/17     | 9/17           |
| Partial | 0        | 1              |

At partial access, the exact interpretation is categorically excluded: the quality filter blocks bare *two* under exact semantics for every observation consistent with speaker uncertainty. The listener's marginalization over interpretations assigns zero mass to the exact reading. At full access, both interpretations are available, with the exact interpretation favored by its greater informativity.

We proved three structural theorems:

1. At full access, the posterior probability of s2 strictly exceeds that of s3.
2. At partial access, s3 receives positive posterior probability.
3. The posterior probability of s3 strictly increases from full to partial access.

These results hold for any uniform prior over interpretations; biasing the prior toward exact (reflecting its status as the basic meaning) would strengthen the full-access exact reading without affecting the qualitative pattern.

## 6. Uniqueness of the Type-Shift

A potential concern is that other type-shifting operations might produce different derived meanings, introducing additional free parameters. This concern is unfounded: the lower-bound meaning is the unique output of the available type-shifting operations.

**Partee's BE** is the standard --- and essentially unique --- operation for lowering a generalized quantifier to a predicative type. Given a GQ Q of type <<e,t>,t>, BE(Q) returns the property lambda x. Q(lambda y. y = x): the set of individuals that Q "picks out" via the identity test.

**Existential closure** is the only viable way to bind the resulting free degree variable. Universal closure would require that for all k at or above the threshold m, the count n equals k simultaneously --- a condition that is unsatisfiable whenever the degree scale contains more than one value above the threshold. We proved this formally: there is no n such that n = 2 and n = 3.

The resulting equivalence --- "there exists k at or above m such that n = k" if and only if "n is at or above m" --- is a tautology of linear orders on the natural numbers. The lower-bound meaning is therefore not a stipulation but a derivational consequence. The prediction has no free parameters beyond the choice of semantic framework (Kennedy) and pragmatic framework (RSA with quality filter).

## 7. When Do Type-Shifted Meanings Matter for RSA?

The analysis raises a general question that, to our knowledge, has not been addressed in the RSA literature: for which expressions should the meaning function include type-shifted variants as alternative interpretations?

Partee's type-shifting operations are always grammatically available. They do not always, however, produce truth-conditionally distinct meanings. The criterion is algebraic: the round-trip through type-shifting (A composed with BE) preserves truth conditions if and only if the expression denotes a **principal ultrafilter** --- that is, if it is equivalent to the lifted meaning of some individual, lift(j) = lambda P. P(j).

For principal ultrafilters --- proper names, pronouns, definite descriptions that uniquely identify an individual --- the round-trip is truth-conditionally transparent. We proved this as a general theorem: for any j in the domain, A(BE(lift(j)))(P) = lift(j)(P) for all predicates P. Intuitively, *John* refers to the same individual whether the NP is interpreted as an entity, a singleton property, or a principal ultrafilter. The type-shifted meaning generates no new information for the listener.

For non-principal quantifiers --- universals, degree quantifiers, numerals under Kennedy's semantics --- the round-trip collapses. We verified on a toy model that A(BE(every)) is the trivially false quantifier: the predicative content of *every* under BE is the empty property (no single entity is identical to all entities), and existential closure over the empty property yields bottom. The type-shifted meaning is genuinely distinct from the original, and the two should be treated as competing interpretations.

This criterion has practical consequences for RSA modeling. Most existing RSA implementations deal with referential expressions (reference games) or expressions that already occupy the "right" semantic type for the model's purposes. For these, type-shifting is invisible. But for any model involving quantificational expressions --- numerals, quantifiers, degree expressions --- the availability of type-shifted meanings constitutes a latent variable that the listener should marginalize over. The Goodman & Stuhlmuller paradigm is the clearest existing case where neglecting this variable produces qualitatively incorrect predictions.

## 8. Discussion

The Goodman & Stuhlmuller knowledge-sensitivity facts are sometimes cited as evidence for lower-bound semantics, on the grounds that the weaker reading must be the literal meaning if it surfaces under conditions of speaker uncertainty. Our analysis shows that this inference is not warranted. Kennedy's exact semantics, combined with his own type-shifting analysis and standard RSA pragmatics, derives the same pattern --- and does so in a way that is arguably more explanatory, because the interpretation selection falls out of the quality filter rather than being stipulated as a feature of the lexical semantics.

The quality filter's role as an interpretation selector deserves emphasis. When a speaker's epistemic state makes one interpretation of an ambiguous expression risky (quality-violating), the filter pushes the speaker toward safer interpretations. The listener, reasoning about this constraint, can recover the intended interpretation from the speaker's epistemic circumstances. This mechanism generalizes beyond numerals to any case where an expression has grammatically available meanings with different truth-conditional profiles and where the speaker's knowledge state differentially affects the viability of those meanings.

## References

- Goodman, N. D. & Stuhlmuller, A. (2013). Knowledge and implicature: Modeling language understanding as social cognition. *Topics in Cognitive Science* 5(1), 173--184.
- Kennedy, C. (2015). A "de-Fregean" semantics (and neo-Gricean pragmatics) for modified and unmodified numerals. *Semantics & Pragmatics* 8(10), 1--44.
- Partee, B. H. (1987). Noun phrase interpretation and type-shifting principles. In J. Groenendijk, D. de Jongh, & M. Stokhof (Eds.), *Studies in Discourse Representation Theory and the Theory of Generalized Quantifiers* (pp. 115--143). Foris.
- Scontras, G. & Pearl, L. (2021). When pragmatics matters more for truth-value judgments: An investigation of quantifier scope ambiguity. *Glossa* 6(1).
