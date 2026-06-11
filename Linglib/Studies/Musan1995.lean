import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.Musan1995

/-!
# [musan-1995]: On the Temporal Interpretation of Noun Phrases
[musan-1995]

Musan's dissertation establishes the **lifetime effects** diagnostic: past
tense with individual-level predicates implicates that the subject no longer
exists. The diagnostic minimal pair, ex (2a)/(2b) p. 11:

- (2a) *Gregory was silent* — stage-level predicate (`silent`); no lifetime
  implicature.
- (2b) *Gregory was from America* — individual-level predicate (`from
  America`); implicates Gregory is dead.

The implicature is not part of the truth conditions but a strong inference
arising from past tense + individual-level predicate composition. Central
to Musan's argument that NP temporal interpretation depends on the
predicate's lexical aspect.

## Schema gap

The lifetime-effects implicature is **not** captured by `ReichenbachFrame`
— the frame can encode past-tense locating (R < P), but the
stage-level/individual-level distinction and the pragmatic inference live
in a separate dimension (lexical aspect of the predicate + Gricean reasoning
over past-tense felicity). The empirical data is anchored in the
`LinguisticExample` JSON; no Reichenbach frame is provided here, since the
relevant content isn't reducible to S/P/R/E.

See `feedback_reichenbach_morph_vs_interp_conflation.md` for the broader
pattern: many tense-related phenomena are not faithfully modeled by
Reichenbach frames alone. -/

namespace Musan1995

open Data.Examples (LinguisticExample)

end Musan1995
