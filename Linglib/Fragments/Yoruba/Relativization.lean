module

public import Linglib.Syntax.Clause.Relative

/-!
# Yoruba Relativization Fragment
[awobuluyi-1978] [keenan-comrie-1979] [ajiboye-2005]

Yoruba forms relative clauses with the introducer `tí` (high tone — distinct
from the toneless preverbal anteriority particle `ti` and the locative-source
preposition `ti`). Strategy varies by Accessibility-Hierarchy position:
subject and genitive use pronoun retention, direct object and most obliques
use gap.

[awobuluyi-1978] §6.18-6.24 is the descriptive primary source (also the
work WALS F122A cites for Yoruba's `.pronounRetention` value).
[keenan-comrie-1979] pp. 349-350 provides the K&C 1977 Table 1 codification
in exemplified form, with an analytical argument that the SU-position pronoun
`ó` is verb agreement rather than a true resumptive (a position the descriptive
Fragment doesn't commit to). K&C 1977 Table 1 p. 79 codes Yoruba as two
strategies: postnom -case (SU+DO) and postnom +case (GEN); IO/OBL/OComp coded
as `*` (does-not-exist-as-such, recast as DO via serial verb).

[awobuluyi-1978] §6.24 explicitly rejects the traditional relative-pronoun
analysis of `tí`, treating it as an "introducer" (≈ complementizer in modern
terms). [ajiboye-2005] §1.2.2 reaffirms a C-head analysis (in his case for
the M-tone `ti` found within genitive DPs, analyzed as a reduced relative).

[awobuluyi-1978] §3.15 additionally shows that genitive-meaning
constructions without overt `tí` (e.g. `owó Dàda` "Dada's money") are derived
from relative-clause sources (`owó tí Dàda ní` "the money that Dada has"), so
the genitive relativization channel is widely available.

Data from [awobuluyi-1978] §6.18–6.24, §3.15 + [keenan-comrie-1979]
ex. 125–128.
-/

@[expose] public section

namespace Yoruba

/-- The introducer *tí* (high tone, [awobuluyi-1978] §6.18), with what occupies the relativized
position by position:

* §6.19, subject: the high-tone third person singular pronoun *ó*, *Ọkùnrin tí ó pè mí* 'the man
  who called me', the pattern of [keenan-comrie-1979]'s example 127. [keenan-comrie-1979]
  analyse *ó* as verb agreement, which [keenan-comrie-1977] exclude from pronoun retention
  (p. 92); it is recorded here as Awobuluyi describes it, a pronoun.
* §6.20, direct object: dropped completely, *Ọkùnrin tí mo rí* 'the man I saw'.
* §6.21–6.22, indirect object and oblique: the prepositions *fi*, *ti*, *bá*, *fún* and *sí* drop
  their object (§6.21), *Ọbẹ tí mo fi gé e* 'the knife I cut it with'; the preposition *ní*
  triggers restructuring, the object dropped and repositioned, with *tí* inserted for place
  nouns and exceptions for *wà* and *gbé* (§6.22). The gap is recorded.
* §6.23, genitive: the qualifier is replaced by *rẹ̀* (singular) or *wọn* (plural), *Ọmọ tí olè
  jí ìwé rẹ̀* 'the child whose books were stolen'. Retention is obligatory
  ([keenan-comrie-1979]'s example 126 rejects the gap), and the genitive is the lowest
  relativizable position. -/
def relTi : Relativizer where
  form := "tí"
  placement := .postNominal
  realize
    | .subject | .genitive => {.resumptive}
    | .directObject | .indirectObject | .oblique => {.gap}
    | .objComparison => ∅

/-- The Yoruba relativizers. -/
def relativizers : List Relativizer := [relTi]

end Yoruba
