import Linglib.Core.Relativization.Basic
import Linglib.Core.Relativization.Profile

/-!
# Yoruba Relativization Fragment
@cite{awobuluyi-1978} @cite{keenan-comrie-1979} @cite{ajiboye-2005}

Yoruba forms relative clauses with the introducer `tí` (high tone — distinct
from the toneless preverbal anteriority particle `ti` and the locative-source
preposition `ti`). Strategy varies by Accessibility-Hierarchy position:
subject and genitive use pronoun retention, direct object and most obliques
use gap.

@cite{awobuluyi-1978} §6.18-6.24 is the descriptive primary source (also the
work WALS F122A cites for Yoruba's `.pronounRetention` value).
@cite{keenan-comrie-1979} pp. 349-350 provides the K&C 1977 Table 1 codification
in exemplified form, with an analytical argument that the SU-position pronoun
`ó` is verb agreement rather than a true resumptive (a position the descriptive
Fragment doesn't commit to). K&C 1977 Table 1 p. 79 codes Yoruba as two
strategies: postnom -case (SU+DO) and postnom +case (GEN); IO/OBL/OComp coded
as `*` (does-not-exist-as-such, recast as DO via serial verb).

@cite{awobuluyi-1978} §6.24 explicitly rejects the traditional relative-pronoun
analysis of `tí`, treating it as an "introducer" (≈ complementizer in modern
terms). @cite{ajiboye-2005} §1.2.2 reaffirms a C-head analysis (in his case for
the M-tone `ti` found within genitive DPs, analyzed as a reduced relative).

@cite{awobuluyi-1978} §3.15 additionally shows that genitive-meaning
constructions without overt `tí` (e.g. `owó Dàda` "Dada's money") are derived
from relative-clause sources (`owó tí Dàda ní` "the money that Dada has"), so
the genitive relativization channel is widely available.

Data from @cite{awobuluyi-1978} §6.18–6.24, §3.15 + @cite{keenan-comrie-1979}
ex. 125–128.
-/

namespace Fragments.Yoruba

open Core

/-- §6.19: Subject relativization. The relativized subject is replaced by the
    high-tone third-person singular pronoun `ó`.
    E.g. `Ọkùnrin tí ó pè mí` 'the man who called me'.
    `bearsCaseMarking := false` per @cite{keenan-comrie-1979}'s analysis of
    `ó` as verb agreement (K&C 1977 Table 1 p. 79 codes Yoruba's SU-strategy
    as -case). -/
def relTiSubject : RelClauseMarker :=
  { form := "tí + ó"
  , npRel := .resumptive
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject]
  , notes := "@cite{awobuluyi-1978} §6.19: subject replaced by ó. " ++
             "@cite{keenan-comrie-1979} ex. 127 confirms (`obinrin t' o maa ra it`); " ++
             "they argue ó is verb agreement, supporting the -case coding " ++
             "(consistent with K&C 1977 Table 1 p. 79). " ++
             "Matches WALS F122A `pronounRetention` (the WALS row also cites Awobuluyi 1978)." }

/-- §6.20: Direct object relativization. The relativized object is dropped
    completely (gap strategy).
    E.g. `Ọkùnrin tí mo rí` 'the man I saw'. -/
def relTiObject : RelClauseMarker :=
  { form := "tí + ∅"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.directObject]
  , notes := "@cite{awobuluyi-1978} §6.20: object dropped completely. " ++
             "@cite{keenan-comrie-1979} ex. 125 confirms (`ìṣu ti mo ra (*a) lana naa` — " ++
             "the resumptive *a is ungrammatical). Matches K&C 1977 Table 1 p. 79 " ++
             "-case strategy DO=+." }

/-- §6.21–6.22: Oblique relativization. Awobuluyi splits this into two
    sub-cases: the prepositions `fi`, `ti`, `bá`, `fún`, `sí` drop their
    object completely (gap, §6.21); the preposition `ní` triggers complex
    restructuring (drop + repositioning, with `tí` insertion for place
    nouns and exceptions for `wà`/`gbé`, §6.22). The single-cell
    `RelClauseMarker.npRel` cannot encode the split, so we record the
    dominant pattern (`gap`) and document the `ní` case in `notes`.
    E.g. `Ọbẹ tí mo fi gé e` 'the knife I cut it with'. -/
def relTiOblique : RelClauseMarker :=
  { form := "tí + ∅ (5 preps); tí + restructuring (ní)"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.indirectObject, .oblique]
  , notes := "@cite{awobuluyi-1978} §6.21: prepositions fi/ti/bá/fún/sí drop their object completely. " ++
             "§6.22: preposition ní triggers drop+repositioning, with tí-insertion for place-noun objects " ++
             "and exceptions for the locative verbs wà and gbé. " ++
             "Indirect object bundled here under §6.21's coverage of fún. " ++
             "@cite{keenan-comrie-1979} p. 349 reanalyzes IO/OBL/OComp relativization via serial-verb " ++
             "construction (the relativized position recast as DO of a serial verb), yielding the " ++
             "same gap strategy by a different analytical route. K&C 1977 Table 1 p. 79 codes these " ++
             "positions as `*` (does-not-exist-as-such)." }

/-- §6.23: Genitive relativization. The relativized genitive qualifier is
    replaced by `rẹ̀` (singular) or `wọn` (plural) — pronoun retention.
    E.g. `Ọmọ tí olè jí ìwé rẹ̀` 'the child whose books were stolen';
    `Àwọn tí olè jí ìwé wọn` 'those whose books were stolen'.
    `bearsCaseMarking := true` per K&C 1977 Table 1 p. 79 (Strategy 2: postnom,
    +case, GEN=+). The genitive-form pronouns `rẹ̀`/`wọn` are morphologically
    distinct from subject `ó` and object `i`/`un`/`ó`, so per Awobuluyi §2.21's
    polymorphic-noun classification they encode their case role lexically. -/
def relTiGenitive : RelClauseMarker :=
  { form := "tí + rẹ̀/wọn"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.genitive]
  , notes := "@cite{awobuluyi-1978} §6.23: genitive qualifier replaced by " ++
             "rẹ̀ (singular) or wọn (plural). Establishes lowestRelativizable " ++
             "= .genitive on the AH (WALS does not code Yoruba on F123A or " ++
             "the AH cutoff). @cite{keenan-comrie-1979} ex. 126 confirms " ++
             "obligatory rẹ retention (`ọkunrin ti mo wọ si ile {rẹ/*0}` — gap is " ++
             "ungrammatical). Matches K&C 1977 Table 1 p. 79 +case strategy GEN=+." }

/-- All Yoruba relative clause markers, anchored to @cite{awobuluyi-1978}
    §6.19–6.23 + @cite{keenan-comrie-1979} ex. 125–128. All four share the
    introducer `tí` (high tone, §6.18). -/
def relMarkers : List RelClauseMarker :=
  [relTiSubject, relTiObject, relTiOblique, relTiGenitive]

/-- Yoruba relativization profile (typological summary). -/
def relativization : Core.Relativization.RelativizationProfile :=
  { subjStrategy := .pronounRetention
  , oblStrategy := .gap
  , rcPosition := .postNominal
  , lowestRelativizable := .genitive
  , internallyHeaded := .absent
  , notes := "Relativizer tí (high tone; distinct from preverbal/preposition ti). "
          ++ "@cite{awobuluyi-1978} §6.19 SU resumption (ó); §6.20 DO gap; "
          ++ "§6.21 OBL gap (fi/ti/bá/fún/sí); §6.22 OBL with ní triggers "
          ++ "drop+repositioning (complexity not captured by oblStrategy field); "
          ++ "§6.23 GEN resumption (rẹ̀/wọn). Matches WALS F122A pronounRetention." }

end Fragments.Yoruba
