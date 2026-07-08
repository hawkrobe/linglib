import Linglib.Semantics.Verb.Basic
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Uyghur Clause-Linking Morphemes and the Say-Complex
[major-2024] [major-2021]

This file records the morphemes implicated in Uyghur (Southeastern
Turkic) clausal embedding per [major-2024]: the verb root *de* 'say',
the converbial suffix -(I)p, and the complementizer *-lik* of the
nominalized (participial) embedding strategy. The apparent
complementizer *dep* is deliberately not an entry: [major-2024] (his
2–3) decomposes it as *de* + -(I)p; the decomposition and its
consequences (adjunction at VP or TP, the argument-position ban) live
in `Studies/Major2024.lean`.

## Main definitions

- `Uyghur.de`, `Uyghur.ip`, `Uyghur.lik` — the say-root, the converb,
  and the nominalized-clause typer, as root `Complementizer` entries;
  the inventory is `Uyghur.complementizers`
- `Uyghur.deVerb`, `Uyghur.oyla`, `Uyghur.warqira` — 'say', 'think',
  'scream': the main verbs whose frames drive [major-2024]'s §3
  argumentation

## Implementation notes

Bare `his (N)` references are to [major-2024]'s example numbers; the
bare -(I)p data of his §2 build on [sugar-2019] and [major-2021].
Forms use the paper's standard-Uyghur Latin transcription; capital `I`
in -(I)p marks the harmonizing high vowel. Verb entries are keyed by
bare stem and their `form` fields carry the stem with a final hyphen
(*de* surfaces as *dé* before the past-tense suffix, his 1).
-/

namespace Uyghur

/-- *de* — the verb root 'say'. A verb root, not an affix: it never
surfaces bare — inflected as a main verb (*dé-d-i* 'say-PST-3', his 1)
or converb-suffixed as a clause-linker (*de-p*, his 2) — so no
attachment of its own is recorded. Main-verb argument structure:
`Uyghur.deVerb`. -/
def de : Complementizer where
  form := "de"

/-- -(I)p — the general-purpose converbial suffix (glossed CNV),
deriving converb clauses that adjoin at VP or TP (his 4; [sugar-2019],
[major-2021]). Not a clause-typing complementizer under [major-2024]:
the same suffix links ordinary serial events ('jump', 'fall', his 3)
and the say-complex *de-p*. -/
def ip : Complementizer where
  form := "-(I)p"
  position := some .postfixed
  verbForm := some .Conv

/-- *-lik* — complementizer of the nominalized embedding strategy,
`V-PTPL-lik-POSS-CASE` (his 40a): case-marked, possessive agreement,
genitive subject — Noonan-nominalized. Participial clauses are
Uyghur's genuine clausal arguments ([major-2024] §3.2): grammatical
subjects (his 49a) and factive complements (his 61a). -/
def lik : Complementizer where
  form := "-lik"
  position := some .postfixed
  noonanType := some .nominalized

/-- The clause-linking morphemes at issue in [major-2024]: the two
pieces of the say-complex plus the rival argument strategy's typer.
Not an exhaustive inventory of Uyghur subordination. -/
def complementizers : List Complementizer := [de, ip, lik]

/-! ### Main verbs

Vendler class stays unset (`Verb.Aspect.vendlerClass` convention for
clause-embedding verbs); `voiceType` stays unset on *de-* because the
paper argues 'say' alternates between an agentive activity and a
subjectless stative description (his §3.3, 66–72). -/

/-- *de-* 'say' as a main verb: transitive with an obligatory internal
argument — bare finite CP (his 1), DP (his 39a: *(birnémi-ler-ni)
dé-d-i*), or participial clause (his 40a). The bare-CP complement must
stay adjacent to the verb, like a bare object, so it merges as
complement to V (his 73). Under [major-2024] this same entry,
converb-suffixed, heads dep clauses (`Studies/Major2024.lean`). -/
def deVerb : Verb where
  form := "de-"
  frames := [Frame.finiteClause, Frame.np]
  speechActVerb := true

/-- *oyla-* 'think' (his 58–59): takes DP objects (*u xewer-ni* 'that
news-ACC', his 59b) and participial complements (his 59a). No finite
frame is recorded: the apparent finite-CP frame (his 37a) is
[major-2024]'s re-analysis target — the dep clause is a VP adjunct
answering *qandaq* 'how' (his 58b, 60), not a complement. -/
def oyla : Verb where
  form := "oyla-"
  frames := [Frame.np, Frame.gerund]
  attitude := some (.doxastic .nonVeridical)

/-- *warqira-* 'scream': unergative, no complement frame — neither DP
(his 39b) nor participial clause (his 40b). With a dep adjunct it is
coerced into a verb of speech (his 38; §3.1). -/
def warqira : Verb where
  form := "warqira-"
  frames := []
  voiceType := some .agentive

end Uyghur
