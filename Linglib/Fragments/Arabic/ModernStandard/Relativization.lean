import Linglib.Syntax.RelativeClause.Basic
import Linglib.Syntax.RelativeClause.WALS

/-!
# Modern Standard Arabic Relativization Fragment
[keenan-comrie-1977] [ryding-2005]

Two definite-headed RC markers, anchored on [ryding-2005] ch. 14
(§14.1–14.4) and cross-checked against [keenan-comrie-1977] Table 1:

- *alladhī/allatii* + no overt subject (Ryding §14.2; K&C -case strategy):
  the relative pronoun agrees with a definite head in gender, number, and
  (in the dual) case. The relativized subject position is unfilled.
- *alladhī/allatii* + resumptive pronoun (Ryding §14.4.1; K&C +case
  strategy): same relative pronoun introduces the RC; a resumptive
  personal pronoun (the *ʿaaʾid* / *raajiʿ*) appears in the relativized
  non-subject position.

`relMarkers` exposes the full Ryding-attested set (4 markers: definite-
headed pair plus indefinite-headed pair from §14.3, §14.4.2 — Ø relative
pronoun, with resumption when relativizing a non-subject). The free
relatives *maa* / *man* (Ryding §14.5) are a separate construction
(no head NP) and are not included. Paper-specific subsets (e.g., the
two-marker subset [keenan-comrie-1977] Table 1 records) live in
the consuming Studies files, not in this Fragment.

## Variety

The data here is Modern Standard Arabic (ISO `arb`); other files in
`Fragments/Arabic/` (`Reference.lean`, `Pronouns.lean`, `Morph.lean`,
`TenseAspect.lean`) target Egyptian Arabic (ISO `arz`). The directory is
already mixed; a future split into `Fragments/StandardArabic/` and
`Fragments/EgyptianArabic/` would resolve the incoherence.
-/

namespace Arabic.ModernStandard

open RelativeClause

/-- Relative pronoun *alladhī* (masc.sg.) / *allatii* (fem.sg.) — head of a
    nine-form paradigm marked for number/gender (and, in the dual, case);
    see [ryding-2005] §14.1 Table. Used with definite antecedents
    (Ryding §14.2). The relativized subject position carries no overt
    NP — verb agreement on the RC's verb encodes the subject. Per
    [keenan-comrie-1977] this is the language's -case strategy and
    is restricted to subject relativization.

    E.g., "hiya llatii ʾarsalat-i l-duktuur-a"
          'she is the one who sent the doctor' (Ryding §14.2). -/
def relAlladhi : Marker :=
  { form := "alladhī/allatii"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject]
  , headDefiniteness := some .definite
  , notes := "Relative pronoun agrees with definite head in number/gender; "
          ++ "no overt subject in RC (verb agreement only); "
          ++ "[ryding-2005] §14.2" }

/-- Relative pronoun *alladhī/allatii* with a resumptive personal pronoun
    (the *ʿaaʾid*) in the relativized position. Used with definite
    antecedents when the relativized position is the object of a verb or
    preposition ([ryding-2005] §14.4 and §14.4.1). The resumptive
    pronoun bears case, instantiating [keenan-comrie-1977]'s +case
    strategy. K&C Table 1 records coverage through the full DO–OCOMP
    range.

    E.g., "al-kitaab-u alladhii qaraʾ-naa-hu"
          'the book that we read (it)' (Ryding §14.4). -/
def relResumptive : Marker :=
  { form := "alladhī/allatii + resumptive"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.directObject, .indirectObject, .oblique, .genitive, .objComparison]
  , headDefiniteness := some .definite
  , notes := "Resumptive pronoun (ʿaaʾid) in relativized position bears case; "
          ++ "[ryding-2005] §14.4.1; K&C Table 1 DO–OCOMP" }

/-- Indefinite-headed RC, subject relativization. Per [ryding-2005]
    §14.3, "a relative clause may refer to an indefinite noun or noun
    phrase in the main clause, in which case the relative pronoun is
    omitted." The relativized subject position is unfilled; the RC's verb
    encodes the subject via agreement.

    E.g., "fii ziyaarat-in li-dimashq-a ta-staghriq-u ʾusbuuʿ-an"
          'on a visit to Damascus [which] lasts a week' (Ryding §14.3). -/
def relAsyndeticGap : Marker :=
  { form := "∅"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject]
  , headDefiniteness := some .indefinite
  , notes := "Indefinite-headed RC; no overt relative pronoun; "
          ++ "subject encoded by RC-verb agreement; "
          ++ "[ryding-2005] §14.3" }

/-- Indefinite-headed RC, non-subject relativization. Per [ryding-2005]
    §14.4.2, "indefinite relative clauses do not include relative pronouns,
    but they must include a resumptive pronoun if the clause refers back to
    a noun or noun phrase that is the object of a preposition or a verb."
    The resumptive pronoun bears case.

    Ryding's examples cover direct objects directly. The §14.4.2 "object
    of a preposition or a verb" formulation extends to oblique positions
    by the same principle; [keenan-comrie-1977] Table 1 covers the
    full DO–OCOMP range with the resumptive strategy in both definite and
    indefinite contexts, and Ryding gives no contrastive restriction. The
    `positions` list reflects this combined Ryding+K&C reading.

    E.g., "wa-qaal-a fii muʾtamar-in SiHaafiyy-in ʿaqad-a-hu ʾams-i"
          'he said in a press conference [which] he held (it) yesterday'
          (Ryding §14.4.2). -/
def relAsyndeticResumptive : Marker :=
  { form := "∅ + resumptive"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.directObject, .indirectObject, .oblique, .genitive, .objComparison]
  , headDefiniteness := some .indefinite
  , notes := "Indefinite-headed RC; no overt relative pronoun; "
          ++ "resumptive pronoun bears case; "
          ++ "[ryding-2005] §14.4.2 (DO directly attested; "
          ++ "non-DO positions per K&C Table 1 + parsimony with definite case)" }

/-- The full MSA RC marker inventory per [ryding-2005] ch. 14:
    definite-headed pair (`relAlladhi`, `relResumptive`) plus
    indefinite-headed pair (`relAsyndeticGap`, `relAsyndeticResumptive`).
    The free relatives *maa* / *man* of §14.5 are a separate construction
    (no head NP) and are not included. -/
def relMarkers : List Marker :=
  [relAlladhi, relResumptive, relAsyndeticGap, relAsyndeticResumptive]

/-- Arabic relativization profile (WALS-style summary).

    `subjStrategy := .gap`: subject relativization uses no overt element
    in the relativized position (Ryding §14.2). The resumptive marker
    does not cover subject (Ryding gives no resumption-in-SU examples;
    K&C confirm SU is gap-only). This matches the convention used for
    Welsh and Hebrew, which also pair a SU gap-strategy with a non-SU
    resumptive strategy.

    `lowestRelativizable := .oblique`: the WALS Ch 122/123 coarse value;
    K&C Table 1 records OCOMP coverage. The bridge theorem
    `arabic_kc_covers_deeper_than_wals` in
    `Studies/KeenanComrie1977.lean` documents
    the systematic K&C-vs-WALS asymmetry. -/
def relativization : RelativeClause.Profile :=
  { subjStrategy := .gap
  , oblStrategy := .pronounRetention
  , rcPosition := .postNominal
  , lowestRelativizable := .oblique
  , notes := "Subject: no overt element in relativized position. "
          ++ "Non-subject (definite head): resumptive pronoun. "
          ++ "[ryding-2005] §14" }

end Arabic.ModernStandard
