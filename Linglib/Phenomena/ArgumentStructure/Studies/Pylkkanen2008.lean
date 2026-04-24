import Linglib.Theories.Syntax.Minimalism.Basic
import Linglib.Theories.Syntax.Minimalism.Applicative
import Linglib.Theories.Syntax.Minimalism.ApplicativeDiagnostics
import Linglib.Theories.Syntax.Minimalism.Voice
import Linglib.Theories.Syntax.Minimalism.VoiceProjection
import Linglib.Theories.Semantics.Verb.EntailmentProfile
import Linglib.Phenomena.Causation.Typology
import Linglib.Phenomena.ArgumentStructure.Studies.Larson1988

/-!
# @cite{pylkkanen-2008} — Introducing Arguments
@cite{pylkkanen-2008} @cite{cuervo-2003} @cite{barss-lasnik-1986}

*Linguistic Inquiry Monographs* 49. MIT Press.

## Core Claims

1. **High vs Low Applicatives**: Applicative heads come in two semantic types.
   Low Appl merges below V, relating the applied argument to the theme
   (transfer-of-possession): `[VP V [ApplP goal [Appl theme]]]`.
   High Appl merges above VP, relating the applied argument to the event
   (benefactive): `[VoiceP agent [Voice [ApplP benef [Appl [VP V theme]]]]]`.

2. **Semantic type distinction**: High Appl denotes an individual-event
   relation `λx.λe. Appl(x,e)`. Low Appl denotes an individual-individual
   relation `λx.λy.λf.λe. f(e,x) & theme(e,x) & to-the-possession(x,y)`.

3. **Low recipient vs low source**: Low applicatives split into recipient
   (`ApplTo`: transfer *to* applied arg) and source (`ApplFrom`: transfer
   *from* applied arg). English DOC is low recipient; Korean theft
   constructions and Hebrew possessor datives are low source.

4. **C-command asymmetries**: In both configurations, the applied argument
   asymmetrically c-commands the theme. This derives the
   @cite{barss-lasnik-1986} binding asymmetries structurally.

5. **Cross-linguistic variation**: English, Japanese, and Korean have LOW
   Appl; Bantu languages (Chaga, Luganda, Venda) and Albanian have HIGH
   Appl.

## Diagnostics (Table 2.1, p. 33)

| Test                                                        | High | Low |
|-------------------------------------------------------------|------|-----|
| 1. Can unergatives be applicativized?                       | Yes  | No  |
| 2. Can static verbs be applicativized?                      | Yes  | No  |
| 3. (If language has English-style depictives) is the        |      |     |
|    applied argument available for depictive modification?   | Yes  | No  |

Test 3 is *conditional* on the language having depictive secondary
predicates with the English distribution. Korean lacks them entirely,
and Venda/Albanian have too-broad depictives — in those languages
Test 3 is *inapplicable*, not "fails." See `ApplDiagnosticResult`
in `Theories/Syntax/Minimalism/ApplicativeDiagnostics.lean`.

## Cross-references

- `Studies/Larson1988.lean`: VP shell predecessor — same c-command
  hierarchy (IO > DO) derived differently. Bridge theorem below proves
  convergence.
- `Studies/Kratzer1996.lean` Part III: Voice-based tree derivations
  (transitive, anticausative) using the same infrastructure.
-/

namespace Pylkkanen2008

open Minimalism

-- ============================================================================
-- § 1: Lexical Items
-- ============================================================================

def voice_ag_t  := mkLeafPhon .Voice [.V]    "Voice[AG]"  400
def appl_low_t  := mkLeafPhon .Appl  [.D]    "Appl[LOW]"  402
def appl_high_t := mkLeafPhon .Appl  [.V]    "Appl[HI]"   403
def V_sent_t    := mkLeafPhon .V     [.Appl] "sent"        404
def V_eat_t     := mkLeafPhon .V     [.D]    "eat"         405
def DP_john_t   := mkLeafPhon .D     []      "John"        406
def DP_mary_t   := mkLeafPhon .D     []      "Mary"        407
def DP_letter_t := mkLeafPhon .D     []      "a letter"    408
def DP_wife_t   := mkLeafPhon .D     []      "wife"        409
def DP_food_t   := mkLeafPhon .D     []      "food"        410

-- ============================================================================
-- § 2: Tree Derivations
-- ============================================================================

/-- Ditransitive with low applicative: "John sent Mary a letter"

    `[VoiceP John [Voice' Voice_AG [VP sent [ApplP Mary [Appl' Appl_LOW [DP a letter]]]]]]`

    Low Appl merges below V: V takes ApplP as complement. The goal
    (Mary) is in Spec-ApplP, c-commanding the theme (a letter) in
    complement of Appl. This derives the @cite{barss-lasnik-1986}
    asymmetry that IO asymmetrically c-commands DO. -/
def ditransitiveTree : SyntacticObject :=
  merge DP_john_t
    (merge voice_ag_t
      (merge V_sent_t
        (merge DP_mary_t
          (merge appl_low_t DP_letter_t))))

/-- High applicative benefactive (Chaga pattern): "he ate food for wife"

    `[VoiceP John [Voice' Voice_AG [ApplP wife [Appl' Appl_HIGH [VP eat [DP food]]]]]]`

    High Appl merges above VP: Appl takes VP as complement. The
    benefactive (wife) is in Spec-ApplP, relating to the event (not the
    theme). High Appl is attested in Bantu languages (Chaga, Luganda,
    Venda) and Albanian, but NOT in English. -/
def benefactiveTree : SyntacticObject :=
  merge DP_john_t
    (merge voice_ag_t
      (merge DP_wife_t
        (merge appl_high_t
          (merge V_eat_t DP_food_t))))

-- ============================================================================
-- § 3: C-command Predictions
-- ============================================================================

-- Ditransitive (low Appl): agent > goal > theme

/-- Agent c-commands goal. -/
theorem ditransitive_agent_ccommands_goal :
    cCommandsIn ditransitiveTree DP_john_t DP_mary_t := by decide

/-- Agent c-commands theme. -/
theorem ditransitive_agent_ccommands_theme :
    cCommandsIn ditransitiveTree DP_john_t DP_letter_t := by decide

/-- Goal c-commands theme — the @cite{barss-lasnik-1986} asymmetry
    derived structurally from V selecting ApplP. -/
theorem ditransitive_goal_ccommands_theme :
    cCommandsIn ditransitiveTree DP_mary_t DP_letter_t := by decide

/-- Theme does NOT c-command goal: the asymmetry is structural. -/
theorem ditransitive_theme_not_ccommands_goal :
    ¬ cCommandsIn ditransitiveTree DP_letter_t DP_mary_t := by decide

-- Benefactive (high Appl): benefactive > theme

/-- Benefactive c-commands theme. -/
theorem benefactive_benef_ccommands_theme :
    cCommandsIn benefactiveTree DP_wife_t DP_food_t := by decide

/-- Theme does NOT c-command benefactive. -/
theorem benefactive_theme_not_ccommands_benef :
    ¬ cCommandsIn benefactiveTree DP_food_t DP_wife_t := by decide

-- Appl head containment

/-- Low applicative marks the ditransitive. -/
theorem send_is_low_appl :
    containsB ditransitiveTree appl_low_t = true := by decide

/-- High applicative marks the benefactive. -/
theorem eat_is_high_appl :
    containsB benefactiveTree appl_high_t = true := by decide

-- ============================================================================
-- § 4: ApplType Association
-- ============================================================================

/-! The lexical items `appl_low_t` and `appl_high_t` correspond to
`ApplHead` instances from `Theories/Syntax/Minimalism/Applicative.lean`:
the ditransitive uses `applLowRecipient` (English DOC = transfer *to*);
the benefactive uses `applHigh` (Chaga = individual-event relation). -/

/-- The ditransitive's applicative is low (recipient). -/
theorem ditransitive_uses_low_recipient :
    applLowRecipient.applType = .lowRecipient ∧ applLowRecipient.applType.IsLow := by
  refine ⟨rfl, ?_⟩; unfold ApplType.IsLow; decide

/-- The benefactive's applicative is high. -/
theorem benefactive_uses_high :
    applHigh.applType = .high ∧ ¬ applHigh.applType.IsLow := by
  refine ⟨rfl, ?_⟩; unfold ApplType.IsLow; decide

-- ============================================================================
-- § 5: Cross-linguistic Applicative Typology (Table 2.1, §2.1.2–§2.1.3)
-- ============================================================================

/-! @cite{pylkkanen-2008} tests the high/low distinction in six languages
using three diagnostics (Table 2.1, p. 33). The diagnostics cluster
into two groups, confirming the typological split. The classifier
`Minimalism.classifyByDiagnostics` derives the high/low classification
from the diagnostic results; we verify that for each language, the
classifier output matches Pylkkänen's annotated classification. -/

/-- A language's diagnostic profile and Pylkkänen's annotated
    classification. The diagnostic results live in
    `Minimalism.ApplDiagnosticBundle`; `classification` records
    Pylkkänen's analytical conclusion. -/
structure LangApplProfile where
  language : String
  diagnostics : ApplDiagnosticBundle
  /-- Pylkkänen's annotated classification (§2.1.2 conclusion). -/
  classification : ApplType
  deriving Repr

/-- Pylkkänen's analytical conclusion is *derivable* from the
    diagnostics: the cluster classifier returns the same result,
    modulo the recipient/source distinction (which Table 2.1's three
    tests don't make — separating low recipient from low source needs
    additional transfer-directionality diagnostics from §2.2/§2.3). -/
def LangApplProfile.DerivationConsistent (l : LangApplProfile) : Prop :=
  match classifyByDiagnostics l.diagnostics with
  | some t => t = l.classification ∨
              (t = .lowRecipient ∧ l.classification = .lowSource)
  | none => False

instance : DecidablePred LangApplProfile.DerivationConsistent := fun l => by
  unfold LangApplProfile.DerivationConsistent
  cases classifyByDiagnostics l.diagnostics <;> infer_instance

-- Language data (§2.1.2–§2.1.3, examples cited by paper line)

/-- English: low recipient. *I ran him (20a); *I held him the bag (20b);
    *John told Mary the news drunk (27e). -/
def english_appl : LangApplProfile :=
  { language := "English"
  , diagnostics :=
    { unergative := .fails
    , staticVerb := .fails
    , depictive := .fails }
  , classification := .lowRecipient }

/-- Japanese: low recipient. *Taroo-ga Hanako-ni hasit-ta (21a);
    *Taroo-ga Hanako-ni kanojo-no kaban-o mot-ta (21b);
    *Taroo-ga hadaka-de Hanako-ni hon-o yonda (40a). -/
def japanese_appl : LangApplProfile :=
  { language := "Japanese"
  , diagnostics :=
    { unergative := .fails
    , staticVerb := .fails
    , depictive := .fails }
  , classification := .lowRecipient }

/-- Korean: low recipient. *Mary-ka John-hanthey talli-ess-ta (22a);
    *John-i Mary-hanthey kabang-ul cap-ass-ta (22b). Korean lacks
    English-style depictives entirely (§2.1.3.2.2), so Test 3 is
    *inapplicable*. -/
def korean_appl : LangApplProfile :=
  { language := "Korean"
  , diagnostics :=
    { unergative := .fails
    , staticVerb := .fails
    , depictive := .inapplicable }
  , classification := .lowRecipient }

/-- Luganda: high. Mukasa ya-tambu-le-dde Katonga (23a); Katonga
    ya-kwaant-i-dde Mukasa ensawo (23b); Mustafa ya-ko-le-dde Katonga
    nga mulwadde (43a). -/
def luganda_appl : LangApplProfile :=
  { language := "Luganda"
  , diagnostics :=
    { unergative := .passes
    , staticVerb := .passes
    , depictive := .passes }
  , classification := .high }

/-- Venda: high. Ndi-do-shum-el-a musadzi (24a); Nd-o-far-el-a Mukasa
    khali (24b). Venda postverbal APs have too broad a distribution to
    qualify as English-style depictives, so Test 3 is *inapplicable*
    (§2.1.3.2.4). -/
def venda_appl : LangApplProfile :=
  { language := "Venda"
  , diagnostics :=
    { unergative := .passes
    , staticVerb := .passes
    , depictive := .inapplicable }
  , classification := .high }

/-- Albanian: high. I vrapova (25a); Agimi i mban Drites çanten time
    (25b). Albanian "depictives" can also modify implicit external
    arguments and DPs inside PPs, so they don't qualify as English-style
    depictives — Test 3 is *inapplicable* (§2.1.3.2.5). -/
def albanian_appl : LangApplProfile :=
  { language := "Albanian"
  , diagnostics :=
    { unergative := .passes
    , staticVerb := .passes
    , depictive := .inapplicable }
  , classification := .high }

/-- Hebrew possessor datives: low source applicative (book §2.2,
    eq. 82a). Hebrew possessor datives are low applicatives, so they
    fail Tests 1 and 2 by the same logic as English low recipient.
    Pylkkänen does not test depictive modification with Hebrew
    possessor datives in §2.1.3, so Test 3 is `.inapplicable` here.
    Note: Table 2.1's three tests don't distinguish recipient from
    source — `derivationConsistent` accepts the cluster classifier's
    `.lowRecipient` output for Hebrew's actual `.lowSource`
    classification (the recipient-vs-source distinction needs the
    additional transfer-directionality diagnostics from §2.2). -/
def hebrew_appl : LangApplProfile :=
  { language := "Hebrew"
  , diagnostics :=
    { unergative := .fails
    , staticVerb := .fails
    , depictive := .inapplicable }
  , classification := .lowSource }

def allLanguages : List LangApplProfile :=
  [english_appl, japanese_appl, korean_appl, luganda_appl, venda_appl, albanian_appl, hebrew_appl]

-- Verification theorems

/-- Seven languages classified (six from Table 2.1 + Hebrew from §2.2). -/
theorem seven_languages : allLanguages.length = 7 := rfl

/-- For each language, Pylkkänen's annotated classification is *derivable*
    from the diagnostic results via the cluster-based classifier. The
    classification isn't stipulated and verified against itself — it's
    derived from the data and proved consistent with the analytical
    conclusion. -/
theorem all_classifications_derive_from_diagnostics :
    ∀ l ∈ allLanguages, LangApplProfile.DerivationConsistent l := by decide

/-- Anchor verifications for the two clusters. The aggregate
    `all_classifications_derive_from_diagnostics` covers all seven
    languages; these two anchor the cluster behavior at each pole. -/
theorem english_classification_derives :
    classifyByDiagnostics english_appl.diagnostics = some .lowRecipient := by decide

theorem luganda_classification_derives :
    classifyByDiagnostics luganda_appl.diagnostics = some .high := by decide

/-- Hebrew possessor datives are classified as `.lowRecipient` by
    Table 2.1's three tests (all-fail cluster), but Pylkkänen's actual
    classification is `.lowSource`. The two are *both* low; the
    recipient-vs-source distinction requires additional diagnostics
    not in Table 2.1. `derivationConsistent` accepts this case. -/
theorem hebrew_classification_derives_to_low :
    classifyByDiagnostics hebrew_appl.diagnostics = some .lowRecipient := by decide

-- ============================================================================
-- § 6: Bridge — Larson VP Shell ↔ Modern Voice/Appl
-- ============================================================================

/-! @cite{larson-1988}'s VP shell is the precursor of the modern Voice +
Applicative decomposition. While the tree shapes differ (Larson uses
one VP-shell layer; modern theory uses Voice and Appl heads), the
c-command hierarchy among DP arguments is identical: agent > goal/IO > theme/DO. -/

open Larson1988 in

/-- @cite{larson-1988}'s DOC and the modern Voice + low-Appl derivation
    produce the same c-command hierarchy: IO asymmetrically c-commands DO.

    This proves that @cite{larson-1988} and @cite{pylkkanen-2008},
    despite different decompositions, converge on the same structural
    prediction for @cite{barss-lasnik-1986} asymmetries. -/
theorem larson_modern_same_hierarchy :
    -- Larson's DOC: IO > DO
    cCommandsIn docDativeShift.final DP_mary DP_letter ∧
    ¬ cCommandsIn docDativeShift.final DP_letter DP_mary ∧
    -- Modern Voice/Appl: goal > theme (same asymmetry)
    cCommandsIn ditransitiveTree DP_mary_t DP_letter_t ∧
    ¬ cCommandsIn ditransitiveTree DP_letter_t DP_mary_t := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §7. Voice as the head that introduces the external argument
    (@cite{pylkkanen-2008} Ch. 3 §3.2 + Ch. 4 §4.2)

@cite{pylkkanen-2008}'s central claim about Voice (Ch. 4 §4.2,
"Eliminating Linking"): the external argument is *not* projected by
the verb itself but by a separate Voice head, following
@cite{kratzer-1996}. Voice combines with VP via Event Identification
(Event Identification, Ch. 1; -- UNVERIFIED: eq. number), introducing the external argument and relating it to
the event described by the verb.

This is one of the two competing views of Voice surveyed in
`Theories/Syntax/Minimalism/VoiceProjection.lean`. The other view,
defended by @cite{collins-2005} and @cite{storment-2026}, treats Voice
as a *structural* head (the smuggling projection) and assigns
external-argument introduction to *v* instead. The two views are
orthogonal — see `VoiceProjection.lean` for the substantive contrast. -/

/-- Pylkkänen's view applied to the canonical agentive Voice: it
    satisfies `IsExternalArgIntroducer` (it does the job Pylkkänen
    attributes to Voice). -/
theorem voice_introduces_external_arg_pylkkanen :
    Minimalism.IsExternalArgIntroducer Minimalism.voiceAgent := by decide

/-! ## §8. Voice-bundling for the English zero-causative
    (@cite{pylkkanen-2008} Ch. 3 §3.3; -- UNVERIFIED: eq. number)

A second contribution of Ch. 3: the difference between English (which
lacks unaccusative causatives) and Japanese/Finnish (which have them)
reduces to whether the language *bundles* Cause and Voice into a
single morphological head. English bundles ([Cause, Voice]); Japanese
and Finnish do not.

The `VoiceBundlingChoice` enum + `CauseSelection` axis + the full 2 × 3
typology cells (Pylkkänen Table 3.1) live in `Phenomena/Causation/
Typology.lean` so other studies of causation can consume the same
inventory. This section just affirms the canonical-instance choices. -/

open Phenomena.Causation.Typology
  (VoiceBundlingChoice englishZeroCausative japaneseLexicalCausative)

theorem english_zero_is_bundled :
    englishZeroCausative.bundling = some VoiceBundlingChoice.bundled := rfl

theorem japanese_lexical_is_independent :
    japaneseLexicalCausative.bundling = some VoiceBundlingChoice.independent := rfl

/-! ## §9. Cause is not a θ-role (@cite{pylkkanen-2008} Ch. 3 §3.2)

Pylkkänen's other major Ch. 3 argument: the causative head Cause
introduces a *causing event*, not a θ-role on the external argument.
Evidence: Japanese adversity causatives (eq. 19–25) have causative
morphology and meaning but no external argument. The bieventive
analysis (Cause = relation between two events) is required by such
data; the θ-role analysis (Cause = relation between a causer and a
caused event) cannot accommodate them.

Formalizing the bieventive vs. θ-role contrast at the level of
detail Pylkkänen offers requires event semantics infrastructure
beyond this study file's scope; the substantive claim is recorded
here for cross-reference. -/

/-! ## §10. Hebrew possessor datives as low source applicatives
    (@cite{pylkkanen-2008} Ch. 2 §2.2, Table 2.2 p. 60)

The second major Chapter 2 contribution: possessor datives in Hebrew
(and German, French, Korean) are *low source applicatives* — not double
object constructions, not possessor-raising. The relation is reversed
directionality: the dative argument is the *source* (former possessor)
of the direct object, not the recipient.

Pylkkänen's Table 2.2 contrasts the predictions of the *possessor-
raising* analysis (Landau 1999, Ura 1996, Kubo 1992) with the *low
applicative* analysis on six properties. The contrast is the paper's
own argument — Pylkkänen explicitly compares the two analyses. -/

/-- The two competing analyses of possessor dative constructions
    (@cite{pylkkanen-2008} §2.2). -/
inductive PossessorDativeAnalysis where
  | possessorRaising  -- Landau 1999, Ura 1996, Kubo 1992
  | lowSourceApplicative  -- Pylkkänen 2008
  deriving DecidableEq, Repr

/-- Property of possessor dative constructions tested in Table 2.2.
    `quantifierBindingContrast` is named to make the encoded property
    explicit: "qbind possible from DOC IO but NOT from possessor
    dative" (Landau's contrast claim). -/
inductive PossessorDativeProperty where
  | pseudopossessiveInterpretation
  | affectedness
  | lackOfAgentiveInterpretation
  | transitivityRestriction
  | quantifierBindingContrast
  | inabilityToControl
  deriving DecidableEq, Repr

/-- A 3-valued verdict for what an analysis says about a property:
    `predicts` (analysis says the property holds), `antipredicts`
    (analysis says the property does *not* hold), `noCleanPrediction`
    (analysis is silent or doesn't make a sharp claim). -/
inductive PredictsVerdict where
  | predicts
  | antipredicts
  | noCleanPrediction
  deriving DecidableEq, Repr

/-- Pylkkänen's Table 2.2 verdict: which analysis predicts each
    property. The qbind row is the most subtle: possessor-raising
    predicts the Landau contrast (qbind from possessor dative but not
    from DOC), while the low-applicative analysis predicts no contrast
    (both should permit qbind). Pylkkänen empirically vindicates the
    low-applicative side: "when pragmatics is controlled for, contrast
    disappears" (Ch. 2 §2.2.5, p. 56–57). -/
def PossessorDativeAnalysis.predicts :
    PossessorDativeAnalysis → PossessorDativeProperty → PredictsVerdict
  | .possessorRaising, .pseudopossessiveInterpretation => .predicts
  | .possessorRaising, .affectedness => .antipredicts
  | .possessorRaising, .lackOfAgentiveInterpretation => .antipredicts
  | .possessorRaising, .transitivityRestriction => .predicts
  | .possessorRaising, .quantifierBindingContrast => .predicts
  | .possessorRaising, .inabilityToControl => .predicts
  | .lowSourceApplicative, .quantifierBindingContrast => .antipredicts
  | .lowSourceApplicative, _ => .predicts

/-- The 5 properties where the low source analysis predicts the
    property holds. (Excludes `quantifierBindingContrast`, where LA
    *anti*predicts: it says no contrast exists — empirically vindicated
    in §2.2.5.) -/
def lowAnalysisPredictedProperties : List PossessorDativeProperty :=
  [.pseudopossessiveInterpretation, .affectedness, .lackOfAgentiveInterpretation,
   .transitivityRestriction, .inabilityToControl]

/-- The low source applicative analysis predicts every property in
    `lowAnalysisPredictedProperties`. -/
theorem low_predicts_five_properties :
    ∀ p ∈ lowAnalysisPredictedProperties,
      PossessorDativeAnalysis.predicts .lowSourceApplicative p = .predicts := by
  decide

/-- The possessor-raising analysis fails on affectedness and lack of
    agentive interpretation — Pylkkänen's two key objections to the
    raising analysis (§2.2.2, §2.2.3). -/
theorem possessor_raising_misses_affectedness_and_agentivity :
    PossessorDativeAnalysis.predicts .possessorRaising .affectedness = .antipredicts ∧
    PossessorDativeAnalysis.predicts .possessorRaising
      .lackOfAgentiveInterpretation = .antipredicts :=
  ⟨rfl, rfl⟩

/-- On the qbind row, the two analyses make *opposing* predictions.
    Pylkkänen's empirical argument (§2.2.5) is that the contrast
    Landau claimed disappears when pragmatics is controlled — so
    LA's `.antipredicts` (no contrast) wins, PR's `.predicts`
    (contrast exists) loses. -/
theorem analyses_oppose_on_qbind :
    PossessorDativeAnalysis.predicts .possessorRaising .quantifierBindingContrast = .predicts ∧
    PossessorDativeAnalysis.predicts .lowSourceApplicative
      .quantifierBindingContrast = .antipredicts :=
  ⟨rfl, rfl⟩

/-! ## §11. Japanese adversity passives: high vs low split
    (Kubo's 1992 work (cited by @cite{pylkkanen-2008}; not yet in linglib bib) diagnostics, reanalyzed in
    @cite{pylkkanen-2008} Ch. 2 §2.3)

Japanese adversity passives split into *gapped* (low source applicative)
and *gapless* (high applicative). The gapped/gapless distinction itself
is Kubo's 1992 work (cited by @cite{pylkkanen-2008}; not yet in linglib bib)'s; @cite{pylkkanen-2008}'s contribution is the
reanalysis as a low-source vs. high applicative typology. Both share
the *-rare-* morphology, but only the gapless type carries an obligatory
adversative entailment (Kubo's 1992 work (cited by @cite{pylkkanen-2008}; not yet in linglib bib)). The diagnostic bundle
distinguishing the two types is not formalized here; this section
records the type-level split for cross-reference. -/

/-- The two types of Japanese adversity passive (@cite{pylkkanen-2008}
    §2.3). -/
inductive JapaneseAdversityType where
  /-- Gapped: low source applicative. The affected DP is inside VP,
      with a transfer-of-possession relation to the underlying object. -/
  | gappedLowSource
  /-- Gapless: high applicative. The affected DP is outside VP,
      relating to the event as a whole. -/
  | gaplessHigh
  deriving DecidableEq, Repr

/-- The classification of an adversity passive type into the standard
    `ApplType` taxonomy. -/
def JapaneseAdversityType.toApplType : JapaneseAdversityType → ApplType
  | .gappedLowSource => .lowSource
  | .gaplessHigh => .high

theorem gapped_is_low_source :
    JapaneseAdversityType.gappedLowSource.toApplType = .lowSource := rfl

theorem gapless_is_high :
    JapaneseAdversityType.gaplessHigh.toApplType = .high := rfl

/-! ## §12. Spanish static low applicatives (@cite{cuervo-2003},
    discussed in @cite{pylkkanen-2008} §2.1.4.2)

@cite{cuervo-2003}'s thesis proposes a *three-way* split of low
applicatives in Spanish: low-to (recipient, dynamic), low-from
(source, dynamic), and low-AT (static possession). The static type is
Cuervo's contribution; Pylkkänen briefly endorses it in §2.1.4.2 as
compatible with her event-vs-state distinction. The static applicative
combines with small clause predicates (e.g. `Pablo le admira la
paciencia a Valeria` "Pablo admires Valeria's patience"), unlike
English low recipients which require event-creating verbs. -/

/-- Cuervo's three-way split of low applicatives. The third type
    (`staticPossession`) is @cite{cuervo-2003}'s extension; it is
    *not* in the canonical `ApplType` taxonomy because it requires
    static rather than dynamic semantics, and (per Cuervo) it
    specifically takes a small-clause complement. -/
inductive CuervoLowAppl where
  | recipient    -- transfer TO (Pylkkänen)
  | source       -- transfer FROM (Pylkkänen)
  | staticPossession  -- static IN-THE-POSSESSION (@cite{cuervo-2003}, Spanish)
  deriving DecidableEq, Repr

/-- Both of Pylkkänen's two low types correspond to dynamic transfer;
    Cuervo's third is static. -/
def CuervoLowAppl.isDynamic : CuervoLowAppl → Bool
  | .recipient | .source => true
  | .staticPossession => false

/-- The static low applicative is *not* one of Pylkkänen's two types
    — it requires the event-vs-state generalization in §2.1.4.2. -/
theorem static_not_dynamic :
    CuervoLowAppl.staticPossession.isDynamic = false := rfl

/-! ## §13. Causative typology — extracted to `Phenomena/Causation/Typology.lean`

Pylkkänen Table 3.1 (§3.4) is a 2 × 3 typology of causative
constructions parameterized by Voice-bundling × selection. The full
inventory (`CausativeCell`, `CauseSelection`, `MorphologyAccess`,
`PredictsVerdict` + 6 canonical instances + prediction theorems) lives
in `Phenomena/Causation/Typology.lean`, alongside @cite{song-1996}'s
orthogonal expression-style typology. Other studies of causation
(Wood 2015, Cuervo 2003 extensions, future Pylkkänen-derived work)
consume the same cell inventory from that file. -/

/-! ## §14. Broader Voice taxonomy under Pylkkänen's view

Pylkkänen's Voice = external-argument introducer. Per
`Theories/Syntax/Minimalism/VoiceProjection.lean`, this is one of two
competing views of Voice (the other being Collins/Storment's smuggling
projection). Test Pylkkänen's view against the broader `VoiceHead`
taxonomy in `Theories/Syntax/Minimalism/Voice.lean`: which Voice flavors
*do* introduce external arguments? -/

/-- Pylkkänen's view of Voice tested against all 8 named canonical
    flavors: voiceAgent, voiceCauser, voiceReflexive, and
    voiceExperiencer introduce external arguments; voiceMiddle
    (expletive), voiceImpersonal, voiceAnticausative, and voicePassive
    do not. The Pylkkänen-coherent Voice flavors are exactly the
    θ-assigning ones. (`.antipassive` is defined as a flavor in the
    Voice taxonomy but lacks a canonical `voiceAntipassive` constant
    in `Voice.lean`.) -/
theorem pylkkanen_view_partitions_voice_flavors :
    Minimalism.IsExternalArgIntroducer Minimalism.voiceAgent ∧
    Minimalism.IsExternalArgIntroducer Minimalism.voiceCauser ∧
    Minimalism.IsExternalArgIntroducer Minimalism.voiceReflexive ∧
    Minimalism.IsExternalArgIntroducer Minimalism.voiceExperiencer ∧
    ¬ Minimalism.IsExternalArgIntroducer Minimalism.voiceMiddle ∧
    ¬ Minimalism.IsExternalArgIntroducer Minimalism.voiceImpersonal ∧
    ¬ Minimalism.IsExternalArgIntroducer Minimalism.voiceAnticausative ∧
    ¬ Minimalism.IsExternalArgIntroducer Minimalism.voicePassive := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;>
    (unfold Minimalism.IsExternalArgIntroducer; decide)

/-! ## §15. Transitivity restriction grounded in EntailmentProfile
    (@cite{pylkkanen-2008} Diagnostic 1; semantic argument at eq. 103 /
    p. 55; -- UNVERIFIED: eq. 17 number)

Pylkkänen's *predicted* generalization (book Ch. 2 §2.1.1, Diagnostic 1):
"Only high applicative heads should be able to combine with
unergatives. Since low applicative heads denote a relation between
the direct object and the indirect object, a low applicative head
cannot appear in a structure that lacks a direct object."

The semantic argument (eq. 103, p. 55): combining low Appl
(`λx.λy.λf.λe. f(e,x) ∧ theme(e,x) ∧ HAVE(x,y)`) with an unergative
VP (`λe. agent(e, Mary) ∧ run(e)`) yields `agent(e, x) ∧ theme(e, x)`
when both arguments bind the same variable — a thematic-uniqueness
contradiction (Carlson, Parsons).

**Status of this formalization**: The composition predicate below uses
`Core.Verbs.EntailmentProfile.pPatientScore` to check whether a verb
has theme-like Proto-Patient entailments. An unergative has either no
object profile (`objectEntailments = none`) or an empty one
(`pPatientScore = 0`). The composition theorem is structural — it
does *not* re-derive the type clash from event-semantic λ-calculus
(that requires the compositional type-driven semantics in
`Theories/Semantics/Composition/`, not yet wired in here). The
substantive content captured: "low Appl needs a theme; unergative
provides none; composition fails." -/

open Semantics.Verb.EntailmentProfile (EntailmentProfile)

/-- A verb has an unsaturated theme argument iff its object entailment
    profile (if any) carries Proto-Patient entailments. Unergatives have
    `objectEntailments = none`; transitives have `pPatientScore ≥ 1`. -/
def hasUnsaturatedTheme (objectProfile : Option EntailmentProfile) : Prop :=
  match objectProfile with
  | some p => p.pPatientScore > 0
  | none => False

instance (op : Option EntailmentProfile) : Decidable (hasUnsaturatedTheme op) := by
  unfold hasUnsaturatedTheme; cases op <;> infer_instance

/-- A composition of an applicative head with a verb's object profile
    is well-formed iff either the applicative doesn't require a theme
    (high) or the verb's object profile provides one (transitive). -/
def applicativeComposition
    (a : ApplType) (objectProfile : Option EntailmentProfile) : Prop :=
  ¬ a.RequiresThemeInComplement ∨ hasUnsaturatedTheme objectProfile

/-- Pylkkänen's Diagnostic 1: low applicatives cannot combine with
    unergative verbs (whose object profile is `none`). The composition
    theorem follows from `ApplType.RequiresThemeInComplement` for low
    types and the empty object profile of an unergative.

    Note: this is structural, not a re-derivation of the eq. 103 type
    contradiction from event-semantic composition. The substantive
    semantic argument requires λ-calculus infrastructure not present
    in `Theories/Semantics/Composition/` for applicatives. The theorem
    captures the empirical content (low + unergative fails) without
    proving it from event-semantic types. -/
theorem low_applicative_blocks_unergative (a : ApplType) (hLow : a.IsLow) :
    ¬ applicativeComposition a none := by
  unfold applicativeComposition
  intro h
  cases h with
  | inl hNotReq =>
    apply hNotReq
    unfold ApplType.RequiresThemeInComplement
    exact hLow
  | inr hTheme =>
    unfold hasUnsaturatedTheme at hTheme
    exact hTheme

/-- High applicatives can combine with unergatives — the empirical
    finding for Luganda/Venda/Albanian (PDF eq. 23a/24a/25a, all
    verified). Follows from `¬ ApplType.high.RequiresThemeInComplement`. -/
theorem high_applicative_combines_with_unergative :
    applicativeComposition .high none := by
  unfold applicativeComposition
  left
  unfold ApplType.RequiresThemeInComplement ApplType.IsLow
  decide

/-- A toy theme-bearing object profile: Proto-Patient with
    `incrementalTheme` set. Used to demonstrate transitive composition
    in the next two theorems. -/
def themeBearingProfile : EntailmentProfile :=
  { volition := false, sentience := false, causation := false
  , movement := false, independentExistence := false
  , changeOfState := false, incrementalTheme := true
  , causallyAffected := false, stationary := false, dependentExistence := false }

theorem themeBearingProfile_has_unsaturated_theme :
    hasUnsaturatedTheme (some themeBearingProfile) := by
  unfold hasUnsaturatedTheme themeBearingProfile EntailmentProfile.pPatientScore
  decide

/-- Low recipient applicatives can combine with verbs providing a
    theme — the canonical English DOC pattern (`I baked him a cake`). -/
theorem low_recipient_combines_with_transitive :
    applicativeComposition .lowRecipient (some themeBearingProfile) := by
  unfold applicativeComposition
  right
  exact themeBearingProfile_has_unsaturated_theme

/-- Low source applicatives also combine with theme-providing verbs
    — Hebrew possessor datives (book §2.2). -/
theorem low_source_combines_with_transitive :
    applicativeComposition .lowSource (some themeBearingProfile) := by
  unfold applicativeComposition
  right
  exact themeBearingProfile_has_unsaturated_theme

/-! ## §16. Voice × Appl licensing matrix
    (`Theories/Syntax/Minimalism/Applicative.lean.licensedWith`)

`ApplHead.licensedWith` (in `Applicative.lean`) checks whether a
particular Appl head is licensed with a given Voice head: high
applicatives require event-introducing Voice (`hasSemantics = true`);
low applicatives are licensed with any Voice. Cross @cite{pylkkanen-2008}'s
high/low Appl typology with the `VoiceHead` taxonomy: which Voice
flavors license high Appl, and which don't?

This connects §14's Pylkkänen-Voice partition with the @cite{pylkkanen-2008}
Appl typology in a single matrix. -/

/-- High Appl requires Voice with event semantics. The named Voice
    flavors split: `voiceAgent`/`voiceCauser`/`voiceMiddle`/
    `voiceImpersonal`/`voiceReflexive`/`voiceExperiencer` carry event
    semantics and license high Appl; `voiceAnticausative`/`voicePassive`
    do not (they're event-semantically inert in this Voice taxonomy)
    and so don't license high Appl. -/
theorem voice_appl_licensing_matrix :
    -- High Appl licensed with event-bearing Voice flavors:
    Minimalism.applHigh.licensedWith Minimalism.voiceAgent = true ∧
    Minimalism.applHigh.licensedWith Minimalism.voiceCauser = true ∧
    -- Low Appl is always licensed (independent of Voice semantics):
    Minimalism.applLowRecipient.licensedWith Minimalism.voiceAgent = true ∧
    Minimalism.applLowRecipient.licensedWith Minimalism.voicePassive = true ∧
    Minimalism.applLowSource.licensedWith Minimalism.voiceAnticausative = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold Minimalism.ApplHead.licensedWith; decide)

end Pylkkanen2008
