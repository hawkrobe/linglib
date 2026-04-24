import Linglib.Theories.Syntax.Minimalism.Basic
import Linglib.Theories.Syntax.Minimalism.Applicative
import Linglib.Theories.Syntax.Minimalism.ApplicativeDiagnostics
import Linglib.Theories.Syntax.Minimalism.Voice
import Linglib.Theories.Syntax.Minimalism.VoiceProjection
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
def LangApplProfile.derivationConsistent (l : LangApplProfile) : Bool :=
  match classifyByDiagnostics l.diagnostics with
  | some t =>
    decide (t = l.classification ∨
            (t = .lowRecipient ∧ l.classification = .lowSource))
  | none => false

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

def allLanguages : List LangApplProfile :=
  [english_appl, japanese_appl, korean_appl, luganda_appl, venda_appl, albanian_appl]

-- Verification theorems

/-- Six languages classified. -/
theorem six_languages : allLanguages.length = 6 := rfl

/-- For each language, Pylkkänen's annotated classification is *derivable*
    from the diagnostic results via the cluster-based classifier. The
    classification isn't stipulated and verified against itself — it's
    derived from the data and proved consistent with the analytical
    conclusion. -/
theorem all_classifications_derive_from_diagnostics :
    allLanguages.all LangApplProfile.derivationConsistent = true := by decide

/-- Per-language verification of the derivation. -/
theorem english_classification_derives :
    classifyByDiagnostics english_appl.diagnostics = some .lowRecipient := by decide

theorem japanese_classification_derives :
    classifyByDiagnostics japanese_appl.diagnostics = some .lowRecipient := by decide

theorem korean_classification_derives :
    classifyByDiagnostics korean_appl.diagnostics = some .lowRecipient := by decide

theorem luganda_classification_derives :
    classifyByDiagnostics luganda_appl.diagnostics = some .high := by decide

theorem venda_classification_derives :
    classifyByDiagnostics venda_appl.diagnostics = some .high := by decide

theorem albanian_classification_derives :
    classifyByDiagnostics albanian_appl.diagnostics = some .high := by decide

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
(Ch. 1 eq. 10), introducing the external argument and relating it to
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
    (@cite{pylkkanen-2008} Ch. 3 §3.3, eq. 42)

A second contribution of Ch. 3: the difference between English (which
lacks unaccusative causatives) and Japanese/Finnish (which have them)
reduces to whether the language *bundles* Cause and Voice into a
single morphological head. English bundles ([Cause, Voice]); Japanese
and Finnish do not. Voice-bundling is what forces causatives to
introduce an external argument in English even though Cause itself
does not (eq. 42).

The bundling claim is a parametric difference between languages, not a
universal — it is a *crosslinguistic variation* parameter. The
formalization here documents the contrast at the type level; concrete
verb-by-verb instantiation lives in language-specific Fragment files. -/

/-- The Voice-bundling parameter (Ch. 3 §3.3) is a binary language-
    specific choice. English bundles; Japanese and Finnish do not. -/
inductive VoiceBundlingChoice where
  /-- English-type: Cause and Voice are bundled into one head;
      every causative therefore introduces an external argument. -/
  | bundled
  /-- Japanese/Finnish-type: Cause and Voice are independent;
      unaccusative causatives (Cause without Voice) are possible. -/
  | independent
  deriving DecidableEq, Repr

/-- The empirical prediction of Voice-bundling: a bundled language
    cannot have unaccusative causatives (since Cause forces Voice to
    project, which introduces the external argument). -/
def VoiceBundlingChoice.permitsUnaccusativeCausative :
    VoiceBundlingChoice → Bool
  | .bundled => false
  | .independent => true

theorem english_no_unaccusative_causative :
    VoiceBundlingChoice.permitsUnaccusativeCausative .bundled = false := rfl

theorem japanese_finnish_unaccusative_causative_possible :
    VoiceBundlingChoice.permitsUnaccusativeCausative .independent = true := rfl

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

/-- Property of possessor dative constructions tested in Table 2.2. -/
inductive PossessorDativeProperty where
  | pseudopossessiveInterpretation
  | affectedness
  | lackOfAgentiveInterpretation
  | transitivityRestriction
  | quantifierBindingIntoDirectObject
  | inabilityToControl
  deriving DecidableEq, Repr

/-- Pylkkänen's Table 2.2 verdict: which analysis predicts each
    property. The possessor-raising analysis predicts only some;
    the low-applicative analysis predicts all. -/
def PossessorDativeAnalysis.predicts :
    PossessorDativeAnalysis → PossessorDativeProperty → Bool
  | .possessorRaising, .pseudopossessiveInterpretation => true
  | .possessorRaising, .affectedness => false
  | .possessorRaising, .lackOfAgentiveInterpretation => false
  | .possessorRaising, .transitivityRestriction => true
  | .possessorRaising, .quantifierBindingIntoDirectObject => true  -- "contrast disappears with pragmatics"
  | .possessorRaising, .inabilityToControl => true
  | .lowSourceApplicative, _ => true  -- all six properties predicted

/-- Pylkkänen's Table 2.2 conclusion: the low source applicative
    analysis predicts every observed property; possessor raising
    misses two (affectedness, lack of agentive interpretation). -/
theorem low_applicative_strictly_better :
    ∀ p, PossessorDativeAnalysis.predicts .lowSourceApplicative p = true ∧
         (PossessorDativeAnalysis.predicts .possessorRaising .affectedness = false ∧
          PossessorDativeAnalysis.predicts .possessorRaising
            .lackOfAgentiveInterpretation = false) := by
  intro p; refine ⟨?_, ?_, ?_⟩
  · cases p <;> rfl
  · rfl
  · rfl

/-- The Hebrew possessor dative example (§2.2, eq. 82a) is grammatical:
    *Ha-yalda kilkela le-Dan et ha-radio* "The girl spoiled Dan's radio
    on him." The dative `le-Dan` is the source (former possessor) of
    the direct object `ha-radio`. -/
def hebrewPossessorDativeExample : String :=
  "Ha-yalda kilkela le-Dan et ha-radio."

/-! ## §11. Japanese adversity passives: high vs low split
    (@cite{pylkkanen-2008} Ch. 2 §2.3)

Japanese adversity passives split into *gapped* (low source applicative)
and *gapless* (high applicative) by Kubo 1992's diagnostics. Both have
the *-rare-* morphology and the adversative meaning; they differ in
whether the affected argument is structurally inside or outside VP. -/

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

/-! ## §12. Spanish static low applicatives (@cite{cuervo-2003}, in
    @cite{pylkkanen-2008} §2.1.4.2)

Spanish has a third type of low applicative — a *static* possession
relation, not transfer (eq. 78b of the book). This extends Pylkkänen's
two-way split (recipient/source) into a three-way split (recipient/
source/static), per Cuervo 2003. The static applicative combines with
small clause predicates (as in `Pablo le admira la paciencia a
Valeria` "Pablo admires Valeria's patience"), unlike English low
recipients which require event-creating verbs. -/

/-- Cuervo's three-way split of low applicatives. The third type
    (`staticPossession`) is Pylkkänen's §2.1.4.2 extension; it is
    *not* in the canonical `ApplType` taxonomy because it requires
    static rather than dynamic semantics. -/
inductive CuervoLowAppl where
  | recipient    -- transfer TO (Pylkkänen)
  | source       -- transfer FROM (Pylkkänen)
  | staticPossession  -- static IN-THE-POSSESSION (Cuervo 2003, Spanish)
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

/-! ## §13. Causative typology (@cite{pylkkanen-2008} Table 3.1, §3.4)

Pylkkänen's Table 3.1 (p. 87) is a 2 × 3 typology of causative
constructions, parameterized by:

- **Voice-bundling** (already formalized in §8):
  bundled (English) vs. independent (Japanese, Finnish)
- **Selection**: what the Cause head's complement is
  (root, verb, or phase)

The combination predicts cross-linguistic patterns about which
verb classes can be causativized and which adverbs can take scope
under Cause. -/

/-- The selection axis of Pylkkänen's causative typology
    (@cite{pylkkanen-2008} §3.4): what does Cause select for? -/
inductive CauseSelection where
  /-- Cause + √Root: causes a category-free root.
      Example: English *zero-causative* (English `melt`). -/
  | root
  /-- Cause + v + √Root: causes a category-defined verb.
      Examples: Bemba *-eshya* causative; Finnish *-tta* causative. -/
  | verb
  /-- Cause + (something at least as big as a phase, can include external args):
      causativizes unergatives and transitives.
      Examples: Luganda *-sa* causative; Venda *-is* causative. -/
  | phase
  deriving DecidableEq, Repr

/-- A causative-typology cell: Voice-bundling × selection. The 6 cells
    of Pylkkänen Table 3.1 each have specific predictions. -/
structure CausativeCell where
  bundling : VoiceBundlingChoice
  selection : CauseSelection
  deriving DecidableEq, Repr

/-- Table 3.1 prediction (1): can a language have unaccusative causatives?
    A bundled language can never have them (Cause forces Voice → external
    arg). An independent language can, regardless of selection. -/
def CausativeCell.permitsUnaccusativeCausative (c : CausativeCell) : Bool :=
  match c.bundling with
  | .bundled => false
  | .independent => true

/-- Table 3.1 prediction (2): can the language causativize unergatives
    and transitives? Only phase-selecting Cause can. -/
def CausativeCell.permitsUnergativeAndTransitiveCausativization
    (c : CausativeCell) : Bool :=
  match c.selection with
  | .phase => true
  | .root | .verb => false

/-- Table 3.1 prediction (3): can morphology intervene between root and
    Cause? Root-selecting Cause: no morphology can intervene; verb-selecting
    Cause: only non-external-argument morphology; phase-selecting Cause:
    all kinds of morphology. -/
def CausativeCell.morphologyCanInterveneBetweenRootAndCause
    (c : CausativeCell) : Bool :=
  match c.selection with
  | .root => false
  | .verb | .phase => true

-- Six canonical instances (Pylkkänen Table 3.1, languages in column headers)

/-- English zero-causative: Voice-bundling root-selecting. -/
def englishZeroCausative : CausativeCell :=
  { bundling := .bundled, selection := .root }

/-- Japanese lexical causative: non-Voice-bundling root-selecting. -/
def japaneseLexicalCausative : CausativeCell :=
  { bundling := .independent, selection := .root }

/-- Bemba *-eshya* causative: Voice-bundling verb-selecting. -/
def bembaEshyaCausative : CausativeCell :=
  { bundling := .bundled, selection := .verb }

/-- Finnish *-tta* causative: non-Voice-bundling verb-selecting. -/
def finnishTtaCausative : CausativeCell :=
  { bundling := .independent, selection := .verb }

/-- Luganda *-sa* causative: phase-selecting (bundling not specified
    in the book — Pylkkänen notes this as not yet known). -/
def lugandaSaCausative : CausativeCell :=
  { bundling := .independent, selection := .phase }  -- bundling default; book says unknown

/-- Venda *-is* causative: phase-selecting (bundling not specified). -/
def vendaIsCausative : CausativeCell :=
  { bundling := .independent, selection := .phase }

/-- English zero-causative: bundled, root-selecting. Predictions:
    no unaccusative causatives (Voice forces ext arg); no causativization
    of unergatives/transitives; no morphology between root and Cause. -/
theorem english_zero_predictions :
    englishZeroCausative.permitsUnaccusativeCausative = false ∧
    englishZeroCausative.permitsUnergativeAndTransitiveCausativization = false ∧
    englishZeroCausative.morphologyCanInterveneBetweenRootAndCause = false :=
  ⟨rfl, rfl, rfl⟩

/-- Japanese lexical causative: independent, root-selecting. Predictions:
    unaccusative causatives possible; no unergative/transitive causativization;
    no morphology between root and Cause. -/
theorem japanese_lexical_predictions :
    japaneseLexicalCausative.permitsUnaccusativeCausative = true ∧
    japaneseLexicalCausative.permitsUnergativeAndTransitiveCausativization = false ∧
    japaneseLexicalCausative.morphologyCanInterveneBetweenRootAndCause = false :=
  ⟨rfl, rfl, rfl⟩

/-- Luganda phase-selecting causative: unaccusative, unergative, and
    transitive causativization all possible; all morphology can intervene. -/
theorem luganda_phase_predictions :
    lugandaSaCausative.permitsUnaccusativeCausative = true ∧
    lugandaSaCausative.permitsUnergativeAndTransitiveCausativization = true ∧
    lugandaSaCausative.morphologyCanInterveneBetweenRootAndCause = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## §14. Broader Voice taxonomy under Pylkkänen's view

Pylkkänen's Voice = external-argument introducer. Per
`Theories/Syntax/Minimalism/VoiceProjection.lean`, this is one of two
competing views of Voice (the other being Collins/Storment's smuggling
projection). Test Pylkkänen's view against the broader `VoiceHead`
taxonomy in `Theories/Syntax/Minimalism/Voice.lean`: which Voice flavors
*do* introduce external arguments? -/

/-- Pylkkänen's view of Voice tested against the named flavors:
    voiceAgent and voiceCauser introduce external arguments;
    voiceMiddle (expletive), voiceImpersonal (impersonal), and
    voiceAnticausative (non-thematic) do not. The Pylkkänen-coherent
    Voice flavors are exactly the θ-assigning ones. -/
theorem pylkkanen_view_partitions_voice_flavors :
    Minimalism.IsExternalArgIntroducer Minimalism.voiceAgent ∧
    Minimalism.IsExternalArgIntroducer Minimalism.voiceCauser ∧
    ¬ Minimalism.IsExternalArgIntroducer Minimalism.voiceMiddle ∧
    ¬ Minimalism.IsExternalArgIntroducer Minimalism.voiceImpersonal ∧
    ¬ Minimalism.IsExternalArgIntroducer Minimalism.voiceAnticausative ∧
    ¬ Minimalism.IsExternalArgIntroducer Minimalism.voicePassive := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;>
    (unfold Minimalism.IsExternalArgIntroducer; decide)

end Pylkkanen2008
