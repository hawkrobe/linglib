import Linglib.Syntax.Minimalist.SyntacticObject.Subterm
import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.Applicative
import Linglib.Syntax.Minimalist.Voice
import Linglib.Syntax.Minimalist.Movement.Smuggling
import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.ArgumentStructure.ArgumentIntroduction
import Linglib.Data.WALS.Features.F109A
import Linglib.Studies.Larson1988

/-!
# [pylkkanen-2008] — Introducing Arguments
[pylkkanen-2008] [cuervo-2003] [barss-lasnik-1986]

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
   [barss-lasnik-1986] binding asymmetries structurally.

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
in the "Applicative diagnostics" section below.

## Cross-references

- `Studies/Larson1988.lean`: VP shell predecessor — same c-command
  hierarchy (IO > DO) derived differently. Bridge theorem below proves
  convergence.
- `Studies/Kratzer1996.lean` Part III: Voice-based tree derivations
  (transitive, anticausative) using the same infrastructure.
-/

namespace Pylkkanen2008

open Minimalist
open RootedTree

/-! ### Voice projection (relocated from Minimalist/VoiceProjection.lean)

# What is Voice? Two competing views
[kratzer-1996] [pylkkanen-2008] [collins-2005] [storment-2026]

A formalizer-side meta-bridge surfacing a substantive theoretical
disagreement neither paper sets up directly: what is the *job* of the
syntactic head called Voice?

## The two views

**Pylkkänen / Kratzer view** ([kratzer-1996], [pylkkanen-2008]):
Voice is the head that *introduces the external argument*. Its job is
thematic — it bears a θ-relation between the external argument and the
event described by the verb (Event Identification, [kratzer-1996]
eq. 10). All argument-structure theory follows from where Voice projects
and what it bundles with (Cause-Voice bundling, [pylkkanen-2008]
Ch. 3 §3.3). Without Voice, no external argument is introduced at all.

**Collins / Storment view** ([collins-2005], [storment-2026]):
Voice is the *smuggling projection*. Its job is structural — it provides
the landing site (Spec,VoiceP) into which a constituent can move,
licensing A-movement past an in-situ external argument. The external
argument itself is introduced by *v*, not Voice
([storment-2026] §4.3). Voice's status as a non-phase head is what
permits smuggling. The voice-as-smuggling-projection conception is "a
notable departure from the view of Voice⁰ as an applicative head that
introduces the external argument" ([storment-2026], §4.3).

## The disagreement is partly substantive, partly terminological

The two camps do not disagree about *the empirical phenomena*. They
disagree about *which functional head does which job*. Pylkkänen
attributes external-argument introduction to Voice and structural
licensing to higher functional projections (`T⁰`, `Infl`). Collins
attributes external-argument introduction to *v* and structural
licensing (Case + smuggling) to Voice. The label "Voice" denotes
different positions in the two systems.

The orthogonality of the two predicates `IsExternalArgIntroducer` and
`IsSmugglingProjection` (defined below) reflects this: a `VoiceHead`
instance can satisfy one, both, or neither. Linglib's `VoiceHead`
structure encodes both axes (`assignsTheta` and `permitsSmuggling`)
independently, accommodating both views simultaneously.

## Where this meta-bridge sits

Per the CLAUDE.md cross-theory-meta-bridges convention, this is a
formalizer-side synthesis (neither Pylkkänen nor Collins/Storment
formulates the contrast in these exact terms). Both views are pure-theory
positions about a syntactic head, with no specific empirical phenomenon
at stake.
-/

/-! #### Two predicates over Voice heads

The Pylkkänen view and the Collins/Storment view make different claims
about what makes a Voice head "well-formed Voice." -/

/-- **Pylkkänen / Kratzer view**: a Voice head is "doing its job" iff
    it introduces an external argument (assigns external θ).
    [kratzer-1996]: Voice = the head bearing the θ-relation. -/
def IsExternalArgIntroducer (v : VoiceHead) : Prop :=
  v.AssignsTheta

instance (v : VoiceHead) : Decidable (IsExternalArgIntroducer v) := by
  unfold IsExternalArgIntroducer; infer_instance

/-- **Collins / Storment view**: a Voice head is "doing its job" iff
    it permits smuggling (it is the structural landing site for a
    constituent moving past an in-situ external argument).
    [collins-2005], [storment-2026]. -/
def IsSmugglingProjection (v : VoiceHead) : Prop :=
  v.permitsSmuggling = true

instance (v : VoiceHead) : Decidable (IsSmugglingProjection v) := by
  unfold IsSmugglingProjection; infer_instance

/-! #### The two views are orthogonal

Linglib's `VoiceHead` already encodes both axes. The question is
whether they coincide for the canonical Voice instances.
**Answer: they don't.** A Voice head can satisfy either one, both, or
neither — the four corners of the orthogonality square. -/

/-- `voiceAgent` satisfies the Pylkkänen view (it introduces the agent
    external argument) but **fails** the Collins/Storment view
    (agentive Voice is a strong phase head; smuggling is blocked). -/
theorem voiceAgent_pylkkanen_yes_collins_no :
    IsExternalArgIntroducer voiceAgent ∧ ¬ IsSmugglingProjection voiceAgent := by
  decide

/-- `voicePassive` satisfies the Collins view (it is the smuggling
    landing site) but **fails** the Pylkkänen view (it does not
    introduce an external argument — the external arg is in Spec,vP
    per [collins-2005] §2 UTAH). The passive Voice head is
    *puzzling* on Pylkkänen's view: a Voice head with no θ-role to
    assign. -/
theorem voicePassive_collins_yes_pylkkanen_no :
    IsSmugglingProjection voicePassive ∧ ¬ IsExternalArgIntroducer voicePassive := by
  decide

/-- `voiceAnticausative` similarly fits the Collins view (smuggling
    target for the unaccusative-like derivation Storment uses for QI
    and LI) and fails the Pylkkänen view (no external argument). -/
theorem voiceAnticausative_collins_yes_pylkkanen_no :
    IsSmugglingProjection voiceAnticausative ∧
    ¬ IsExternalArgIntroducer voiceAnticausative := by
  decide

/-- The two views are not equivalent: there exist Voice heads
    distinguishing them (in fact, the canonical instances above all do). -/
theorem views_not_equivalent :
    ¬ (∀ v : VoiceHead, IsExternalArgIntroducer v ↔ IsSmugglingProjection v) := by
  intro h
  -- voiceAgent introduces external arg but blocks smuggling
  have hExt : IsExternalArgIntroducer voiceAgent := by decide
  have hSmug : IsSmugglingProjection voiceAgent := (h voiceAgent).mp hExt
  exact absurd hSmug (by decide)

/-! #### What the disagreement amounts to

In Pylkkänen's framework, every Voice head should be an
`IsExternalArgIntroducer`. The fact that linglib's `voicePassive` and
`voiceAnticausative` are not means *Pylkkänen would not call these
"Voice"* — she would attribute the structural-licensing function to a
different (perhaps unnamed) head.

In Collins/Storment's framework, every Voice head should be an
`IsSmugglingProjection`. The fact that linglib's `voiceAgent` is not
means *Collins/Storment would not call this "Voice"* — they would call
it *v* (which `voiceAgent`'s thematic role and phase status more
closely match in their system).

The disagreement is therefore partly *labeling*: which functional head
gets the name "Voice." But it is also partly *substantive*: whether the
same syntactic position can simultaneously introduce an external
argument *and* serve as a smuggling target. Pylkkänen's framework
requires Voice to do (a); Collins/Storment's framework requires Voice
to do (b); and the two functions are made structurally incompatible by
the phase/θ-role correlations Storment defends in §4 of his paper. -/

/-- The substantive incompatibility: a Voice head cannot simultaneously
    satisfy both views. (Equivalently: introducing an external argument
    requires being a phase head, which blocks smuggling.) -/
theorem views_jointly_unsatisfiable_for_canonical_voices :
    ¬ (IsExternalArgIntroducer voiceAgent ∧ IsSmugglingProjection voiceAgent) ∧
    ¬ (IsExternalArgIntroducer voicePassive ∧ IsSmugglingProjection voicePassive) ∧
    ¬ (IsExternalArgIntroducer voiceAnticausative ∧ IsSmugglingProjection voiceAnticausative) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### Applicative diagnostics (relocated from Minimalist/ApplicativeDiagnostics.lean)

# Applicative diagnostics
[pylkkanen-2008]

Cluster-based diagnostic classifier for the high/low applicative
distinction ([pylkkanen-2008], Table 2.1). Three diagnostics:

1. Can unergative verbs be applicativized? (Ch. 2 §2.1.2)
2. Can static verbs be applicativized? (Ch. 2 §2.1.2)
3. *If the language has English-style depictive secondary predicates*,
   is the applied argument available for depictive modification?
   (Ch. 2 §2.1.3)

## Cluster-based classification

A high applicative passes *all* tests; a low applicative fails *all*
tests. Test 3 is conditional — when a language lacks English-style
depictives (e.g., Korean) or has too-broad depictives (Venda, Albanian),
the test is *inapplicable* (`.inapplicable`), not "fails." The
classifier ignores inapplicable tests and classifies on the cluster of
applicable ones.

This is stricter than an OR-based classifier (which would misclassify
a language passing one test by accident). Languages that don't pattern
cleanly with either cluster yield `none`, requiring further
investigation rather than a forced classification.
-/

/-- The result of running a single Pylkkänen diagnostic on a language. -/
inductive ApplDiagnosticResult where
  /-- The diagnostic is applicable and the language passes
      (the construction in question is grammatical). -/
  | passes
  /-- The diagnostic is applicable and the language fails
      (the construction is ungrammatical). -/
  | fails
  /-- The diagnostic is *inapplicable* in this language — e.g., Korean
      lacks English-style depictives entirely, so Test 3 cannot be run.
      Distinct from `.fails`: an inapplicable test contributes no
      classification evidence. -/
  | inapplicable
  deriving DecidableEq, Repr

/-- A bundle of Pylkkänen Table 2.1's three diagnostic results for a
    given language. Test 3's `inapplicable` value handles the
    language-conditional cases (Korean lacks depictives; Venda and
    Albanian have too-broad depictives to test). -/
structure ApplDiagnosticBundle where
  /-- Test 1: can unergative verbs be applicativized? -/
  unergative : ApplDiagnosticResult
  /-- Test 2: can static verbs be applicativized? -/
  staticVerb : ApplDiagnosticResult
  /-- Test 3: depictive modification of applied argument
      (conditional on language having English-style depictives). -/
  depictive : ApplDiagnosticResult
  deriving Repr

/-- The list of diagnostic results in a bundle, for cluster checks. -/
def ApplDiagnosticBundle.results (b : ApplDiagnosticBundle) : List ApplDiagnosticResult :=
  [b.unergative, b.staticVerb, b.depictive]

/-- The applicable (non-`.inapplicable`) results in a bundle. -/
def ApplDiagnosticBundle.applicableResults (b : ApplDiagnosticBundle) :
    List ApplDiagnosticResult :=
  b.results.filter (· ≠ .inapplicable)

/-- Cluster-based classification ([pylkkanen-2008], Table 2.1):
    a language has *high* applicatives iff every applicable diagnostic
    passes; *low* iff every applicable diagnostic fails; otherwise the
    pattern is mixed and the classifier returns `none`, requiring
    further investigation rather than forcing a classification.

    Note: this returns `Option ApplType` collapsed to `.high` or
    `.lowRecipient` — distinguishing recipient from source low
    applicatives requires *additional* diagnostics (transfer
    directionality, §2.2 + §2.3) not in Table 2.1. -/
def classifyByDiagnostics (b : ApplDiagnosticBundle) : Option ApplType :=
  let applicable := b.applicableResults
  if applicable.isEmpty then none
  else if applicable.all (· = .passes) then some .high
  else if applicable.all (· = .fails) then some .lowRecipient
  else none

/-! #### Soundness theorems

The classifier returns `.high` only on all-pass bundles, `.lowRecipient`
only on all-fail bundles. Mixed bundles and empty/all-inapplicable
bundles yield `none`. Soundness is checked structurally on the four
canonical bundle shapes below. -/

/-- A bundle with all three results `.passes` classifies as high. -/
theorem all_pass_classifies_high :
    classifyByDiagnostics
      { unergative := .passes, staticVerb := .passes, depictive := .passes } =
        some .high := by decide

/-- A bundle with all three results `.fails` classifies as low. -/
theorem all_fail_classifies_low :
    classifyByDiagnostics
      { unergative := .fails, staticVerb := .fails, depictive := .fails } =
        some .lowRecipient := by decide

/-- A bundle with mixed results does not classify. -/
theorem mixed_does_not_classify :
    classifyByDiagnostics
      { unergative := .passes, staticVerb := .fails, depictive := .fails } = none := by decide

/-- An all-inapplicable bundle does not classify. -/
theorem all_inapplicable_does_not_classify :
    classifyByDiagnostics
      { unergative := .inapplicable, staticVerb := .inapplicable, depictive := .inapplicable } =
        none := by decide

/-- Inapplicable tests are excluded from the cluster: a bundle with
    one `.inapplicable` and two `.passes` still classifies as high. -/
theorem inapplicable_excluded :
    classifyByDiagnostics
      { unergative := .passes, staticVerb := .passes, depictive := .inapplicable } =
        some .high := by decide

/-- Inapplicable + all-fails still classifies as low. -/
theorem inapplicable_with_fails_classifies_low :
    classifyByDiagnostics
      { unergative := .fails, staticVerb := .fails, depictive := .inapplicable } =
        some .lowRecipient := by decide

-- ============================================================================
-- § 1: Lexical Items
-- ============================================================================

def voice_ag_t  := SO.mkLeafPhon .Voice [.V]    "Voice[AG]"  400
def appl_low_t  := SO.mkLeafPhon .Appl  [.D]    "Appl[LOW]"  402
def appl_high_t := SO.mkLeafPhon .Appl  [.V]    "Appl[HI]"   403
def V_sent_t    := SO.mkLeafPhon .V     [.Appl] "sent"        404
def V_eat_t     := SO.mkLeafPhon .V     [.D]    "eat"         405
def DP_john_t   := SO.mkLeafPhon .D     []      "John"        406
def DP_mary_t   := SO.mkLeafPhon .D     []      "Mary"        407
def DP_letter_t := SO.mkLeafPhon .D     []      "a letter"    408
def DP_wife_t   := SO.mkLeafPhon .D     []      "wife"        409
def DP_food_t   := SO.mkLeafPhon .D     []      "food"        410

/-! Planar leaf tokens, used to build the concrete trees the c-command
    theorems reason over (Merge `SO.node` is noncomputable; trees are
    built planar-first via `SO.ofPlanar`). -/

private def t_voice_ag  : LIToken := ⟨.simple .Voice [.V] (phonForm := "Voice[AG]"), 400⟩
private def t_appl_low  : LIToken := ⟨.simple .Appl [.D] (phonForm := "Appl[LOW]"), 402⟩
private def t_appl_high : LIToken := ⟨.simple .Appl [.V] (phonForm := "Appl[HI]"), 403⟩
private def t_V_sent    : LIToken := ⟨.simple .V [.Appl] (phonForm := "sent"), 404⟩
private def t_V_eat     : LIToken := ⟨.simple .V [.D] (phonForm := "eat"), 405⟩
private def t_DP_john   : LIToken := ⟨.simple .D [] (phonForm := "John"), 406⟩
private def t_DP_mary   : LIToken := ⟨.simple .D [] (phonForm := "Mary"), 407⟩
private def t_DP_letter : LIToken := ⟨.simple .D [] (phonForm := "a letter"), 408⟩
private def t_DP_wife   : LIToken := ⟨.simple .D [] (phonForm := "wife"), 409⟩
private def t_DP_food   : LIToken := ⟨.simple .D [] (phonForm := "food"), 410⟩

-- ============================================================================
-- § 2: Tree Derivations
-- ============================================================================

/-- Ditransitive with low applicative: "John sent Mary a letter"

    `[VoiceP John [Voice' Voice_AG [VP sent [ApplP Mary [Appl' Appl_LOW [DP a letter]]]]]]`

    Low Appl merges below V: V takes ApplP as complement. The goal
    (Mary) is in Spec-ApplP, c-commanding the theme (a letter) in
    complement of Appl. This derives the [barss-lasnik-1986]
    asymmetry that IO asymmetrically c-commands DO. Built planar-first
    so the c-command theorems `decide`. -/
def ditransitiveTree : SyntacticObject :=
  SO.ofPlanar
    (SO.nodeP (SO.leafP t_DP_john)
      (SO.nodeP (SO.leafP t_voice_ag)
        (SO.nodeP (SO.leafP t_V_sent)
          (SO.nodeP (SO.leafP t_DP_mary)
            (SO.nodeP (SO.leafP t_appl_low) (SO.leafP t_DP_letter))))))

/-- High applicative benefactive (Chaga pattern): "he ate food for wife"

    `[VoiceP John [Voice' Voice_AG [ApplP wife [Appl' Appl_HIGH [VP eat [DP food]]]]]]`

    High Appl merges above VP: Appl takes VP as complement. The
    benefactive (wife) is in Spec-ApplP, relating to the event (not the
    theme). High Appl is attested in Bantu languages (Chaga, Luganda,
    Venda) and Albanian, but NOT in English. -/
def benefactiveTree : SyntacticObject :=
  SO.ofPlanar
    (SO.nodeP (SO.leafP t_DP_john)
      (SO.nodeP (SO.leafP t_voice_ag)
        (SO.nodeP (SO.leafP t_DP_wife)
          (SO.nodeP (SO.leafP t_appl_high)
            (SO.nodeP (SO.leafP t_V_eat) (SO.leafP t_DP_food))))))

-- ============================================================================
-- § 3: C-command Predictions
-- ============================================================================

-- Ditransitive (low Appl): agent > goal > theme

/-- Agent c-commands goal. -/
theorem ditransitive_agent_ccommands_goal :
    SO.cCommandsIn ditransitiveTree DP_john_t DP_mary_t := by decide

/-- Agent c-commands theme. -/
theorem ditransitive_agent_ccommands_theme :
    SO.cCommandsIn ditransitiveTree DP_john_t DP_letter_t := by decide

/-- Goal c-commands theme — the [barss-lasnik-1986] asymmetry
    derived structurally from V selecting ApplP. -/
theorem ditransitive_goal_ccommands_theme :
    SO.cCommandsIn ditransitiveTree DP_mary_t DP_letter_t := by decide

/-- Theme does NOT c-command goal: the asymmetry is structural. -/
theorem ditransitive_theme_not_ccommands_goal :
    ¬ SO.cCommandsIn ditransitiveTree DP_letter_t DP_mary_t := by decide

-- Benefactive (high Appl): benefactive > theme

/-- Benefactive c-commands theme. -/
theorem benefactive_benef_ccommands_theme :
    SO.cCommandsIn benefactiveTree DP_wife_t DP_food_t := by decide

/-- Theme does NOT c-command benefactive. -/
theorem benefactive_theme_not_ccommands_benef :
    ¬ SO.cCommandsIn benefactiveTree DP_food_t DP_wife_t := by decide

-- Appl head containment

/-- Low applicative marks the ditransitive. -/
theorem send_is_low_appl :
    SO.contains ditransitiveTree appl_low_t := by decide

/-- High applicative marks the benefactive. -/
theorem eat_is_high_appl :
    SO.contains benefactiveTree appl_high_t := by decide

-- ============================================================================
-- § 4: ApplType Association
-- ============================================================================

/-! The lexical items `appl_low_t` and `appl_high_t` correspond to
`ApplHead` instances from `Syntax/Minimalism/Applicative.lean`:
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

/-! [pylkkanen-2008] tests the high/low distinction in six languages
using three diagnostics (Table 2.1, p. 33). The diagnostics cluster
into two groups, confirming the typological split. The classifier
`classifyByDiagnostics` derives the high/low classification
from the diagnostic results; we verify that for each language, the
classifier output matches Pylkkänen's annotated classification. -/

/-- A language's diagnostic profile and Pylkkänen's annotated
    classification. The diagnostic results live in
    `ApplDiagnosticBundle`; `classification` records
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
    (25b). Albanian postverbal APs pattern like English ones (modifying
    internal and external but not implicit external arguments), except
    that — unlike English depictives — they can also easily modify DPs
    inside PPs. That extra breadth disqualifies them as English-style
    depictives, so Test 3 is *inapplicable* (§2.1.3.2.5). -/
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

/-! [larson-1988]'s VP shell is the precursor of the modern Voice +
Applicative decomposition. While the tree shapes differ (Larson uses
one VP-shell layer; modern theory uses Voice and Appl heads), the
c-command hierarchy among DP arguments is identical: agent > goal/IO > theme/DO. -/

open Larson1988 in

/-- [larson-1988]'s DOC and the modern Voice + low-Appl derivation
    produce the same c-command hierarchy: IO asymmetrically c-commands DO.

    This proves that [larson-1988] and [pylkkanen-2008],
    despite different decompositions, converge on the same structural
    prediction for [barss-lasnik-1986] asymmetries. (Larson's side is
    stated over `docDativeShiftTree`, the planar-built result tree of his
    Dative-Shift derivation; `docDativeShift.final` is noncomputable on
    the `SO` carrier.) -/
theorem larson_modern_same_hierarchy :
    -- Larson's DOC: IO > DO
    SO.cCommandsIn docDativeShiftTree DP_mary DP_letter ∧
    ¬ SO.cCommandsIn docDativeShiftTree DP_letter DP_mary ∧
    -- Modern Voice/Appl: goal > theme (same asymmetry)
    SO.cCommandsIn ditransitiveTree DP_mary_t DP_letter_t ∧
    ¬ SO.cCommandsIn ditransitiveTree DP_letter_t DP_mary_t := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §7. Voice as the head that introduces the external argument
    ([pylkkanen-2008] Ch. 3 §3.2 + Ch. 4 §4.2)

[pylkkanen-2008]'s central claim about Voice (Ch. 4 §4.2,
"Eliminating Linking"): the external argument is *not* projected by
the verb itself but by a separate Voice head, following
[kratzer-1996]. Voice combines with VP via Event Identification
(Event Identification, Ch. 1; -- UNVERIFIED: eq. number), introducing the external argument and relating it to
the event described by the verb.

This is one of the two competing views of Voice surveyed in
the "Voice projection" section above. The other view,
defended by [collins-2005] and [storment-2026], treats Voice
as a *structural* head (the smuggling projection) and assigns
external-argument introduction to *v* instead. The two views are
orthogonal — see the "Voice projection" section for the substantive
contrast. -/

/-- Pylkkänen's view applied to the canonical agentive Voice: it
    satisfies `IsExternalArgIntroducer` (it does the job Pylkkänen
    attributes to Voice). -/
theorem voice_introduces_external_arg_pylkkanen :
    IsExternalArgIntroducer Minimalist.voiceAgent := by decide

/-! ## §8. Voice-bundling for the English zero-causative
    ([pylkkanen-2008] Ch. 3 §3.3; -- UNVERIFIED: eq. number)

A second contribution of Ch. 3: the difference between English (which
lacks unaccusative causatives) and Japanese/Finnish (which have them)
reduces to whether the language *bundles* Cause and Voice into a
single morphological head. English bundles ([Cause, Voice]); Japanese
and Finnish do not.

The `VoiceBundlingChoice` enum + `CauseSelection` axis + the full 2 × 3
typology cells (Pylkkänen Table 3.1) are defined in §13 below, since
this is the only Pylkkänen-derived consumer in the codebase. The two
canonical-instance affirmations (`english_zero_is_bundled`,
`japanese_lexical_is_independent`) live alongside the cell definitions
in §13. -/

/-! ## §9. Cause is not a θ-role ([pylkkanen-2008] Ch. 3 §3.2)

Pylkkänen's other major Ch. 3 argument: the causative head Cause
introduces a *causing event*, not a θ-role on the external argument.
Evidence: Japanese adversity causatives (§3.2.2) have causative
morphology and meaning but no external argument. The bieventive
analysis (Cause = relation between two events) is required by such
data; the θ-role analysis (Cause = relation between a causer and a
caused event) cannot accommodate them.

The bieventive vs. θ-role contrast is formalized in
`Semantics/ArgumentStructure/ArgumentIntroduction.lean`:
`causeBieventive_no_external_arg` shows a causing event with no causer
participant (the Japanese adversity causative), while
`causeThetaRole_forces_causer` shows the θ-role denotation entails a causer
— so only the bieventive analysis accommodates the data, derived from the
denotations. -/

open Semantics.ArgumentStructure in
/-- [pylkkanen-2008] §3.2: the Japanese adversity causative — a causing
    event with no external argument — is admitted by the bieventive Cause
    denotation, which the θ-role analysis (forcing a causer) cannot model. -/
theorem cause_bieventive_admits_adversity_causative
    {Time : Type*} [LinearOrder Time]
    (cause : Event Time → Event Time → Prop) (caused : Event Time → Prop)
    (e e' : Event Time) (hc : caused e') (hcause : cause e e') :
    causeBieventive cause caused e :=
  causeBieventive_no_external_arg cause caused e e' hc hcause

/-! ## §10. Hebrew possessor datives as low source applicatives
    ([pylkkanen-2008] Ch. 2 §2.2, Table 2.2 p. 60)

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
    ([pylkkanen-2008] §2.2). -/
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
    (Kubo's 1992 work (cited by [pylkkanen-2008]; not yet in linglib bib) diagnostics, reanalyzed in
    [pylkkanen-2008] Ch. 2 §2.3)

Japanese adversity passives split into *gapped* (low source applicative)
and *gapless* (high applicative). The gapped/gapless distinction itself
is Kubo's 1992 work (cited by [pylkkanen-2008]; not yet in linglib bib)'s; [pylkkanen-2008]'s contribution is the
reanalysis as a low-source vs. high applicative typology. Both share
the *-rare-* passive morphology; the distinguishing criterion is the
possessive/transfer relation to the direct object — the gapped (low
source) type requires it, the gapless (high malefactive) type bears a
malefactive relation to the event and no necessary relation to the
object. The diagnostic bundle
distinguishing the two types is not formalized here; this section
records the type-level split for cross-reference. -/

/-- The two types of Japanese adversity passive ([pylkkanen-2008]
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

/-! ## §12. Spanish static low applicatives ([cuervo-2003],
    discussed in [pylkkanen-2008] §2.1.4.2)

[cuervo-2003]'s thesis proposes a *three-way* split of low
applicatives in Spanish: low-to (recipient, dynamic), low-from
(source, dynamic), and low-AT (static possession). The static type is
Cuervo's contribution; Pylkkänen briefly endorses it in §2.1.4.2 as
compatible with her event-vs-state distinction. The static applicative
combines with small clause predicates (e.g. `Pablo le admira la
paciencia a Valeria` "Pablo admires Valeria's patience"), unlike
English low recipients which require event-creating verbs. -/

/-- Cuervo's three-way split of low applicatives. The third type
    (`staticPossession`) is [cuervo-2003]'s extension; it is
    *not* in the canonical `ApplType` taxonomy because it requires
    static rather than dynamic semantics, and (per Cuervo) it
    specifically takes a small-clause complement. -/
inductive CuervoLowAppl where
  | recipient    -- transfer TO (Pylkkänen)
  | source       -- transfer FROM (Pylkkänen)
  | staticPossession  -- static IN-THE-POSSESSION ([cuervo-2003], Spanish)
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

/-! ## §13. Causative typology (Pylkkänen Table 3.1, Ch. 3 intro p. 87)

Pylkkänen Table 3.1 (Chapter 3 introduction, p. 87 — *not* §3.4, which
argues the three-way *selection* split and carries the separate Table 3.2)
is a 2 × 3 typology of causative constructions
parameterized by Voice-bundling × selection. The inventory
(`VoiceBundlingChoice`, `CauseSelection`, `MorphologyAccess`,
`CausativeCell` + 6 canonical instances + 4 prediction theorems) lives
here; Pylkkanen2008 is the sole writer in the codebase, so substrate
promotion is unwarranted (per CLAUDE.md "promote when ≥2 consumers").

Orthogonal to [song-1996]'s expression-style typology in
`Studies/Song1996.lean`: Song classifies the
morphosyntactic *packaging* of a causative (compact / and / purp);
Pylkkänen classifies the underlying syntactic *configuration*
(Voice-bundled vs independent; selecting root, verb, or phase). A
language is characterized along both axes (English is COMPACT in Song,
bundled-root in Pylkkänen).

If Wood 2015 / Cuervo 2003 / Folli-Harley 2005 get formalized later as
generative-side updates of this typology and re-use these cells, they
should consume them from here. The earlier extracted-to-Causation/Typology
plan was overengineering for n=1 writer; the file relocates here when
the natural single home turns out to be the only home. -/

/-- [pylkkanen-2008] §3.3: whether Cause and Voice are bundled
    into one morphological head. English bundles ([Cause, Voice]);
    Japanese and Finnish do not. -/
inductive VoiceBundlingChoice where
  | bundled       -- English-type
  | independent   -- Japanese/Finnish-type
  deriving DecidableEq, Repr

/-- [pylkkanen-2008] §3.4: what does Cause select for? -/
inductive CauseSelection where
  /-- Cause + √Root: causes a category-free root (English zero-causative). -/
  | root
  /-- Cause + v + √Root: causes a category-defined verb (Bemba *-eshya*,
      Finnish *-tta*). -/
  | verb
  /-- Cause + (something at least as big as a phase, can include
      external args): causativizes unergatives and transitives
      (Luganda *-sa*, Venda *-is*). -/
  | phase
  deriving DecidableEq, Repr

/-- Three levels of root-Cause morpheme intervention. The three-way
    distinction is essential — collapsing to Bool would lose §3.4's
    central typological claim. -/
inductive MorphologyAccess where
  | none                  -- root-selecting Cause
  | categoryDefiningOnly  -- verb-selecting Cause
  | allMorphology         -- phase-selecting Cause
  deriving DecidableEq, Repr

/-- A causative-typology cell: Voice-bundling × selection.
    `bundling` is `Option` because Pylkkänen Table 3.1 footnote *a*
    explicitly states the Voice-bundling properties of Bemba,
    Luganda, and Venda causatives are not known. -/
structure CausativeCell where
  bundling : Option VoiceBundlingChoice
  selection : CauseSelection
  deriving DecidableEq, Repr

/-- Table 3.1 prediction (1): can a language have unaccusative
    causatives? Bundled → no (Voice forces ext arg); independent →
    yes; unknown → no clean prediction. (Reuses the `PredictsVerdict`
    enum defined in §10 above for `PossessorDativeAnalysis.predicts`.) -/
def CausativeCell.permitsUnaccusativeCausative (c : CausativeCell) : PredictsVerdict :=
  match c.bundling with
  | none => .noCleanPrediction
  | some .bundled => .antipredicts
  | some .independent => .predicts

/-- Table 3.1 prediction (2): can the language causativize unergatives
    and transitives? Verb- and phase-selecting Cause can; only
    root-selecting Cause cannot. (Table 3.1's prediction (2) is identical
    across both Voice-bundling columns, so it turns on selection alone.) -/
def CausativeCell.permitsUnergativeAndTransitiveCausativization
    (c : CausativeCell) : Bool :=
  match c.selection with
  | .verb | .phase => true
  | .root => false

/-- Table 3.1 prediction (3): what morphology can intervene between
    root and Cause? -/
def CausativeCell.morphologyAccess (c : CausativeCell) : MorphologyAccess :=
  match c.selection with
  | .root => .none
  | .verb => .categoryDefiningOnly
  | .phase => .allMorphology

-- Six canonical instances (Pylkkänen Table 3.1)

/-- English zero-causative: Voice-bundling root-selecting. -/
def englishZeroCausative : CausativeCell :=
  { bundling := some .bundled, selection := .root }

/-- Japanese lexical causative: non-Voice-bundling root-selecting. -/
def japaneseLexicalCausative : CausativeCell :=
  { bundling := some .independent, selection := .root }

/-- Bemba *-eshya* causative: verb-selecting; bundling unknown
    (Table 3.1 footnote a). -/
def bembaEshyaCausative : CausativeCell :=
  { bundling := none, selection := .verb }

/-- Finnish *-tta* causative: non-Voice-bundling verb-selecting. -/
def finnishTtaCausative : CausativeCell :=
  { bundling := some .independent, selection := .verb }

/-- Luganda *-sa* causative: phase-selecting; bundling unknown. -/
def lugandaSaCausative : CausativeCell :=
  { bundling := none, selection := .phase }

/-- Venda *-is* causative: phase-selecting; bundling unknown. -/
def vendaIsCausative : CausativeCell :=
  { bundling := none, selection := .phase }

/-- §11 Voice-bundling cross-references. English bundles, Japanese does
    not — the two canonical affirmations §11 promised live here alongside
    the Cell definitions they consume. -/
theorem english_zero_is_bundled :
    englishZeroCausative.bundling = some VoiceBundlingChoice.bundled := rfl

theorem japanese_lexical_is_independent :
    japaneseLexicalCausative.bundling = some VoiceBundlingChoice.independent := rfl

theorem english_zero_predictions :
    englishZeroCausative.permitsUnaccusativeCausative = .antipredicts ∧
    englishZeroCausative.permitsUnergativeAndTransitiveCausativization = false ∧
    englishZeroCausative.morphologyAccess = .none :=
  ⟨rfl, rfl, rfl⟩

theorem japanese_lexical_predictions :
    japaneseLexicalCausative.permitsUnaccusativeCausative = .predicts ∧
    japaneseLexicalCausative.permitsUnergativeAndTransitiveCausativization = false ∧
    japaneseLexicalCausative.morphologyAccess = .none :=
  ⟨rfl, rfl, rfl⟩

theorem finnish_tta_predictions :
    finnishTtaCausative.permitsUnaccusativeCausative = .predicts ∧
    finnishTtaCausative.permitsUnergativeAndTransitiveCausativization = true ∧
    finnishTtaCausative.morphologyAccess = .categoryDefiningOnly :=
  ⟨rfl, rfl, rfl⟩

theorem luganda_phase_predictions :
    lugandaSaCausative.permitsUnaccusativeCausative = .noCleanPrediction ∧
    lugandaSaCausative.permitsUnergativeAndTransitiveCausativization = true ∧
    lugandaSaCausative.morphologyAccess = .allMorphology :=
  ⟨rfl, rfl, rfl⟩

/-! ## §14. Broader Voice taxonomy under Pylkkänen's view

Pylkkänen's Voice = external-argument introducer. Per the "Voice
projection" section above, this is one of two
competing views of Voice (the other being Collins/Storment's smuggling
projection). Test Pylkkänen's view against the broader `VoiceHead`
taxonomy in `Syntax/Minimalism/Voice.lean`: which Voice flavors
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
    IsExternalArgIntroducer Minimalist.voiceAgent ∧
    IsExternalArgIntroducer Minimalist.voiceCauser ∧
    IsExternalArgIntroducer Minimalist.voiceReflexive ∧
    IsExternalArgIntroducer Minimalist.voiceExperiencer ∧
    ¬ IsExternalArgIntroducer Minimalist.voiceMiddle ∧
    ¬ IsExternalArgIntroducer Minimalist.voiceImpersonal ∧
    ¬ IsExternalArgIntroducer Minimalist.voiceAnticausative ∧
    ¬ IsExternalArgIntroducer Minimalist.voicePassive := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §15. Transitivity restriction grounded in EntailmentProfile
    ([pylkkanen-2008] Diagnostic 1 = eq. 17, p. 18; semantic
    argument at eq. 103, p. 55)

Pylkkänen's *predicted* generalization (book Ch. 2 §2.1.1, Diagnostic 1,
eq. 17, p. 18):
"Only high applicative heads should be able to combine with
unergatives. Since low applicative heads denote a relation between
the direct object and the indirect object, a low applicative head
cannot appear in a structure that lacks a direct object."

The semantic argument (eq. 103, p. 55): combining low Appl
(`λx.λy.λf.λe. f(e,x) ∧ theme(e,x) ∧ HAVE(x,y)`) with an unergative
VP (`λe. agent(e, Mary) ∧ run(e)`) yields `agent(e, x) ∧ theme(e, x)`
when both arguments bind the same variable — a thematic-uniqueness
contradiction.

**Status of this formalization**: The composition predicate below uses
`Semantics.ArgumentStructure.EntailmentProfile.pPatientScore` to check whether a verb
has theme-like Proto-Patient entailments. An unergative has either no
object profile (`objectEntailments = none`) or an empty one
(`pPatientScore = 0`). This `EntailmentProfile`-based predicate is the
structural surface; the event-semantic *derivation* of the eq. 103 type
clash is now wired in via `Semantics/ArgumentStructure/ArgumentIntroduction.lean`
and consumed in §15c below (`low_appl_blocks_unergative_denotational`,
`low_external_arg_clash`). -/

open Semantics.ArgumentStructure.EntailmentProfile (EntailmentProfile)

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
    in `Semantics/Composition/` for applicatives. The theorem
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

/-! ## §15c. Event-semantic grounding: the transitivity restriction derived

The `applicativeComposition` predicate above captures the empirical content
structurally (via `ApplType.RequiresThemeInComplement`). The denotational
*derivation* of [pylkkanen-2008]'s eq. 103 — the type clash that forces
the transitivity restriction — lives in
`Semantics/ArgumentStructure/ArgumentIntroduction.lean`. There the high/low
contrast is `IntroMode.toEvent`/`.toTheme`, the two diagnostics are
`toTheme_blocks_unergative` (Diagnostic 1, no internal argument) and
`toTheme_blocks_kimian` (Diagnostic 2, no event argument — Kimian states,
[moltmann-2025]), and the thematic-uniqueness contradiction is
`low_external_arg_clash`. We record the correspondence: Pylkkänen's `ApplType`
projects to an `IntroMode`, and the empirical diagnostics are *instances* of
the substrate theorems rather than restatements of the `IsLow` predicate. -/

open Semantics.ArgumentStructure

/-- Pylkkänen's high/low `ApplType` as a denotational introduction mode
    ([wood-marantz-2017]'s contextually-interpreted introducer). -/
def applIntroMode : ApplType → IntroMode
  | .high         => .toEvent
  | .lowRecipient => .toTheme
  | .lowSource    => .toTheme

/-- The transitivity restriction, derived from the denotations: a low
    applicative (recipient or source) cannot license an unergative verb,
    because the low denotation has no event-internal theme to relate to.
    This is `low_applicative_blocks_unergative` re-grounded in the
    `ArgumentIntroduction` substrate rather than the `IsLow` alias. -/
theorem low_appl_blocks_unergative_denotational
    {Entity Time : Type*} [LinearOrder Time] (a : ApplType) (hLow : a.IsLow)
    (body : Event Time → Prop) :
    ¬ (applIntroMode a).Licenses (VerbDenot.unergative (Entity := Entity) body) := by
  have h : applIntroMode a = .toTheme := by
    cases a <;> first | rfl | exact absurd hLow (by decide)
  rw [h]; exact toTheme_blocks_unergative body

/-- High applicatives license unergatives, derived denotationally
    (Luganda/Venda/Albanian, PDF eq. 23a/24a/25a). -/
theorem high_appl_licenses_unergative_denotational
    {Entity Time : Type*} [LinearOrder Time]
    (body : Event Time → Prop) :
    (applIntroMode .high).Licenses (VerbDenot.unergative (Entity := Entity) body) :=
  toEvent_licenses_all _

/-! ## §16. Voice × Appl licensing matrix
    (`Syntax/Minimalism/Applicative.lean.Licensed`)

`ApplHead.Licensed` (in `Applicative.lean`) checks whether a
particular Appl head is licensed with a given Voice head: high
applicatives require event-introducing Voice (`hasSemantics = true`);
low applicatives are licensed with any Voice. Cross [pylkkanen-2008]'s
high/low Appl typology with the `VoiceHead` taxonomy: which Voice
flavors license high Appl, and which don't?

This connects §14's Pylkkänen-Voice partition with the [pylkkanen-2008]
Appl typology in a single matrix. -/

/-- High Appl requires Voice with event semantics. The named Voice
    flavors split: `voiceAgent`/`voiceCauser`/`voiceMiddle`/
    `voiceImpersonal`/`voiceReflexive`/`voiceExperiencer` carry event
    semantics and license high Appl; `voiceAnticausative`/`voicePassive`
    do not (they're event-semantically inert in this Voice taxonomy)
    and so don't license high Appl. -/
theorem voice_appl_licensing_matrix :
    -- High Appl licensed with event-bearing Voice flavors:
    Minimalist.applHigh.Licensed Minimalist.voiceAgent ∧
    Minimalist.applHigh.Licensed Minimalist.voiceCauser ∧
    -- Low Appl is always licensed (independent of Voice semantics):
    Minimalist.applLowRecipient.Licensed Minimalist.voiceAgent ∧
    Minimalist.applLowRecipient.Licensed Minimalist.voicePassive ∧
    Minimalist.applLowSource.Licensed Minimalist.voiceAnticausative := by decide

/-! ## §17. WALS-vs-Pylkkänen divergence on English/Japanese applicatives

The WALS Ch 109 typology classifies English and Japanese as having
"no applicative" (no overt valence-increasing morphology). Pylkkänen's
analysis classifies the English double-object construction (DOC) and
the Japanese -ni recipient construction as **low recipient applicatives**
(structural Appl head merged below V relating recipient to theme).

The divergence is not empirical — both accounts agree on the same
constructions. It is a methodological choice about what counts as an
"applicative." WALS counts overt verbal applicative morphology;
Pylkkänen counts the structural ApplP projection regardless of
morphological exponent. The substrate is designed to make this kind
of cross-framework editorial disagreement visible. -/

/-- WALS Ch 109 codes English as `.noApplicative` (no overt valence-increasing
    morphology), while Pylkkänen's analysis (`english_appl.classification`)
    classifies the English double-object construction as `.lowRecipient`.
    The disagreement is about the criterion for "applicative," not the data. -/
theorem wals_pylkkanen_diverge_on_english :
    (Data.WALS.F109A.lookupISO "eng").map (·.value) = some .noApplicative ∧
    english_appl.classification = .lowRecipient := by
  refine ⟨?_, rfl⟩
  decide

theorem wals_pylkkanen_diverge_on_japanese :
    (Data.WALS.F109A.lookupISO "jpn").map (·.value) = some .noApplicative ∧
    japanese_appl.classification = .lowRecipient := by
  refine ⟨?_, rfl⟩
  decide

end Pylkkanen2008
