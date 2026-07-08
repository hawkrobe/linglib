import Linglib.Morphology.DM.Categorizer
import Linglib.Syntax.Minimalist.Verbal.Applicative
import Linglib.Syntax.Minimalist.Agree.Checking
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Minimalist.Verbal.Decomposition
import Linglib.Studies.Baker1985
import Linglib.Studies.Kratzer1996
import Linglib.Studies.Wood2015

/-!
# Verbal Templates Can Influence L-Selection in Semitic

Formalization of [hewett-2026] (*Linguistic Inquiry* 57(1), 197–215): l-selection —
which preposition heads a verb's PP complement — varies by verbal template (binyan)
in Tunisian Arabic, Syrian Arabic, and Hebrew. Neither the consonantal root nor the
categorizing head varies across templates, so the data are problematic for
root-based selection ([harley-2014]) and categorizer-based selection
([merchant-2019]) alike. Hewett's solution is joint selection via Activate
(ex. (23), adapted from [merchant-2015]): a root's selectional feature is indexed
by an ordered tuple of category features — for Semitic `(V, Template)` — and each
c-commanding head strips one index; the feature determines the l-selected P only
once fully activated.

## Main declarations

* `SemiticTemplate`, `lSelect`: the binyan inventory and l-selection as a joint
  function of root and template.
* `lSelData`, `lSelect_consistent`: the paper's attested data (exx. (11)–(18)) and
  the proof that `lSelect` matches every datum.
* `templateInvariant`: the invariance prediction shared by root-only and
  categorizer-only accounts; refuted by `krh_not_templateInvariant`,
  `dwr_not_templateInvariant`, `Hkm_not_templateInvariant`.
* `SelectionalFeature`: an l-selectional feature indexed by an `ActivationIndex`,
  with the paper's worked derivations (exx. (24)–(25)).

## Implementation notes

The Voice typing (`SemiticTemplate.toVoiceHead`), the bridges to [kratzer-1996],
[wood-2015], and [pylkkanen-2008], and the verbal-decomposition rendering of
mono-eventivity (fn. 11, [nie-2020]) are this formalization's connections to the
linglib Voice substrate, not claims of [hewett-2026], which deliberately leaves the
template-head inventory open (fn. 8; p. 201: templates realize "a head or series
of heads capable of inducing changes in adicity, presumably v/Voice"). Likewise
the Mirror-Principle observation (`templates_outside_mirror_scope`): [baker-1985]
scopes the Mirror Principle to concatenative morphology, so templatic l-selection
sits outside it — a linglib cross-reference Hewett does not draw.
-/

namespace Hewett2026

open Minimalist (Voice.Flavor Voice.Head VerbHead Cat FeatureStatus
  ActivationIndex ApplHead applHigh applLowRecipient Voice.buildDecomposition
  Voice.agentive Voice.causer Voice.passive Voice.anticausative isCausative
  low_licensed_with_any high_licensed_of_assignsTheta)
open Morphology.DM (CategorizedRoot Categorizer)
open Morphology.MirrorPrinciple (MorphDomain)
open Wood2015 (Construction)

/-! ### Semitic verbal templates (binyanim) -/

/-- Semitic verbal templates (binyanim) attested in the paper's l-selection data.
    Realized as nonconcatenative vocalic patterns on consonantal roots (for the
    phonological CV-skeleton view see the template infrastructure in
    `Studies/Faust2026.lean`);
    syntactically they realize functional heads above the root. -/
inductive SemiticTemplate where
  | XaYaZ     -- Form I: basic active (Arabic faʕal)
  | XaYYaZ    -- Form II: intensive/causative (Arabic faʕʕal)
  | nXaYaZ    -- Form VII: medio-passive (Arabic infaʕal)
  | tXaYYaZ   -- Form V: reflexive/medio-passive (Arabic tafaʕʕal)
  | hiXYiZ    -- Hifil: causative (Hebrew)
  | huXYaZ    -- Hufal: passive of Hifil (Hebrew)
  | XiYeZ     -- Piel: intensive/causative (Hebrew)
  | XuYaZ     -- Pual: passive of Piel (Hebrew)
  deriving DecidableEq, Repr

/-- Map each template to a canonical Voice head. Formalizer's bridge into the
    linglib Voice substrate: [hewett-2026] assumes only that templates realize a
    head or series of heads capable of inducing changes in adicity, presumably
    v/Voice (p. 201), and deliberately leaves the inventory open (fn. 8); the
    mapping below follows the templates' traditional active, causative, and
    medio-passive glosses. -/
def SemiticTemplate.toVoiceHead : SemiticTemplate → Voice.Head
  | .XaYaZ => Voice.agentive
  | .XaYYaZ | .hiXYiZ | .XiYeZ => Voice.causer
  | .nXaYaZ | .huXYaZ | .XuYaZ => Voice.passive
  | .tXaYYaZ => Voice.anticausative

/-- The Voice flavor a template realizes, derived from `toVoiceHead`. -/
def SemiticTemplate.toVoiceFlavor (t : SemiticTemplate) : Voice.Flavor :=
  t.toVoiceHead.flavor

/-- Templates are nonconcatenative, hence outside the Mirror Principle's scope as
    formalized by [baker-1985]'s `MorphDomain.InScope` — a linglib cross-reference;
    [hewett-2026] does not discuss the Mirror Principle. -/
theorem templates_outside_mirror_scope :
    ¬ MorphDomain.InScope .nonconcatenative := by decide

/-! ### Roots and prepositions -/

/-- Consonantal roots with attested l-selection data, transliterated to ASCII-safe
    identifiers. -/
inductive RootLabel where
  | xwf    -- xwf 'fear/frighten' (Tunisian Arabic, ex. (11))
  | krh    -- krh 'hate/make hate' (Tunisian Arabic, ex. (13a))
  | dwr    -- dwr 'encircle/make encircle' (Tunisian Arabic, ex. (13b))
  | Hkm    -- ħkm 'sentence/referee' (Syrian Arabic, ex. (14))
  | tpl    -- tpl 'treat' (Hebrew, ex. (17))
  | shps   -- ʃpʕ 'influence' (Hebrew, ex. (18))
  deriving DecidableEq, Repr

/-- Prepositions attested in the paper's l-selection data. -/
inductive SemiticPrep where
  | fi      -- 'in' (Tunisian Arabic)
  | bi      -- 'with/in' (Tunisian Arabic)
  | Eala    -- 'on/over' (Tunisian Arabic: ʕla, clitic form ʕli:)
  | min     -- 'from' (Tunisian Arabic)
  | Ealej   -- 'on' (Syrian Arabic: ʕalej)
  | be      -- 'in' (Hebrew)
  | al      -- 'on' (Hebrew)
  deriving DecidableEq, Repr

/-- Languages providing l-selection data in the paper. -/
inductive SemiticLang where
  | tunisianArabic
  | syrianArabic
  | hebrew
  deriving DecidableEq, Repr

/-! ### L-selection data -/

/-- An l-selection datum: a root in a template selects a preposition, or none
    (bare transitive use or passive P-suppression). -/
structure LSelDatum where
  root : RootLabel
  template : SemiticTemplate
  prep : Option SemiticPrep
  lang : SemiticLang
  deriving Repr

/-- Template-independent l-selection (ex. (11)): xwf 'fear' selects *min* 'from' in
    both XaYaZ (xa:f min l-ʔasad 'He was afraid of the lion') and XaYYaZ
    (xawwəf-u min l-ʔasad 'He made him afraid of the lion'). -/
def xwf_XaYaZ : LSelDatum :=
  { root := .xwf, template := .XaYaZ, prep := some .min, lang := .tunisianArabic }

/-- See `xwf_XaYaZ`. -/
def xwf_XaYYaZ : LSelDatum :=
  { root := .xwf, template := .XaYYaZ, prep := some .min, lang := .tunisianArabic }

/-- Template-dependent l-selection (ex. (13a)): krh 'hate' is bare transitive in
    XaYaZ (kraht (*fi) Sami 'I hate Sami') but requires *fi* in XaYYaZ
    (karraht-ha *(fi) Sami 'I made her hate Sami'). -/
def krh_XaYaZ : LSelDatum :=
  { root := .krh, template := .XaYaZ, prep := none, lang := .tunisianArabic }

/-- See `krh_XaYaZ`. -/
def krh_XaYYaZ : LSelDatum :=
  { root := .krh, template := .XaYYaZ, prep := some .fi, lang := .tunisianArabic }

/-- Template-dependent l-selection (ex. (13b)): dwr 'encircle' selects *bi:* in
    XaYaZ (l-hnaʃ da:r bi:-k 'The snake encircled you') but *ʕla* in XaYYaZ
    (dawwart l-hnaʃ ʕli:-k 'I made the snake encircle you'). -/
def dwr_XaYaZ : LSelDatum :=
  { root := .dwr, template := .XaYaZ, prep := some .bi, lang := .tunisianArabic }

/-- See `dwr_XaYaZ`. -/
def dwr_XaYYaZ : LSelDatum :=
  { root := .dwr, template := .XaYYaZ, prep := some .Eala, lang := .tunisianArabic }

/-- Direction-reversing case (ex. (14), Syrian Arabic): ħkm selects *ʕalej* in
    XaYaZ (hakam ʕalej-o b-s-sidʒn 'He sentenced him to jail') but rejects any PP
    in XaYYaZ (hakkam (l-muba:re:t) 'He refereed (the match)'). -/
def Hkm_XaYaZ : LSelDatum :=
  { root := .Hkm, template := .XaYaZ, prep := some .Ealej, lang := .syrianArabic }

/-- See `Hkm_XaYaZ`. -/
def Hkm_XaYYaZ : LSelDatum :=
  { root := .Hkm, template := .XaYYaZ, prep := none, lang := .syrianArabic }

/-- Hebrew P-suppression (ex. (17)): tpl 'treat' selects *be* in XiYeZ (tipel be-)
    and suppresses it in the passive XuYaZ (tupal). -/
def tpl_XiYeZ : LSelDatum :=
  { root := .tpl, template := .XiYeZ, prep := some .be, lang := .hebrew }

/-- See `tpl_XiYeZ`. -/
def tpl_XuYaZ : LSelDatum :=
  { root := .tpl, template := .XuYaZ, prep := none, lang := .hebrew }

/-- Hebrew P-suppression (ex. (18)): ʃpʕ 'influence' selects *al* in hiXYiZ
    (hišpia al) and suppresses it in the passive huXYaZ (hušpa). -/
def shps_hiXYiZ : LSelDatum :=
  { root := .shps, template := .hiXYiZ, prep := some .al, lang := .hebrew }

/-- See `shps_hiXYiZ`. -/
def shps_huXYaZ : LSelDatum :=
  { root := .shps, template := .huXYaZ, prep := none, lang := .hebrew }

/-- The pooled l-selection data (exx. (11), (13), (14), (17), (18)). -/
def lSelData : List LSelDatum :=
  [xwf_XaYaZ, xwf_XaYYaZ, krh_XaYaZ, krh_XaYYaZ, dwr_XaYaZ, dwr_XaYYaZ,
   Hkm_XaYaZ, Hkm_XaYYaZ, tpl_XiYeZ, tpl_XuYaZ, shps_hiXYiZ, shps_huXYaZ]

/-! ### Joint selection -/

/-- L-selection as a joint function of root and template — the paper's core claim.
    `none` marks bare transitive use or passive P-suppression; unattested
    root–template pairs also map to `none`. xwf is generalized to all templates per
    the paper's claim that its l-selection is stable across templatic realizations
    of the root (p. 202). -/
def lSelect : RootLabel → SemiticTemplate → Option SemiticPrep
  | .xwf,  _        => some .min
  | .krh,  .XaYaZ   => none
  | .krh,  .XaYYaZ  => some .fi
  | .dwr,  .XaYaZ   => some .bi
  | .dwr,  .XaYYaZ  => some .Eala
  | .Hkm,  .XaYaZ   => some .Ealej
  | .Hkm,  .XaYYaZ  => none
  | .tpl,  .XiYeZ   => some .be
  | .tpl,  .XuYaZ   => none
  | .shps, .hiXYiZ  => some .al
  | .shps, .huXYaZ  => none
  | _, _ => none

/-- `lSelect` agrees with every attested datum. -/
theorem lSelect_consistent :
    ∀ d ∈ lSelData, lSelect d.root d.template = d.prep := by decide

/-! ### Template-(in)dependence

`templateInvariant` is the prediction shared by root-only ([harley-2014]) and
categorizer-only ([merchant-2019]) selection: since neither root nor categorizer
varies across templates, l-selection should not either. The attested
counterexamples refute it; xwf shows the invariant case also exists.

Template-dependence cannot be reduced to homophonous roots (krh₁ in XaYaZ, krh₂ in
XaYYaZ): that would leave their mutually exclusive distribution unexplained,
parallel to the nonoverlapping distribution of suppletive go ~ went (p. 208).
`RootLabel` accordingly carries a single `krh` constructor. -/

/-- L-selection for root `r` is constant across templates — the prediction both
    root-only and categorizer-only accounts make. -/
def templateInvariant (r : RootLabel) : Prop :=
  ∀ t1 t2 : SemiticTemplate, lSelect r t1 = lSelect r t2

/-- xwf 'fear' is template-independent: *min* in every template (ex. (11)). -/
theorem xwf_templateInvariant : templateInvariant .xwf := fun t1 t2 => by
  cases t1 <;> cases t2 <;> rfl

/-- krh 'hate' refutes template-invariance: bare transitive in XaYaZ but *fi* in
    XaYYaZ (ex. (13a)) — the counterexample to [harley-2014]'s root-level
    l-selection. -/
theorem krh_not_templateInvariant : ¬ templateInvariant .krh :=
  fun h => absurd (h .XaYaZ .XaYYaZ) (by decide)

/-- dwr 'encircle' refutes template-invariance with two distinct prepositions:
    *bi:* in XaYaZ vs *ʕla* in XaYYaZ (ex. (13b)) — an independent counterexample
    to [merchant-2019]'s categorizer-level l-selection. -/
theorem dwr_not_templateInvariant : ¬ templateInvariant .dwr :=
  fun h => absurd (h .XaYaZ .XaYYaZ) (by decide)

/-- ħkm refutes template-invariance in the reverse direction: PP in XaYaZ, none in
    XaYYaZ (ex. (14)). -/
theorem Hkm_not_templateInvariant : ¬ templateInvariant .Hkm :=
  fun h => absurd (h .XaYaZ .XaYYaZ) (by decide)

/-- C-selection (arity) is root-level ([harley-2014]; see
    `complement_selection_at_root_level` in `Categorizer.lean`) but l-selection is
    not: the two kinds of selection factor differently in the grammar. -/
theorem cSelection_vs_lSelection :
    (∀ (r : RootClassification) (c1 c2 : Categorizer),
      (CategorizedRoot.mk r c1).root.arity = (CategorizedRoot.mk r c2).root.arity) ∧
    (∃ r : RootLabel, ¬ templateInvariant r) :=
  ⟨fun _ _ _ => rfl, ⟨.krh, krh_not_templateInvariant⟩⟩

/-! ### Verbalized roots -/

/-- A root that has been categorized as a verb and placed in a template — the
    structure that jointly determines l-selection. Bridges `CategorizedRoot`
    (categorizer side) and the template's Voice contribution. -/
structure VerbalizedRoot where
  /-- The root with its categorizer. -/
  categorized : CategorizedRoot
  /-- The Semitic template (functional head bundle). -/
  template : SemiticTemplate
  /-- The root label for l-selection lookup. -/
  rootLabel : RootLabel
  deriving Repr

/-- The l-selected preposition, derived from root and template. -/
def VerbalizedRoot.lSelectedP (vr : VerbalizedRoot) : Option SemiticPrep :=
  lSelect vr.rootLabel vr.template

/-- The Voice flavor, determined by the template rather than the root. -/
def VerbalizedRoot.voiceFlavor (vr : VerbalizedRoot) : Voice.Flavor :=
  vr.template.toVoiceFlavor

/-- Arity is template-invariant (root-level), unlike l-selection: c-selection and
    l-selection factor differently in the grammar. -/
theorem arity_template_invariant (cr : CategorizedRoot) (rl : RootLabel)
    (t1 t2 : SemiticTemplate) :
    (VerbalizedRoot.mk cr t1 rl).categorized.root.arity =
      (VerbalizedRoot.mk cr t2 rl).categorized.root.arity := rfl

/-! ### Template-to-Voice correspondence

Formalizer's bridge (see the module docstring): the template determines the Voice
head merged above the verbalized root, and that functional structure — above the
selectional domain — is what varies across templates while root and categorizer
stay fixed. -/

/-- The basic active template maps to θ-assigning (agentive) Voice. -/
theorem active_template_assigns_theta :
    (SemiticTemplate.toVoiceHead .XaYaZ).AssignsTheta := by decide

/-- Causative templates map to θ-assigning (causer) Voice. -/
theorem causer_template_assigns_theta :
    (SemiticTemplate.toVoiceHead .XaYYaZ).AssignsTheta := by decide

/-- Passive templates map to non-θ-assigning Voice — the structural basis for
    Hebrew P-suppression under passivization (exx. (17b), (18b)). -/
theorem passive_template_no_theta :
    ¬ (SemiticTemplate.toVoiceHead .huXYaZ).AssignsTheta := by decide

/-- XaYaZ and XaYYaZ differ in Voice contribution (agentive vs causer): the
    functional structure above the selectional domain varies even when root and
    categorizer do not. -/
theorem voice_distinguishes_templates :
    SemiticTemplate.toVoiceFlavor .XaYaZ ≠ SemiticTemplate.toVoiceFlavor .XaYYaZ := by
  decide

/-- [kratzer-1996]'s severing instantiated for Semitic: root-level arity is
    template-invariant while the Voice contribution varies by template. -/
theorem severing_instantiated (cr : CategorizedRoot) (rl : RootLabel) :
    (VerbalizedRoot.mk cr .XaYaZ rl).categorized.root.arity =
      (VerbalizedRoot.mk cr .XaYYaZ rl).categorized.root.arity ∧
    SemiticTemplate.toVoiceFlavor .XaYaZ ≠ SemiticTemplate.toVoiceFlavor .XaYYaZ :=
  ⟨arity_template_invariant cr rl .XaYaZ .XaYYaZ, voice_distinguishes_templates⟩

/-! ### Cross-linguistic Voice coverage

Formalizer's bridge, not content of [hewett-2026] (which cites [wood-2015] only in
passing, as a language where Voice is overt): Semitic templates and Icelandic -st
relate to Voice differently. Each Semitic template *realizes* a single Voice flavor
(including the θ-assigning ones); -st is a clitic that merely *co-occurs* with a
Voice flavor without realizing it ([wood-2015]). Read as coverage sets over
`Voice.Flavor`, the Semitic image and the set of flavors -st appears with overlap on
the non-thematic and agentive flavors (the latter because -st appears in agentive
figure reflexives) but diverge elsewhere. The Icelandic set is derived from
[wood-2015]'s `Construction.voiceFlavor`, so the theorem relates the two studies' actual
mappings. -/

/-- The Voice flavors Semitic templates realize: the image of `toVoiceFlavor`. -/
def semiticVoiceFlavors : List Voice.Flavor :=
  [SemiticTemplate.XaYaZ.toVoiceFlavor, SemiticTemplate.XaYYaZ.toVoiceFlavor,
   SemiticTemplate.nXaYaZ.toVoiceFlavor, SemiticTemplate.tXaYYaZ.toVoiceFlavor]

/-- Every template's flavor is in the Semitic coverage set. -/
theorem template_flavors_in_coverage (t : SemiticTemplate) :
    t.toVoiceFlavor ∈ semiticVoiceFlavors := by cases t <;> decide

/-- The host-clause Voice flavors Icelandic -st co-occurs with, derived from
    [wood-2015]'s `Construction.voiceFlavor`. -/
def icelandicStFlavors : List Voice.Flavor :=
  [Construction.anticausative.voiceFlavor, Construction.middle.voiceFlavor,
   Construction.reflexive.voiceFlavor, Construction.subjectExp.voiceFlavor]

/-- Every -st configuration's flavor is in the Icelandic coverage set (inherent and
    reciprocal reuse flavors of the four representatives). -/
theorem stType_flavors_in_coverage (st : Construction) :
    st.voiceFlavor ∈ icelandicStFlavors := by cases st <;> decide

/-- The two coverage sets overlap on `.nonThematic` (Semitic medio-passive,
    Icelandic anticausative -st) and `.agentive` (Semitic active templates,
    Icelandic figure reflexives — -st co-occurs with agentive Voice); Semitic
    alone realizes the causer and passive flavors, Icelandic -st alone appears
    with the expletive Voice of the generic middle. -/
theorem voice_coverage_complementary :
    (.nonThematic : Voice.Flavor) ∈ semiticVoiceFlavors ∧
    (.nonThematic : Voice.Flavor) ∈ icelandicStFlavors ∧
    (.agentive : Voice.Flavor) ∈ semiticVoiceFlavors ∧
    (.agentive : Voice.Flavor) ∈ icelandicStFlavors ∧
    (.causer : Voice.Flavor) ∉ icelandicStFlavors ∧
    (.passive : Voice.Flavor) ∉ icelandicStFlavors ∧
    (.expletive : Voice.Flavor) ∈ icelandicStFlavors ∧
    (.expletive : Voice.Flavor) ∉ semiticVoiceFlavors := by decide

/-- The Semitic XaYaZ ~ tXaYYaZ alternation instantiates [kratzer-1996]'s causative
    alternation: `toVoiceHead` maps the two templates to the canonical heads, so the
    Semitic statement *is* `Kratzer1996.causative_pair_voice_contrast`. -/
theorem causative_alternation_parallel :
    (SemiticTemplate.toVoiceHead .XaYaZ).AssignsTheta ∧
    ¬ (SemiticTemplate.toVoiceHead .tXaYYaZ).AssignsTheta :=
  Kratzer1996.causative_pair_voice_contrast

/-! ### Template → Voice → applicative licensing

Formalizer's bridge to [pylkkanen-2008] (not cited by [hewett-2026]): high
applicatives require Voice with event semantics, low applicatives are
unconditional. Pulled back along `toVoiceHead`, the Voice-predicate chain
`assignsTheta ⊂ hasSemantics = licenses high Appl ⊂ licenses low Appl = ⊤`
yields: +θ templates ⊊ high-Appl-licensing templates ⊊ all templates. The general
inclusions live in the substrate (`Voice.Head.AssignsTheta.hasSemantics`,
`high_licensed_of_assignsTheta`, `low_licensed_with_any`); this section
instantiates them for the Semitic template space, paralleling the Icelandic
asymmetry in `Wood2015.dative_voice_asymmetry`. -/

/-- Does this template license a given applicative type? Composes the substrate's
    `ApplHead.Licensed` with `toVoiceHead`. -/
def SemiticTemplate.licensesAppl (t : SemiticTemplate) (appl : ApplHead) : Prop :=
  appl.Licensed t.toVoiceHead

instance (t : SemiticTemplate) (appl : ApplHead) : Decidable (t.licensesAppl appl) :=
  inferInstanceAs (Decidable (appl.Licensed t.toVoiceHead))

/-- High-Appl licensing factors through `HasSemantics`. -/
theorem high_appl_iff_hasSemantics (t : SemiticTemplate) :
    t.licensesAppl applHigh ↔ t.toVoiceHead.HasSemantics := by
  cases t <;> decide

/-- A template that blocks high applicatives assigns no θ — via the substrate
    implication, not template enumeration. -/
theorem high_appl_blocked_implies_no_theta (t : SemiticTemplate)
    (h : ¬ t.licensesAppl applHigh) : ¬ t.toVoiceHead.AssignsTheta :=
  fun hθ => h (high_licensed_of_assignsTheta t.toVoiceHead hθ)

/-- A θ-assigning template licenses every applicative type. -/
theorem theta_licenses_all_appl (t : SemiticTemplate) (appl : ApplHead)
    (hθ : t.toVoiceHead.AssignsTheta) : t.licensesAppl appl :=
  fun _ => hθ.hasSemantics

/-- The Voice-predicate chain pulled back to the Semitic template space; both
    inclusions are strict: nXaYaZ licenses high Appl without assigning θ, and
    tXaYYaZ blocks high Appl. -/
theorem voice_predicate_chain :
    (∀ t : SemiticTemplate,
      t.toVoiceHead.AssignsTheta → t.licensesAppl applHigh) ∧
    (∃ t : SemiticTemplate,
      t.licensesAppl applHigh ∧ ¬ t.toVoiceHead.AssignsTheta) ∧
    (∀ t : SemiticTemplate,
      t.licensesAppl applHigh → t.licensesAppl applLowRecipient) ∧
    (∃ t : SemiticTemplate, ¬ t.licensesAppl applHigh) :=
  ⟨fun t hθ => high_licensed_of_assignsTheta t.toVoiceHead hθ,
    ⟨.nXaYaZ, by decide, by decide⟩,
    fun t _ => (low_licensed_with_any t.toVoiceHead).1,
    ⟨.tXaYYaZ, by decide⟩⟩

/-! ### Feature activation

[hewett-2026] ex. (23) (adapted from [merchant-2015]): Activate(X,Y;F) — X bears a
category feature c; Y bears an inactive feature F^C with C = (c₁,...,cₙ) an
ordered tuple. If c = c₁, Activate strips c₁; when the tuple is exhausted, F is
fully active. For Semitic l-selection the tuple is (V, Template): the categorizing
head strips the first index, the template-defining head the second. The tuple
machinery is `ActivationIndex` from `Checking.lean`. -/

/-- Activation keys for Semitic l-selection: the activation tuple mixes syntactic
    categories (stripped by the categorizing head) and template identities
    (stripped by the template-defining head). -/
inductive ActivationKey where
  /-- A syntactic category key. -/
  | cat : Cat → ActivationKey
  /-- A template key. -/
  | template : SemiticTemplate → ActivationKey
  deriving DecidableEq, Repr

/-- `BEq` via `decide` so that activation reduces definitionally on concrete keys
    (`ActivationIndex` requires `[BEq α]`). -/
instance : BEq ActivationKey := ⟨λ a b => decide (a = b)⟩

instance : LawfulBEq ActivationKey where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- A selectional feature indexed by an ordered activation tuple ([hewett-2026]
    ex. (23)): `selectedP` becomes visible to selection only once `activation` is
    exhausted. -/
structure SelectionalFeature where
  /-- The preposition selected when fully activated. -/
  selectedP : SemiticPrep
  /-- Ordered activation tuple; empty = fully active. -/
  activation : ActivationIndex ActivationKey
  deriving Repr

/-- The feature's lifecycle status, via `ActivationIndex.toStatus`. -/
def SelectionalFeature.status (sf : SelectionalFeature) : FeatureStatus :=
  sf.activation.toStatus

/-- Attempt to activate with the given key (matching left-to-right stripping,
    via `ActivationIndex.activate`). -/
def SelectionalFeature.activate (sf : SelectionalFeature)
    (key : ActivationKey) : SelectionalFeature :=
  { sf with activation := sf.activation.activate key }

/-- A dormant feature indexed by `(V, T)`: needs V then T to activate. -/
def SelectionalFeature.dormant (p : SemiticPrep)
    (t : SemiticTemplate) : SelectionalFeature :=
  { selectedP := p, activation := ⟨[.cat .v, .template t]⟩ }

/-- A dormant feature is inactive. -/
theorem dormant_is_inactive (p : SemiticPrep) (t : SemiticTemplate) :
    (SelectionalFeature.dormant p t).status = .inactive := rfl

/-- Activating V alone strips one key but leaves the template key. -/
theorem cat_alone_inactive (p : SemiticPrep) (t : SemiticTemplate) :
    (SelectionalFeature.dormant p t |>.activate (.cat .v)).status = .inactive := rfl

/-- Activating with a non-matching key (template before V) is a no-op: ex. (23)
    strips only when the key matches the leftmost index. -/
theorem wrong_order_noop (p : SemiticPrep) (t : SemiticTemplate) :
    (SelectionalFeature.dormant p t |>.activate (.template t)).status
    = .inactive := rfl

/-- Both activations in the correct order yield an active feature. -/
theorem both_activations_active (p : SemiticPrep) (t : SemiticTemplate) :
    (SelectionalFeature.dormant p t
      |>.activate (.cat .v)
      |>.activate (.template t)).status = .active := by
  cases t <;> rfl

/-! ### Worked derivation (exx. (24)–(25)) -/

/-- The root dwr carries one selectional feature per template pairing
    ([hewett-2026] exx. (24)–(25)): `[SEL: bi^(V, XaYaZ)]` selects *bi:* when
    activated by V and XaYaZ. -/
def dwr_sel_XaYaZ : SelectionalFeature :=
  SelectionalFeature.dormant .bi .XaYaZ

/-- `[SEL: ʕla^(V, XaYYaZ)]` selects *ʕla* when activated by V and XaYYaZ. -/
def dwr_sel_XaYYaZ : SelectionalFeature :=
  SelectionalFeature.dormant .Eala .XaYYaZ

/-- Ex. (24), dar b- 'encircled': V strips `.cat .v` from both features; XaYaZ then
    strips the template key from the bi: feature only (template mismatch leaves the
    ʕla feature inactive), and the active feature matches `lSelect`. -/
theorem dwr_XaYaZ_derivation :
    let bi_afterV := dwr_sel_XaYaZ.activate (.cat .v)
    let bi_afterT := bi_afterV.activate (.template .XaYaZ)
    let eala_afterV := dwr_sel_XaYYaZ.activate (.cat .v)
    let eala_afterT := eala_afterV.activate (.template .XaYaZ)
    bi_afterT.status = .active ∧
    bi_afterT.selectedP = .bi ∧
    eala_afterT.status = .inactive ∧
    some bi_afterT.selectedP = lSelect .dwr .XaYaZ := ⟨rfl, rfl, rfl, rfl⟩

/-- Ex. (25), dawwər ʕla 'made encircle': same root, different template — XaYYaZ
    activates the ʕla feature and leaves the bi: feature inactive. -/
theorem dwr_XaYYaZ_derivation :
    let eala_afterV := dwr_sel_XaYYaZ.activate (.cat .v)
    let eala_afterT := eala_afterV.activate (.template .XaYYaZ)
    let bi_afterV := dwr_sel_XaYaZ.activate (.cat .v)
    let bi_afterT := bi_afterV.activate (.template .XaYYaZ)
    eala_afterT.status = .active ∧
    eala_afterT.selectedP = .Eala ∧
    bi_afterT.status = .inactive ∧
    some eala_afterT.selectedP = lSelect .dwr .XaYYaZ := ⟨rfl, rfl, rfl, rfl⟩

/-! ### Mono-eventive causatives

Fn. 11 (p. 204): XaYYaZ causatives reject conflicting temporal adverbials, which
[hewett-2026] takes to show they are mono-eventive, assuming with [nie-2020] that
morphological causatives are crosslinguistically mono-eventive. The decompositions
below render this in the local `VerbHead` substrate — the formalizer's encoding,
not the paper's ([nie-2020]'s own analysis is Voice-over-Voice, not a subevent
inventory). -/

/-- Mono-eventive causative decomposition: θ-assigning Voice over a root structure
    lacking the becoming subevent vGO. -/
def monoEventiveCausative : List VerbHead :=
  Voice.buildDecomposition Voice.causer [.vCAUSE, .vBE]

/-- Bi-eventive causative decomposition (analytic causatives): θ-assigning Voice
    over the full change-of-state root structure. -/
def biEventiveCausative : List VerbHead :=
  Voice.buildDecomposition Voice.causer [.vCAUSE, .vGO, .vBE]

/-- Mono-eventive causatives have CAUSE but lack GO. -/
theorem mono_eventive_has_cause_no_go :
    VerbHead.vCAUSE ∈ monoEventiveCausative ∧
    VerbHead.vGO ∉ monoEventiveCausative := by decide

/-- Mono-eventive causatives are not standard causatives (which require the vGO
    becoming subevent). -/
theorem mono_eventive_not_standard_causative :
    isCausative monoEventiveCausative = false := by decide

/-- Bi-eventive causatives are standard causatives. -/
theorem bi_eventive_is_causative :
    isCausative biEventiveCausative = true := by decide

/-! ### Summary -/

/-- **Main result**: l-selection is a function of root and template jointly —
    template-dependent and template-independent roots both exist, so neither root
    alone ([harley-2014]) nor categorizer alone ([merchant-2019]) determines it. -/
theorem joint_selection :
    (∃ r : RootLabel, ¬ templateInvariant r) ∧
    (∃ r : RootLabel, templateInvariant r) :=
  ⟨⟨.krh, krh_not_templateInvariant⟩, ⟨.xwf, xwf_templateInvariant⟩⟩

end Hewett2026
