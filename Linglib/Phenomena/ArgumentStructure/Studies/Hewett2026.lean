import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Syntax.Minimalism.Core.Applicative
import Linglib.Theories.Syntax.Minimalism.Core.Checking
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Syntax.Minimalism.Core.VerbalDecomposition
import Linglib.Theories.Morphology.Core.MirrorPrinciple

/-!
# Verbal Templates Can Influence L-Selection in Semitic
@cite{hewett-2026}

*Linguistic Inquiry* 57(1): 197--215.

L-selection — which specific preposition heads a PP complement —
can vary by verbal template (binyan) in Tunisian Arabic, Syrian Arabic,
and Hebrew. This falsifies both @cite{harley-2014} (roots select) and
@cite{merchant-2019} (categorizing heads select), because neither
root nor categorizer varies across templates.

## Core Contribution

**Joint Selection via Activate** (Def 23, adapted from
@cite{merchant-2019}): roots carry inactive selectional features
indexed by an ordered tuple of category features. Each head that
c-commands the root strips one category from the tuple. When the
tuple is exhausted, the feature is fully active and determines the
l-selected P. For Semitic, the tuple is `(V, Template)`: the
categorizing head V strips the first index, the template-defining
head strips the second.

## Scope

Templates are realized by nonconcatenative morphology (vocalic melodies
applied to consonantal roots). The Mirror Principle
(@cite{baker-1985}) explicitly scopes out nonconcatenative morphology
(see `Theories.Morphology.MirrorPrinciple.MorphDomain.inScope`).
Template-dependent l-selection is therefore a phenomenon that falls
outside the domain where morphological and syntactic orderings are
required to mirror each other.
-/

namespace Phenomena.ArgumentStructure.Studies.Hewett2026

open Minimalism (VoiceFlavor VoiceHead VerbHead Cat FeatureStatus TrackedFeature
  ActivationIndex ApplType ApplHead applHigh applLowRecipient applLowSource
  buildDecomposition voiceAgent voiceCauser voiceAnticausative
  voiceMiddle voicePassive voiceReflexive voiceExperiencer isCausative)
open Theories.Morphology.DM (CategorizedRoot Categorizer)
open Theories.Morphology.MirrorPrinciple (MorphDomain)

-- ============================================================================
-- S1: Semitic Verbal Templates (Binyanim)
-- ============================================================================

/-- Semitic verbal templates (binyanim).

    Each template is realized as a nonconcatenative vocalic pattern
    applied to a consonantal root. Syntactically, templates correspond
    to bundles of functional heads (v, Voice) — they are not
    roots, and they are not categorizers.

    @cite{hewett-2026} assumes templates realize a head or series of
    heads capable of inducing changes in adicity, presumably v/Voice
    (p. 201). -/
inductive SemiticTemplate where
  | XaYaZ     -- Form I: basic active (Arabic fal)
  | XaYYaZ    -- Form II: intensive/causative (Arabic faal)
  | nXaYaZ    -- Form VII: medio-passive (Arabic infaal)
  | tXaYYaZ   -- Form V: reflexive/medio-passive (Arabic tafaal)
  | hiXYiZ    -- Hifil: causative (Hebrew)
  | huXYaZ    -- Hufal: passive of Hifil (Hebrew)
  | XiYeZ     -- Piel: intensive/causative (Hebrew)
  | XuYaZ     -- Pual: passive of Piel (Hebrew)
  deriving DecidableEq, Repr

/-- `BEq` via `DecidableEq` so that `decide (a = b)` reduces
    definitionally on concrete values — required for `rfl` proofs
    in the activation mechanism. -/
instance : BEq SemiticTemplate := ⟨λ a b => decide (a = b)⟩

instance : LawfulBEq SemiticTemplate where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- Map templates to Voice flavors.

    Active templates (XaYaZ, XaYYaZ, XiYeZ, hiXYiZ) select agentive or
    causer Voice. Passive/medio-passive templates (nXaYaZ, tXaYYaZ,
    huXYaZ, XuYaZ) correspond to passive or non-thematic Voice.

    XaYYaZ introduces a causer (intensive/causative), distinguished from
    XaYaZ (basic agentive). This is the key structural difference that
    drives l-selection variation: the template determines which Voice
    head merges, and the Voice head is above the selectional domain. -/
def SemiticTemplate.toVoiceFlavor : SemiticTemplate → VoiceFlavor
  | .XaYaZ   => .agentive
  | .XaYYaZ  => .causer
  | .nXaYaZ  => .passive
  | .tXaYYaZ => .nonThematic
  | .hiXYiZ  => .causer
  | .huXYaZ  => .passive
  | .XiYeZ   => .causer
  | .XuYaZ   => .passive

/-- Does this template introduce a causer argument? -/
def SemiticTemplate.introducesCauser : SemiticTemplate → Bool
  | .XaYYaZ | .hiXYiZ | .XiYeZ => true
  | _ => false

/-- Is this template passive or medio-passive? -/
def SemiticTemplate.isPassiveLike : SemiticTemplate → Bool
  | .nXaYaZ | .tXaYYaZ | .huXYaZ | .XuYaZ => true
  | _ => false

/-- Templates are nonconcatenative morphology — outside the scope of
    the Mirror Principle (@cite{baker-1985} S5). -/
theorem templates_outside_mirror_scope :
    MorphDomain.inScope .nonconcatenative = false := rfl

-- ============================================================================
-- S2: Roots and Prepositions
-- ============================================================================

/-- Consonantal roots from the paper's examples.
    Only roots with attested l-selection data are included.
    Transliterated to ASCII-safe identifiers. -/
inductive RootLabel where
  | xwf    -- xwf 'fear/frighten' (Tunisian Arabic, ex. 11)
  | krh    -- krh 'hate/make hate' (Tunisian Arabic, ex. 13)
  | dwr    -- dwr 'encircle/make encircle' (Tunisian Arabic, ex. 13b)
  | Hkm    -- Hkm 'sentence/referee' (Syrian Arabic, ex. 14)
  | tpl    -- tpl 'treat' (Hebrew, ex. 17)
  | shps   -- shps 'influence' (Hebrew, ex. 18)
  deriving DecidableEq, Repr, BEq

/-- Prepositions attested in the paper's l-selection data. -/
inductive SemiticPrep where
  | fi      -- 'in' (Tunisian Arabic)
  | bi      -- 'with/in' (Tunisian Arabic)
  | Eala    -- 'on/over' (Tunisian Arabic: ʕla / ʕli:)
  | min     -- 'from' (Tunisian/Syrian Arabic)
  | Ealej   -- 'on' (Syrian Arabic: ʕalej)
  | be      -- 'in' (Hebrew)
  | al      -- 'on' (Hebrew)
  deriving DecidableEq, Repr, BEq

/-- Languages providing l-selection data in the paper. -/
inductive SemiticLang where
  | tunisianArabic
  | syrianArabic
  | hebrew
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- S3: L-Selection Data
-- ============================================================================

/-- An l-selection datum: a root in a specific template selects a
    specific preposition (or none, for transitive/unergative uses
    or passive P-suppression). -/
structure LSelDatum where
  root : RootLabel
  template : SemiticTemplate
  prep : Option SemiticPrep
  lang : SemiticLang
  deriving Repr, BEq

/-- Template-independent l-selection: xwf selects *min* 'from'
    regardless of template.
    XaYaZ: xa:f min l-?asad 'He was afraid of the lion.'
    XaYYaZ: xawwaf-u min l-?asad 'He made him afraid of the lion.'
    @cite{hewett-2026} ex. (11). -/
def xwf_XaYaZ : LSelDatum :=
  { root := .xwf, template := .XaYaZ, prep := some .min, lang := .tunisianArabic }

def xwf_XaYYaZ : LSelDatum :=
  { root := .xwf, template := .XaYYaZ, prep := some .min, lang := .tunisianArabic }

/-- Template-dependent l-selection: krh 'hate'.
    XaYaZ: kraht (*fi) Sami 'I hate (*in) Sami.' — no PP, transitive.
    XaYYaZ: karraht-ha *(fi) Sami 'I made her hate *(in) Sami.' — requires *fi*.
    @cite{hewett-2026} ex. (13a). -/
def krh_XaYaZ : LSelDatum :=
  { root := .krh, template := .XaYaZ, prep := none, lang := .tunisianArabic }

def krh_XaYYaZ : LSelDatum :=
  { root := .krh, template := .XaYYaZ, prep := some .fi, lang := .tunisianArabic }

/-- Template-dependent l-selection: dwr 'encircle'.
    XaYaZ: l-hnash da:r bi: k 'The snake encircled you.' — selects bi:.
    XaYYaZ: dawwart l-hnash fli: k 'I made the snake encircle you.' — selects fli: (= Eala).
    @cite{hewett-2026} ex. (13b). -/
def dwr_XaYaZ : LSelDatum :=
  { root := .dwr, template := .XaYaZ, prep := some .bi, lang := .tunisianArabic }

def dwr_XaYYaZ : LSelDatum :=
  { root := .dwr, template := .XaYYaZ, prep := some .Eala, lang := .tunisianArabic }

/-- Template-dependent l-selection: Hkm 'sentence/referee' (Syrian Arabic).
    XaYaZ: hakam Ealej-o b-s-sidjn 'He sentenced him to jail.' — selects *Ealej*.
    XaYYaZ: Hakkam (l-muba:re:t) 'He refereed (the match).' — no PP (rejects Eala and b-).
    @cite{hewett-2026} ex. (14). -/
def Hkm_XaYaZ : LSelDatum :=
  { root := .Hkm, template := .XaYaZ, prep := some .Ealej, lang := .syrianArabic }

def Hkm_XaYYaZ : LSelDatum :=
  { root := .Hkm, template := .XaYYaZ, prep := none, lang := .syrianArabic }

/-- Template-dependent l-selection: tpl 'treat' (Hebrew).
    XiYeZ: tipel be- NP 'treated in NP'. — selects *be*.
    XuYaZ: NP tupal (al jedej NP) 'NP was treated (by NP).' — P suppressed by passive.
    @cite{hewett-2026} ex. (17). -/
def tpl_XiYeZ : LSelDatum :=
  { root := .tpl, template := .XiYeZ, prep := some .be, lang := .hebrew }

def tpl_XuYaZ : LSelDatum :=
  { root := .tpl, template := .XuYaZ, prep := none, lang := .hebrew }

/-- Template-dependent l-selection: shps 'influence' (Hebrew).
    hiXYiZ: hishpia al NP 'influenced over NP'. — selects *al*.
    huXYaZ: NP hushpa (al jedej NP) 'NP was influenced (by NP).' — P suppressed by passive.
    @cite{hewett-2026} ex. (18). -/
def shps_hiXYiZ : LSelDatum :=
  { root := .shps, template := .hiXYiZ, prep := some .al, lang := .hebrew }

def shps_huXYaZ : LSelDatum :=
  { root := .shps, template := .huXYaZ, prep := none, lang := .hebrew }

-- ============================================================================
-- S4: Joint Selection Function
-- ============================================================================

/-- L-selection as a function of root AND template — the paper's core
    insight. L-selection is NOT a function of root alone.

    Returns `none` when the root+template combination does not select a
    PP complement (transitive/unergative use or passive suppression).

    xwf uses a wildcard: the paper attests *min* in both XaYaZ and
    XaYYaZ, and the claim is that xwf is template-independent — we
    generalize to all templates. -/
def lSelect : RootLabel → SemiticTemplate → Option SemiticPrep
  -- Template-independent: xwf always selects *min*
  | .xwf,  _         => some .min
  -- Template-dependent: krh
  | .krh,  .XaYaZ   => none
  | .krh,  .XaYYaZ  => some .fi
  -- Template-dependent: dwr
  | .dwr,  .XaYaZ   => some .bi
  | .dwr,  .XaYYaZ  => some .Eala
  -- Template-dependent: Hkm
  | .Hkm,  .XaYaZ   => some .Ealej
  | .Hkm,  .XaYYaZ  => none
  -- Template-dependent: tpl (Hebrew)
  | .tpl,  .XiYeZ   => some .be
  | .tpl,  .XuYaZ   => none
  -- Template-dependent: shps (Hebrew)
  | .shps,  .hiXYiZ  => some .al
  | .shps,  .huXYaZ  => none
  -- Default: no data
  | _, _ => none

/-- Verify data consistency: `lSelect` matches each LSelDatum. -/
theorem xwf_data_consistent :
    lSelect xwf_XaYaZ.root xwf_XaYaZ.template = xwf_XaYaZ.prep ∧
    lSelect xwf_XaYYaZ.root xwf_XaYYaZ.template = xwf_XaYYaZ.prep := ⟨rfl, rfl⟩

theorem krh_data_consistent :
    lSelect krh_XaYaZ.root krh_XaYaZ.template = krh_XaYaZ.prep ∧
    lSelect krh_XaYYaZ.root krh_XaYYaZ.template = krh_XaYYaZ.prep := ⟨rfl, rfl⟩

theorem dwr_data_consistent :
    lSelect dwr_XaYaZ.root dwr_XaYaZ.template = dwr_XaYaZ.prep ∧
    lSelect dwr_XaYYaZ.root dwr_XaYYaZ.template = dwr_XaYYaZ.prep := ⟨rfl, rfl⟩

theorem Hkm_data_consistent :
    lSelect Hkm_XaYaZ.root Hkm_XaYaZ.template = Hkm_XaYaZ.prep ∧
    lSelect Hkm_XaYYaZ.root Hkm_XaYYaZ.template = Hkm_XaYYaZ.prep := ⟨rfl, rfl⟩

theorem tpl_data_consistent :
    lSelect tpl_XiYeZ.root tpl_XiYeZ.template = tpl_XiYeZ.prep ∧
    lSelect tpl_XuYaZ.root tpl_XuYaZ.template = tpl_XuYaZ.prep := ⟨rfl, rfl⟩

theorem shps_data_consistent :
    lSelect shps_hiXYiZ.root shps_hiXYiZ.template = shps_hiXYiZ.prep ∧
    lSelect shps_huXYaZ.root shps_huXYaZ.template = shps_huXYaZ.prep := ⟨rfl, rfl⟩

-- ============================================================================
-- S5: Template-Dependence (Derived, Not Stipulated)
-- ============================================================================

/-- A root is template-dependent for l-selection iff there exist two
    *attested* template pairings for which `lSelect` returns different
    prepositions. Derived from `lSelect`, not stipulated. -/
def isTemplateDependentWitness (r : RootLabel) :
    Option (SemiticTemplate × SemiticTemplate) :=
  match r with
  | .krh  => some (.XaYaZ, .XaYYaZ)
  | .dwr  => some (.XaYaZ, .XaYYaZ)
  | .Hkm  => some (.XaYaZ, .XaYYaZ)
  | .tpl  => some (.XiYeZ, .XuYaZ)
  | .shps => some (.hiXYiZ, .huXYaZ)
  | .xwf  => none

/-- Derived classification: a root is template-dependent iff a
    witnessing pair exists AND its two values actually differ. -/
def isTemplateDependent (r : RootLabel) : Bool :=
  match isTemplateDependentWitness r with
  | some (t1, t2) => lSelect r t1 != lSelect r t2
  | none => false

/-- xwf is template-independent: same P regardless of template. -/
theorem xwf_template_independent :
    lSelect .xwf .XaYaZ = lSelect .xwf .XaYYaZ := rfl

/-- krh is template-dependent: different P across templates. -/
theorem krh_template_dependent :
    isTemplateDependent .krh = true := by native_decide

/-- dwr is template-dependent: different P across templates. -/
theorem dwr_template_dependent :
    isTemplateDependent .dwr = true := by native_decide

/-- Hkm is template-dependent: the direction reverses
    (XaYaZ takes PP, XaYYaZ doesn't). -/
theorem Hkm_template_dependent :
    isTemplateDependent .Hkm = true := by native_decide

/-- xwf is NOT template-dependent. -/
theorem xwf_not_template_dependent :
    isTemplateDependent .xwf = false := by native_decide

-- ============================================================================
-- S6: Falsification of Harley 2014 and Merchant 2019
-- ============================================================================

/-- **Template-invariance prediction**: l-selection for a given root
    is constant across all templates.

    Both @cite{harley-2014} (roots select) and @cite{merchant-2019}
    (categorizing heads select) predict this, for different reasons:
    - Harley: the root takes its complement directly, so only the root
      determines the l-selected P.
    - Merchant: the categorizing head (V) selects, but since all
      templates verbalize the root with the same categorizer V, the
      l-selected P should be template-invariant.

    Since neither root nor categorizer varies across templates,
    both theories make the same prediction for verbs. The paper
    shows this prediction is false. -/
def templateInvariant (r : RootLabel) : Prop :=
  ∀ t1 t2 : SemiticTemplate, lSelect r t1 = lSelect r t2

/-- @cite{harley-2014} is falsified: krh is a counterexample.
    XaYaZ krh is transitive (no PP), XaYYaZ krh requires *fi*. -/
theorem harley_falsified : ¬ templateInvariant .krh := by
  intro h
  have := h .XaYaZ .XaYYaZ
  simp [lSelect] at this

/-- @cite{merchant-2019} is falsified by independent data: dwr.
    XaYaZ dwr selects *bi:*, XaYYaZ dwr selects *Eala*. -/
theorem merchant_falsified : ¬ templateInvariant .dwr := by
  intro h
  have := h .XaYaZ .XaYYaZ
  simp [lSelect] at this

/-- Template-independent roots DO satisfy the invariance prediction.
    Joint Selection is a refinement, not a wholesale rejection: it
    reduces to root-level selection when the template dimension is
    vacuous (the selectional feature's template index is the same
    across all templates). -/
theorem xwf_satisfies_invariance : templateInvariant .xwf := by
  intro t1 t2
  cases t1 <;> cases t2 <;> rfl

/-- **The homophony argument** (p. 208): template-dependent l-selection
    cannot be explained by positing distinct homophonous roots
    (krh₁ for XaYaZ, krh₂ for XaYYaZ), because this would fail to
    explain mutual exclusivity — krh₁ only appears in XaYaZ and krh₂
    only in XaYYaZ, parallel to the suppletive distribution of go~went.

    If roots were truly distinct, we'd expect each to freely appear in
    any template. The mutual exclusivity shows a single root with
    template-sensitive selectional properties. -/
theorem homophony_argument_krh :
    -- A single root produces different l-selections in different templates
    lSelect .krh .XaYaZ ≠ lSelect .krh .XaYYaZ ∧
    -- But there is only ONE root entry — not two homophonous roots
    -- (the enum has a single .krh constructor)
    (∀ r : RootLabel, r = .krh → lSelect r .XaYaZ = none ∧ lSelect r .XaYYaZ = some .fi) := by
  constructor
  · decide
  · intro r hr; subst hr; exact ⟨rfl, rfl⟩

/-- C-selection (arity) IS root-level per @cite{harley-2014} S3.
    This connects to `complement_selection_at_root_level` in
    Categorizer.lean. L-selection is the dimension that escapes
    root determination, not c-selection. -/
theorem cSelection_vs_lSelection :
    -- Arity is root-invariant (from Categorizer.lean)
    (∀ (r : Root) (c1 c2 : Categorizer),
      (CategorizedRoot.mk r c1).root.arity =
      (CategorizedRoot.mk r c2).root.arity) ∧
    -- But l-selection is NOT root-invariant
    (∃ r : RootLabel, ¬ templateInvariant r) := by
  exact ⟨fun _ _ _ => rfl, ⟨.krh, harley_falsified⟩⟩

-- ============================================================================
-- S7: VerbalizedRoot — Bridging Categorizer and Voice
-- ============================================================================

/-- A verbalized root: a root that has been categorized as a verb AND
    placed in a specific template. This is the structure that jointly
    determines l-selection.

    `VerbalizedRoot` bridges two types that never previously appeared
    together: `CategorizedRoot` (from Categorizer.lean) and `VoiceHead`
    (from Voice.lean). The template connects them — it determines which
    Voice flavor the root appears with AND which P is l-selected. -/
structure VerbalizedRoot where
  /-- The root with its categorizer. -/
  categorized : CategorizedRoot
  /-- The Semitic template (functional head bundle). -/
  template : SemiticTemplate
  /-- The paper-specific root label (for l-selection lookup). -/
  rootLabel : RootLabel
  /-- The l-selected preposition, derived from root + template. -/
  lSelectedP : Option SemiticPrep := lSelect rootLabel template
  deriving Repr

/-- The Voice flavor is determined by the template, not the root. -/
def VerbalizedRoot.voiceFlavor (vr : VerbalizedRoot) : VoiceFlavor :=
  vr.template.toVoiceFlavor

/-- Arity is template-invariant (root-level) but l-selection is not.
    This is the core architectural claim: c-selection and l-selection
    factor differently in the grammar. -/
theorem arity_template_invariant (cr : CategorizedRoot) (rl : RootLabel)
    (t1 t2 : SemiticTemplate) :
    ({ categorized := cr, template := t1, rootLabel := rl : VerbalizedRoot }).categorized.root.arity =
    ({ categorized := cr, template := t2, rootLabel := rl : VerbalizedRoot }).categorized.root.arity := rfl

-- ============================================================================
-- S7b: Voice Bridge Theorems
-- ============================================================================

/-- Causer templates map to theta-assigning Voice.
    XaYYaZ introduces a causer → theta-assigning → vDO in decomposition.
    This is why the template can influence l-selection: it determines
    the functional structure above VP. -/
theorem causer_template_assigns_theta :
    let voice : VoiceHead := { flavor := SemiticTemplate.toVoiceFlavor .XaYYaZ,
                                hasD := true, phaseHead := true }
    voice.assignsTheta = true := rfl

/-- Basic active template maps to agentive Voice, also theta-assigning. -/
theorem active_template_assigns_theta :
    let voice : VoiceHead := { flavor := SemiticTemplate.toVoiceFlavor .XaYaZ,
                                hasD := true, phaseHead := true }
    voice.assignsTheta = true := rfl

/-- Passive templates do NOT assign theta — the external argument is
    demoted or absent. This is the structural basis for Hebrew
    P-suppression: the passivizing template head merged above the
    verbalized root suppresses the l-selected P. -/
theorem passive_template_no_theta :
    let voice : VoiceHead := { flavor := SemiticTemplate.toVoiceFlavor .huXYaZ,
                                hasD := true, phaseHead := false }
    voice.assignsTheta = false := rfl

/-- XaYaZ and XaYYaZ differ in their Voice contribution: XaYaZ maps
    to agentive, XaYYaZ maps to causer. This Voice difference is what
    drives the l-selection variation — it's the functional structure
    ABOVE the selectional domain that varies. -/
theorem voice_distinguishes_templates :
    SemiticTemplate.toVoiceFlavor .XaYaZ ≠
    SemiticTemplate.toVoiceFlavor .XaYYaZ := by decide

-- ============================================================================
-- S7c: Cross-Linguistic Voice Bridges
-- ============================================================================

/-! ### Connection to @cite{kratzer-1996} and @cite{wood-2015}

@cite{kratzer-1996} argues that Voice is a separate head from V,
introducing the external argument. @cite{wood-2015} shows Icelandic
-st morphology spells out Voice across six distinct configurations
(anticausative, middle, reflexive, experiencer, inherent, reciprocal),
parameterized by ±θ (theta-assignment) and ±D (specifier requirement).

Semitic templates instantiate the SAME Voice architecture:
`toVoiceFlavor` maps each template to a `VoiceFlavor`, and the
resulting `VoiceHead` determines theta-assignment via `assignsTheta`.
The cross-linguistic parallel: Semitic templates and Icelandic -st are
both morphology that realizes Voice heads, determining argument
structure above the root.

The key difference: Semitic templates are EACH associated with a
SINGLE Voice flavor (XaYaZ → agentive, XaYYaZ → causer, etc.), while
Icelandic -st spells out ALL non-agentive Voice types as an elsewhere
exponent. The two languages carve up the VoiceFlavor space
complementarily. -/

/-- **Exhaustive theta classification**: every template maps to either
    theta-assigning (+θ) or non-theta-assigning (-θ) Voice.
    Active templates (XaYaZ, XaYYaZ, hiXYiZ, XiYeZ) are +θ;
    passive/medio-passive templates (nXaYaZ, tXaYYaZ, huXYaZ, XuYaZ)
    are -θ. This is an exhaustive partition with no exceptions. -/
def SemiticTemplate.isTheta : SemiticTemplate → Bool
  | .XaYaZ | .XaYYaZ | .hiXYiZ | .XiYeZ => true
  | .nXaYaZ | .tXaYYaZ | .huXYaZ | .XuYaZ => false

/-- `isTheta` agrees with `VoiceHead.assignsTheta` for all templates. -/
theorem isTheta_matches_assignsTheta (t : SemiticTemplate) :
    let voice : VoiceHead := { flavor := t.toVoiceFlavor,
                                hasD := true, phaseHead := t.isTheta }
    voice.assignsTheta = t.isTheta := by
  cases t <;> rfl

/-- @cite{kratzer-1996}'s severing instantiated for Semitic:
    `VerbalizedRoot` factors argument structure into V (`CategorizedRoot`)
    and Voice (`template.toVoiceFlavor`). The categorizer determines
    arity (c-selection); Voice determines whether an external argument
    is introduced. L-selection depends on both — it is determined by
    the root AND the Voice-determining template jointly. -/
theorem severing_instantiated (cr : CategorizedRoot) (rl : RootLabel) :
    -- V-level properties are template-invariant (root arity)
    ({ categorized := cr, template := .XaYaZ, rootLabel := rl : VerbalizedRoot }).categorized.root.arity =
    ({ categorized := cr, template := .XaYYaZ, rootLabel := rl : VerbalizedRoot }).categorized.root.arity ∧
    -- Voice-level properties are template-VARIANT
    SemiticTemplate.toVoiceFlavor .XaYaZ ≠
    SemiticTemplate.toVoiceFlavor .XaYYaZ := by
  exact ⟨rfl, by decide⟩

/-- **Semitic Voice coverage**: the four VoiceFlavor values that Semitic
    templates produce. These are exactly the flavors relevant to
    TRANSITIVE and PASSIVE argument structure. -/
def semiticVoiceFlavors : List VoiceFlavor :=
  [.agentive, .causer, .passive, .nonThematic]

/-- All template voice flavors are in the Semitic coverage set. -/
theorem template_flavors_in_coverage (t : SemiticTemplate) :
    semiticVoiceFlavors.contains (t.toVoiceFlavor) = true := by
  cases t <;> native_decide

/-- **Icelandic -st Voice coverage**: the non-agentive flavors from
    @cite{wood-2015}. These are exactly the flavors relevant to
    DETRANSITIVIZED and DERIVED argument structure. -/
def icelandicStFlavors : List VoiceFlavor :=
  [.nonThematic, .expletive, .reflexive, .experiencer]

/-- The Semitic and Icelandic coverage sets are complementary: they
    share only `.nonThematic` (anticausative, which in Semitic is the
    medio-passive template nXaYaZ/tXaYYaZ and in Icelandic is -st). -/
theorem voice_coverage_complementary :
    -- Shared: nonThematic
    semiticVoiceFlavors.contains .nonThematic = true ∧
    icelandicStFlavors.contains .nonThematic = true ∧
    -- Semitic-only: agentive, causer, passive
    icelandicStFlavors.contains .agentive = false ∧
    icelandicStFlavors.contains .causer = false ∧
    icelandicStFlavors.contains .passive = false ∧
    -- Icelandic-only: expletive (middle), reflexive, experiencer
    semiticVoiceFlavors.contains .expletive = false ∧
    semiticVoiceFlavors.contains .reflexive = false ∧
    semiticVoiceFlavors.contains .experiencer = false := by
  native_decide

/-- The canonical Voice heads from Voice.lean that correspond to each
    template family. Active templates map to `voiceAgent`/`voiceCauser`;
    passive templates map to `voicePassive`/`voiceAnticausative`.
    This is the same typology @cite{kratzer-1996} uses for the causative
    alternation and @cite{wood-2015} extends for Icelandic -st. -/
theorem templates_map_to_canonical_voices :
    -- Active: agentive voice (= Kratzer's Voice_AG)
    voiceAgent.flavor = SemiticTemplate.toVoiceFlavor .XaYaZ ∧
    -- Causative: causer voice (= Schäfer's Voice_CAUSE)
    voiceCauser.flavor = SemiticTemplate.toVoiceFlavor .XaYYaZ ∧
    -- Passive: passive voice (= Collins's by-Voice)
    voicePassive.flavor = SemiticTemplate.toVoiceFlavor .nXaYaZ ∧
    -- Medio-passive: anticausative voice (= Wood's Voice_{D}/[-θ])
    voiceAnticausative.flavor = SemiticTemplate.toVoiceFlavor .tXaYYaZ := ⟨rfl, rfl, rfl, rfl⟩

/-- @cite{kratzer-1996}'s causative alternation parallels the Semitic
    template alternation: both are Voice alternations over a shared VP.
    Kratzer: "John broke the vase" (Voice_AG) ↔ "The vase broke" (Voice_∅).
    Semitic: dar b- (XaYaZ/agentive) ↔ ndar (nXaYaZ/passive).
    In both, the causal relation is shared; only Voice varies. -/
theorem causative_alternation_parallel :
    -- Kratzer: agentive assigns θ, anticausative does not
    voiceAgent.assignsTheta = true ∧
    voiceAnticausative.assignsTheta = false ∧
    -- Semitic: active templates assign θ, passive templates do not
    SemiticTemplate.isTheta .XaYaZ = true ∧
    SemiticTemplate.isTheta .nXaYaZ = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- S7d: Template → Voice → Applicative Licensing
-- ============================================================================

/-! ### The Template → Voice → Applicative chain

@cite{pylkknen-2008} establishes that high applicatives require Voice
with event semantics, while low applicatives are independent of Voice.
@cite{hewett-2026}'s template system instantiates this: each template
determines a VoiceFlavor (via `toVoiceFlavor`), and that flavor
determines whether Voice has event semantics (via `hasSemantics`).

The mathematical content is a chain of strict inclusions on Voice
predicates:

    assignsTheta ⊂ hasSemantics = licensesAppl(high) ⊂ licensesAppl(low) = ⊤

The first inclusion is a general property of the Voice architecture
(`theta_implies_hasSemantics`), not specific to Semitic: every θ-role
assigning Voice head contributes event semantics, but the converse
fails (passive and impersonal Voice have semantics without θ). The
second inclusion is trivial — low applicatives are unconditional.

For the Semitic template space, the pullback of this chain yields:
+θ templates ⊂ high-Appl-licensing templates ⊂ all templates.
The blocking set `{tXaYYaZ}` is a singleton because the Semitic
inventory includes exactly one semantics-free flavor (`.nonThematic`).

This instantiates for Semitic the same high/low asymmetry that
@cite{wood-2015} documents for Icelandic (`dative_voice_asymmetry`
in `Wood2015.lean`): middles block ethical datives but license
possessive datives. -/

-- ── General Voice properties (not template-specific) ─────────────────

/-- θ-assignment entails event semantics: every Voice head that
    introduces an external argument also contributes semantic content.
    The converse fails (`hasSemantics_not_implies_theta`). -/
theorem theta_implies_hasSemantics (v : VoiceHead) :
    v.assignsTheta = true → v.hasSemantics = true := by
  cases v with | mk flavor _ _ _ _ =>
  cases flavor <;> simp [VoiceHead.assignsTheta, VoiceHead.hasSemantics]

/-- The converse fails: passive Voice has semantics (it contributes
    a *by*-phrase) but does not assign θ (the external argument is
    demoted). Impersonal Voice is another counterexample (existential
    closure without a projected specifier). -/
theorem hasSemantics_not_implies_theta :
    voicePassive.hasSemantics = true ∧ voicePassive.assignsTheta = false ∧
    voiceMiddle.hasSemantics = false ∧ voiceMiddle.assignsTheta = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Contrapositive: no event semantics entails no θ-assignment.
    Derived from `theta_implies_hasSemantics`, not proved by cases. -/
theorem no_semantics_implies_no_theta (v : VoiceHead) :
    v.hasSemantics = false → v.assignsTheta = false := by
  intro h
  cases hθ : v.assignsTheta with
  | false => rfl
  | true => simp [theta_implies_hasSemantics v hθ] at h

/-- Low applicatives are unconditionally licensed regardless of Voice.
    The `if` on `requiresEventSemantics` takes the `else` branch for
    both low types, yielding `true` for any Voice head. -/
theorem low_appl_unconditional (v : VoiceHead) :
    applLowRecipient.licensedWith v = true ∧
    applLowSource.licensedWith v = true := ⟨rfl, rfl⟩

-- ── Template-level definitions ───────────────────────────────────────

/-- Construct a canonical VoiceHead from a template. `hasD` and
    `phaseHead` are set to match the template's θ properties;
    only `flavor` matters for applicative licensing (via
    `hasSemantics`). -/
def SemiticTemplate.toVoiceHead (t : SemiticTemplate) : VoiceHead :=
  { flavor := t.toVoiceFlavor, hasD := t.isTheta, phaseHead := t.isTheta }

/-- Does this template license a given applicative type?
    Composes `licensedWith ∘ toVoiceHead`. -/
def SemiticTemplate.licensesAppl (t : SemiticTemplate) (appl : ApplHead) : Bool :=
  appl.licensedWith t.toVoiceHead

-- ── Derived template-level theorems ──────────────────────────────────

/-- Licensing factors through `hasSemantics` for high Appl. -/
theorem high_appl_iff_hasSemantics (t : SemiticTemplate) :
    t.licensesAppl applHigh = t.toVoiceHead.hasSemantics := by
  cases t <;> rfl

/-- If a template blocks high applicatives, it also fails to assign θ.
    Proved via the general implication `θ → hasSemantics`, not by
    enumerating templates. -/
theorem high_appl_blocked_implies_no_theta (t : SemiticTemplate) :
    t.licensesAppl applHigh = false →
    t.toVoiceHead.assignsTheta = false := by
  intro h
  rw [high_appl_iff_hasSemantics] at h
  exact no_semantics_implies_no_theta _ h

/-- If a template assigns θ, it licenses ALL applicative types.
    Chain: θ → hasSemantics → high licensed; low always licensed.
    Proved via the general implication, quantified over `ApplHead`. -/
theorem theta_licenses_all_appl (t : SemiticTemplate) (appl : ApplHead) :
    t.toVoiceHead.assignsTheta = true →
    t.licensesAppl appl = true := by
  intro hθ
  have hSem := theta_implies_hasSemantics _ hθ
  simp only [SemiticTemplate.licensesAppl, ApplHead.licensedWith]
  split
  · exact hSem
  · rfl

/-- The full implication chain on Voice predicates, instantiated for the
    Semitic template space. Both inclusions are STRICT:

    1. +θ templates ⊂ high-Appl-licensing templates: nXaYaZ (passive)
       licenses high Appl but assigns no θ.
    2. High-Appl-licensing templates ⊂ all templates: tXaYYaZ blocks
       high Appl.

    The first inclusion is proved via the general `theta_implies_hasSemantics`,
    not by enumerating templates. -/
theorem voice_predicate_chain :
    (∀ t : SemiticTemplate, t.toVoiceHead.assignsTheta = true → t.licensesAppl applHigh = true) ∧
    (∃ t : SemiticTemplate, t.licensesAppl applHigh = true ∧ t.toVoiceHead.assignsTheta = false) ∧
    (∀ t : SemiticTemplate, t.licensesAppl applHigh = true → t.licensesAppl applLowRecipient = true) ∧
    (∃ t : SemiticTemplate, t.licensesAppl applHigh = false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- θ → high licensed (via general theta_implies_hasSemantics)
    intro t hθ
    rw [high_appl_iff_hasSemantics]
    exact theta_implies_hasSemantics _ hθ
  · -- Proper: nXaYaZ (passive) licenses high but has no θ
    exact ⟨.nXaYaZ, rfl, rfl⟩
  · -- High licensed → low licensed (via unconditional low licensing)
    intro t _; exact (low_appl_unconditional t.toVoiceHead).1
  · -- Proper: tXaYYaZ blocks high
    exact ⟨.tXaYYaZ, rfl⟩

-- ============================================================================
-- S8: Feature Activation (Def 23)
-- ============================================================================

/-- Activation keys for Semitic l-selection. The activation tuple
    `(c₁, …, cₙ)` in @cite{hewett-2026} Def 23 mixes two sorts of key:
    syntactic categories (`Cat` from the Minimalist architecture) and
    template identities. This sum type makes the key space explicit. -/
inductive ActivationKey where
  /-- A syntactic category key (stripped by a categorizing head). -/
  | cat : Cat → ActivationKey
  /-- A template key (stripped by the template-defining head). -/
  | template : SemiticTemplate → ActivationKey
  deriving DecidableEq, Repr

/-- `BEq` via `DecidableEq` ensures `LawfulBEq` follows trivially. -/
instance : BEq ActivationKey := ⟨λ a b => decide (a = b)⟩

instance : LawfulBEq ActivationKey where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- A selectional feature indexed by an ordered activation tuple.

    @cite{hewett-2026} Def 23 (adapted from @cite{merchant-2019}):
    Activate(X,Y;F) — X activates F on Y. X bears a category feature c,
    Y bears an inactive feature F^C where C = (c₁,...,cₙ). If c = c₁,
    Activate strips c₁ from C, leaving F^(c₂,...,cₙ). If n = 1 and
    c = c₁, F^C becomes F (fully active).

    The `activation` field uses the general `ActivationIndex` from
    Checking.lean — the same ordered n-tuple stripping mechanism. For
    Semitic l-selection, the tuple is `[.cat .v, .template T]`: the
    categorizing head V strips the first index, the template-defining
    head strips the second. -/
structure SelectionalFeature where
  /-- The preposition this feature selects when fully activated. -/
  selectedP : SemiticPrep
  /-- Ordered activation tuple. Empty = fully active. -/
  activation : ActivationIndex ActivationKey
  deriving Repr

/-- The overall status of a selectional feature, derived from its
    activation tuple. Maps to the `FeatureStatus` lifecycle in
    Checking.lean via `ActivationIndex.toStatus`. -/
def SelectionalFeature.status (sf : SelectionalFeature) : FeatureStatus :=
  sf.activation.toStatus

/-- Attempt to activate this feature with the given key. Delegates to
    `ActivationIndex.activate` (matching left-to-right stripping). -/
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
    (SelectionalFeature.dormant p t |>.activate (.cat .v)).status
    = .inactive := rfl

/-- Activating with a non-matching key (template before V) is a no-op. -/
theorem wrong_order_noop (p : SemiticPrep) (t : SemiticTemplate) :
    (SelectionalFeature.dormant p t |>.activate (.template t)).status
    = .inactive := rfl

/-- Both activations in the correct order yield an active feature. -/
theorem both_activations_active (p : SemiticPrep) (t : SemiticTemplate) :
    (SelectionalFeature.dormant p t
      |>.activate (.cat .v)
      |>.activate (.template t)).status = .active := by
  cases t <;> rfl

/-- Connect to Checking.lean's lifecycle: a dormant selectional feature
    uses the `.inactive` status, and after both activations it transitions
    to `.active`, ready for the standard checking lifecycle. -/
theorem activation_matches_lifecycle (p : SemiticPrep)
    (t : SemiticTemplate) :
    let dormant := SelectionalFeature.dormant p t
    let activated := dormant.activate (.cat .v) |>.activate (.template t)
    dormant.status = .inactive ∧ activated.status = .active := by
  constructor
  · rfl
  · cases t <;> rfl

/-- The Checking.lean lifecycle continues after activation: an activated
    selectional feature can be checked and erased. -/
theorem activated_feature_enters_lifecycle :
    let tf : TrackedFeature := ⟨.phi (.person .first), .v, .uninterpretable, .inactive⟩
    ∃ tf1, tf.activate = some tf1 ∧
    ∃ tf2, tf1.check = some tf2 ∧
    ∃ tf3, tf2.erase = some tf3 ∧ tf3.status = .erased := by
  simp [TrackedFeature.activate, TrackedFeature.check, TrackedFeature.erase]

-- ============================================================================
-- S8b: Worked Derivation (ex. 24--25)
-- ============================================================================

/-- The root dwr carries two selectional features, each indexed by
    `[.cat .v, .template T]` for its specific template.
    [SEL: bi^{V, XaYaZ}] selects *bi:* when activated by V + XaYaZ.
    [SEL: Eala^{V, XaYYaZ}] selects *Eala* when activated by V + XaYYaZ.
    @cite{hewett-2026} ex. (24)--(25). -/
def dwr_sel_XaYaZ : SelectionalFeature :=
  SelectionalFeature.dormant .bi .XaYaZ
def dwr_sel_XaYYaZ : SelectionalFeature :=
  SelectionalFeature.dormant .Eala .XaYYaZ

/-- Derivation of ex. (24): dar b- 'encircled'.
    Step 1: V merges → strips `.cat .v` from both features.
    Step 2: XaYaZ merges → strips `.template .XaYaZ` from the bi: feature
    (match!), but NOT from the Eala feature (`.template .XaYYaZ ≠
    .template .XaYaZ` — no match, no strip).
    Result: bi: feature is fully active; Eala feature stays inactive. -/
theorem dwr_XaYaZ_derivation :
    let bi_afterV := dwr_sel_XaYaZ.activate (.cat .v)
    let bi_afterT := bi_afterV.activate (.template .XaYaZ)
    let eala_afterV := dwr_sel_XaYYaZ.activate (.cat .v)
    let eala_afterT := eala_afterV.activate (.template .XaYaZ)
    -- The bi: feature is fully active
    bi_afterT.status = .active ∧
    bi_afterT.selectedP = .bi ∧
    -- The Eala feature stays inactive (template mismatch!)
    eala_afterT.status = .inactive ∧
    -- And the active feature matches lSelect
    some bi_afterT.selectedP = lSelect .dwr .XaYaZ := ⟨rfl, rfl, rfl, rfl⟩

/-- Derivation of ex. (25): dawwar Eala 'made encircle'.
    Same root, different template → different feature activated.
    Now XaYYaZ strips `.template .XaYYaZ` from the Eala feature (match!),
    but NOT from the bi: feature (`.template .XaYaZ ≠ .template .XaYYaZ`). -/
theorem dwr_XaYYaZ_derivation :
    let eala_afterV := dwr_sel_XaYYaZ.activate (.cat .v)
    let eala_afterT := eala_afterV.activate (.template .XaYYaZ)
    let bi_afterV := dwr_sel_XaYaZ.activate (.cat .v)
    let bi_afterT := bi_afterV.activate (.template .XaYYaZ)
    -- The Eala feature is fully active
    eala_afterT.status = .active ∧
    eala_afterT.selectedP = .Eala ∧
    -- The bi: feature stays inactive (template mismatch!)
    bi_afterT.status = .inactive ∧
    -- And the active feature matches lSelect
    some eala_afterT.selectedP = lSelect .dwr .XaYYaZ := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- S9: Mono-Eventive Causatives (fn 11, p. 204)
-- ============================================================================

/-- XaYYaZ causatives are mono-eventive: they don't license conflicting
    temporal adverbials (Nie 2020). If XaYYaZ were bi-eventive
    (containing a syntactically represented causing event), we'd expect
    multiple temporal adverbials to modify distinct subevents. The
    prediction is not borne out (p. 204, fn 11).

    Formally: XaYYaZ's decomposition lacks vGO — it is [vDO, vCAUSE, vBE],
    a direct causation structure without a separate becoming subevent.
    This contrasts with analytic causatives that have the full
    [vDO, vCAUSE, vGO, vBE] decomposition. -/
def monoEventiveCausative : List VerbHead := [.vDO, .vCAUSE, .vBE]

/-- Mono-eventive causatives have CAUSE but lack GO. -/
theorem mono_eventive_has_cause_no_go :
    monoEventiveCausative.contains .vCAUSE = true ∧
    monoEventiveCausative.contains .vGO = false := by native_decide

/-- Mono-eventive causatives are NOT classified as standard causatives
    (which require vGO for the becoming subevent). -/
theorem mono_eventive_not_standard_causative :
    isCausative monoEventiveCausative = false := by native_decide

/-- The full bi-eventive causative decomposition from Voice.lean. -/
def biEventiveCausative : List VerbHead := [.vDO, .vCAUSE, .vGO, .vBE]

/-- Bi-eventive causatives ARE standard causatives. -/
theorem bi_eventive_is_causative :
    isCausative biEventiveCausative = true := by native_decide

-- ============================================================================
-- S10: Summary Theorems
-- ============================================================================

/-- **Main result**: l-selection is a function of root AND template
    jointly. Neither root alone (@cite{harley-2014}) nor categorizer
    alone (@cite{merchant-2019}) determines l-selection. -/
theorem joint_selection :
    -- Template-dependent roots exist
    (∃ r : RootLabel, isTemplateDependent r = true) ∧
    -- Template-independent roots also exist
    (∃ r : RootLabel, isTemplateDependent r = false) :=
  ⟨⟨.krh, krh_template_dependent⟩, ⟨.xwf, xwf_not_template_dependent⟩⟩

/-- Harley's root-level account of ARITY (c-selection) is correct.
    His root-level account of L-SELECTION is not. The two types of
    selection factor differently in the grammar. -/
theorem selection_factors :
    (∀ (r : Root) (c1 c2 : Categorizer),
      (CategorizedRoot.mk r c1).root.arity =
      (CategorizedRoot.mk r c2).root.arity) ∧
    (∃ r : RootLabel, ¬ templateInvariant r) :=
  cSelection_vs_lSelection

/-- The activation mechanism produces the correct l-selected P for
    every root with data in both templates. Matching activation ensures
    only the correct feature activates in each template environment. -/
theorem activation_matches_lSelect_dwr :
    let bi := dwr_sel_XaYaZ.activate (.cat .v) |>.activate (.template .XaYaZ)
    let eala := dwr_sel_XaYYaZ.activate (.cat .v) |>.activate (.template .XaYYaZ)
    bi.selectedP = .bi ∧
    some .bi = lSelect .dwr .XaYaZ ∧
    eala.selectedP = .Eala ∧
    some .Eala = lSelect .dwr .XaYYaZ := ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.ArgumentStructure.Studies.Hewett2026
