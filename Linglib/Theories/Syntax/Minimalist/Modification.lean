import Linglib.Theories.Syntax.Minimalist.Features
import Linglib.Core.Morphology.MorphRule

/-!
# Syntactic Modification via Feature Composition
@cite{alexeyenko-zeijlstra-2025}

Nominal modification as a species of complementation: adjectives and nouns
cannot directly merge because neither c-selects the other. Resolution comes
either from the adjective lexically carrying `[N, uN]` (in φ/κ-complete
languages like Greek) or from an **Attr head** that mediates the feature
conversion.

## Core Claims

1. **Modification = complementation**: both are driven by c-selection features
   (`[uF]` checked under sisterhood with `[F]`). An adjective `[A]` and a
   noun `[N]` can merge only if one bears the other's uninterpretable
   categorial feature.

2. **Two feature compositions** (§5.1):
   - **Direct**: adjective enters as `[N, uN]`, selects and merges with `[N]`
     directly. Available only when pred & attr adjectives have identical
     φ/κ-specification. Corresponds semantically to predicate modification.
   - **Attr-mediated**: an Attr head converts `[A] → [N, uN]` (part of xAP)
     or `[N] → [N, uA]` (part of xNP). Required when adjectives lack full
     φ/κ-specification.

3. **Attr status determines linearization** (§5.2): the morphophonological
   realization of Attr (affix / clitic / free word / null) determines
   whether it must be linearly adjacent to its host, via the Input
   Correspondence Principle (@cite{ackema-neeleman-2004}).

## Types Exported

- `AttrStatus` — morphophonological status of the attributivizer
- `AdjMorphProfile` — per-language adjective morphosyntactic profile
- `ModificationRoute` — direct (no Attr) vs Attr-mediated modification
- `morphStatusToAttrStatus` — bridge from `Core.Lexical.MorphRule.MorphStatus`
-/

namespace Minimalist.Modification

open Core.Morphology (MorphStatus)

-- ============================================================================
-- § 1: Attributivizer Status
-- ============================================================================

/-- Morphophonological status of the attributivizer (Attr head, §5.2).
    Determines whether Attr imposes linear adjacency with the adjective. -/
inductive AttrStatus where
  | affix     -- must be adjacent to host per ICP: German -er, Dutch -e, Basque
  | clitic    -- morphophonologically independent: Mandarin 的, Farsi ezafe
  | freeWord  -- independent word form
  | null      -- covert but syntactically present: English, Hungarian
  deriving DecidableEq, Repr

/-- Position of attributive adjectives relative to the modified noun. -/
inductive AdjPosition where
  | prenominal   -- A–N: English, German, Russian, Greek
  | postnominal  -- N–A: Basque, Farsi, Eastern Oromo
  | both         -- both orders productive: Latin, Tagalog
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Adjective Morphosyntactic Profile
-- ============================================================================

/-- Morphosyntactic profile of adjectives in a language.

    The MAG (34) is determined by two independent factors:
    - **Morphosyntactic** (§5.1): agreement identity between predicative and
      attributive forms, and completeness of that agreement for all φ/κ-features
    - **Morphophonological** (§5.2): status of the attributivizer -/
structure AdjMorphProfile where
  /-- Primary position of attributive adjectives relative to N -/
  adjPosition              : AdjPosition
  /-- Internal head direction of the AP -/
  apDirection              : HeadDirection
  /-- MAG (34a), clause 1: the agreement marker on attr adjectives is
      also present on predicative adjectives (pred = attr featurally). -/
  predAttrSameAgreement    : Bool
  /-- MAG (34a), clause 2: the agreement marker is specified for ALL
      φ/κ-features available in the DP. Per fn 17, κ (case) is always
      a DP feature whether morphologically realized or not. -/
  agreementPhiKappaComplete : Bool
  /-- MAG (34b): morphophonological status of the attributivizer -/
  attrStatus               : AttrStatus
  deriving DecidableEq, Repr

-- ============================================================================
-- § 3: Modification Routes (§5.1)
-- ============================================================================

/-- The two routes to nominal modification (§5.1.2 vs §5.1.3).

    - **direct**: adjective lexically carries `[N, uN]`, merges directly
      with the noun. No Attr head needed. Only available in φ/κ-complete
      languages (Greek, Russian, Latin, Kalaallisut).
    - **attrMediated**: an Attr functional head mediates the feature
      conversion. Required when adjectives lack full φ/κ-specification.
      Attr may be part of the extended adjectival projection (xAP) or
      the extended nominal projection (xNP). -/
inductive ModificationRoute where
  | direct        -- [N, uN] + [N] → no Attr needed (§5.1.2)
  | attrMediated  -- Attr converts [A] → [N, uN] or [N] → [N, uA] (§5.1.3)
  deriving DecidableEq, Repr

/-- Determine the modification route from the adjective morphosyntactic
    profile. φ/κ-complete languages use direct modification; all others
    require an Attr head. -/
def modificationRoute (prof : AdjMorphProfile) : ModificationRoute :=
  if prof.predAttrSameAgreement && prof.agreementPhiKappaComplete then
    .direct
  else
    .attrMediated

/-- φ/κ-complete languages use direct modification. -/
theorem phiKappaComplete_implies_direct (prof : AdjMorphProfile)
    (hSame : prof.predAttrSameAgreement = true)
    (hComplete : prof.agreementPhiKappaComplete = true) :
    modificationRoute prof = .direct := by
  simp [modificationRoute, hSame, hComplete]

/-- Languages with pred ≠ attr require Attr. -/
theorem predNeAttr_implies_attrMediated (prof : AdjMorphProfile)
    (h : prof.predAttrSameAgreement = false) :
    modificationRoute prof = .attrMediated := by
  simp [modificationRoute, h]

/-- Languages with incomplete φ/κ require Attr. -/
theorem incomplete_implies_attrMediated (prof : AdjMorphProfile)
    (h : prof.agreementPhiKappaComplete = false) :
    modificationRoute prof = .attrMediated := by
  simp [modificationRoute, h]

-- ============================================================================
-- § 4: Bridge from MorphStatus to AttrStatus
-- ============================================================================

/-- Map the framework-agnostic `MorphStatus` (from Zwicky & Pullum's
    clitic-affix cline) to the MAG's `AttrStatus`. Both inflectional
    and derivational affixes impose adjacency per the ICP. Both simple
    and special clitics are morphophonologically independent. -/
def morphStatusToAttrStatus : MorphStatus → AttrStatus
  | .freeWord      => .freeWord
  | .simpleClitic  => .clitic
  | .specialClitic => .clitic
  | .inflAffix     => .affix
  | .derivAffix    => .affix

/-- Affixes impose adjacency. -/
theorem affix_maps_to_affix :
    morphStatusToAttrStatus .inflAffix = .affix := rfl

/-- Clitics are morphophonologically independent. -/
theorem clitic_maps_to_clitic :
    morphStatusToAttrStatus .simpleClitic = .clitic := rfl

/-- Free words map to free words. -/
theorem freeWord_maps_to_freeWord :
    morphStatusToAttrStatus .freeWord = .freeWord := rfl

-- ============================================================================
-- § 5: MAG Feature Types (bridge to Minimalist features)
-- ============================================================================

/-- The feature types that MAG condition (a) requires agreement for.
    φ-features map to `Minimalist.PhiFeature`, κ-features to `Core.Case`. -/
inductive MAGFeatureType where
  | phi : Minimalist.PhiFeature → MAGFeatureType
  | kappa : Core.Case → MAGFeatureType
  deriving DecidableEq, Repr

/-- An adjective agreement entry: which features are morphologically
    realized on adjectives in each syntactic position. -/
structure AdjAgreementEntry where
  /-- Features realized on predicative adjectives. -/
  predFeatures : List MAGFeatureType
  /-- Features realized on attributive adjectives. -/
  attrFeatures : List MAGFeatureType
  /-- All φ/κ-features available in the DP of this language. -/
  dpFeatures   : List MAGFeatureType
  deriving Repr

/-- Derive `predAttrSameAgreement` from an agreement entry:
    true iff the attr feature list is a subset of the pred features and
    vice versa (same set). Simplified to list equality for decidability. -/
def AdjAgreementEntry.sameAgreement (e : AdjAgreementEntry) : Bool :=
  e.predFeatures.length == e.attrFeatures.length &&
  e.attrFeatures.all (e.predFeatures.contains ·)

/-- Derive `agreementPhiKappaComplete` from an agreement entry:
    true iff every DP feature appears on the attributive adjective. -/
def AdjAgreementEntry.phiKappaComplete (e : AdjAgreementEntry) : Bool :=
  e.dpFeatures.all (e.attrFeatures.contains ·)

end Minimalist.Modification
