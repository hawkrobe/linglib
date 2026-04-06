import Linglib.Core.Lexical.MorphRule

/-!
# The Mirror Principle
@cite{baker-1985}

"Morphological derivations must directly reflect syntactic derivations
(and vice versa)." (@cite{baker-1985} (4))

Each grammatical function changing rule (GF-rule) — passive, causative,
applicative, reflexive/reciprocal — simultaneously:
- adds an affix to the verb (morphological effect)
- changes the grammatical functions of arguments (syntactic effect)

Given a verb with structure `[... [afB [afA [root]]]]`, the inside-out
layering tells us affix A was added before affix B. The Mirror Principle
requires the corresponding syntactic rules to have applied in the same
order: process A before process B.

## Architectural Status

@cite{baker-1985} §6 argues the Mirror Principle should not be a
stipulation but should follow from the architecture of the grammar.
In a framework where GF-rules are a single process with both
morphological and syntactic effects, mirroring is by construction.
We formalize this via the `DerivationStep` type, which bundles the
morphological and syntactic aspects of each rule into a single object.

## Key Prediction: The Agreement Restriction

Of four logical combinations of agreement position (inner/outer
relative to a GF-rule morpheme) and agreement target (semantic/surface
GFs), only two are attested (@cite{baker-1985} (27)):

- Inner + semantic ✓  (agreement added before GF-rule → sees pre-rule GFs)
- Outer + surface ✓  (agreement added after GF-rule → sees post-rule GFs)
- Inner + surface ✗  (would require seeing ahead to unapplied rule)
- Outer + semantic ✗  (would require seeing past already-applied rule)

## Scope

The Mirror Principle applies to concatenative (agglutinative)
morphology. Clitics and nonconcatenative morphology are outside its
scope (@cite{baker-1985} §5).
-/

namespace Theories.Morphology.MirrorPrinciple

open Core.Morphology (MorphCategory)

-- ============================================================================
-- §1: GF-Rule Types
-- ============================================================================

/-- Grammatical function changing rules (GF-rules): processes that
    simultaneously add an affix to the verb and change the grammatical
    functions of arguments. @cite{baker-1985} §§2–4. -/
inductive GFRuleType where
  /-- Promotes object to subject; marks verb.
      Chamorro *-in-*, English *be + -en*. -/
  | passive
  /-- Adds causer as new subject; marks verb.
      Chamorro *na'-*, Quechua *-chi*. -/
  | causative
  /-- Promotes oblique to direct object; marks verb.
      Kinyarwanda *-iish*, Huichol *-ri*. -/
  | applicative
  /-- Binds object to subject (reflexive) or establishes mutual
      binding (reciprocal); marks verb.
      Quechua *-ku* (refl) / *-naku* (recip). -/
  | reflexReciprocal
  deriving DecidableEq, Repr, BEq

/-- Map GF-rules to @cite{bybee-1985}'s morphological categories.

    Passive maps to voice; causative, applicative, and
    reflexive/reciprocal map to valence. These are the
    categories that Bybee's relevance hierarchy predicts
    will appear close to the verbal stem. -/
def GFRuleType.toMorphCategory : GFRuleType → MorphCategory
  | .passive => .voice
  | .causative => .valence
  | .applicative => .valence
  | .reflexReciprocal => .valence

-- ============================================================================
-- §2: Derivation Steps
-- ============================================================================

/-- A single step in a morphosyntactic derivation. Bundles the
    morphological effect (adding an affix) with the syntactic
    effect (a GF-rule) — they are aspects of a single process.

    The `isPrefix` field records the directionality of affixation:
    prefixing languages (Chamorro, Bantu) vs suffixing (Quechua).

    By bundling affix and rule together, the `DerivationStep` type
    makes the Mirror Principle hold by construction: there is no
    way to separate the morphological and syntactic orderings. -/
structure DerivationStep where
  /-- Which GF-rule applies. -/
  rule : GFRuleType
  /-- The affix added to the verb. -/
  affix : String
  /-- Is the affix a prefix (true) or suffix (false)? -/
  isPrefix : Bool := false
  deriving DecidableEq, Repr, BEq

/-- A morphosyntactic derivation: a list of steps ordered from
    first-applied (innermost affix) to last-applied (outermost
    affix). By construction, the morphological ordering (affix
    layering) and syntactic ordering (rule application sequence)
    are identical — this IS the Mirror Principle, as an
    architectural property rather than a stipulated constraint. -/
abbrev Derivation := List DerivationStep

/-- The syntactic ordering: GF-rules from first to last applied. -/
def ruleOrder (d : Derivation) : List GFRuleType :=
  d.map (·.rule)

/-- The morphological ordering: affixes from inner to outer. -/
def affixOrder (d : Derivation) : List String :=
  d.map (·.affix)

/-- The orderings are isomorphic by construction (same length,
    corresponding elements). This is the Mirror Principle. -/
theorem mirror_by_construction (d : Derivation) :
    (ruleOrder d).length = (affixOrder d).length := by
  simp [ruleOrder, affixOrder]

-- ============================================================================
-- §3: The Agreement Restriction
-- ============================================================================

/-- Position of an agreement morpheme relative to a GF-rule
    morpheme on the verb. -/
inductive AgreementPosition where
  /-- Agreement morpheme is closer to the verb root (inner). -/
  | inner
  /-- Agreement morpheme is farther from the verb root (outer). -/
  | outer
  deriving DecidableEq, Repr, BEq

/-- What grammatical functions the agreement morpheme references. -/
inductive GFReference where
  /-- References semantic/underlying GFs (pre-rule). -/
  | semantic
  /-- References surface/derived GFs (post-rule). -/
  | surface
  deriving DecidableEq, Repr, BEq

/-- A combination of morphological position and GF reference.
    @cite{baker-1985} (27). -/
structure AgreementPattern where
  position : AgreementPosition
  reference : GFReference
  deriving DecidableEq, Repr, BEq

/-- The Mirror Principle derives the correct GF reference from
    morphological position alone — no stipulation needed.

    Inner position → agreement was added before the GF-rule
    → it can only see the pre-rule (semantic) GFs.
    Outer position → agreement was added after the GF-rule
    → it can only see the post-rule (surface) GFs. -/
def deriveReference : AgreementPosition → GFReference
  | .inner => .semantic
  | .outer => .surface

/-- The Agreement Restriction: which patterns are attested?

    Derived from `deriveReference`, not stipulated independently:
    a pattern is attested iff its GF reference matches what the
    Mirror Principle predicts for its morphological position.

    This makes the Agreement Restriction a consequence of the
    Mirror Principle rather than a separate stipulation.

    @cite{baker-1985} (27). -/
def AgreementPattern.isAttested (p : AgreementPattern) : Bool :=
  p.reference == deriveReference p.position

theorem inner_semantic_attested :
    (AgreementPattern.mk .inner .semantic).isAttested = true := rfl

theorem outer_surface_attested :
    (AgreementPattern.mk .outer .surface).isAttested = true := rfl

theorem outer_semantic_unattested :
    (AgreementPattern.mk .outer .semantic).isAttested = false := rfl

theorem inner_surface_unattested :
    (AgreementPattern.mk .inner .surface).isAttested = false := rfl

/-- Exactly two of the four patterns are attested. -/
theorem agreement_restriction_count :
    (([⟨.inner, .semantic⟩, ⟨.outer, .semantic⟩,
       ⟨.inner, .surface⟩, ⟨.outer, .surface⟩] :
       List AgreementPattern).filter (·.isAttested)).length
    = 2 := by
  native_decide

/-- The two attested patterns are (27a) and (27d). -/
theorem attested_are_27a_and_27d :
    ([⟨.inner, .semantic⟩, ⟨.outer, .semantic⟩,
      ⟨.inner, .surface⟩, ⟨.outer, .surface⟩] :
      List AgreementPattern).filter (·.isAttested)
    = [⟨.inner, .semantic⟩, ⟨.outer, .surface⟩] := by
  native_decide

/-- The derived reference always produces an attested pattern.
    With `isAttested` defined via `deriveReference`, this reduces
    to `x == x = true` — the Agreement Restriction follows from
    the Mirror Principle by construction. -/
theorem derived_reference_attested (pos : AgreementPosition) :
    (AgreementPattern.mk pos (deriveReference pos)).isAttested = true := by
  cases pos <;> rfl

-- ============================================================================
-- §4: Affix Ordering Predictions
-- ============================================================================

/-- Rule A feeds rule B: A's GF-change creates an argument
    configuration that B requires in order to operate.

    Applicative promotes an oblique to direct object; passive
    requires a direct object to promote to subject. Therefore
    applicative universally feeds passive: V-appl-pass.

    Other rule pairs (causative + reciprocal) can appear in
    either order depending on the language's GF-changing
    properties (Quechua vs Bemba), so their ordering is
    parametric, not fixed by feeding.

    @cite{baker-1985} §4.2. -/
def GFRuleType.feeds : GFRuleType → GFRuleType → Bool
  | .applicative, .passive => true
  | _, _ => false

/-- When two GF-rules interact (one feeds the other), the feeding
    rule must apply first, so its affix is closer to the root.
    Returns the predicted ordering: [feeder, fed]. -/
def feedingOrder (feeder fed : GFRuleType) : List GFRuleType :=
  [feeder, fed]

/-- Applicative feeds passive: creates the direct object that
    passive promotes to subject. @cite{baker-1985} §4.2. -/
theorem appl_feeds_passive :
    GFRuleType.feeds .applicative .passive = true := rfl

/-- The predicted ordering matches the feeding direction. -/
theorem appl_pass_predicted :
    feedingOrder .applicative .passive = [.applicative, .passive] := rfl

-- ============================================================================
-- §5: Scope
-- ============================================================================

/-- The morphological domain to which the Mirror Principle applies.
    @cite{baker-1985} §5. -/
inductive MorphDomain where
  /-- Concatenative affixation: in scope. -/
  | concatenative
  /-- Clitics: syntactically independent, phonologically bound.
      Outside scope (their distribution is syntactically rather
      than morphologically fixed). -/
  | cliticization
  /-- Nonconcatenative (Semitic templates, umlaut, reduplication):
      open question — depends on whether these can be reduced to
      underlying concatenative processes. -/
  | nonconcatenative
  deriving DecidableEq, Repr

/-- Only concatenative morphology is in scope. -/
def MorphDomain.inScope : MorphDomain → Bool
  | .concatenative => true
  | _ => false

-- ============================================================================
-- §6: Bridge to Bybee Relevance Hierarchy
-- ============================================================================

/-- Baker's GF-rule morphemes correspond to Bybee categories
    that are closer to the stem than agreement — consistent
    with the Mirror Principle's prediction that agreement is
    typically outer relative to GF-rule morphemes.
    @cite{baker-1985} (27), @cite{bybee-1985}. -/
theorem gfRule_inside_agreement (r : GFRuleType) :
    r.toMorphCategory.relevanceRank < MorphCategory.agreement.relevanceRank := by
  cases r <;> native_decide

end Theories.Morphology.MirrorPrinciple
