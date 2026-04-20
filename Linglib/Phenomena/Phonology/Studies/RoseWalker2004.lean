/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Theories.Phonology.Subregular.ForbidPairs

/-!
# Rose & Walker (2004) @cite{rose-walker-2004}

A Typology of Consonant Agreement as Correspondence. *Language* 80(3):
475–531.

@cite{rose-walker-2004} present a typology of long-distance consonant
agreement (LDCA) — covering nasal, laryngeal, liquid, coronal, and
dorsal harmonies — and analyze it within Optimality Theory using a
correspondence-theoretic apparatus: pairs of similar consonants in the
output stand in a CORR-CC correspondence relation, and IDENT-CC[F]
constraints require corresponding consonants to share the value of
feature [F]. Their architecture predicts that agreement is more likely
between more similar consonants and that intervening dissimilar
material is "neutral" rather than blocking.

## What this file formalizes (and what it does not)

We do **not** formalize Rose & Walker's correspondence apparatus
(CORR-CC, IDENT-CC[F], the similarity-based ranking) — that is a
constraint architecture in OT and lives outside the subregular layer.
What we formalize here is the *surface stringset* of one of their core
case studies — Kikongo nasal harmony, the paper's leading example —
as a tier-based strictly 2-local language, following the
Heinz/Rogers/Hansson subregular tradition (@cite{hansson-2010},
@cite{mcmullin-2016}).

The framing is: Rose & Walker's correspondence analysis *derives* the
surface generalization; the TSL_2 description *characterizes* the
surface stringset that their derivation produces. The two analyses
operate at different levels and are not in competition for the same
explanatory work.

Kikongo nasal harmony is *asymmetric*: the forbidden tier-adjacent pair
is `(nasal, voiced-stop)`, not the reverse. This is a strict instance of
the generic `TSLGrammar.ofForbiddenPairs` constructor and does **not**
factor through either `TSLGrammar.ocp` (`R := (· = ·)`) or
`TSLGrammar.agree` (`R := (· ≠ ·)`); the AGREE specialization captures
*symmetric* harmony (e.g. Navajo sibilant harmony in `Hansson2010.lean`).
The asymmetry here tracks the morphological geometry (stem→suffix
direction), not a feature-symmetric agreement relation.

## Design boundary

Things this formalization is silent on, by design:
1. **Similarity-scaled correspondence**: in ABC, harmony probability
   depends gradiently on featural similarity. The TSL_2 stringset is
   sharp — a pair either is or is not forbidden.
2. **Trigger/target asymmetry**: the OT derivation distinguishes the
   feature *source* from its *target*; the surface phonotactic does
   not.
3. **Transparency vs blocking by similarity**: ABC predicts that
   intervening segments behave differently depending on how similar
   they are to the harmonizing pair. Single-tier TSL with a fixed
   tier predicate cannot express this — see the design-boundary
   docstring on `tierProject` non-monotonicity in `ForbiddenPairs.lean`.
   Cases where transparency *is* similarity-graded (e.g. the
   Sanskrit n-retroflexion pattern Rose & Walker discuss) require
   richer formalisms (multi-tier strictly local; ITSL).

## Kikongo nasal harmony — the paper's leading case

@cite{rose-walker-2004} open with Kikongo (Bantu): a voiced oral stop
in the suffix is realized as a nasal stop when the stem contains a
preceding nasal consonant. For example, the suffix `-idi` alternates
to `-ini` after a nasal. Equivalently, the surface phonotactic is:
**no nasal consonant may be followed at any consonantal distance by a
voiced oral stop within the relevant morphological domain**.

The TSL_2 description: project the harmonizing-class tier (only nasal
consonants and voiced oral stops project; neutral consonants and vowels
are transparent), then forbid any tier-adjacent pair `(C₁, C₂)` where
`C₁` is `[+nasal]` and `C₂` is a voiced oral stop.
-/

namespace Phonology.Studies.RoseWalker2004

open Core Core.Computability.Subregular Phonology.Subregular

-- ============================================================================
-- § 1: A toy Kikongo segmental alphabet
-- ============================================================================

/-- A minimal alphabet sufficient to demonstrate Kikongo nasal harmony as
a TSL_2 stringset. We do **not** model the full Kikongo inventory —
just enough segment classes to distinguish the relevant natural classes
(nasal consonants, voiced oral stops, neutral consonants, vowels). -/
inductive KSeg where
  /-- A nasal consonant ([+nasal, +cons], e.g. /n/, /m/, /ŋ/). -/
  | nasalC
  /-- A voiced oral stop ([+voice, −nasal, +cons, −cont], e.g. /b/, /d/, /g/). -/
  | voicedStop
  /-- A neutral (non-nasal, non-voiced-stop) consonant ([+cons], e.g. /s/, /k/, /t/). -/
  | neutralC
  /-- A vowel ([−cons]) — transparent for nasal harmony. -/
  | vowel
  deriving DecidableEq, Repr

/-- The harmonizing-class tier predicate: nasal consonants and voiced
oral stops are on-tier. Neutral consonants and vowels are transparent
(off-tier). This corresponds to the long-distance reading of the
@cite{rose-walker-2004} typology — only the segments participating in
the agreement form the relevant locality domain. The tier choice is the
substantive theoretical commitment (cf. the design-boundary docstring
on `tierProject` non-monotonicity in `ForbiddenPairs.lean`). -/
@[reducible] def KSeg.onTier : KSeg → Prop
  | .nasalC | .voicedStop => True
  | .neutralC | .vowel => False

instance : DecidablePred KSeg.onTier
  | .nasalC | .voicedStop => isTrue trivial
  | .neutralC | .vowel => isFalse not_false

/-- The forbidden-pair relation: a nasal consonant immediately followed
on the harmonizing-class tier by a voiced oral stop. Asymmetric: the
surface phonotactic emerges from a stem→suffix morphological geometry,
in which only the (nasal stem, voiced-stop suffix) configuration arises.
The reverse order (voiced stop then nasal) is unattested in the
relevant domain rather than independently licit; the asymmetry tracks
the morphological geometry, not a separately stipulated directionality
of agreement. -/
@[reducible] def KSeg.forbidNasalStop : KSeg → KSeg → Prop
  | .nasalC, .voicedStop => True
  | _, _ => False

instance : DecidableRel KSeg.forbidNasalStop
  | .nasalC, .voicedStop => isTrue trivial
  | .nasalC, .nasalC | .nasalC, .neutralC | .nasalC, .vowel
  | .voicedStop, _ | .neutralC, _ | .vowel, _ => isFalse not_false

-- ============================================================================
-- § 2: The TSL_2 grammar
-- ============================================================================

/-- The Kikongo nasal-harmony grammar as a tier-based strictly 2-local
language: project to the harmonizing-class tier (nasals + voiced stops),
forbid `nasalC`-then-`voicedStop` adjacency on the tier. -/
@[reducible] def kikongoNasalHarmony : TSLGrammar 2 KSeg :=
  TSLGrammar.ofForbiddenPairs KSeg.forbidNasalStop KSeg.onTier

-- ============================================================================
-- § 3: Concrete data — pre-harmony vs post-harmony surface forms
-- ============================================================================

/-- A schematic pre-harmony form: a nasal stem consonant followed
(across vowels and a neutral coda) by a voiced oral stop in the suffix.
Illustrates the offending input configuration that Kikongo harmony
resolves; not a verbatim Kikongo lexical item. -/
@[reducible] def preHarmonyNasalStop : List KSeg :=
  [.nasalC, .vowel, .neutralC, .neutralC, .vowel, .voicedStop, .vowel]

/-- The corresponding post-harmony surface form: the suffix voiced stop
has been realized as a nasal. Illustrates the resolved configuration; not
a verbatim Kikongo lexical item. -/
@[reducible] def postHarmonyNasalNasal : List KSeg :=
  [.nasalC, .vowel, .neutralC, .neutralC, .vowel, .nasalC, .vowel]

/-- A schematic control form with no nasal trigger: the voiced stop is
licit because no preceding tier element is `nasalC`. -/
@[reducible] def controlNoTrigger : List KSeg :=
  [.neutralC, .vowel, .neutralC, .vowel, .voicedStop, .vowel]

-- ============================================================================
-- § 4: Theorems — TSL_2 captures the surface phonotactic
-- ============================================================================

/-- The pre-harmony underlying form is **rejected**: it contains a
tier-adjacent `nasalC`-`voicedStop` pair. -/
theorem preHarmonyNasalStop_violates :
    preHarmonyNasalStop ∉ kikongoNasalHarmony.lang := by decide

/-- The post-harmony surface form is **accepted**: every tier-adjacent
pair is licit. -/
theorem postHarmonyNasalNasal_legal :
    postHarmonyNasalNasal ∈ kikongoNasalHarmony.lang := by decide

/-- Forms with no nasal trigger are **accepted** even if they contain
voiced stops — the constraint is conditional on a preceding tier-
adjacent nasal. -/
theorem controlNoTrigger_legal :
    controlNoTrigger ∈ kikongoNasalHarmony.lang := by decide

-- ============================================================================
-- § 5: OT-side bridge — markedness constraint co-extensive with the language
-- ============================================================================

/-- The OT markedness constraint corresponding to the Kikongo nasal-harmony
phonotactic: AGREE-style markedness penalizing each tier-adjacent
`nasalC`-`voicedStop` pair on the harmonizing-class tier. The OT-side
counterpart of `kikongoNasalHarmony` — same forbidden-pair relation,
same tier predicate, packaged as a `NamedConstraint`. The TSL grammar
characterizes the *language*; this constraint *evaluates* it.

This case does *not* use `mkAgreeOnTier` (the symmetric `R := (· ≠ ·)`
specialization) because Kikongo's forbidden pair is asymmetric — see the
"What this file formalizes" docstring above. -/
def kikongoAgree : Constraint.OT.NamedConstraint (List KSeg) :=
  Phonology.Constraints.mkForbidPairsOnTier
    "AGREE-[nas]/CC" KSeg.forbidNasalStop (Tier.byClass KSeg.onTier) id

/-- `kikongoAgree` is a markedness constraint by construction. -/
theorem kikongoAgree_is_markedness :
    kikongoAgree.family = Constraint.OT.ConstraintFamily.markedness :=
  Phonology.Constraints.mkForbidPairsOnTier_is_markedness _ _ _ _

/-- **Bridge**: `kikongoAgree` evaluates to zero on a candidate iff the
candidate is in the TSL_2 language. The "OT-side" and "subregular-side"
characterizations of the same Kikongo phonotactic coincide — making the
co-extensiveness of the two analyses true by construction rather than a
separately-proved equivalence. -/
theorem kikongoAgree_zero_iff_in_TSL (c : List KSeg) :
    kikongoAgree.eval c = 0 ↔ c ∈ kikongoNasalHarmony.lang :=
  mkForbidPairsOnTier_zero_iff_in_lang
    "AGREE-[nas]/CC" KSeg.forbidNasalStop KSeg.onTier id c

end Phonology.Studies.RoseWalker2004
