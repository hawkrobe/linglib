/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.ForbiddenPairs
import Linglib.Theories.Phonology.Subregular.ForbidPairs

/-!
# Hansson (2010) @cite{hansson-2010}

Consonant Harmony: Long-Distance Interaction in Phonology. *University
of California Publications in Linguistics* 145.

@cite{hansson-2010} surveys ~175 cases of long-distance consonant
agreement across >130 languages, organized by harmonizing property
(coronal/sibilant, dorsal, labial, secondary-articulation, nasal,
liquid, stricture, laryngeal). The formal analysis is a modified
Agreement-by-Correspondence model after @cite{rose-walker-2004}, with
two theoretical refinements: (a) C-C correspondence is construed as
directionally asymmetric (strictly anticipatory), and (b) the relevant
agreement constraints are formulated as *targeted* constraints in the
Wilson sense.

## What this file formalizes (and what it does not)

We do **not** formalize Hansson's correspondence apparatus, his
targeted-constraint architecture, or his speech-error / palatal-bias
arguments — those live in the OT layer and the speech-planning
literature. What we formalize here is the *surface stringset* of one
of the leading case studies — Navajo sibilant harmony, prominently
featured in @cite{hansson-2010}'s introduction (§1.1) and discussed
in detail in §2.4.1.1 — as a tier-based strictly 2-local language,
following the subregular tradition (@cite{mcmullin-2016}).

The framing is the same as in `RoseWalker2004.lean`: the ABC-style
analysis *derives* the surface generalization; the TSL_2 description
*characterizes* the surface stringset. The two analyses operate at
different levels and are not in competition for the same explanatory
work.

## Design boundary

Things this formalization is silent on, by design:
1. **Directionality**: @cite{hansson-2010} argues consonant harmony is
   strictly anticipatory (right-to-left). The TSL_2 description with
   symmetric forbidden pairs licenses the surface stringset regardless
   of which segment "triggered" the harmony — the directional
   derivation lives in the OT/ABC layer.
2. **Stem control / trigger-target asymmetry**: the targeted-constraint
   architecture distinguishes the feature source from its target.
   Single-tier TSL with a fixed predicate has no notion of source vs
   target.
3. **Similarity scaling**: in ABC, the CORR-C↔C constraint family is
   scaled by featural similarity and distance (@cite{hansson-2010}
   §4.2.1.1) — only sufficiently similar consonants enter into
   correspondence. The TSL_2 stringset is sharp.
4. **Speech-error parallels (palatal bias)**: @cite{hansson-2010}'s
   chapter 6 argues that consonant harmony has its roots in
   speech-planning errors, with the palatal bias as the central
   diagnostic. This is an extragrammatical claim outside any synchronic
   surface description.
5. **Similarity-graded transparency vs opacity**: @cite{hansson-2010}'s
   chapter 3 reviews cases where intervening segments behave
   differently depending on how similar they are to the harmonizing
   pair. Single-tier TSL with a fixed tier predicate cannot express
   this — see the design-boundary docstring on `tierProject`
   non-monotonicity in `ForbiddenPairs.lean`, and the connection there
   to gradient consonant harmony (@cite{frisch-pierrehumbert-broe-2004}).
   Closely related: the autosegmental/feature-geometry tradition
   (@cite{sagey-1986}) treats the harmonizing feature itself as a
   tier-resident object; that representational layer is upstream of
   the surface stringset characterized here.

## Navajo sibilant harmony — the leading case

Navajo (Athapaskan; @cite{hansson-2010} §1.1, §2.4.1.1) has two
contrasting sibilant series: an alveolar series {s, z, ts, tsʼ, dz}
and a postalveolar series {ʃ, ʒ, tʃ, tʃʼ, dʒ}. A sibilant in the
verb root determines the realization of all sibilants in preceding
"conjunct" prefixes. For example (data from McDonough 1991, cited
as Hansson's example (6)): underlying /si-dʒéːʔ/ surfaces as
[ʃidʒéːʔ] 'they lie (slender stiff objects)' — the alveolar /s/ in
the prefix harmonizes to the postalveolar place of the root /dʒ/;
underlying /ʃ-is-ná/ surfaces as [sisná] 'he carried me' — the
postalveolar /ʃ/ in the prefix harmonizes to the alveolar place of
the root /s/.

The surface generalization: **no two sibilants of differing place
(anterior vs posterior) may co-occur within the harmonic domain**.

The TSL_2 description: project the sibilant tier (other consonants and
vowels are transparent), then forbid any tier-adjacent pair drawn
from different sibilant series.
-/

namespace Phonology.Studies.Hansson2010

open Core.Computability.Subregular

-- ============================================================================
-- § 1: A toy Navajo segmental alphabet
-- ============================================================================

/-- A minimal alphabet sufficient to demonstrate Navajo sibilant harmony as
a TSL_2 stringset. We do **not** model the full Navajo inventory — just
enough segment classes to distinguish the relevant natural classes (the
two sibilant series, non-sibilant consonants, vowels). -/
inductive NSeg where
  /-- An anterior (alveolar) sibilant: /s, z, ts, tsʼ, dz/. -/
  | antSib
  /-- A posterior (postalveolar) sibilant: /ʃ, ʒ, tʃ, tʃʼ, dʒ/. -/
  | postSib
  /-- A non-sibilant consonant — transparent for sibilant harmony. -/
  | neutralC
  /-- A vowel — transparent for sibilant harmony. -/
  | vowel
  deriving DecidableEq, Repr

/-- The harmonizing-class tier predicate: only sibilants project. Non-
sibilant consonants and vowels are transparent (off-tier). This
corresponds to the long-distance reading of @cite{hansson-2010}'s
typology — only the segments participating in the agreement form the
relevant locality domain. The tier choice is the substantive theoretical
commitment (cf. the design-boundary docstring on `tierProject`
non-monotonicity in `ForbiddenPairs.lean`). -/
def NSeg.onTier : NSeg → Prop
  | .antSib | .postSib => True
  | .neutralC | .vowel => False

instance : DecidablePred NSeg.onTier := fun s => by
  cases s <;> unfold NSeg.onTier <;> infer_instance

/-- The forbidden-pair relation: two tier-adjacent sibilants drawn from
different series. Symmetric — both `(antSib, postSib)` and
`(postSib, antSib)` are forbidden, since the surface phonotactic does
not distinguish trigger from target. The directional asymmetry that
@cite{hansson-2010} argues for (anticipatory derivation) is an OT-layer
claim about *how* a violating pair gets resolved, not about *which*
strings are licit. -/
def NSeg.forbidDisagreement : NSeg → NSeg → Prop
  | .antSib, .postSib => True
  | .postSib, .antSib => True
  | _, _ => False

instance : DecidableRel NSeg.forbidDisagreement := fun a b => by
  cases a <;> cases b <;> unfold NSeg.forbidDisagreement <;> infer_instance

-- ============================================================================
-- § 2: The TSL_2 grammar
-- ============================================================================

/-- The Navajo sibilant-harmony grammar as a tier-based strictly 2-local
language: project to the sibilant tier (anterior + posterior sibilants),
forbid any tier-adjacent disagreeing pair. -/
def navajoSibilantHarmony : TSLGrammar 2 NSeg :=
  TSLGrammar.ofForbiddenPairs NSeg.forbidDisagreement NSeg.onTier

-- ============================================================================
-- § 3: Concrete data — pre-harmony vs post-harmony surface forms
-- ============================================================================

/-- A pre-harmony underlying form analogous to /si-dʒéːʔ/: an anterior
sibilant prefix preceding a postalveolar sibilant in the root, across
an intervening vowel. The two disagreeing sibilants are tier-adjacent
under the sibilant projection. -/
def preSiDze : List NSeg :=
  [.antSib, .vowel, .postSib, .vowel, .neutralC]

/-- The post-harmony surface form analogous to [ʃidʒéːʔ]: the prefix
sibilant has been realized as postalveolar to agree with the root. -/
def postShiDze : List NSeg :=
  [.postSib, .vowel, .postSib, .vowel, .neutralC]

/-- A control form analogous to [sisná]: only anterior sibilants in the
word, with intervening vowels and a non-sibilant consonant. -/
def controlOnlyAnterior : List NSeg :=
  [.antSib, .vowel, .antSib, .neutralC, .vowel]

/-- A control form with no sibilants at all — vacuously legal, since the
tier projection is empty. -/
def controlNoSibilants : List NSeg :=
  [.neutralC, .vowel, .neutralC, .vowel, .neutralC]

-- ============================================================================
-- § 4: Theorems — TSL_2 captures the surface phonotactic
-- ============================================================================

/-- The pre-harmony underlying form is **rejected** by the surface
grammar: it contains a tier-adjacent `antSib`-`postSib` pair.
Closed by the `decidableMemOfForbiddenPairsLang` instance. -/
theorem preSiDze_violates :
    preSiDze ∉ navajoSibilantHarmony.lang := by
  unfold navajoSibilantHarmony preSiDze; decide

/-- The post-harmony surface form is **accepted**: every tier-adjacent
sibilant pair agrees in place. -/
theorem postShiDze_legal :
    postShiDze ∈ navajoSibilantHarmony.lang := by
  unfold navajoSibilantHarmony postShiDze; decide

/-- A form with only anterior sibilants is **accepted** — the constraint
forbids disagreement, not co-occurrence. -/
theorem controlOnlyAnterior_legal :
    controlOnlyAnterior ∈ navajoSibilantHarmony.lang := by
  unfold navajoSibilantHarmony controlOnlyAnterior; decide

/-- Forms with no sibilants are vacuously accepted — the tier projection
is empty, so there are no tier-adjacent pairs to check. -/
theorem controlNoSibilants_legal :
    controlNoSibilants ∈ navajoSibilantHarmony.lang := by
  unfold navajoSibilantHarmony controlNoSibilants; decide

-- ============================================================================
-- § 5: OT-side bridge — markedness constraint co-extensive with the language
-- ============================================================================

open Core

/-- The OT markedness constraint corresponding to the Navajo
sibilant-harmony phonotactic: AGREE-style markedness penalizing each
tier-adjacent disagreeing sibilant pair on the sibilant tier. The OT-side
counterpart of `navajoSibilantHarmony` — same forbidden-pair relation,
same tier predicate, packaged as a `NamedConstraint`. The TSL grammar
characterizes the *language*; this constraint *evaluates* it. -/
def navajoAgreeAntCC : Core.Constraint.OT.NamedConstraint (List NSeg) :=
  Phonology.Constraints.mkForbidPairsOnTier
    "AGREE-[ant]/CC" NSeg.forbidDisagreement (Tier.byClass NSeg.onTier) id

/-- The AGREE constraint is a markedness constraint by construction. -/
theorem navajoAgreeAntCC_is_markedness :
    navajoAgreeAntCC.family = Core.Constraint.OT.ConstraintFamily.markedness :=
  Phonology.Constraints.mkForbidPairsOnTier_is_markedness _ _ _ _

/-- **Bridge**: `navajoAgreeAntCC` evaluates to zero on a candidate iff
the candidate is in the TSL_2 language. The "OT-side" and
"subregular-side" characterizations of the same Navajo phonotactic
coincide — making the co-extensiveness of the two analyses true by
construction rather than a separately-proved equivalence. -/
theorem navajoAgreeAntCC_zero_iff_in_TSL (c : List NSeg) :
    navajoAgreeAntCC.eval c = 0 ↔ c ∈ navajoSibilantHarmony.lang :=
  Phonology.Subregular.mkForbidPairsOnTier_zero_iff_in_lang
    "AGREE-[ant]/CC" NSeg.forbidDisagreement NSeg.onTier id c

end Phonology.Studies.Hansson2010
