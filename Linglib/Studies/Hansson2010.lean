/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Subregular.Agree
import Linglib.Core.Computability.Subregular.StrictlyPiecewise
import Linglib.Core.Computability.Subregular.Multitier

/-!
# Hansson (2010) [hansson-2010]

Consonant Harmony: Long-Distance Interaction in Phonology. *University
of California Publications in Linguistics* 145.

[hansson-2010] surveys ~175 cases of long-distance consonant
agreement across >130 languages, organized by harmonizing property
(coronal/sibilant, dorsal, labial, secondary-articulation, nasal,
liquid, stricture, laryngeal). The formal analysis is a modified
Agreement-by-Correspondence model after [rose-walker-2004], with
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
featured in [hansson-2010]'s introduction (§1.1) and discussed
in detail in §2.4.1.1 — as a tier-based strictly 2-local language,
following the subregular tradition ([mcmullin-2016]).

The framing is the same as in `RoseWalker2004.lean`: the ABC-style
analysis *derives* the surface generalization; the TSL_2 description
*characterizes* the surface stringset. The two analyses operate at
different levels and are not in competition for the same explanatory
work.

Sibilant harmony is a *symmetric* dissimilation-style phonotactic — the
forbidden pair is "tier-adjacent and *unequal*" — so this study is the
canonical instance of the AGREE specialization in
`Phonology/Subregular/Agree.lean`, the non-identity dual of the
OCP ([goldsmith-1976], [mccarthy-1986]). The Kikongo case in
`RoseWalker2004.lean` is *asymmetric* and instantiates the generic
forbidden-pair constructor directly rather than via AGREE.

## Design boundary

Things this formalization is silent on, by design:
1. **Directionality**: [hansson-2010] argues consonant harmony is
   strictly anticipatory (right-to-left). The TSL_2 description with
   symmetric forbidden pairs licenses the surface stringset regardless
   of which segment "triggered" the harmony — the directional
   derivation lives in the OT/ABC layer.
2. **Stem control / trigger-target asymmetry**: the targeted-constraint
   architecture distinguishes the feature source from its target.
   Single-tier TSL with a fixed predicate has no notion of source vs
   target.
3. **Similarity scaling**: in ABC, the CORR-C↔C constraint family is
   scaled by featural similarity and distance ([hansson-2010]
   §4.2.1.1) — only sufficiently similar consonants enter into
   correspondence. The TSL_2 stringset is sharp.
4. **Speech-error parallels (palatal bias)**: [hansson-2010]'s
   chapter 6 argues that consonant harmony has its roots in
   speech-planning errors, with the palatal bias as the central
   diagnostic. This is an extragrammatical claim outside any synchronic
   surface description.
5. **Similarity-graded transparency vs opacity**: [hansson-2010]'s
   chapter 3 reviews cases where intervening segments behave
   differently depending on how similar they are to the harmonizing
   pair. Single-tier TSL with a fixed tier predicate cannot express
   this — see the design-boundary docstring on `tierProject`
   non-monotonicity in `ForbiddenPairs.lean`, and the load-bearing
   gradient-OCP instance in
   `Studies/FrischPierrehumbertBroe2004.lean`,
   which formalises [frisch-pierrehumbert-broe-2004]'s
   natural-classes similarity metric (eq. 7) and proves no
   similarity-threshold TSL_2 grammar can match three Table IV bins.
   Closely related: the autosegmental/feature-geometry tradition
   ([sagey-1986]) treats the harmonizing feature itself as a
   tier-resident object; that representational layer is upstream of
   the surface stringset characterized here.

## Function-level subregular classification (cross-reference)

The TSL_2 description here characterizes the **stringset** of Navajo
sibilant harmony — the language that the harmony filter accepts. The
**function** that maps an underlying form to its surface realization
admits a separate subregular classification per
`Core/Computability/Subregular/Function/`: long-distance consonant
agreement is generally **Tier-Subsequential** (not ISL or OSL — those
require a *contiguous* k-window), and per [hansson-2010]'s
strictly-anticipatory directionality argument it is specifically
**Right-Tier-Subsequential**. We do not encode the function-level
classification here; the language-level TSL_2 statement is the cleaner
unit because the directionality is upstream and the surface filter is
direction-symmetric.

## Navajo sibilant harmony — the leading case

Navajo (Athapaskan; [hansson-2010] §1.1, §2.4.1.1) has two
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
Equivalently, every tier-adjacent pair of sibilants must *agree* in
place — the TSL_2 instance of `TSLGrammar.agree`.
-/

namespace Phonology.Studies.Hansson2010

open Core Core.Computability.Subregular Phonology.Subregular

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
corresponds to the long-distance reading of [hansson-2010]'s
typology — only the segments participating in the agreement form the
relevant locality domain. The tier choice is the substantive theoretical
commitment (cf. the design-boundary docstring on `tierProject`
non-monotonicity in `ForbiddenPairs.lean`). -/
@[reducible] def NSeg.onTier : NSeg → Prop
  | .antSib | .postSib => True
  | .neutralC | .vowel => False

instance : DecidablePred NSeg.onTier
  | .antSib | .postSib => isTrue trivial
  | .neutralC | .vowel => isFalse not_false

-- ============================================================================
-- § 2: The TSL_2 grammar — instance of the AGREE specialization
-- ============================================================================

/-- The Navajo sibilant-harmony grammar as a tier-based strictly 2-local
language: project to the sibilant tier (anterior + posterior sibilants),
forbid any tier-adjacent disagreeing pair. Symmetric forbidden-pair
relation = `(· ≠ ·)` restricted to on-tier elements, so the grammar is
exactly the AGREE specialization `TSLGrammar.agree NSeg.onTier`. -/
@[reducible] def navajoSibilantHarmony : TSLGrammar 2 NSeg :=
  TSLGrammar.agree NSeg.onTier

-- ============================================================================
-- § 3: Concrete data — pre-harmony vs post-harmony surface forms
-- ============================================================================

/-- A pre-harmony underlying form analogous to /si-dʒéːʔ/: an anterior
sibilant prefix preceding a postalveolar sibilant in the root, across
an intervening vowel. The two disagreeing sibilants are tier-adjacent
under the sibilant projection. -/
@[reducible] def preSiDze : List NSeg :=
  [.antSib, .vowel, .postSib, .vowel, .neutralC]

/-- The post-harmony surface form analogous to [ʃidʒéːʔ]: the prefix
sibilant has been realized as postalveolar to agree with the root. -/
@[reducible] def postShiDze : List NSeg :=
  [.postSib, .vowel, .postSib, .vowel, .neutralC]

/-- A control form analogous to [sisná]: only anterior sibilants in the
word, with intervening vowels and a non-sibilant consonant. -/
@[reducible] def controlOnlyAnterior : List NSeg :=
  [.antSib, .vowel, .antSib, .neutralC, .vowel]

/-- A control form with no sibilants at all — vacuously legal, since the
tier projection is empty. -/
@[reducible] def controlNoSibilants : List NSeg :=
  [.neutralC, .vowel, .neutralC, .vowel, .neutralC]

-- ============================================================================
-- § 4: Theorems — TSL_2 captures the surface phonotactic
-- ============================================================================

/-- **Navajo sibilant harmony stringset is TSL_2** (Hansson 2010 §2.4.1.1).
Explicit `IsTierStrictlyLocal 2` typing of the implicit complexity claim
made by the `navajoSibilantHarmony : TSLGrammar 2 NSeg` grammar — the
co-extensiveness of "the surface phonotactic" and "TSL_2 stringset" was
asserted in the file docstring; this theorem types that assertion. -/
theorem navajoSibilantHarmony_lang_isTSL2 :
    Core.Computability.Subregular.IsTierStrictlyLocal 2
      navajoSibilantHarmony.lang :=
  ⟨navajoSibilantHarmony, rfl⟩

/-- **BTSL_2 corollary** (via the PR-4 bridge `IsTierStrictlyLocal.toIsBTSL`
in `Core.Computability.Subregular.Multitier`): the Navajo sibilant
harmony stringset is in the multitier closure of strictly local
languages. Hands the [lambert-2026] BTC framework a Hansson-data
consumer without re-proving anything. -/
theorem navajoSibilantHarmony_lang_isBTSL2 :
    Core.Computability.Subregular.IsBTSL 2 navajoSibilantHarmony.lang :=
  navajoSibilantHarmony_lang_isTSL2.toIsBTSL

/-- The pre-harmony underlying form is **rejected**: it contains a
tier-adjacent disagreeing-sibilant pair. -/
theorem preSiDze_violates : preSiDze ∉ navajoSibilantHarmony.lang := by
  unfold navajoSibilantHarmony TSLGrammar.agree; decide

/-- The post-harmony surface form is **accepted**: every tier-adjacent
sibilant pair agrees in place. -/
theorem postShiDze_legal : postShiDze ∈ navajoSibilantHarmony.lang := by
  unfold navajoSibilantHarmony TSLGrammar.agree; decide

/-- A form with only anterior sibilants is **accepted** — the AGREE
constraint forbids disagreement, not co-occurrence. -/
theorem controlOnlyAnterior_legal :
    controlOnlyAnterior ∈ navajoSibilantHarmony.lang := by
  unfold navajoSibilantHarmony TSLGrammar.agree; decide

/-- Forms with no sibilants are vacuously accepted — the tier projection
is empty, so there are no tier-adjacent pairs to check. -/
theorem controlNoSibilants_legal :
    controlNoSibilants ∈ navajoSibilantHarmony.lang := by
  unfold navajoSibilantHarmony TSLGrammar.agree; decide

-- ============================================================================
-- § 5: OT-side bridge — markedness constraint co-extensive with the language
-- ============================================================================

/-- The OT markedness constraint corresponding to the Navajo
sibilant-harmony phonotactic: AGREE-style markedness penalizing each
tier-adjacent disagreeing sibilant pair on the sibilant tier. The OT-side
counterpart of `navajoSibilantHarmony` — same tier predicate, packaged as
a `NamedConstraint` via the `mkAgreeOnTier` specialization. The TSL
grammar characterizes the *language*; this constraint *evaluates* it. -/
def navajoAgree : Phonology.Constraint.OT.NamedConstraint (List NSeg) :=
  Phonology.Constraints.mkAgreeOnTier
    "AGREE-[ant]/CC" (Tier.byClass NSeg.onTier) id

/-- `navajoAgree` is a markedness constraint by construction. -/
theorem navajoAgree_is_markedness :
    navajoAgree.family = Phonology.Constraint.OT.ConstraintFamily.markedness :=
  Phonology.Constraints.mkAgreeOnTier_is_markedness _ _ _

/-- **Bridge**: `navajoAgree` evaluates to zero on a candidate iff the
candidate is in the TSL_2 language. The "OT-side" and "subregular-side"
characterizations of the same Navajo phonotactic coincide — making the
co-extensiveness of the two analyses true by construction rather than a
separately-proved equivalence. -/
theorem navajoAgree_zero_iff_in_TSL (c : List NSeg) :
    navajoAgree.eval c = 0 ↔ c ∈ navajoSibilantHarmony.lang :=
  mkAgreeOnTier_zero_iff_in_agree_lang "AGREE-[ant]/CC" NSeg.onTier id c

-- ============================================================================
-- § 6: SP_2 vs TSL_2 — cross-framework comparison (after [mcmullin-2016])
-- ============================================================================

/-! ### § 6.1 The SP_2 formalisation of Navajo

The same long-distance phonotactic — *no anterior+posterior sibilant
co-occurrence* — admits a strictly piecewise (SP_2) characterisation
that uses *subsequences* (non-contiguous selections) rather than tier
projection. The SP_2 grammar forbids the length-2 subsequences
`[antSib, postSib]` and `[postSib, antSib]`; intervening material is
invisible by construction (subsequences ignore position). This
naturally captures *transparent* harmony — exactly Navajo's profile.

[mcmullin-2016] argues that consonant harmony in general requires
TSL_2, not SP_2: SP cannot model **blocker-style opacity** (where a
specific intervening consonant breaks long-distance harmony). For
Navajo's transparent harmony, the two classifications coincide on the
surface stringset; the typological argument for TSL ⊃ SP shows up only
when the alphabet admits an opaque blocker (§6.3 below). -/

/-- The SP_2 grammar for Navajo sibilant harmony: the permitted
length-2 subsequences are everything except mixed-place sibilant pairs.
Note this is a forbidden *subsequence* (non-contiguous), not a
forbidden *factor* (contiguous), so transparency to intervening
material is built in. The `permitted` field is given as a function
(rather than `{s | ...}` set-builder) so that `Decidable` synthesis sees
through to the underlying decidable equalities on `NSeg` lists. -/
def navajoSibilantHarmonySP : SPGrammar 2 NSeg where
  permitted s := s ≠ [.antSib, .postSib] ∧ s ≠ [.postSib, .antSib]

/-- **Navajo sibilant harmony stringset is SP_2** under the alternative
[mcmullin-2016] characterisation. Explicit `IsStrictlyPiecewise 2`
typing of the SP_2 grammar's implicit complexity claim. -/
theorem navajoSibilantHarmonySP_lang_isSP2 :
    Core.Computability.Subregular.IsStrictlyPiecewise 2
      navajoSibilantHarmonySP.lang :=
  ⟨navajoSibilantHarmonySP, rfl⟩

/-! ### § 6.2 Agreement on Navajo's transparent inputs

On the canonical Navajo inputs introduced in §3, the TSL_2 and SP_2
analyses make the same accept/reject prediction. The structural reason
is captured by `sp_lang_of_one_sibilant_class_absent`: any input
lacking either sibilant class is in the SP-harmony language, since no
length-2 sublist can be the forbidden mixed-place pair. -/

/-- Both elements of a length-2 sublist of `w` are members of `w`. -/
private lemma _pair_mem_of_sublist {α : Type*} {w : List α} {a b : α}
    (hsub : List.Sublist [a, b] w) : a ∈ w ∧ b ∈ w :=
  ⟨hsub.mem (List.mem_cons_self),
   hsub.mem (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- **Structural agreement helper**: any input lacking either anterior
or posterior sibilants is in the SP_2 sibilant-harmony language. The
forbidden subsequences `[antSib, postSib]` and `[postSib, antSib]` both
require *both* sibilant classes, so the absence of either suffices. -/
theorem sp_lang_of_one_sibilant_class_absent {w : List NSeg}
    (h : NSeg.antSib ∉ w ∨ NSeg.postSib ∉ w) :
    w ∈ navajoSibilantHarmonySP.lang := by
  intro s _ hsub
  refine ⟨?_, ?_⟩ <;> intro heq <;> subst heq <;>
    rcases h with hAnt | hPost
  · exact hAnt (_pair_mem_of_sublist hsub).1
  · exact hPost (_pair_mem_of_sublist hsub).2
  · exact hAnt (_pair_mem_of_sublist hsub).2
  · exact hPost (_pair_mem_of_sublist hsub).1

/-- Pre-harmony underlying form is rejected by SP_2 too — the
mixed-place subsequence `[antSib, postSib]` is present at positions
0 and 2 (separated by a vowel), violating the forbidden-subsequence
ban. The witness is exhibited explicitly. -/
theorem preSiDze_violates_SP : preSiDze ∉ navajoSibilantHarmonySP.lang := by
  intro h
  have hwit : List.Sublist [NSeg.antSib, NSeg.postSib] preSiDze := by
    -- preSiDze = [antSib, vowel, postSib, vowel, neutralC]; pick positions 0 and 2.
    refine .cons₂ _ <| .cons _ <| .cons₂ _ <| .cons _ <| .cons _ <| .slnil
  exact (h _ rfl hwit).1 rfl

/-- Post-harmony surface form is accepted by SP_2 too — `postSib`
appears but `antSib` does not, so the forbidden mixed-place
subsequences cannot occur. Direct corollary of the structural helper. -/
theorem postShiDze_legal_SP : postShiDze ∈ navajoSibilantHarmonySP.lang :=
  sp_lang_of_one_sibilant_class_absent (.inl (by decide))

/-- Only-anterior control is accepted by SP_2 too — symmetrically,
`antSib` appears but `postSib` does not. -/
theorem controlOnlyAnterior_legal_SP :
    controlOnlyAnterior ∈ navajoSibilantHarmonySP.lang :=
  sp_lang_of_one_sibilant_class_absent (.inr (by decide))

/-- No-sibilant control is accepted by SP_2 too — the input has neither
sibilant class, so the structural helper applies trivially. -/
theorem controlNoSibilants_legal_SP :
    controlNoSibilants ∈ navajoSibilantHarmonySP.lang :=
  sp_lang_of_one_sibilant_class_absent (.inl (by decide))

/-! ### § 6.3 Where the two diverge: blocker-style opacity

The agreement above is a property of *Navajo*, not of TSL_2 vs SP_2 in
general. To make the predictive divergence visible we extend the
alphabet with an **opaque blocker** segment — a non-sibilant consonant
that, in some hypothetical opaque harmony, projects to the sibilant
tier and disagrees with both sibilant series. With the blocker on the
TSL tier, TSL_2 rejects the input `[antSib, blocker, antSib]` (the
tier-adjacent (antSib, blocker) pair disagrees), while SP_2 accepts it
(no mixed-place sibilant subsequence is present). This is the
typological force of [mcmullin-2016]: SP_2 cannot express
blocker-style opacity at all, regardless of the choice of forbidden
subsequence — a point that, for Navajo specifically, is moot but for
the broader class of consonant-harmony systems is decisive. -/

/-- Extended alphabet with an opaque blocker. Used only in §6.3 to
witness the TSL_2 vs SP_2 divergence — not part of the Navajo
empirical formalisation in §1–§5. -/
inductive NSegB where
  | antSib | postSib | blocker | neutral
  deriving DecidableEq, Repr

/-- Tier predicate for the *opaque-harmony* TSL_2 instance: the blocker
projects to the sibilant tier alongside the two sibilant series. With
AGREE this rejects any tier-adjacent disagreement, including
sibilant–blocker pairs. -/
@[reducible] def NSegB.onTierWithBlocker : NSegB → Prop
  | .antSib | .postSib | .blocker => True
  | .neutral => False

instance : DecidablePred NSegB.onTierWithBlocker
  | .antSib | .postSib | .blocker => isTrue trivial
  | .neutral => isFalse not_false

/-- The TSL_2 grammar with the blocker on the sibilant tier — the
naïve formalisation of opaque consonant harmony in TSL terms. -/
@[reducible] def opaqueHarmonyTSL : TSLGrammar 2 NSegB :=
  TSLGrammar.agree NSegB.onTierWithBlocker

/-- The SP_2 grammar with the same forbidden mixed-sibilant
subsequences — the SP analysis is unchanged when the alphabet is
extended, since the blocker is not part of the forbidden subsequences. -/
def opaqueHarmonySP : SPGrammar 2 NSegB where
  permitted s := s ≠ [.antSib, .postSib] ∧ s ≠ [.postSib, .antSib]

/-- Same structural agreement helper as in §6.2, transported to the
extended alphabet `NSegB`: any input lacking either sibilant class is
in `opaqueHarmonySP.lang` regardless of how many blockers it contains. -/
theorem opaqueSP_lang_of_one_sibilant_class_absent {w : List NSegB}
    (h : NSegB.antSib ∉ w ∨ NSegB.postSib ∉ w) :
    w ∈ opaqueHarmonySP.lang := by
  intro s _ hsub
  refine ⟨?_, ?_⟩ <;> intro heq <;> subst heq <;>
    rcases h with hAnt | hPost
  · exact hAnt (_pair_mem_of_sublist hsub).1
  · exact hPost (_pair_mem_of_sublist hsub).2
  · exact hAnt (_pair_mem_of_sublist hsub).2
  · exact hPost (_pair_mem_of_sublist hsub).1

/-- **Cross-framework divergence** (after [mcmullin-2016]): on the
input `[antSib, blocker, antSib]` (an opaque-blocker configuration with
two same-place sibilants), the TSL_2 grammar with the blocker on the
sibilant tier *rejects*, while the SP_2 grammar *accepts*. SP cannot
express blocker-style opacity — there is no choice of forbidden
length-2 subsequence that would reject this input without also
rejecting transparent same-place sibilant pairs like `[antSib, antSib]`.
This is the typological force of McMullin's TSL ⊃ SP claim for
consonant harmony.

The TSL rejection is structural: the input is fully on-tier (all three
symbols project), so its filter is itself; tier-adjacent pair
`(antSib, blocker)` disagrees, breaking the `IsChain (· = ·)` predicate
required for membership. The SP acceptance falls out of
`opaqueSP_lang_of_one_sibilant_class_absent` since `postSib` is absent. -/
theorem TSL_SP_divergence_on_blocker :
    [NSegB.antSib, .blocker, .antSib] ∉ opaqueHarmonyTSL.lang ∧
    [NSegB.antSib, .blocker, .antSib] ∈ opaqueHarmonySP.lang := by
  refine ⟨?_, ?_⟩
  · -- TSL rejects: the on-tier filter is the input itself, and the
    -- tier-adjacent (antSib, blocker) pair disagrees.
    intro hmem
    have hchain := (mem_ofForbiddenPairs_lang_iff_filter_isChain
      (α := NSegB) (· ≠ ·) NSegB.onTierWithBlocker
      [NSegB.antSib, .blocker, .antSib]).mp hmem
    have hfilter :
        ([NSegB.antSib, .blocker, .antSib] : List NSegB).filter
          (fun x => decide (NSegB.onTierWithBlocker x)) =
        [NSegB.antSib, .blocker, .antSib] := by
      decide
    rw [hfilter, List.isChain_cons_cons] at hchain
    exact hchain.1 (by decide)
  · -- SP accepts: postSib does not appear in the input.
    exact opaqueSP_lang_of_one_sibilant_class_absent (.inr (by decide))

end Phonology.Studies.Hansson2010
