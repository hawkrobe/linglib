/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Subregular.Sibilant
import Linglib.Phonology.Subregular.Agree
import Linglib.Core.Computability.Subregular.Language.StrictlyPiecewise
import Linglib.Core.Computability.Subregular.Language.Multitier

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

open Subregular Phonology

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

/-- `NSeg`'s sibilant class, grounding the tier predicate in the shared
`Subregular.Sibilant` substrate: the two sibilant series map to `anterior` and
`posterior`, the transparent material (non-sibilant consonants, vowels) to `neutral`. -/
@[reducible] def NSeg.toSibilant : NSeg → Sibilant
  | .antSib => .anterior
  | .postSib => .posterior
  | .neutralC | .vowel => .neutral

/-- The harmonizing-class tier predicate: only sibilants project; non-sibilant
consonants and vowels are transparent (off-tier). Grounded in `Sibilant.onTier`
through `NSeg.toSibilant` rather than re-stipulated, so the tier choice — the
substantive theoretical commitment — lives in one place. -/
@[reducible] def NSeg.onTier (s : NSeg) : Prop := Sibilant.onTier s.toSibilant

instance : DecidablePred NSeg.onTier :=
  fun s => inferInstanceAs (Decidable (Sibilant.onTier s.toSibilant))

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
    Language.IsTierStrictlyLocal 2
      navajoSibilantHarmony.lang :=
  ⟨navajoSibilantHarmony, rfl⟩

/-- **BTSL_2 corollary** (via the PR-4 bridge `IsTierStrictlyLocal.toIsBTSL`
in `Subregular.Multitier`): the Navajo sibilant harmony
stringset lies in the multitier (Boolean) closure of strictly local languages —
immediate from the TSL_2 result. -/
theorem navajoSibilantHarmony_lang_isBTSL2 :
    Language.IsBTSL 2 navajoSibilantHarmony.lang :=
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
def navajoAgree : Constraints.NamedConstraint (List NSeg) :=
  OptimalityTheory.mkAgreeOnTier
    "AGREE-[ant]/CC" (TierProjection.byClass NSeg.onTier) id

/-- `navajoAgree` is a markedness constraint by construction. -/
theorem navajoAgree_is_markedness :
    navajoAgree.family = Constraints.ConstraintFamily.markedness :=
  OptimalityTheory.mkAgreeOnTier_is_markedness _ _ _

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
Navajo's transparent harmony the two classifications coincide on the
surface stringset; the typological argument for TSL ⊃ SP turns on opaque
blockers, which are unattested in Navajo — the rare opaque cases are
Rwanda and Berber ([hansson-2010] ch. 3) — and are not formalised here. -/

/-- The SP_2 grammar for Navajo sibilant harmony: the permitted
length-2 subsequences are everything except mixed-place sibilant pairs.
Note this is a forbidden *subsequence* (non-contiguous), not a
forbidden *factor* (contiguous), so transparency to intervening
material is built in. The grammar is written as a function (rather than a
`{s | ...}` set-builder) so that `Decidable` synthesis sees through to the
underlying decidable equalities on `NSeg` lists. -/
def navajoSibilantHarmonySP : SPGrammar NSeg :=
  fun s => s ≠ [.antSib, .postSib] ∧ s ≠ [.postSib, .antSib]

/-- **Navajo sibilant harmony stringset is SP_2** under the alternative
[mcmullin-2016] characterisation. Explicit `Language.IsStrictlyPiecewise`
typing of the SP_2 grammar's implicit complexity claim. -/
theorem navajoSibilantHarmonySP_lang_isSP2 :
    (navajoSibilantHarmonySP.language 2).IsStrictlyPiecewise 2 :=
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
    w ∈ navajoSibilantHarmonySP.language 2 := by
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
theorem preSiDze_violates_SP : preSiDze ∉ navajoSibilantHarmonySP.language 2 := by
  intro h
  have hwit : List.Sublist [NSeg.antSib, NSeg.postSib] preSiDze := by
    -- preSiDze = [antSib, vowel, postSib, vowel, neutralC]; pick positions 0 and 2.
    refine .cons₂ _ <| .cons _ <| .cons₂ _ <| .cons _ <| .cons _ <| .slnil
  exact (h _ rfl hwit).1 rfl

/-- Post-harmony surface form is accepted by SP_2 too — `postSib`
appears but `antSib` does not, so the forbidden mixed-place
subsequences cannot occur. Direct corollary of the structural helper. -/
theorem postShiDze_legal_SP : postShiDze ∈ navajoSibilantHarmonySP.language 2 :=
  sp_lang_of_one_sibilant_class_absent (.inl (by decide))

/-- Only-anterior control is accepted by SP_2 too — symmetrically,
`antSib` appears but `postSib` does not. -/
theorem controlOnlyAnterior_legal_SP :
    controlOnlyAnterior ∈ navajoSibilantHarmonySP.language 2 :=
  sp_lang_of_one_sibilant_class_absent (.inr (by decide))

/-- No-sibilant control is accepted by SP_2 too — the input has neither
sibilant class, so the structural helper applies trivially. -/
theorem controlNoSibilants_legal_SP :
    controlNoSibilants ∈ navajoSibilantHarmonySP.language 2 :=
  sp_lang_of_one_sibilant_class_absent (.inl (by decide))

end Phonology.Studies.Hansson2010
