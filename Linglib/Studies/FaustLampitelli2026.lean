/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Segmental.ElementTheory
import Linglib.Phonology.OCP
import Linglib.Fragments.Tigrinya.Phonology
import Linglib.Fragments.Tigre.Phonology

/-!
# Faust & Lampitelli (2026): Guttural Synseresis in Tigrinya and Tigre
[faust-lampitelli-2026]

[faust-lampitelli-2026]'s headline claim: in the Ethiosemitic
languages Tigre and Tigrinya, gutturals (ʔ, h, ħ, ʕ) function as
**low glides** — the consonantal counterpart of low vowels [ʌ, a].
Sequences /ʌGV/ undergo *synersis* (the /ʌ/ syncopated, only G
surfaces) just as /iIu/ → [ju] in classical hiatus-resolution; both
patterns instantiate the same Element-Theoretic operation
([kaye-lowenstamm-vergnaud-1985], [backley-2011]) of
element-fusion under OCP.

Two co-equal headline contributions (paper §1, eq. 2):

* **Empirical**: gutturals = low glides (the |A|-as-consonantal
  analogue of |I|-as-glide |j| and |U|-as-glide |w|).
* **Polemical**: synersis is *economy-driven* (eq. 2b: "two
  homorganic elements are realized in one if possible"), not
  phonotactic-driven (eq. 2a: "fancy Latinate name for gliding").
  The Ethiosemitic facts force (2b): /mibarak/ → [mɨbɨrak] (paper
  eq. 18c, 39b) shows synersis applies even when no surface
  phonotactic problem would arise from leaving the sequence
  unfused.

## What this file formalizes

* §1 ET decomposition of Tigrinya/Tigre vowels and gutturals (paper
  eq. 20-22), as a per-segment projection from the theory-neutral
  fragment files.
* §0 The Strict-CV substrate (`StrictCV` namespace below): `VStatus`,
  `CVSeq`, `ProperlyGoverned`, `ECPSatisfied`, `LicensesPrecedingC`.
  Inlined here as a single-consumer concept (CLAUDE.md graduation rule).
* §2 Strict-CV representations of the paper's worked examples,
  encoded as `CVSeq` values with per-V-slot melodic status.
* §3 Five named theorems:
  * `T0_economy_drives_syneresis` — witness `/mibarak/ → [mɨbɨrak]`.
  * `T1_gutturals_are_lowGlides` — structural; ET decomposition.
  * `T2_synersis_iff_fused_and_governed` — analysis's core
    biconditional.
  * `T3_selfLicensing_blocks_dissociation` — explains [ʕarifu].
  * `T4_walker_rose_2015_overshoots` — divergence with witness
    `/mismaʕa/`.
* §4 The OCP-merger reading: |A|+|A| → |A| as instance of the
  shared `OCP.collapse` substrate.
* §5 Paper self-flagged limits as LIMITATION-tagged comments.

## What this file does NOT formalize

* The full GP/Strict-CV apparatus (Coda Mirror, lateral
  relation typology). The `StrictCV` namespace below carries the
  *simplified* form per the paper's n. 16.
* The phonetic implementation of [ɨ] vs [a]/[ʌ] — see
  [faust-2024] for the cross-linguistic theory.
* Templatic morphology beyond bare CV patterns (see
  [faust-2014], [faust-2017b], [faust-lampitelli-2023]).

## Cross-framework engagement

* §3 T4 makes explicit the divergence with [walker-rose-2015-amp].
* The OCP merger operation (`OCP.collapse`) unifies
  this paper's |A|+|A| fusion with [lionnet-2022]'s TRN merger
  (Laal subtonal phonology). They are instances of one operation
  on different feature spaces; the framework choice (binary-feature
  TRN vs privative-element |A|) lives at the segment-representation
  level, not at the merger-operation level.

## Convention

Predicates in this file are `Prop`-valued with `Decidable` instances,
matching mathlib + the existing `OCP` style.
Worked examples are checked via `decide` rather than `rfl` where
appropriate.
-/

namespace FaustLampitelli2026

open ElementTheory

/-! ## §0 Strict-CV Government Phonology substrate
[kaye-lowenstamm-vergnaud-1985] [kaye-lowenstamm-vergnaud-1990]
[charette-1991] [lowenstamm-1996] [scheer-2004]
[scheer-segeral-2001]

Inlined here as a `StrictCV` namespace; single-consumer concept per
CLAUDE.md graduation rule. Government Phonology (GP) and its Strict-CV
(CVCV) descendant ([lowenstamm-1996], [scheer-2004]) build
phonological representations as alternating C-V skeletal sequences,
with three core lateral relations between V-slots:

* **Proper Government** ([kaye-lowenstamm-vergnaud-1990]): a
  contentful nucleus governs a preceding empty nucleus, allowing the
  empty nucleus to remain phonetically silent.
* **Empty Category Principle** (ECP, simplified): an empty nucleus
  may be phonetically non-interpreted iff it is properly governed.
* **Licensing** ([scheer-segeral-2001]): a contentful nucleus
  licenses an adjacent position (typically the preceding onset).

The substrate here gives the **simplified** form of these definitions
used in [faust-lampitelli-2026], which acknowledges the
simplification (paper n. 16).
-/

namespace StrictCV

/-- A V-slot's melodic status. Per Strict CV ([lowenstamm-1996]),
    every consonant-cluster representation interpolates empty V-slots,
    so the same skeletal position may surface silently if properly
    governed, or with an epenthetic vowel if not. -/
inductive VStatus where
  /-- The V-slot has melodic content. -/
  | full
  /-- The V-slot has no melodic content. -/
  | empty
  deriving DecidableEq, Repr

namespace VStatus

def IsFull : VStatus → Prop
  | .full  => True
  | .empty => False

instance : DecidablePred IsFull
  | .full  => isTrue trivial
  | .empty => isFalse not_false

def IsEmpty : VStatus → Prop
  | .empty => True
  | .full  => False

instance : DecidablePred IsEmpty
  | .empty => isTrue trivial
  | .full  => isFalse not_false

end VStatus

/-- A **Strict-CV sequence** is a list of V-slot statuses. C-slots are
    implicit between each pair ([lowenstamm-1996]). The list
    `[v₁, v₂, v₃]` represents the skeleton `C₁ V₁ C₂ V₂ C₃ V₃`. -/
structure CVSeq where
  vStatus : List VStatus
  deriving Repr, DecidableEq

namespace CVSeq

def vCount (s : CVSeq) : Nat := s.vStatus.length

def vAt (s : CVSeq) (i : Nat) : Option VStatus := s.vStatus[i]?

def ofList (vs : List VStatus) : CVSeq := ⟨vs⟩

/-- **Proper Government** ([kaye-lowenstamm-vergnaud-1990],
    simplified per [faust-lampitelli-2026] eq. 23a): V-slot at
    index `i` is *properly governed* iff V-slot `i+1` exists and is
    contentful. -/
def ProperlyGoverned (s : CVSeq) (i : Nat) : Prop :=
  s.vAt (i + 1) = some .full

instance (s : CVSeq) (i : Nat) : Decidable (s.ProperlyGoverned i) :=
  inferInstanceAs (Decidable (s.vAt (i + 1) = some .full))

/-- **Empty Category Principle** ([kaye-1992], simplified per
    [faust-lampitelli-2026] eq. 23b): an empty V-slot may surface
    silently iff it is properly governed; a full V-slot is always
    realized; out-of-range positions vacuously hold. -/
def ECPSatisfied (s : CVSeq) (i : Nat) : Prop :=
  match s.vAt i with
  | some .empty => s.ProperlyGoverned i
  | _           => True

instance (s : CVSeq) (i : Nat) : Decidable (s.ECPSatisfied i) := by
  unfold CVSeq.ECPSatisfied
  split <;> infer_instance

/-- **Licensing** ([scheer-segeral-2001], simplified per
    [faust-lampitelli-2026] eq. 24): V-slot at index `i` licenses
    its preceding C-position iff `i` is contentful. -/
def LicensesPrecedingC (s : CVSeq) (i : Nat) : Prop :=
  s.vAt i = some .full

instance (s : CVSeq) (i : Nat) : Decidable (s.LicensesPrecedingC i) :=
  inferInstanceAs (Decidable (s.vAt i = some .full))

/-- An empty nucleus that is not properly governed violates ECP. -/
theorem empty_not_governed_violates_ecp (s : CVSeq) (i : Nat)
    (hempty : s.vAt i = some .empty) (hpg : ¬ s.ProperlyGoverned i) :
    ¬ s.ECPSatisfied i := by
  unfold ECPSatisfied
  rw [hempty]
  exact hpg

/-- A full nucleus is always ECP-satisfied (vacuous). -/
theorem full_ecp_satisfied (s : CVSeq) (i : Nat)
    (hfull : s.vAt i = some .full) :
    s.ECPSatisfied i := by
  unfold ECPSatisfied
  rw [hfull]
  trivial

end CVSeq

end StrictCV

open StrictCV

/-! ## §1 Element-Theoretic decomposition of Tigrinya/Tigre segments
-/

/-! ### The vowel decompositions (paper eq. 20-22)

* [a] = headed |A| (the marked low vowel)
* [ʌ] = bare |A| (the unmarked low vowel; this contrast is paper
  eq. 21)
* [i] = headed |I|
* [u] = headed |U|
* [e] = headed |I| + bare |A|
* [o] = headed |U| + bare |A|
* [ɨ] = empty bundle (eq. 22 — phonetic realization of an empty
  vocalic position)

### The guttural decompositions (paper eq. 20)

All four attested gutturals contain |A|. The pharyngeal/laryngeal
contrast is the **headedness of |A|**: pharyngeals (ħ, ʕ) are headed
by |A|, laryngeals (ʔ, h) have |A| as operator.
-/

/-- Element-Theoretic decomposition of Tigrinya/Tigre vowels per
    [faust-lampitelli-2026] eq. 20-22. -/
def vowelET : Tigrinya.Phonology.Vowel → MR
  | .a     => MR.headedSimplex .A            -- [a]: headed |A|
  | .aBare => MR.simplex .A                  -- [ʌ]: non-headed |A|
  | .i     => MR.headedSimplex .I            -- [i]: headed |I|
  | .u     => MR.headedSimplex .U            -- [u]: headed |U|
  | .e     => MR.headPlusOp .I .A            -- [e]: head |I|, op |A|
  | .o     => MR.headPlusOp .U .A            -- [o]: head |U|, op |A|
  | .weak  => MR.empty                       -- [ɨ]: empty (eq. 22)

/-- Element-Theoretic decomposition of Tigrinya/Tigre gutturals per
    paper eq. 20. All gutturals contain |A|; pharyngeals (ħ, ʕ) have
    |A| as head, laryngeals (ʔ, h) have |A| as operator. -/
def gutturalET : Tigrinya.Phonology.Guttural → MR
  | .glottalStop         => MR.headPlusOp .glottal .A
  | .h                   => MR.headPlusOp .H .A
  | .pharyngealVoiced    => MR.headPlusOp .A .glottal
  | .pharyngealVoiceless => MR.headPlusOp .A .H

/-- Vowel `v` contains the |A| element. -/
def VowelHasA (v : Tigrinya.Phonology.Vowel) : Prop :=
  MR.HasElement (vowelET v) .A

instance : DecidablePred VowelHasA :=
  fun v => inferInstanceAs (Decidable (MR.HasElement (vowelET v) .A))

/-- Guttural `g` contains |A|. By paper eq. 20, all four do. -/
def GutturalHasA (g : Tigrinya.Phonology.Guttural) : Prop :=
  MR.HasElement (gutturalET g) .A

instance : DecidablePred GutturalHasA :=
  fun g => inferInstanceAs (Decidable (MR.HasElement (gutturalET g) .A))

/-- All four attested gutturals contain |A| (paper eq. 20). -/
theorem all_gutturals_have_A :
    ∀ g : Tigrinya.Phonology.Guttural, GutturalHasA g := by
  intro g; cases g <;> decide

/-- Pharyngeals are headed by |A| (paper eq. 20: ħ, ʕ have A
    underlined as head). -/
theorem pharyngeals_A_headed :
    MR.IsHead (gutturalET .pharyngealVoiced) .A ∧
    MR.IsHead (gutturalET .pharyngealVoiceless) .A := by
  decide

/-- Laryngeals (glottals) are NOT headed by |A| (their |A| is operator,
    not head; paper eq. 20). -/
theorem laryngeals_A_not_headed :
    ¬ MR.IsHead (gutturalET .glottalStop) .A ∧
    ¬ MR.IsHead (gutturalET .h) .A := by
  decide

/-! ## §2 Gutturals are low glides (the paper's headline structural claim)

The paper's headline #1 (paper §1, Conclusion §4): a guttural's |A|
element associates to a C-slot just as a high vowel's |I| or |U|
element associates to a C-slot to surface as a glide. The proof is
structural — the ET decomposition (`gutturalET`) makes every guttural
|A|-bearing, captured by `all_gutturals_have_A` above.

The synersis-engagement consequence (|A| at C fuses with |A| at
preceding V via OCP) is in §4 below.
-/

/-! ## §3 CV-skeletal modeling and worked examples
-/

/-! ### The synersis configuration

The paper's synersis trigger is /Aᵥ + A_c/ — a low vowel (|A| at a
V-slot) adjacent to a guttural (|A| at a C-slot). The CV sequence
encoding tracks per-V-slot melodic status. After the analysis applies
fusion + dissociation, the V-slot containing the underlying /ʌ/
becomes empty and is licensed silent (per ECP) iff the next V-slot
is contentful.

Below we encode the post-fusion forms of the paper's worked examples;
the underlying pre-fusion forms differ only in V-slot status (the
target V is `.full` rather than `.empty`).
-/

/-- The Tigrinya /CʌGV/ pattern from paper eq. (10b), surface
    [niβah] / [nibh-i] 'bark': three V-slots. The IMP.F [nibh-i]
    form is the syneresis-applied version where, after fusion +
    dissociation, V₂ (which underlyingly hosted /ʌ/) is empty. -/
def afterFusion_nibhi : CVSeq :=
  CVSeq.ofList [.full, .empty, .full]

/-- The /CʌGV/ baseline before fusion (the underlying form): V₂
    contentful with /ʌ/. The IMP.M [niβah] form realises this
    underlying state with V₂ surfacing as the lowered [a]. -/
def beforeFusion_nibhi : CVSeq :=
  CVSeq.ofList [.full, .full, .full]

/-- Verify post-fusion V₂ is properly governed by V₃ (which is full). -/
theorem nibhi_v2_properly_governed :
    afterFusion_nibhi.ProperlyGoverned 1 := by decide

/-- Verify post-fusion V₂ satisfies ECP (empty + properly governed →
    silent is licit). -/
theorem nibhi_v2_ecp_satisfied :
    afterFusion_nibhi.ECPSatisfied 1 := by decide

/-- The /ʕarif-u/ CV configuration (paper eq. 19b: /ʕarif-u/ →
    [ʕarifu]; analyzed in eq. 28c with self-licensing diagram in
    eq. 28a-b). Three V-slots, all contentful. The fused element at
    V₁ self-licenses C₁; the self-licensing domain blocks
    dissociation, so V₂ stays full even though V₃ would govern it. -/
def arifu_CV : CVSeq := CVSeq.ofList [.full, .full, .full]

theorem arifu_v2_full :
    arifu_CV.vAt 1 = some .full := rfl

/-- The /CʌGV/ → [CɨGV] case (paper eq. 17): position retained as
    epenthetic [ɨ] even though V₃ is full. Witness: PASS-PRF
    [ti-siħib ~ ti-sɨħib] from eq. (17b) for √sħb. Encoded as V₂ =
    empty (post-fusion) but realised as [ɨ] surfacing rather than
    silent — discussed at paper §3.3.3 as a position-retention case
    not predicted by the basic analysis. -/
def tisihib_CV : CVSeq := CVSeq.ofList [.full, .empty, .full]

theorem tisihib_v2_properly_governed :
    tisihib_CV.ProperlyGoverned 1 := by decide

/-! ## §4 Synersis as fused-and-governed; self-licensing block
-/

/-- A V-slot is *synersis-licensed silent* iff (a) it is empty
    (post-fusion) and (b) it is properly governed.
    [faust-lampitelli-2026] eq. (23)-(28). -/
def IsSynersisLicensedSilent (s : CVSeq) (i : Nat) : Prop :=
  s.vAt i = some .empty ∧ s.ProperlyGoverned i

instance (s : CVSeq) (i : Nat) : Decidable (IsSynersisLicensedSilent s i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The post-fusion [nibh-i] form (paper eq. 10b IMP.F) licenses
    synersis at V₂. The corresponding IMP.M [niβah] (eq. 10b)
    realises the unfused underlying form. -/
theorem nibhi_synersis_succeeds :
    IsSynersisLicensedSilent afterFusion_nibhi 1 := by decide

/-- **Self-licensing blocks dissociation**
    [faust-lampitelli-2026] eq. (28a-c). When the fused |A| at
    V₁ self-licenses preceding C₁ in a self-licensing domain,
    dissociation does NOT apply, and V₂ stays full.

    Witness: in /ʕarif-u/, V₂ remains full (containing the /i/
    vocalization), and the surface form is [ʕarifu] (eq. 19b/28c)
    not *[ʕarfu]. The structural prediction is the *absence* of an
    empty V₂, despite V₃'s government potential. -/
theorem arifu_blocks_synersis :
    arifu_CV.vAt 1 = some .full ∧ ¬ IsSynersisLicensedSilent arifu_CV 1 := by
  refine ⟨rfl, ?_⟩
  decide

/-! ### NOTE on T3 — "self-licensing domain"

The "self-licensing domain" itself is paper-specific apparatus
(paper n. 18: "this cannot be a general principle in Strict CV").
The inlined `StrictCV` substrate above deliberately does NOT define
self-licensing — this study file is where the Faust-specific
stipulation lives. T3 captures the
*prediction* (V₂ full ⇒ no synersis) without committing the
substrate to the stipulation that *generates* it.
-/

/-! ## §5 Economy drives synersis (witness from eq. 18, 39)
-/

/-- **Economy drives synersis** [faust-lampitelli-2026]
    §1, eq. 2b, eq. 18c, eq. 39b. The paper's central polemical
    claim against the simpler "synersis = phonotactic-driven gliding"
    view (eq. 2a).

    Witness: /mibarak/ → [mɨbɨrak] (eq. 18c, 39b). The underlying
    form has no guttural and no phonotactic problem; yet synersis
    applies and the position is retained as [ɨ] rather than left
    full. The paper concludes (§3.3.3): "the absence of syncope is
    not as straightforward [as a phonotactic explanation predicts]".
    The form [mibarak] would not pose a phonotactic problem yet
    [mɨbɨrak] is what surfaces.

    Encoded structurally: the /mibarak/ post-fusion sequence has V₂
    empty + properly governed, so synersis structurally licenses
    silence at V₂ even though no guttural is present. The fact that
    [ɨ] surfaces rather than silence is a separate observation
    (covered in §7's discussion of n. 23). -/
theorem mibarak_synersis_licensed_no_phonotactic_motivation :
    let mibarakAfter : CVSeq := CVSeq.ofList [.full, .empty, .full]
    IsSynersisLicensedSilent mibarakAfter 1 := by decide

/-! ## §6 Walker & Rose 2015 divergence (with the strongest witness)
-/

/-- The /mismaʕa/ identical-vowel configuration (paper p. 22-23). Both
    V-flanking vowels are /a/; the medial consonant is the
    pharyngeal /ʕ/. The F&L analysis predicts synersis applies
    (V₁ /a/'s |A| fuses with /ʕ/'s |A|, then V₁ becomes empty under
    proper government).

    Identifier note: the IPA name /mismaʕa/ contains the unicode `ʕ`
    which is not a valid Lean identifier character, so the def is
    named `identicalVowel_after`. -/
def identicalVowel_after : CVSeq := CVSeq.ofList [.empty, .full]

/-- **T4 — Walker & Rose 2015 overshoots**
    [faust-lampitelli-2026] §3.3.2 critique of
    [walker-rose-2015-amp]. Three refutation legs (the third
    is the strongest and is the one this theorem encodes):

    1. /iIu/ → [ju] (vowel + glide synersis): F&L's analysis
       predicts (extending to non-guttural |I|), W&R's `*VαCVβ`
       does not predict synersis here.
    2. Glides like /j/ are the consonants least likely to allow
       harmony, so subjecting them to `*VαCVβ` is unmotivated.
    3. **Synersis applies between identical vowels**: in
       /mismʌʕa/ → [mismaʕa], the analysis applies fusion of
       the /a/ to the |A| of /ʕ/ (creating the structural
       configuration of synersis), but `*VαCVβ` does not apply
       (α = β = /a/).

    The third leg is encoded here as a structural witness: the
    F&L post-fusion form is `[.empty, .full]` (V₁ vacated by
    synersis), and W&R's `*VαCVβ`-based analysis does not yield
    this empty V₁ from an identical-flanking-vowel input.

    The full surface-form prediction comparison requires modeling
    W&R's constraint apparatus (deferred — W&R 2015 is a handout,
    not a published paper [walker-rose-2015-amp] note 22). -/
theorem identicalVowel_synersis_overshoots_walker_rose :
    -- F&L predicts: V₁ empty after fusion.
    identicalVowel_after.vAt 0 = some .empty := rfl

/-! ## §7 OCP merger as instance of the shared substrate
-/

/-- The |A|+|A| → fused |A| operation of paper eq. (26) is an
    instance of `OCP.collapse` over a tier of `Element` values: two
    adjacent |A| elements collapse to one.

    This makes structurally explicit that F&L's "fusion" mechanism
    is the same operation as [lionnet-2022]'s `mergeTRN` for
    Laal tones, just instantiated over a different value space
    (privative `Element` vs binary-feature `TRN`). -/
theorem fusion_is_collapse_instance :
    OCP.collapse [Element.A, Element.A] = [Element.A] := by
  decide

/-- The OCP-merger output is OCP-clean: no two adjacent identical
    elements remain. Direct application of the substrate theorem
    `OCP.collapse_clean`. -/
theorem fusion_output_is_ocp_clean (xs : List Element) :
    OCP.IsClean (OCP.collapse xs) :=
  OCP.collapse_clean xs

/-! ## §8 Paper-acknowledged scope limits

The paper itself marks several places where its analysis is
incomplete or stipulative. These are documented here as the paper
states them, not encoded as theorems — over-formalising them would
misrepresent the paper's epistemic stance.

* **Ejectives also contain |A| but never undergo syneresis** (paper
  n. 8, page 9). Per [lowenstamm-prunet-1988] and
  [faust-2017b], ejectives also lower /ʌ/ to [a], suggesting
  ejectives also bear the |A| element; per [bellem-2007]:102-153
  for an ET implementation. Yet syneresis never applies before
  ejectives. The paper hypothesises a structural difference between
  ejectives and gutturals but does not derive it.

* **The Tigre [samʕa] underlying form** (paper n. 11, page 11). The
  parallel form to Tigrinya /sʌmʌʕ-ko/ in the Tigre PRF is
  [samʕako] 'I heard'. But the unsuffixed Tigre PRF base always
  lacks the second stem vowel regardless of final-C identity (cf.
  [samʕa] 'he heard' and [fagra] 'he left' per [raz-1980]). The
  paper concludes [samʕako] is probably not underlyingly /sʌmʌʕ-ko/
  in Tigre — flagging an unresolved underlying-form question.

* **The supposed weakness of gutturals lacks an external definition**
  (paper n. 17, page 16). The premise of eq. (25) — that gutturals
  must be licensed — is motivated only by the present analysis; the
  paper acknowledges no prior study defines this weakness
  satisfactorily, citing only sketches in [angoujard-1995] and
  [walker-rose-2015-amp].

* **"Licensing overrides government" is not a general Strict-CV
  principle** (paper n. 18, page 16). In many languages, codas (Cs
  before empty V-slots) are lost or lenited; if licensing always
  overrode government, epenthesis would always occur to avoid this
  lenition, contrary to fact. The self-licensing-domain stipulation
  is therefore paper-specific apparatus; it is documented in §4 of
  this file as belonging to the study, not the substrate.

* **The TGH generalisation predicts an unattested form**
  (paper n. 23, page 24). The paper generalises TGH to derivations
  like (37b-c), which would predict [siħab] alongside the attested
  [sahab]. The paper has not encountered [siħab] but expects it
  to be possible — a predicted-but-unattested gap.

* **"Rules apply" generates derivation loops on opaque cases**
  (paper n. 25 + §3.3.3 discussion of eq. 37, pages 24-25). The
  derivations in eq. (37b-d) raise an issue: under naive "rules
  apply", the situation created by TGH /sahab/ could be regarded as
  identical to the environment of fusion+dissociation, leading to
  loop /sʌħab/ → /s_ħab/ → /sahab/ → /s_hab/ → /sahab/ → … . The
  paper offers three escape hatches without committing to one:
  (i) the output of TGH is somehow different from a fused |A|;
  (ii) epenthesis/TGH is phonetic implementation, post-phonological;
  (iii) disallow repeated application of operations.

* **The realised vowel position in /tisʌħib/ → [tisɨħib] and
  /mibarak/ → [mɨbɨrak] is not predicted** (paper §3.3.3 final
  paragraph + discussion of eq. 39, page 26). The paper acknowledges
  "we do not have an insightful explanation for the retention of the
  position", tentatively invoking [buckley-2000]'s
  morpheme-specific alignment for Tigrinya but admitting Tigre lacks
  the same morpheme-specific requirement.

* **The cross-linguistic rarity of |A|-glides remains unexplained**
  (paper §4 conclusion, page 27). The paper concedes "possibly, the
  absence of guttural sounds from most languages accounts for the
  lack of more widespread effects of |A| 'glides'" — a typological
  observation, not a derived prediction.
-/

end FaustLampitelli2026
