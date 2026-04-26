import Linglib.Fragments.Mwaghavul.Basic
import Linglib.Theories.Pragmatics.Expressives.Basic
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Phonology.Autosegmental.CoPScope
import Linglib.Theories.Phonology.Autosegmental.Floating
import Linglib.Theories.Phonology.Tone.Constraints
import Linglib.Core.Constraint.OT.HarmonicSerialism
import Linglib.Phenomena.Tone.Studies.Hyman2006

/-!
# Akinbo & Fwangwar (2026): Grammatical tones targeting ideophones
@cite{akinbo-fwangwar-2026}

Akinbo, S. K. & Fwangwar, T. R. (2026). Iconicity and expressiveness of
grammatical tones targeting ideophones in Mwaghavul. *Natural Language
& Linguistic Theory* 44:21.

## Empirical claims

1. **Grammatical tone targets ideophones.** Mwaghavul derives verbs
   from ideophones via two segmentally null verbalisers with M and M-H
   tonal melodies as their sole exponents.

2. **Anchor + INTEGRITY OT analysis** (paper §4.3, eq. 22). The tonal
   alternations are accounted for by morpheme-specific correspondence
   constraints (@cite{finley-2009}): LEFT-ANCHOR-Tᵥ, RIGHT-ANCHOR-Tᵥ,
   INTEGRITY-Tᵥ, and MAX-Tone.

3. **Iconic Phonological Disharmony.** In pluractional verbs, the M-H
   verbaliser realises M on every TBU of the reduplicant and H on
   every TBU of the base. This disharmony iconically marks
   "distinguishable identity" (@cite{dingemanse-thompson-2020}).

4. **Expressiveness survives integration.** Derived ideophonic verbs
   retain expressive properties (affective meaning,
   nondisplaceability, ineffability) despite full morphosyntactic
   integration (@cite{potts-2005}-style secondary meanings),
   challenging the inverse correlation predicted by
   @cite{dingemanse-akita-2017}.

## Substrate

The OT analysis is built on `Phonology.Autosegmental.FloatingForm Syl`
(Goldsmith-style autosegmental representation; built originally for
@cite{mcpherson-lamont-2026}). Each `ulTones` entry is one
autosegment; `surfaceLinks` records associations between tier and
TBUs. This represents spreading (one autosegment, multi-linked) and
copying (multiple autosegments) as distinct objects — load-bearing
for the INTEGRITY-Mᵥ constraint that rules out the copying variant of
Tableau 24's optimum (paper p. 26 eq. 22c).

Constraint primitives come from
`Theories/Phonology/Tone/Constraints.lean`, with Mwaghavul-specific
anchor combinators defined in §2 below.

## Section structure

- §1 Substrate setup (morpheme IDs, tone/segment helpers)
- §2 Constraints over `MwaghavulForm` — anchor + INTEGRITY + MAX-Tone,
  with per-root variants for the pluractional tableau
- §3 Tableau 24 — M verbaliser + wùlàʃ (INTEGRITY rules out copying)
- §4 Tableau 25 — M-H verbaliser + háŋláyáp
- §5 Tableau 26 — pluractional jàlpàt with per-root anchoring
- §6 Classification under @cite{rolle-2018} — replacive-dominant GT
- §7 Empirical generalisations
- §8 Connection to Distributed Morphology categorisers
- §9 Expressiveness preservation
-/

namespace AkinboFwangwar2026

open Core.Constraint.OT
open Phonology.Autosegmental
open Phonology.Autosegmental.RegisterTier (TRN)
open Phonology.Tone (integrityTone)
open Fragments.Mwaghavul

-- ============================================================================
-- §1: Substrate Setup
-- ============================================================================

/-- The Mwaghavul-instantiated autosegmental form. -/
abbrev MwaghavulForm := FloatingForm Syl

/-- Morpheme ID for the ideophone root (wùlàʃ in Tableau 24, háŋláyáp
    in Tableau 25). Both single-root tableaux share this ID. -/
def rootMorph : MorphemeId := 0

/-- Morpheme ID for the verbaliser. The M-tone verbaliser (Tableau 24)
    and the M-H verbaliser (Tableaux 25/26) share this ID — they're
    suppletive allomorphs of the same verbaliser morpheme per paper
    p. 20 eq. (17). -/
def vbzMorph : MorphemeId := 1

/-- Morpheme ID for the reduplicant root in pluractional Tableau 26. -/
def rootRedMorph : MorphemeId := 2

/-- Morpheme ID for the base root in pluractional Tableau 26. -/
def rootBaseMorph : MorphemeId := 3

/-- Wrap a Mwaghavul syllable as a TBU of the (single) ideophone root. -/
def rootSeg (s : Syl) : SegSpec Syl := { seg := s, morpheme := rootMorph }

/-- Wrap a syllable as a TBU of the reduplicant (Tableau 26). -/
def redSeg (s : Syl) : SegSpec Syl := { seg := s, morpheme := rootRedMorph }

/-- Wrap a syllable as a TBU of the base (Tableau 26). -/
def baseSeg (s : Syl) : SegSpec Syl := { seg := s, morpheme := rootBaseMorph }

/-- L tone of the (single) ideophone root. -/
def rootL : ToneSpec := { tone := TRN.L, morpheme := rootMorph }

/-- M tone of the verbaliser. -/
def vbzM : ToneSpec := { tone := TRN.M, morpheme := vbzMorph }

/-- H tone of the verbaliser. -/
def vbzH : ToneSpec := { tone := TRN.H, morpheme := vbzMorph }

/-- L tone of the reduplicant root (Tableau 26). -/
def lRed : ToneSpec := { tone := TRN.L, morpheme := rootRedMorph }

/-- L tone of the base root (Tableau 26). -/
def lBase : ToneSpec := { tone := TRN.L, morpheme := rootBaseMorph }

-- ============================================================================
-- §2: Constraints over `MwaghavulForm`
-- ============================================================================

/-! Anchor + INTEGRITY + MAX-Tone constraints. Anchor constraints come
    in two flavours:
    - **Single-root** (`lAnchToneC`/`rAnchToneC`): scope over all TBUs.
      Correct for Tableaux 24/25 with one root morpheme.
    - **Per-root, summed across roots** (`lAnchToneCAcross` /
      `rAnchToneCAcross`): scope to each root morpheme separately, sum
      violations; if no root hosts the gram tone, every TBU of every
      targeted root counts (paper p. 28). Required for Tableau 26's
      two-root pluractional. -/

section SingleRoot

/-- Does TBU `i` bear a tone of value `t` from morpheme `m`? -/
def isGramTbu (t : TRN) (m : MorphemeId) (f : MwaghavulForm) (i : SegIdx) : Bool :=
  (f.linksTo i).any fun k =>
    (f.ulTones[k]?).any fun ts => decide (ts.tone = t ∧ ts.morpheme = m)

/-- L-ANCHOR-`t`-from-`m`: number of TBUs (in tier order) before the
    leftmost gram-`t`-from-`m` TBU. If no such TBU exists, every TBU
    counts (full TBU count). -/
def lAnchTone (t : TRN) (m : MorphemeId) (f : MwaghavulForm) : Nat :=
  match (List.range f.segs.length).findIdx? (isGramTbu t m f) with
  | some i => i
  | none   => f.segs.length

/-- R-ANCHOR-`t`-from-`m`: counted from the right edge. -/
def rAnchTone (t : TRN) (m : MorphemeId) (f : MwaghavulForm) : Nat :=
  match (List.range f.segs.length).reverse.findIdx? (isGramTbu t m f) with
  | some i => i
  | none   => f.segs.length

/-- MAX-Tone (per autosegment): count of deleted ulTones entries.
    Matches paper p. 26 per-autosegment counting. -/
def maxToneAuto (f : MwaghavulForm) : Nat :=
  (List.range f.ulTones.length).countP (fun k => decide (f.IsDeleted k))

/-- L-ANCHOR-Mᵥ as a `DirectionalConstraint`. -/
def lAnchToneC (t : TRN) (m : MorphemeId) : DirectionalConstraint MwaghavulForm where
  name := s!"L-ANCH-{reprStr t}({m})"
  family := .faithfulness
  eval := fun f => [lAnchTone t m f]

/-- R-ANCHOR-Mᵥ as a `DirectionalConstraint`. -/
def rAnchToneC (t : TRN) (m : MorphemeId) : DirectionalConstraint MwaghavulForm where
  name := s!"R-ANCH-{reprStr t}({m})"
  family := .faithfulness
  eval := fun f => [rAnchTone t m f]

/-- MAX-Tone as a `DirectionalConstraint`. -/
def maxToneC : DirectionalConstraint MwaghavulForm where
  name := "MAX-Tone"
  family := .faithfulness
  eval := fun f => [maxToneAuto f]

/-- INTEGRITY-Mᵥ for the verbaliser (canonical case). -/
def integMv : DirectionalConstraint MwaghavulForm := integrityTone vbzMorph TRN.M

/-- L-ANCHOR-Mᵥ for the verbaliser. -/
def lAnchMv : DirectionalConstraint MwaghavulForm := lAnchToneC TRN.M vbzMorph

/-- R-ANCHOR-Mᵥ for the verbaliser. -/
def rAnchMv : DirectionalConstraint MwaghavulForm := rAnchToneC TRN.M vbzMorph

/-- L-ANCHOR-Hᵥ for the verbaliser (paper p. 25 fn: H-tone version of
    eq. 22 has the same conditions). -/
def lAnchHv : DirectionalConstraint MwaghavulForm := lAnchToneC TRN.H vbzMorph

/-- R-ANCHOR-Hᵥ for the verbaliser. -/
def rAnchHv : DirectionalConstraint MwaghavulForm := rAnchToneC TRN.H vbzMorph

end SingleRoot

section PerRoot

/-- TBU indices belonging to root morpheme `rm`. -/
def rootTbus (rm : MorphemeId) (f : MwaghavulForm) : List SegIdx :=
  (List.range f.segs.length).filter fun i =>
    (f.segs[i]?).any (fun sp => decide (sp.morpheme = rm))

/-- A gram-`t`-from-`m` tone is realised on root `rm` iff some TBU of
    `rm` bears one. -/
def isRealisedOnRoot (t : TRN) (m : MorphemeId) (rm : MorphemeId)
    (f : MwaghavulForm) : Bool :=
  (rootTbus rm f).any (isGramTbu t m f)

/-- L-ANCHOR scoped to root `rm`. 0 if `t`-from-`m` not realised on
    `rm` (per paper p. 28: "no violation to the other root morpheme");
    else count TBUs of `rm` before the leftmost gram-`t` TBU of `rm`. -/
def lAnchTonePerRoot (t : TRN) (m : MorphemeId) (rm : MorphemeId)
    (f : MwaghavulForm) : Nat :=
  if isRealisedOnRoot t m rm f then
    match (rootTbus rm f).findIdx? (isGramTbu t m f) with
    | some i => i
    | none   => 0
  else 0

/-- R-ANCHOR scoped to root `rm`. -/
def rAnchTonePerRoot (t : TRN) (m : MorphemeId) (rm : MorphemeId)
    (f : MwaghavulForm) : Nat :=
  if isRealisedOnRoot t m rm f then
    match (rootTbus rm f).reverse.findIdx? (isGramTbu t m f) with
    | some i => i
    | none   => 0
  else 0

/-- L-ANCHOR summed across a list of root morphemes. If the gram tone
    is not realised on ANY of the roots, paper p. 28 assigns one
    violation per TBU of every targeted root (not 0). -/
def lAnchToneAcrossRoots (t : TRN) (m : MorphemeId) (rms : List MorphemeId)
    (f : MwaghavulForm) : Nat :=
  if rms.any (fun rm => isRealisedOnRoot t m rm f) then
    rms.foldl (fun acc rm => acc + lAnchTonePerRoot t m rm f) 0
  else
    rms.foldl (fun acc rm => acc + (rootTbus rm f).length) 0

/-- R-ANCHOR summed across a list of root morphemes. -/
def rAnchToneAcrossRoots (t : TRN) (m : MorphemeId) (rms : List MorphemeId)
    (f : MwaghavulForm) : Nat :=
  if rms.any (fun rm => isRealisedOnRoot t m rm f) then
    rms.foldl (fun acc rm => acc + rAnchTonePerRoot t m rm f) 0
  else
    rms.foldl (fun acc rm => acc + (rootTbus rm f).length) 0

/-- L-ANCHOR-`t`-from-`m`-across-roots as a `DirectionalConstraint`. -/
def lAnchToneCAcross (t : TRN) (m : MorphemeId) (rms : List MorphemeId) :
    DirectionalConstraint MwaghavulForm where
  name := s!"L-ANCH-{reprStr t}({m},across)"
  family := .faithfulness
  eval := fun f => [lAnchToneAcrossRoots t m rms f]

/-- R-ANCHOR across roots as a `DirectionalConstraint`. -/
def rAnchToneCAcross (t : TRN) (m : MorphemeId) (rms : List MorphemeId) :
    DirectionalConstraint MwaghavulForm where
  name := s!"R-ANCH-{reprStr t}({m},across)"
  family := .faithfulness
  eval := fun f => [rAnchToneAcrossRoots t m rms f]

end PerRoot

-- ============================================================================
-- §3: Tableau 24 — M verbaliser + wùlàʃ (with INTEGRITY)
-- ============================================================================

/-! Paper Tableau 24 (p. 26): `(wùlàʃ)₁ + Mᵥ`. Six candidates including
    the copying variant (24f) that the paper rules out via INTEGRITY-Mᵥ.

    Encoding: ONE lex L autosegment multi-linked to both TBUs of the
    bisyllabic root (Goldsmith 1976 convention; paper notation
    `(wùlàʃ)₁` confirms a single morpheme-internal melody). -/

namespace Tableau24

/-- Faithful input: ulTones = `[L_root (multi-linked), M_vbz (floating)]`. -/
def input : MwaghavulForm :=
  FloatingForm.mkInput
    (segs := [rootSeg ⟨"wù"⟩, rootSeg ⟨"làʃ"⟩])
    (ulTones := [rootL, vbzM])
    (ulLinks := {(0, 0), (0, 1)})

/-- (24a) `(wùlàʃ)₁ M₂`: M still floating; L unchanged. -/
def candA : MwaghavulForm := input

/-- (24b) `(wùlàʃ)₁`: M deleted; L unchanged. -/
def candB : MwaghavulForm := input.deleteTone 1

/-- (24c) `(wù)₁(làʃ)₂`: L on σ0 only; M docked on σ1 only. -/
def candC : MwaghavulForm := input.deleteLink 0 1 |>.insertLink 1 1

/-- (24d) `(wū)₂(làʃ)₁`: M on σ0 only; L on σ1 only. -/
def candD : MwaghavulForm := input.deleteLink 0 0 |>.insertLink 1 0

/-- (24e) ☞ `(wūlāʃ)₂` SPREADING: M multi-linked to both TBUs; L
    deleted. ONE M autosegment, two surface links. -/
def candE : MwaghavulForm :=
  input.deleteTone 0 |>.insertLink 1 0 |>.insertLink 1 1

/-- (24f) `(wū)₂(lāʃ)₂` COPYING: TWO separate M autosegments, each
    linked to one TBU. L deleted. Differs from (24a-e) in `ulTones`
    — the autosegmental representation has an *extra* M autosegment.
    INTEGRITY-Mᵥ fatally penalises this copying. -/
def candF : MwaghavulForm :=
  { input with
    ulTones := [rootL, vbzM, vbzM]
    deletedTones := {0}
    surfaceLinks := {(1, 0), (2, 1)} }

def candidates : Finset MwaghavulForm := {candA, candB, candC, candD, candE, candF}

theorem nonempty : candidates.Nonempty := by decide

/-- Ranking from paper §4.3 + p. 26: `INTEG-Mᵥ ≫ L-ANCH-Mᵥ ≫
    R-ANCH-Mᵥ ≫ MAX-Tone`. -/
def ranking : List (DirectionalConstraint MwaghavulForm) :=
  [integMv, lAnchMv, rAnchMv, maxToneC]

def tableau : DirectionalTableau MwaghavulForm where
  candidates := candidates
  ranking := ranking
  evalMode := .parallel
  nonempty := nonempty

/-- (24a) profile `[INTEG-Mᵥ, L-ANCH-Mᵥ, R-ANCH-Mᵥ, MAX-T] = [0, 2, 2, 0]`:
    M floating, both anchors fail (no gram-M TBU), no deletions. -/
theorem candA_profile :
    ranking.map (fun c => c.eval candA) = [[0], [2], [2], [0]] := by decide

/-- (24b) profile `[0, 2, 2, 1]`: M deleted, anchors fail, MAX-T fires. -/
theorem candB_profile :
    ranking.map (fun c => c.eval candB) = [[0], [2], [2], [1]] := by decide

/-- (24c) profile `[0, 1, 0, 0]`: M on σ1; L-ANCH = 1 (M not at left). -/
theorem candC_profile :
    ranking.map (fun c => c.eval candC) = [[0], [1], [0], [0]] := by decide

/-- (24d) profile `[0, 0, 1, 0]`: M on σ0; R-ANCH = 1 (M not at right). -/
theorem candD_profile :
    ranking.map (fun c => c.eval candD) = [[0], [0], [1], [0]] := by decide

/-- (24e) ☞ profile `[0, 0, 0, 1]`: M multi-linked, anchors satisfied;
    INTEG = 0 (1 alive vbz M); MAX-T = 1 (L deleted). The unique optimum. -/
theorem candE_profile :
    ranking.map (fun c => c.eval candE) = [[0], [0], [0], [1]] := by decide

/-- (24f) profile `[1, 0, 0, 1]`: TWO M autosegments → INTEG = 1 (fatal
    under the ranking, even though anchors and MAX-T tie with (24e)). -/
theorem candF_profile :
    ranking.map (fun c => c.eval candF) = [[1], [0], [0], [1]] := by decide

/-- **Headline**: `(24e)` is the unique optimum under
    `INTEG-Mᵥ ≫ L-ANCH-Mᵥ ≫ R-ANCH-Mᵥ ≫ MAX-Tone`. The copying variant
    (24f) is ruled out by INTEGRITY; (24a-d) lose on anchors. -/
theorem optimal : tableau.optimal = {candE} := by decide

end Tableau24

-- ============================================================================
-- §4: Tableau 25 — M-H verbaliser + háŋláyáp
-- ============================================================================

/-! Paper Tableau 25 (p. 27): `(háŋláyáp)₁ + M₂H₃ᵥ`. Seven candidates;
    no INTEGRITY column (no copying variant arises). Encoding: ONE
    lex H autosegment multi-linked to all 3 TBUs (Goldsmith convention). -/

namespace Tableau25

/-- Faithful input: ulTones = `[H_root (multi-linked), M_vbz, H_vbz]`. -/
def input : MwaghavulForm :=
  FloatingForm.mkInput
    (segs := [rootSeg ⟨"haŋ"⟩, rootSeg ⟨"la"⟩, rootSeg ⟨"yap"⟩])
    (ulTones := [{ tone := TRN.H, morpheme := rootMorph }, vbzM, vbzH])
    (ulLinks := {(0, 0), (0, 1), (0, 2)})

/-- (25a) `(háŋláyáp)₁`: lex H linked; both vbz tones deleted. -/
def candA : MwaghavulForm := input.deleteTone 1 |>.deleteTone 2

/-- (25b) `(hāŋlā)₂(yáp)₁`: M on σ0-σ1; lex H on σ2; vbz H deleted. -/
def candB : MwaghavulForm :=
  input.deleteLink 0 0 |>.deleteLink 0 1
    |>.insertLink 1 0 |>.insertLink 1 1
    |>.deleteTone 2

/-- (25c) `(háŋláyáp)₃`: vbz H multi-linked to all TBUs; vbz M and lex H
    deleted. -/
def candC : MwaghavulForm :=
  input.deleteTone 0 |>.deleteTone 1
    |>.insertLink 2 0 |>.insertLink 2 1 |>.insertLink 2 2

/-- (25d) `(hāŋlāyāp)₂`: vbz M multi-linked to all TBUs; vbz H and lex H
    deleted. -/
def candD : MwaghavulForm :=
  input.deleteTone 0 |>.deleteTone 2
    |>.insertLink 1 0 |>.insertLink 1 1 |>.insertLink 1 2

/-- (25e) ☞ `(hāŋlā)₂(yáp)₃`: vbz M on σ0-σ1; vbz H on σ2; lex H
    deleted. The winner. -/
def candE : MwaghavulForm :=
  input.deleteTone 0
    |>.insertLink 1 0 |>.insertLink 1 1
    |>.insertLink 2 2

/-- (25f) `(hāŋ)₂(láyáp)₃`: vbz M on σ0; vbz H on σ1-σ2; lex H deleted. -/
def candF : MwaghavulForm :=
  input.deleteTone 0
    |>.insertLink 1 0
    |>.insertLink 2 1 |>.insertLink 2 2

/-- (25g) `(hāŋ)₂(lá)₁(yáp)₃`: vbz M on σ0; lex H on σ1; vbz H on σ2.
    Lex H NOT deleted. -/
def candG : MwaghavulForm :=
  input.deleteLink 0 0 |>.deleteLink 0 2
    |>.insertLink 1 0
    |>.insertLink 2 2

def candidates : Finset MwaghavulForm :=
  {candA, candB, candC, candD, candE, candF, candG}

theorem nonempty : candidates.Nonempty := by decide

/-- Ranking from paper Tableau 25 (p. 27):
    `L-ANCH-Mᵥ ≫ R-ANCH-Hᵥ ≫ R-ANCH-Mᵥ ≫ L-ANCH-Hᵥ ≫ MAX-Tone`. -/
def ranking : List (DirectionalConstraint MwaghavulForm) :=
  [lAnchMv, rAnchHv, rAnchMv, lAnchHv, maxToneC]

def tableau : DirectionalTableau MwaghavulForm where
  candidates := candidates
  ranking := ranking
  evalMode := .parallel
  nonempty := nonempty

/-- (25a) profile `[3, 3, 3, 3, 2]`: no verbaliser realised. -/
theorem candA_profile :
    ranking.map (fun c => c.eval candA) = [[3], [3], [3], [3], [2]] := by decide

/-- (25b) profile `[0, 3, 1, 3, 1]`: vbz M docked left; vbz H deleted. -/
theorem candB_profile :
    ranking.map (fun c => c.eval candB) = [[0], [3], [1], [3], [1]] := by decide

/-- (25c) profile `[3, 0, 3, 0, 2]`: vbz H spreading; vbz M deleted. -/
theorem candC_profile :
    ranking.map (fun c => c.eval candC) = [[3], [0], [3], [0], [2]] := by decide

/-- (25d) profile `[0, 3, 0, 3, 2]`: vbz M spreading; vbz H deleted. -/
theorem candD_profile :
    ranking.map (fun c => c.eval candD) = [[0], [3], [0], [3], [2]] := by decide

/-- (25e) ☞ profile `[0, 0, 1, 2, 1]`: M on σ0-σ1; H on σ2; lex H
    deleted. Winner. -/
theorem candE_profile :
    ranking.map (fun c => c.eval candE) = [[0], [0], [1], [2], [1]] := by decide

/-- (25f) profile `[0, 0, 2, 1, 1]`. -/
theorem candF_profile :
    ranking.map (fun c => c.eval candF) = [[0], [0], [2], [1], [1]] := by decide

/-- (25g) profile `[0, 0, 2, 2, 0]`: lex H NOT deleted (still on σ1). -/
theorem candG_profile :
    ranking.map (fun c => c.eval candG) = [[0], [0], [2], [2], [0]] := by decide

/-- **Headline**: (25e) is the unique optimum. (25a-d) lose on the
    top-tier anchors; (25f-g) tie with (25e) on top constraints but
    lose on R-ANCH-Mᵥ. -/
theorem optimal : tableau.optimal = {candE} := by decide

end Tableau25

-- ============================================================================
-- §5: Tableau 26 — pluractional jàlpàt + per-root anchoring
-- ============================================================================

/-! Paper Tableau 26 (p. 28): `(jàlpàt)₁ + (jàlpàt)₂ + M₃H₄ᵥ`. Two
    root morphemes (reduplicant + base), each with /LL/ lexical
    melody (one L autosegment multi-linked to its 2 TBUs). The M-H
    verbaliser realises M on RED's TBUs and H on BASE's TBUs.

    Per-root anchoring (paper p. 28): if vbz M is realised on one root,
    the other root contributes no violation. If unrealised on both,
    every TBU of every targeted root counts. The
    `lAnchToneCAcross`/`rAnchToneCAcross` constraints in §2 implement
    this. -/

namespace Tableau26

/-- Faithful input: ulTones = `[L_RED (multi-linked), L_BASE
    (multi-linked), M_vbz, H_vbz]`. Each lex L is multi-linked to its
    own root's 2 TBUs. -/
def input : MwaghavulForm :=
  FloatingForm.mkInput
    (segs := [redSeg ⟨"jàl"⟩, redSeg ⟨"pàt"⟩, baseSeg ⟨"jàl"⟩, baseSeg ⟨"pàt"⟩])
    (ulTones := [lRed, lBase, vbzM, vbzH])
    (ulLinks := {(0, 0), (0, 1), (1, 2), (1, 3)})

/-- Per-root anchor instantiations for the two-root pluractional. -/
def lAnchMv26 : DirectionalConstraint MwaghavulForm :=
  lAnchToneCAcross TRN.M vbzMorph [rootRedMorph, rootBaseMorph]
def rAnchHv26 : DirectionalConstraint MwaghavulForm :=
  rAnchToneCAcross TRN.H vbzMorph [rootRedMorph, rootBaseMorph]
def rAnchMv26 : DirectionalConstraint MwaghavulForm :=
  rAnchToneCAcross TRN.M vbzMorph [rootRedMorph, rootBaseMorph]
def lAnchHv26 : DirectionalConstraint MwaghavulForm :=
  lAnchToneCAcross TRN.H vbzMorph [rootRedMorph, rootBaseMorph]

/-- (26a): both vbz tones deleted; both lex Ls survive. -/
def candA : MwaghavulForm := input.deleteTone 2 |>.deleteTone 3

/-- (26b): vbz M on σ1 (rightmost of RED); vbz H on σ3 (rightmost of
    BASE); lex Ls survive on σ0 and σ2 respectively. -/
def candB : MwaghavulForm :=
  input.deleteLink 0 1 |>.insertLink 2 1
    |>.deleteLink 1 3 |>.insertLink 3 3

/-- (26c): vbz M on σ0 (leftmost of RED); vbz H on σ2 (leftmost of
    BASE); lex Ls survive on σ1 and σ3. -/
def candC : MwaghavulForm :=
  input.deleteLink 0 0 |>.insertLink 2 0
    |>.deleteLink 1 2 |>.insertLink 3 2

/-- (26d) ☞: M spreading on RED (both σ0, σ1); H spreading on BASE
    (both σ2, σ3); both lex Ls deleted. The winner — iconic M-on-RED
    + H-on-BASE pattern. -/
def candD : MwaghavulForm :=
  input.deleteTone 0 |>.deleteTone 1
    |>.insertLink 2 0 |>.insertLink 2 1
    |>.insertLink 3 2 |>.insertLink 3 3

/-- (26e): vbz M on σ0; vbz H on σ1 (both within RED); lex L of BASE
    survives multi-linked. Lex L of RED deleted. -/
def candE : MwaghavulForm :=
  input.deleteTone 0
    |>.insertLink 2 0
    |>.insertLink 3 1

/-- (26f): vbz M spreading on RED + σ2 (first BASE TBU); vbz H on σ3. -/
def candF : MwaghavulForm :=
  input.deleteTone 0 |>.deleteLink 1 2
    |>.insertLink 2 0 |>.insertLink 2 1 |>.insertLink 2 2
    |>.insertLink 3 3

/-- (26g): vbz M on σ0 (RED) + σ2 (BASE); lex L of RED on σ1; vbz H on σ3. -/
def candG : MwaghavulForm :=
  input.deleteLink 0 0 |>.deleteLink 1 2
    |>.insertLink 2 0 |>.insertLink 2 2
    |>.insertLink 3 3

def candidates : Finset MwaghavulForm :=
  {candA, candB, candC, candD, candE, candF, candG}

theorem nonempty : candidates.Nonempty := by decide

/-- Ranking, same shape as Tableau 25 but with per-root anchors:
    `L-ANCH-Mᵥ ≫ R-ANCH-Hᵥ ≫ R-ANCH-Mᵥ ≫ L-ANCH-Hᵥ ≫ MAX-Tone`. -/
def ranking : List (DirectionalConstraint MwaghavulForm) :=
  [lAnchMv26, rAnchHv26, rAnchMv26, lAnchHv26, maxToneC]

def tableau : DirectionalTableau MwaghavulForm where
  candidates := candidates
  ranking := ranking
  evalMode := .parallel
  nonempty := nonempty

/-- (26d) profile `[0, 0, 0, 0, 2]`: perfect realisation — vbz M on
    every TBU of RED, vbz H on every TBU of BASE. Both lex Ls deleted
    (MAX-T = 2). -/
theorem candD_profile :
    ranking.map (fun c => c.eval candD) = [[0], [0], [0], [0], [2]] := by decide

/-- **Headline**: (26d) is the unique optimum — the iconic M-on-RED +
    H-on-BASE disharmony pattern. -/
theorem optimal : tableau.optimal = {candD} := by decide

end Tableau26

-- ============================================================================
-- §6: Classification under @cite{rolle-2018}
-- ============================================================================

/-! The Mwaghavul verbalisers are classified under @cite{rolle-2018}'s
    grammatical-tone framework as **replacive-dominant** GT (Def 1):
    automatic replacement of the underlying tone within the valuation
    window of the target-host. Verbalisers are word-level + independent
    prosodic exponence (segmentally null — tone is the sole exponent). -/

open Phonology.Autosegmental.GrammaticalTone
  (GTSpec GTDominance GTLevel ExponenceType DominantGTAsymmetry)
open Phonology.Autosegmental.CoPScope
  (CoPPosition dominant_gt_asymmetry_from_scope)

/-- M-tone verbaliser (VBZ₁) classified under Rolle 2018:
    replacive-dominant, word-level, independent. -/
def verbM_GT : GTSpec :=
  { name := "VBZ₁"
    melody := [.M]
    window := .whole
    dominance := .replaciveDominant
    level := .word
    exponence := .independent }

/-- M-H verbaliser (VBZ₂). -/
def verbMH_GT : GTSpec :=
  { name := "VBZ₂"
    melody := [.M, .H]
    window := .nonfinalFinal
    dominance := .replaciveDominant
    level := .word
    exponence := .independent }

/-- Both verbalisers are dominant: they neutralise the target's
    lexical tonal contrast. -/
theorem verbalizers_are_dominant :
    verbM_GT.dominance.IsDominant ∧ verbMH_GT.dominance.IsDominant :=
  ⟨by decide, by decide⟩

/-- Mwaghavul verbalisers classify as `dominant` at the abstract
    prosodic level. -/
theorem verbalizers_prosodic_dominant :
    verbM_GT.dominance.toProsodicDominance = .dominant ∧
    verbMH_GT.dominance.toProsodicDominance = .dominant := ⟨rfl, rfl⟩

/-- The verbaliser-to-root relationship satisfies the dominant GT
    asymmetry, **derived** from CoP-scope: verbaliser is in Spec
    (dependent), root is in Head. Spec scopes over Head, so the
    asymmetry holds. -/
theorem verbalizer_asymmetry_holds :
    DominantGTAsymmetry.holds
      ⟨CoPPosition.isDependent .spec, !CoPPosition.isDependent .head⟩ = true :=
  dominant_gt_asymmetry_from_scope .spec .head rfl rfl

/-- VBZ₁'s `GTSpec.toSpec` recovers the `Spec` used by `deriveVerb`. -/
theorem verbM_GT_toSpec_eq : verbM_GT.toSpec = verbM := rfl

/-- VBZ₂'s `GTSpec.toSpec` recovers the `Spec` used by `deriveVerb`. -/
theorem verbMH_GT_toSpec_eq : verbMH_GT.toSpec = verbMH := rfl

-- ============================================================================
-- §7: Empirical Generalisations
-- ============================================================================

/-! Cross-verb generalisations about the Mwaghavul ideophone-to-verb
    derivation (paper §3, summarised in eq. (13)). These are
    properties of the data, decidable from the `Ideophone` records in
    `Fragments/Mwaghavul/Basic.lean`. -/

/-- The M-H tonal melody is attested only in derived verbs (paper
    eq. 13e). No underived Mwaghavul verb has M-H. We test against
    the concrete ideophone data. -/
theorem mh_only_from_mh_verbalizer :
    ∀ i ∈ [bishool, kitiif, kodzoong, kitfor, korjong, mondos,
           vwaplas, jalpat, hanlayap, hamhoyof],
    i.verbType = .mh := by decide

/-- All M-tone ideophones produce uniform M output. -/
theorem m_verbs_all_uniform :
    ∀ i ∈ [zut, diis, kwaaj, vjaar, shweer, wuulash, fooyoop, vjayaap],
    deriveVerb i = i.tones.map (λ _ => TRN.M) := by decide

/-- Pluractional verbs always use M-H (paper eq. 13f). -/
theorem pluractional_uses_mh :
    jalpat.verbType = .mh ∧ hanlayap.verbType = .mh := ⟨rfl, rfl⟩

/-- Mwaghavul satisfies @cite{hyman-2006}'s tonal-language definition
    (3): "an indication of pitch enters into the lexical realisation
    of at least some morphemes." -/
theorem mwaghavul_is_tonal_hyman :
    Hyman2006.isTonalUnderHyman wordProsodicType = true := rfl

-- ============================================================================
-- §8: Connection to Distributed Morphology
-- ============================================================================

/-! The segmentally null verbalisers that trigger the tonal
    alternations are instances of the verbal categoriser **v** in
    Distributed Morphology (@cite{marantz-1997}, @cite{harley-2014}).
    The ideophonic base (noun, adjective, or adverb) is recategorised
    as a verb through merger with v, whose sole phonological exponent
    is a tonal melody. -/

open Morphology.DM

/-- The verbaliser produces verbal category. -/
def verbalizerCat : CatHead := CatHead.v_plain

theorem verbalizer_is_verbal : verbalizerCat.cat = .v := rfl

/-- Denominal verb derivation (n → v): `Recategorization.denominal`. -/
theorem denominal_ideophone_verb :
    Recategorization.denominal.source = .n ∧
    Recategorization.denominal.target = .v := ⟨rfl, rfl⟩

/-- Deadjectival verb derivation (a → v). -/
theorem deadjectival_ideophone_verb :
    Recategorization.deadjectival.source = .a ∧
    Recategorization.deadjectival.target = .v := ⟨rfl, rfl⟩

-- ============================================================================
-- §9: Expressiveness Preservation (after @cite{potts-2005})
-- ============================================================================

/-! @cite{akinbo-fwangwar-2026} §4.2 argues that derived ideophonic
    verbs retain @cite{potts-2005}-style expressive properties despite
    morphosyntactic integration: affective meaning, nondisplaceability,
    descriptive ineffability, context-dependence. This challenges
    @cite{dingemanse-akita-2017}'s prediction of inverse correlation
    between integration and expressiveness. -/

open Pragmatics.Expressives

/-- Derived ideophonic verbs exhibit all canonical expressive
    properties: independent, nondisplaceable, perspective-dependent,
    descriptively ineffable, immediate, repeatable, no perspective
    shift, no discourse antecedent required. -/
def ideophoneVerbProperties : SecondaryMeaningProperties :=
  { independent := true
    nondisplaceable := true
    perspectiveDependent := true
    descriptivelyIneffable := true
    immediate := true
    repeatable := true
    allowsPerspectiveShift := false
    requiresDiscourseAntecedent := false }

/-- Derived ideophonic verbs share the canonical expressive property
    profile. Definitionally `rfl` because both records instantiate
    the same field assignments — kept as `example` (not `theorem`)
    per CLAUDE.md "encoding conclusions as definitions" discipline.
    The empirical claim — that derived verbs bear these properties —
    is recorded by `ideophoneVerbProperties` itself; this `example`
    merely verifies our two records have matching field values. -/
example : ideophoneVerbProperties = expressiveProperties := rfl

end AkinboFwangwar2026
