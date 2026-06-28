import Mathlib.Data.List.Basic
import Linglib.Core.Computability.Subregular.Logic.Transduction

/-!
# Dolatian 2020: pre-inflectional vowel reduction and the Prosodic Stem
[dolatian-2020]

Dolatian, H. (2020). *Computational locality of cyclic phonology in Armenian.*
PhD dissertation, Stony Brook University.

Eastern Armenian Destressed High Vowel Reduction (DHR) overapplies *before
V-initial inflection* but not *before C-initial inflection*: *amusín* 'husband'
→ *amusn-óv* (INST, V-initial: reduces) vs *amusin-nér* (PL, C-initial: no
reduction). Dolatian argues the conditioning constituent is neither the foot
(§2.5.3.1, fails) nor a (recursive) prosodic word (§2.5.3.2, argued *against*),
but Downing's **Prosodic Stem** (PStem), an intermediate constituent mapped from
the morphological stem. Before V-initial inflection the PStem is *misaligned*
from syllable boundaries (onset maximization resyllabifies the stem-final
consonant) and *expands*; expansion triggers the PStem-level cophonology, which
in Eastern Armenian reduces, in Western Armenian only shifts stress (§2.5.4 (76),
(78)). Before C-initial inflection the PStem stays isomorphic with the MStem, so
nothing triggers.

This is **not** an OT analysis: Dolatian formalizes it as a serial/cyclic
derivation (and computationally as MSO logical transductions), explicitly noting
(fn. 20) that an OT/Match-theoretic formalization is an *alternative* he does not
adopt. We therefore model the mechanism derivationally — onset-maximization
syllabification → PStem misalignment → PStem-cophonology → DHR — rather than as
constraint optimization. DHR is *derived* from the mechanism (see `dhr_iff`), not
stipulated as a dialect × inflection table.

Dolatian also formalizes the phonology *computationally*, as MSO/quantifier-free
logical transductions over word models (§4), whose locality (QF ⟹ Input Strictly
Local, hence learnable) is his central computational claim. The final section
realizes the Eastern Armenian cophonology in that framework
(`Core.Computability.Subregular.Logic`): DHR is the local rewrite `H → ∅ / _ C V`,
and the cyclic derivation is transduction composition. Reproducing the *amusin*
contrast segmentally recovers the serial result by a different route
(`transduction_matches_trigger`).

## Main definitions

* `Dolatian2020.pstemMisaligned` — the MStem boundary no longer coincides with a
  syllable boundary (V-initial suffix resyllabified the stem-final consonant).
* `Dolatian2020.dhrApplies` — DHR derived from PStem expansion × dialect cophonology.
* `Dolatian2020.dhrEast` / `dhrWest` — the dialect cophonologies as quantifier-free
  logical transductions; `dhrEast` deletes the destressed high vowel before `C V`.
-/

namespace Dolatian2020

/-- Coarse segment type — enough for onset-maximization syllabification. -/
inductive Seg | C | V
  deriving DecidableEq, Repr

/-- An inflectional suffix, as a segment string (only its initial segment matters
    for syllabification/misalignment). -/
abbrev Suffix := List Seg

/-- Western vs Eastern Armenian. The dialects share the morphology and the PStem;
    they differ only in the PStem-level cophonology ([dolatian-2020] §2.5.4 (76)). -/
inductive Dialect | eArm | wArm
  deriving DecidableEq, Repr

/-- The PStem-level cophonology: Eastern Armenian's PStem triggers stress *and*
    DHR; Western Armenian's triggers only stress ([dolatian-2020] (76)). -/
def Dialect.pstemReduces : Dialect → Bool
  | .eArm => true
  | .wArm => false

/-- Onset maximization: a V-initial suffix pulls a single stem-final consonant
    into its onset, resyllabifying it across the MStem boundary. A C-initial
    suffix leaves the boundary at a syllable edge. -/
def resyllabifiesAcrossStemBoundary (stem : List Seg) (suf : Suffix) : Bool :=
  (stem.getLast? == some .C) && (suf.head? == some .V)

/-- PStem misalignment ([dolatian-2020] §2.5.3): the MStem boundary no longer
    coincides with a syllable boundary, because a V-initial suffix resyllabified
    the stem-final consonant. -/
def pstemMisaligned (stem : List Seg) (suf : Suffix) : Bool :=
  resyllabifiesAcrossStemBoundary stem suf

/-- The PStem-level cophonology is triggered exactly when the PStem is
    misaligned and so expands by incorporating the V-initial suffix
    ([dolatian-2020]: the PStem cophonology applies *only* to misaligned PStems). -/
def pstemCophonologyTriggered (stem : List Seg) (suf : Suffix) : Bool :=
  pstemMisaligned stem suf

/-- Destressed High Vowel Reduction applies iff the expanded PStem-level
    cophonology is triggered **and** the dialect's PStem reduces. The pattern is
    *derived* from the cyclic mechanism, not a stipulated table (see `dhr_iff`). -/
def dhrApplies (d : Dialect) (stem : List Seg) (suf : Suffix) : Bool :=
  pstemCophonologyTriggered stem suf && d.pstemReduces

/-! ### Worked forms: *amusin* 'husband' with V- and C-initial inflection -/

/-- *amusin* = a.mu.sin, consonant-final. -/
def amusin : List Seg := [.V, .C, .V, .C, .V, .C]
/-- *-ov* (INST): V-initial. -/
def sufOv  : Suffix := [.V, .C]
/-- *-ner* (PL): C-initial. -/
def sufNer : Suffix := [.C, .V, .C]

-- The misalignment contrast is the V- vs C-initial discriminator, prior to DHR.
theorem ov_misaligns  : pstemMisaligned amusin sufOv  = true  := by decide
theorem ner_aligned   : pstemMisaligned amusin sufNer = false := by decide

-- The faithful 2×2 ([dolatian-2020] (78)): DHR overapplies only in EArm before
-- V-initial inflection.
theorem earm_ov_reduces  : dhrApplies .eArm amusin sufOv  = true  := by decide  -- amusn-óv
theorem earm_ner_blocks  : dhrApplies .eArm amusin sufNer = false := by decide  -- amusin-nér
theorem warm_ov_blocks   : dhrApplies .wArm amusin sufOv  = false := by decide  -- amusin-óv (stress only)
theorem warm_ner_blocks  : dhrApplies .wArm amusin sufNer = false := by decide

/-- Characterization: pre-inflectional DHR is exactly Eastern Armenian with a
    misaligned PStem. The V- vs C-initial split falls out of onset-maximization
    syllabification; the dialect split out of the PStem cophonology — neither is
    stipulated as a lookup table. -/
theorem dhr_iff (d : Dialect) (stem : List Seg) (suf : Suffix) :
    dhrApplies d stem suf = true ↔ d = .eArm ∧ pstemMisaligned stem suf = true := by
  cases d <;>
    simp [dhrApplies, Dialect.pstemReduces, pstemCophonologyTriggered]

/-! ### The cophonology as a quantifier-free logical transduction

[dolatian-2020]'s computational formalization (§4): the cophonology as an MSO/quantifier-free
logical transduction over a word model. Eastern Armenian DHR is the local rewrite `H → ∅ / _ C V`
— the stem-final high vowel drops when a following consonant resyllabifies into a V-initial
suffix's onset — realized with `Core.Computability.Subregular.Logic`. The rewrite reads a bounded
right context, so it is quantifier-free, hence subregular and learnable (Dolatian's thesis). -/

section Transductions

open Subregular.Logic

/-- Segments refined with the high-vowel target `H` of DHR. -/
inductive Phone | C | V | H
  deriving DecidableEq, Repr

private def x : Term (Fin 1) := .var 0

/-- Eastern Armenian DHR as a logical transduction: delete a high vowel before `C V` (the
resyllabification-and-expansion context); every other segment is faithful. A high vowel in that
context matches no clause and is dropped. -/
def dhrEast : Transduction Phone Phone where
  copies := 1
  clause _ :=
    [ (QF.conj (.atom (.label .H x))
        (QF.neg (QF.conj (.atom (.label .C x.succ)) (.atom (.label .V x.succ.succ)))), .H),
      (.atom (.label .C x), .C), (.atom (.label .V x), .V) ]

/-- Western Armenian: the PStem cophonology shifts stress but does not reduce, so the high vowel is
faithful in every context ([dolatian-2020] (76)). -/
def dhrWest : Transduction Phone Phone where
  copies := 1
  clause _ := [(.atom (.label .H x), .H), (.atom (.label .C x), .C), (.atom (.label .V x), .V)]

/-- *amusin* a-mu-si-n, segmentally `V C V C H C` (the stem-final high vowel is `H`). -/
def amusinP : List Phone := [.V, .C, .V, .C, .H, .C]
/-- *-ov* (INST), V-initial. -/
def ovP : List Phone := [.V, .C]
/-- *-ner* (PL), C-initial. -/
def nerP : List Phone := [.C, .V, .C]

-- Eastern Armenian: the high vowel deletes before V-initial *-ov* (→ amusn-ov) but survives before
-- C-initial *-ner* (→ amusin-ner) — Dolatian's (78), recovered at the segmental level.
theorem dhrEast_ov : dhrEast.apply (amusinP ++ ovP) = [.V, .C, .V, .C, .C, .V, .C] := by decide
theorem dhrEast_ner : dhrEast.apply (amusinP ++ nerP) = amusinP ++ nerP := by decide
-- Western Armenian reduces in neither context.
theorem dhrWest_ov : dhrWest.apply (amusinP ++ ovP) = amusinP ++ ovP := by decide

/-- The transduction's segmental action agrees with the serial trigger `dhrApplies`: the form
changes exactly when (Eastern, misaligned) DHR is predicted — the two formalizations coincide. -/
theorem transduction_matches_trigger :
    (dhrEast.apply (amusinP ++ ovP) ≠ amusinP ++ ovP ∧ dhrApplies .eArm amusin sufOv = true) ∧
    (dhrEast.apply (amusinP ++ nerP) = amusinP ++ nerP ∧ dhrApplies .eArm amusin sufNer = false) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

/-- Cyclicity ([dolatian-2020]: interactionist derivation = transduction composition): a further
cophonology cycle composes with the first, and DHR is stable under re-application. -/
theorem dhr_cyclic_stable :
    dhrEast.applyComp dhrEast (amusinP ++ ovP) = dhrEast.apply (amusinP ++ ovP) := by decide

end Transductions

end Dolatian2020
