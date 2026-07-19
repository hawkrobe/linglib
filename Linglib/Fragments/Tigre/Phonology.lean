/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Root.Consonantal
import Linglib.Fragments.Tigrinya.Phonology

/-!
# Tigre Phonological Inventory and Verbal Roots
[raz-1980] [raz-1983] [lowenstamm-prunet-1988]
[faust-2014] [faust-2015] [faust-2017b]
[faust-lampitelli-2026]

Theory-neutral IPA inventory and the Tigre verbal roots used in the
[faust-lampitelli-2026] guttural-synersis analysis.

Per the paper §2.1: "The vocalic systems of Tigre and Tigrinya are
quite similar. In both languages, one finds six full vowel qualities
[a, ʌ, i, u, e, o] and a weak vowel [ɨ]." The guttural inventories
also coincide: ʔ, h, ʕ, ħ in both, with χ/ʁ unattested in either
(paper n. 14).

This file therefore **re-exports** the Tigrinya `Vowel` and `Guttural`
types per [lowenstamm-prunet-1988]'s observation that the two
languages share their vowel and guttural systems. The differences
between Tigre and Tigrinya lie in:

* templatic morphology (Tigre's PRF [samʕa] vs Tigrinya's
  [sʌβʌrʌ]; Tigre dialects exhibit different verb stems per
  [raz-1980], [raz-1983]),
* vowel harmony processes (Tigre rounding/lowering harmonies per
  [lowenstamm-prunet-1988], [faust-2017b], mostly
  irrelevant for the present synersis discussion).

## Cross-reference: PHOIBLE 2.0

[moran-mccloy-2019] has two Tigre inventories (both glottocode
`tigr1270`): ID 130 (donor `spa`) with 87 phonemes including length
and gemination contrasts, and ID 576 (donor `upsid`) with 33
phonemes (no length). Both confirm the four-guttural inventory
`{ʔ, h, ʕ, ħ}` exactly as the paper claims, with [χ, ʁ] absent
(paper n. 14, confirmed). The 7-vowel inventory is also present in
both PHOIBLE inventories, but transcribed differently: PHOIBLE
follows [raz-1980]'s long-vowel notation (`iː, uː, e̞ː, o̞ː,
a̟ː, ə, ɜ`) where the paper follows [buckley-1997-vowel-length]'s
no-length analysis (`i, u, e, o, a, ɨ, ʌ`). The seven-element
*partition* is identical: 5 peripheral + 1 weak (ə ↔ ɨ) + 1
marked-low (ɜ ↔ ʌ); the dispute is over whether the peripheral
five are phonologically long. Paper p. 6 explicitly notes "for
Tigre the facts are less clear" and sides with the no-length
analysis.

The verbal roots below are the Tigre exemplars from
[faust-lampitelli-2026] eq. (5)-(6) and eq. (12), used for the
parallel-language demonstration of guttural synersis. Naming
convention follows `Fragments/Tigrinya/Phonology.lean`: ASCII
identifiers; IPA forms in docstrings.
-/

namespace Tigre.Phonology

open Morphology

/-- Re-export the Tigrinya vowel type for Tigre. The two languages
    share the same seven-vowel inventory per paper §2.1 +
    [lowenstamm-prunet-1988]. -/
abbrev Vowel := Tigrinya.Phonology.Vowel

/-- Re-export the Tigrinya guttural type for Tigre. Both languages
    have the same four attested gutturals (paper §2.1, n. 14). -/
abbrev Guttural := Tigrinya.Phonology.Guttural

-- ============================================================================
-- § 1: Tigre verbal roots (the F&L 2026 working set)
-- ============================================================================

/-- √mzn — 'weigh'. Tigre. Paper 2-JUSS [ti-mazzɨn] / IMP [mazzɨn]
    (eq. 5a) — non-guttural triradical, control case for the [ɨ]
    epenthesis in initial-cluster position. -/
def weigh : ConsonantalRoot String := ⟨["m", "z", "n"]⟩

/-- √fgr — 'leave'. Tigre. Paper PRF-3MSG [fagr-a] / 2-JUSS
    [ti-fgʌr] (eq. 6a, 5b). Non-guttural triradical baseline. -/
def leave : ConsonantalRoot String := ⟨["f", "g", "r"]⟩

/-- √ħtʕb — 'wash'. Tigre. Paper PRF-3MSG [ħatʔb-a] / 2-JUSS
    [ti-hitʔʕab] (eq. 6b) — the bold [i] in 2-JUSS marks epenthetic
    [ɨ] inserted to license the medial pharyngeal codas. -/
def wash : ConsonantalRoot String := ⟨["ħ", "t", "ʕ", "b"]⟩

/-- √hrb — 'flee'. Tigre. Paper PRF-3MSG [harb-a] / 2-JUSS
    [ti-hirʌb] (eq. 6c), where the bold [i] marks the epenthetic
    [ɨ] licensing the initial guttural. -/
def flee : ConsonantalRoot String := ⟨["h", "r", "b"]⟩

/-- √knʕ — 'get up'. Tigre. Paper 2-JUSS [ti-kʔnʌʕ] / IMP [kʔɨnʌʕ]
    (eq. 5c). Quadri-radical (k, ʔ, n, ʕ) — illustrates how an
    initial-cluster epenthetic [ɨ] interacts with a final guttural. -/
def getUp : ConsonantalRoot String := ⟨["k", "ʔ", "n", "ʕ"]⟩

/-- √fgr — 'whip'. Tigre. Paper 2-IMP.M [(ti-)fʌggɨr] (eq. 12a) —
    the regular Tigre imperfective with medial geminate, baseline
    for eq. (12)'s /CʌGV/ → CGV in Tigre imperfectives discussion. -/
def whip : ConsonantalRoot String := ⟨["f", "g", "r"]⟩

/-- √sʔl — 'ask'. Tigre. Paper 2-IMP.M [ti-sʔil] (eq. 12b). Same
    root as Tigrinya. The bold [i] marks epenthetic [ɨ]. -/
def ask : ConsonantalRoot String := ⟨["s", "ʔ", "l"]⟩

/-- √tʔʕn — 'load'. Tigre. Paper 2-IMP.M [ti-tʔʕin] (eq. 12c).
    Quadri-radical (t, ʔ, ʕ, n) with medial pharyngeal /ʕ/. -/
def load : ConsonantalRoot String := ⟨["t", "ʔ", "ʕ", "n"]⟩

/-- √shk — 'uncover'. Tigre. Paper 2-IMP.M [ti-shik] (eq. 12d). -/
def uncoverTigre : ConsonantalRoot String := ⟨["s", "h", "k"]⟩

/-- √sħb — 'pull'. Tigre version of Tigrinya √sħb. Paper Tigre form
    [ti-sħib] from /tisʌħib/ (eq. 26d). -/
def pull : ConsonantalRoot String := ⟨["s", "ħ", "b"]⟩

end Tigre.Phonology
