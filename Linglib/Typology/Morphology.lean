import Linglib.Data.WALS.Aggregation
import Linglib.Data.WALS.Features.F20A
import Linglib.Data.WALS.Features.F21A
import Linglib.Data.WALS.Features.F21B
import Linglib.Data.WALS.Features.F22A
import Linglib.Data.WALS.Features.F23A
import Linglib.Data.WALS.Features.F24A
import Linglib.Data.WALS.Features.F25A
import Linglib.Data.WALS.Features.F25B
import Linglib.Data.WALS.Features.F26A
import Linglib.Data.WALS.Features.F27A
import Linglib.Data.WALS.Features.F28A
import Linglib.Data.WALS.Features.F29A
import Linglib.Data.WALS.Features.F62A
import Linglib.Data.WALS.Features.F79A
import Linglib.Data.WALS.Features.F79B
import Linglib.Data.WALS.Features.F80A

/-!
# Typology.Morphology
[bickel-nichols-2013a] [bickel-nichols-2013b] [bickel-nichols-2013c]
[nichols-bickel-2013] [nichols-bickel-2013a]
[nichols-bickel-2013b] [nichols-bickel-2013c] [nichols-bickel-2013d]
[baerman-brown-2013] [baerman-brown-2013a]
[dryer-2013-wals] [rubino-2013]

Per-language typological substrate for morphological mechanisms, covering
WALS chapters 20--29 (fusion, exponence, synthesis, locus of marking,
prefixing/suffixing, reduplication, syncretism) plus thematically-related
Ch 21B, 62, 79A, 79B, 80A.

Mirrors the `Linglib/Typology/{Possession,Negation,Comparison,Coordination,
Modality,Gender,Alignment,ArgumentStructure,Copulas}` substrate-extension
pattern. Fragment-importable.

## What lives here

The morphological **types** themselves -- `Fusion`, `Flexivity`, `Exponence`,
`ExponenceScope`, `VerbSynthesis`, `LocusOfMarking`, `PrefixSuffix`,
`Reduplication`, `LocusClause`, `LocusPossessive`, `WholeLanguageMarking`,
`ZeroMarkingAP`, `CaseSyncretism`, `VerbalSyncretism`, `TAMExponence`,
`ActionNominal`, `SuppletionTA`, `SuppletionImperative`, `VerbalNumber` --
plus the `MorphProfile` struct and the `fromWALS{20A..80A}` converters --
already live in `Morphology/MorphProfile.lean` (Fragments depend on
them directly).

This file adds the WALS-aggregate layer:

- `WALSCount` row struct + `WALSCount.totalOf` summer.
- Per-chapter WALS distribution lists (`ch20Distribution` ... `ch80Distribution`).
- WALS aggregate sample-size theorems (`ch20_total` ... `ch80_total`).
- Corpus-only generalisations: Greenberg's Universal 27 (suffixing
  dominates), concatenative dominance (Ch 20), reduplication majority (Ch 27),
  Ch 22 moderate-synthesis dominance.

## Out of scope

The 18-language `MorphProfile` sample and the cross-chapter theorems built
on it -- B&N orthogonality (concatenative × flexivity), agglutinating-vs-
fusional partition, head-marking-implies-high-synthesis -- live in
`Studies/BickelNichols2013.lean`.

[ackerman-malouf-2013]'s `LanguageData` (10-language E/I-complexity
sample) and the LCEC apparatus live in
`Studies/AckermanMalouf2013.lean`.
-/

set_option autoImplicit false

namespace Typology.Morphology

private abbrev ch20  := Data.WALS.F20A.allData
private abbrev ch21  := Data.WALS.F21A.allData
private abbrev ch21b := Data.WALS.F21B.allData
private abbrev ch22  := Data.WALS.F22A.allData
private abbrev ch23  := Data.WALS.F23A.allData
private abbrev ch24  := Data.WALS.F24A.allData
private abbrev ch25a := Data.WALS.F25A.allData
private abbrev ch25b := Data.WALS.F25B.allData
private abbrev ch26  := Data.WALS.F26A.allData
private abbrev ch27  := Data.WALS.F27A.allData
private abbrev ch28  := Data.WALS.F28A.allData
private abbrev ch29  := Data.WALS.F29A.allData
private abbrev ch62  := Data.WALS.F62A.allData
private abbrev ch79a := Data.WALS.F79A.allData
private abbrev ch79b := Data.WALS.F79B.allData
private abbrev ch80  := Data.WALS.F80A.allData

/-! `WALSCount` + `WALSCount.totalOf` are imported from
    `Linglib/Data/WALS/Aggregation.lean` (shared with the other
    Typology files that consume WALS distributions). -/

open Data.WALS (WALSCount)


/-- WALS Ch 20: exclusively concatenative is the most common single
    fusion type, exceeding both isolating and tonal. -/
theorem concatenative_most_common_wals :
    let concat := (ch20.filter (·.value == .exclusivelyConcatenative)).length
    let isolating := (ch20.filter (·.value == .exclusivelyIsolating)).length
    let tonal := (ch20.filter (·.value == .exclusivelyTonal)).length
    concat > isolating ∧ concat > tonal := by native_decide

/-- WALS Ch 27: productive reduplication (full or full+partial) is
    present in the majority of WALS-sampled languages. -/
theorem reduplication_in_majority_wals :
    let hasRedup := (ch27.filter (·.value != .noProductiveReduplication)).length
    hasRedup * 2 > ch27.length := by native_decide

/-- WALS Ch 22: most languages have 2--7 categories per verb word; the
    extremes (0--1 and 12--13) are rare. -/
theorem ch22_moderate_dominant :
    let mid := (ch22.filter (λ d =>
      d.value == .categoriesPerWord2_3 ||
      d.value == .categoriesPerWord4_5 ||
      d.value == .categoriesPerWord6_7)).length
    mid * 2 > ch22.length := by native_decide

end Typology.Morphology
