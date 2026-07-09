import Linglib.Features.WordOrder

/-!
# K'iche' Word-Order Profile

Grammar-grounded word-order profile for K'iche' (K'ichean Mayan) from
[mondloch-2017], who documents verb-initial order: VS for intransitives
and VOS for transitives. K'iche' is not coded in WALS Chs 81/82/83 (ISO
`quc` is absent), so the fields override `.notInWALS` rather than
deriving via `WordOrderProfile.ofWALS`.

## Implementation notes

The `.vos` basic order follows Mondloch's preferred-order analysis.
Basic word order in K'iche'an (and Mayan generally) is contested:
K'iche' admits both VOS and VSO for transitives, with subject-initial
orders increasingly attested under Spanish contact. Sister-language
WALS codings illustrate the divergence — Kaqchikel `cak` is `.vos` in
Ch 81, Tzutujil `tzj` is `.noDominantOrder`, Mam `mam` is `.vso`
(different branch but verb-initial). [clemens-coon-2018] surveys
derivational accounts of Mayan verb-initiality; an alternative
substrate commitment would be `.noDominant` (parallel to Tzutujil) or
`.vso` per a corpus analysis. The `.vs`/`.vo` commitments are robust
across the contestation — K'iche' is verb-initial in both intransitive
and transitive clauses.
-/

namespace Kiche

/-- K'iche' word-order profile, grammar-grounded from [mondloch-2017]
    ("the preferred word order appears to be: verb-subject", VOS for
    transitives); not in WALS Chs 81/82/83, so fields override
    `.notInWALS`. -/
def wordOrder : WordOrder.WordOrderProfile :=
  { basicOrder := .vos
    svOrder := .vs
    ovOrder := .vo }

/-- Drift sentinel: the profile is internally consistent. -/
theorem wordOrder_consistent : wordOrder.IsConsistent := by decide

end Kiche
