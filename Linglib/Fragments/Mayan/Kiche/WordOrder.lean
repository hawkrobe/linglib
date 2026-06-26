import Linglib.Features.WordOrder

/-!
# K'iche' word-order profile [mondloch-2017] [clemens-coon-2018]

K'iche' is not coded in WALS Chs 81/82/83 (ISO `quc` is absent), so
the profile is grammar-grounded from [mondloch-2017] rather than
via `WordOrderProfile.ofWALS`. Mondloch documents verb-initial order:
VS for intransitives and VOS for transitives.

## A contested classification

The `.vos` choice follows Mondloch's preferred-order analysis. The
broader Mayanist literature on basic word order in K'iche'an (and
Mayan more generally) is contested: K'iche' admits both VOS and VSO
for transitive clauses, with subject-initial orders increasingly
attested under Spanish contact. Sister-language WALS codings
illustrate the divergence — Kaqchikel `cak` is `.vos` in Ch 81,
Tzutujil `tzj` is `.noDominantOrder`, Mam `mam` is `.vso` (different
branch but verb-initial). [clemens-coon-2018] surveys
derivational accounts of verb-initiality across Mayan; an alternative
substrate commitment would be `.noDominant` (parallel to Tzutujil) or
`.vso` per a corpus analysis. The Fragment commits to `.vos` because
that is Mondloch's explicit description; consumers wanting a different
basic-order claim should override. The `.vs` svOrder + `.vo` ovOrder
commitments are robust across the contestation (K'iche' is verb-
initial in both intransitive and transitive clauses).
-/

namespace Kiche

/-- K'iche' word-order profile, grammar-grounded from
    [mondloch-2017] ("the preferred word order appears to be:
    verb-subject", with VOS for transitives). Not in WALS Chs
    81/82/83 — fields override `.notInWALS`. The `.vos` basic-order
    commitment is contested across Mayanist literature; see module
    docstring. -/
def wordOrder : WordOrder.WordOrderProfile :=
  { basicOrder := .vos
    svOrder := .vs
    ovOrder := .vo }

/-- Drift sentinel: the profile is internally consistent. -/
theorem wordOrder_consistent : wordOrder.IsConsistent := by decide

end Kiche
