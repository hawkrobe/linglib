import Linglib.Phenomena.Conditionals.LeftNested.Data
import Linglib.Fragments.Japanese.Conditionals
import Linglib.Fragments.German.Conditionals

/-!
# Left-Nested Conditionals: Bridge

Connects the LNC empirical data from Lassiter (2025) to the conditional
marker typology in `Fragments/{Language}/Conditionals.lean`.

## Bridge Structure

1. **Marker type verification**: the LNC acceptability pattern correlates
   with marker type — PC-compatible markers (`.both`) yield acceptable LNCs,
   HC-only markers (`.hcOnly`) yield degraded LNCs.
2. **Per-datum marker connection**: links specific LNC examples to their
   corresponding Fragment marker entries.
-/

namespace Phenomena.Conditionals.LeftNested.Bridge

open Semantics.Conditionals (ConditionalMarkerType)

-- ════════════════════════════════════════════════════════════════
-- § Marker Type Verification
-- ════════════════════════════════════════════════════════════════

/-!
The LNC acceptability pattern correlates with marker type:
- PC-compatible markers (`.both`) yield acceptable LNCs
- HC-only markers (`.hcOnly`) yield degraded LNCs

These guards verify that the Fragment marker entries have the expected
types, connecting the LNC empirical data to the marker typology.
-/

-- PC-compatible markers → acceptable LNCs
#guard Fragments.Japanese.Conditionals.nara.markerType == .both
#guard Fragments.German.Conditionals.wenn.markerType == .both

-- HC-only markers → degraded LNCs
#guard Fragments.Japanese.Conditionals.ra.markerType == .hcOnly
#guard Fragments.German.Conditionals.falls.markerType == .hcOnly

-- ════════════════════════════════════════════════════════════════
-- § Acceptability–Marker Type Correlation
-- ════════════════════════════════════════════════════════════════

/-- Japanese nara (PC-compatible) yields acceptable LNC. -/
theorem nara_ok_and_pc_compatible :
    ex15_japaneseNara.acceptability == "ok" ∧
    Fragments.Japanese.Conditionals.nara.markerType == .both :=
  ⟨rfl, rfl⟩

/-- Japanese -ra (HC-only) yields degraded LNC. -/
theorem ra_odd_and_hc_only :
    ex16_japaneseRa.acceptability == "odd" ∧
    Fragments.Japanese.Conditionals.ra.markerType == .hcOnly :=
  ⟨rfl, rfl⟩

/-- German wenn (PC-compatible) yields acceptable LNC. -/
theorem wenn_ok_and_pc_compatible :
    ex20_germanWenn.acceptability == "ok" ∧
    Fragments.German.Conditionals.wenn.markerType == .both :=
  ⟨rfl, rfl⟩

/-- German falls (HC-only) yields degraded LNC. -/
theorem falls_marginal_and_hc_only :
    ex21_germanFalls.acceptability == "marginal" ∧
    Fragments.German.Conditionals.falls.markerType == .hcOnly :=
  ⟨rfl, rfl⟩

end Phenomena.Conditionals.LeftNested.Bridge
