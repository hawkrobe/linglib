import Linglib.Fragments.English.TemporalExpressions

/-!
# Japanese Temporal Connectives Fragment

Lexical entries for Japanese temporal subordinating connectives *前 mae*
('before') and *後 ato* ('after'), typed by `TemporalConnectiveEntry`.

The key cross-linguistic observation (O&ST 2024, §3): *mae* requires
non-past tense in its complement even in past-tense contexts, while
*ato* allows past tense. This morphological asymmetry independently
supports the veridicality contrast — *mae* presents the complement
as unrealized, *ato* as realized.

## References

- Ogihara, T. & Steinert-Threlkeld, S. (2024). An interval-based
  semantics for *before* and *after*. §3.
- Ogihara, T. (1996). Tense, attitudes, and scope.
-/

namespace Fragments.Japanese.TemporalConnectives

open Fragments.English.TemporalExpressions

-- ============================================================================
-- § 1: Entries
-- ============================================================================

/-- Japanese *前 mae* ('before'): licenses NPIs (*dare-mo* 'anyone'),
    complement requires non-past tense even in past contexts.
    Non-veridical: 「爆弾が誰かが解除する前に爆発した」
    "The bomb exploded before anyone defused it" — compatible with
    nobody defusing it. -/
def mae : TemporalConnectiveEntry :=
  { form := "前"
  , order := .before
  , licensesNPI := true
  , defaultReading := .beforeStart
  , coercedReading := some .beforeFinish
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := false }

/-- Japanese *後 ato* ('after'): does not license NPIs,
    complement allows past tense.
    Veridical: 「彼女が着いた後に彼は出発した」
    "He left after she arrived" — entails she arrived. -/
def ato : TemporalConnectiveEntry :=
  { form := "後"
  , order := .after
  , licensesNPI := false
  , defaultReading := .afterFinish
  , coercedReading := some .afterStart
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := true }

-- ============================================================================
-- § 2: Cross-Linguistic Agreement
-- ============================================================================

/-- Japanese *mae* and English *before* agree on all semantic properties. -/
theorem mae_matches_before :
    mae.order = before_.order ∧
    mae.licensesNPI = before_.licensesNPI ∧
    mae.defaultReading = before_.defaultReading ∧
    mae.complementVeridical = before_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Japanese *ato* and English *after* agree on all semantic properties. -/
theorem ato_matches_after :
    ato.order = after_.order ∧
    ato.licensesNPI = after_.licensesNPI ∧
    ato.defaultReading = after_.defaultReading ∧
    ato.complementVeridical = after_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The veridicality asymmetry holds cross-linguistically:
    *mae* is non-veridical, *ato* is veridical. -/
theorem veridicality_asymmetry :
    mae.complementVeridical = false ∧ ato.complementVeridical = true :=
  ⟨rfl, rfl⟩

/-- The NPI licensing asymmetry holds cross-linguistically:
    *mae* licenses NPIs, *ato* does not. -/
theorem npi_asymmetry :
    mae.licensesNPI = true ∧ ato.licensesNPI = false :=
  ⟨rfl, rfl⟩

end Fragments.Japanese.TemporalConnectives
