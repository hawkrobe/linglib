import Linglib.Fragments.Mam.ExtractionMorphology

/-!
# Oblique Extraction Data

@cite{elkins-imanishi-coon-2026}

Theory-neutral empirical data on oblique extraction morphology in SJO Mam.

The primary data is in `Fragments.Mam.ExtractionMorphology`, which defines
data points, judgments, and generalizations. Bridge files connecting
this data to specific theories are in `Phenomena/FillerGap/Bridge/`:

- `MinimalismOblExtraction.lean`: Agree + Spellout analysis
- `MayanExtractionComparison.lean`: Mam =(y)a' vs. K'iche' *wi*

## Key Empirical Findings

1. **=(y)a' is oblique-specific**: Subject (AF) and object extraction do
   not trigger it (§3).
2. **=(y)a' is clause-size-sensitive**: Licensed iff Voice is projected (§6).
3. **Multiple spellout**: In long-distance extraction, =(y)a' can appear
   on both matrix and embedded predicates (Table 4, §6.2).
4. **Island-sensitive**: =(y)a' is blocked by islands, arguing against
   a resumptive analysis (§7.1).
5. **Not Agent Focus**: Co-occurs with passive *-njtz* (§7.2).
6. **Temporal obliques exempt**: 'when' does not trigger =(y)a' (§8.1).

## References

- Elkins, N., Y. Imanishi & J. Coon (2026). Wh-movement and oblique
  extraction in SJO Mam.
-/
