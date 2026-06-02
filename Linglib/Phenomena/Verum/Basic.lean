import Linglib.Semantics.Composition.Layered
import Linglib.Semantics.Highlighting

/-!
# Verum: theory-neutral substrate
[hohle-1992] [romero-han-2004] [repp-2013]
[gutzmann-hartmann-matthewson-2020] [goodhue-2022a]
[goodhue-2022b] [matthewson-2021] [bendezu-2023]
[martinez-vera-2026]

Cross-linguistic verum strategies. A "verum marker" is any morphological,
prosodic, or syntactic device whose felicitous use requires that the
truth of its scope proposition be at issue in a way that excludes (or
strongly contrasts with) its negation. The class is open and contested:
some accounts treat verum as polarity focus
([hohle-1992], [repp-2013], [goodhue-2022a]); others treat
it as a dedicated semantic operator on the common ground
([romero-han-2004], [gutzmann-hartmann-matthewson-2020]); still
others treat it as a discourse-management device
([matthewson-2021], [martinez-vera-2026]).

This file provides the **shared substrate**: the `VerumStrategy`
typology and the `VerumOperator` shared abstraction that both
`Studies/Hohle1992.lean` and `Studies/MartinezVera2026.lean` instantiate.

Per-marker data (which morpheme in which language) is **not** stored
here as `def` records — that pattern duplicates Fragment data and
ages badly. Instead, per-language verum-marker data lives in the
relevant Fragment file (`Fragments/{Lang}/PolarityMarking.lean` for
languages with `Strategy.verumFocus`-typed entries; `Fragments/{Lang}/
Evidentiality.lean` for morphological markers); the typological
inventory is reconstructed by the relevant `Studies/` files when
needed.

The architectural decision to land Verum as its own `Phenomena/`
directory rather than as a sub-section of `Polarity/` or `Questions/`
follows the basic-level grouping principle (CLAUDE.md): verum has a
self-contained literature with its own minimal pairs, cross-linguistic
typology, and competing formal analyses.

## Cross-linguistic empirical signature

A device counts as a verum strategy when it satisfies (at least) the
following felicity profile:

1. **Anti-discourse-initial**: infelicitous out-of-the-blue
   ([hohle-1992], [martinez-vera-2026]).
2. **Anti-unbiased-question response**: infelicitous when answering an
   unbiased polar question ([romero-han-2004],
   [gutzmann-hartmann-matthewson-2020]).
3. **Felicitous in the presence of contextual ¬p salience**: the
   negation of the scope proposition must be available in the prior
   discourse (assertion of ¬p, biased question towards ¬p, or — for
   Saraguro Kichwa — a reportative-evidential antecedent).

Theories disagree on the *mechanism* (focus over polarity, VERUM
operator over CommonGround membership, focus + discourse-management); they agree
on the *licensing profile*. This file documents the agreement via the
shared `VerumOperator` abstraction; the disagreement lives in the
`Studies/` files as different `VerumOperator`-instantiating predicates.
-/

namespace Phenomena.Verum.Basic

open Semantics.Composition.Layered (BiLayered)
open Semantics.Highlighting (HighlightingContext)

/-- Cross-linguistic strategy types for verum marking
    ([gutzmann-hartmann-matthewson-2020] typology).

    Note the partial overlap with `Typology.PolarityMarking.Strategy`,
    which has a single `verumFocus` cell that this enum's `prosodic`
    case generalises (Höhle 1992 verum focus is the prosodic verum
    strategy par excellence). The two enums coexist because
    `PolarityMarking.Strategy` partitions ALL polarity-marking devices
    while `VerumStrategy` finer-grains the verum slice. -/
inductive VerumStrategy where
  | prosodic
  | morphological
  | lexical
  | syntactic
  deriving DecidableEq, Repr, Inhabited

/-- A verum operator: a function from a discourse context and a layered
    proposition to a felicity proposition.

    Inhabitants of this structure formalise different verum-marker
    analyses across the literature:

    * `Hohle1992.verumFocusOp` (paired with
      `verumFelicitous`) — Höhle's polarity-focus account.
    * `MartinezVera2026.miFelicitous`
      (instantiated with the polar partition) — MV's focus-marker
      account, equivalent to Höhle's on the polar reduction (see
      `mi_polar_iff_verumFelicitous` in that file).
    * Future Goodhue 2022a, Bill-Koev 2021, Bassel 2023, Matthewson 2021
      analyses plug in here.

    The shared signature lets cross-paper bridge / refutation theorems
    be stated uniformly: "instance A and instance B agree on input X"
    or "instance A and instance B differ on input Y." -/
structure VerumOperator (W : Type*) where
  /-- The felicity condition: when does the verum-marker license the
      utterance in this discourse context for this layered prejacent? -/
  felicitous : HighlightingContext W → BiLayered W → Prop

end Phenomena.Verum.Basic
