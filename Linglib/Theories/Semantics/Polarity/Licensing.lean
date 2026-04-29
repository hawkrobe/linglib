import Linglib.Core.Logic.NaturalLogic
import Linglib.Features.LicensingContext

/-!
# Semantics.Polarity.Licensing
@cite{ladusaw-1979} @cite{kadmon-landman-1993} @cite{zwarts-1998}
@cite{von-fintel-1999} @cite{chierchia-2006}
@cite{horn-1996} @cite{hoeksema-1983} @cite{bhatt-pancheva-2004}
@cite{heim-2006} @cite{iatridou-2000} @cite{dayal-1996}
@cite{van-rooy-2003}

Monotonicity-based licensing infrastructure for polarity-sensitive items:
the `LicensingContext` enum (~22 contexts), the `LicensingMechanism`
classification (K&L domain-widening + strengthening, plus refinements
for non-K&L licensing), the `ContextProperties` synthesis bundling
DE-strength signatures with mechanism + Strawson-DE flagging, and the
canonical `contextProperties` map projecting each context to its
theoretical lineage.

## Provenance

Split from `Core/Lexical/PolarityItem.lean` in the cleanup that
dissolved `Core/Lexical/`. The Israel scalar machinery
(`ScalarValue`/`ScalarDirection`/`Canonicity`/`LikelihoodEffect`)
moved to the sibling file `Typology/PolarityItem.lean` (which also
holds `PolarityItemEntry` and `predictCanonicity`); the cross-file
gap between Israel's scalar model and Ladusaw/K&L's monotonicity
model is documented there.

## Framework commitment

The `contextProperties` map encodes the **monotonicity-based**
licensing tradition: @cite{ladusaw-1979} (DE-licensing), @cite{zwarts-1998}
(anti-additive/anti-morphic refinement), @cite{kadmon-landman-1993}
(domain widening + strengthening), @cite{von-fintel-1999} (Strawson-DE
extension), and the every-restrictor-as-LAA result (variously
attributed to Zwarts 1981 / van Benthem 1986 / Sánchez Valencia 1991;
none currently in `references.bib`).
Per-paper classifiers (`Ladusaw1979.licensingStrength`,
`KadmonLandman1993.klExplanation`) project from this single record
rather than parallel-stipulating.

The `LicensingMechanism` 5-way enum refines the original 3-way
{byStrengthening, byGenericIndefinite, byOtherMechanism} into the
substantively distinct cases:

- `byStrengthening`: K&L-canonical DE + widening (covers Ladusaw 1979).
- `byGenericIndefinite`: non-DE FC any (modals, generics, free relatives).
- `byStrawsonDE`: licensing via Strawson entailment (superlatives) —
  @cite{von-fintel-1999} / Herdan & Sharvit (UNVERIFIED — bib entry missing).
- `byEntropy`: entropy-based licensing (questions per @cite{van-rooy-2003}).
- `strengtheningFails`: contexts that *don't* license despite surface
  appearance (e.g., NP-comparatives that lack covert clausal structure).

The earlier `byOtherMechanism` constructor used by some study files
(e.g., `KadmonLandman1993.lean` for ungrammatical examples) maps to
`strengtheningFails`; the legitimate non-K&L cases (entropy questions,
Strawson-DE superlatives) get their own dedicated constructors.

## Out of scope: Israel↔Ladusaw cross-framework gap

This file's `contextProperties.signature` field is Ladusaw/Zwarts/P&W
canonical: each context has *one* DE/anti-additive/anti-morphic
signature, regardless of which item is being licensed. Israel's scalar
model rejects this per-context signature framing — for him,
polarity-sensitivity is determined by the item's scale + role, not by
the context's monotonicity. The cross-framework gap is real and is
NOT closed by this restructure; see `Typology/PolarityItem.lean` for
the Israel-side machinery and the documented refutation-theorem TODO.
-/

namespace Semantics.Polarity.Licensing

open Features (LicensingContext)

-- ════════════════════════════════════════════════════
-- § 1. Licensing Mechanism (refined 5-way)
-- ════════════════════════════════════════════════════

/-- The mechanism by which a context licenses NPIs.

    @cite{kadmon-landman-1993} unify NPI licensing under domain widening +
    strengthening. The substrate refines K&L's original 3-way classification
    into 5 substantively distinct cases.

    - `byStrengthening` — DE contexts where widening strengthens the assertion.
      Covers @cite{ladusaw-1979}'s monotonicity-based licensing.
    - `byGenericIndefinite` — Non-DE contexts (modals, generics, free relatives)
      where *any* surfaces as the generic indefinite (FC any).
    - `byStrawsonDE` — Strawson-DE licensing (superlatives per
      Herdan & Sharvit's superlative-NPI work [UNVERIFIED — bib entry
      missing] and @cite{von-fintel-1999}).
    - `byEntropy` — Entropy-based licensing (questions per @cite{van-rooy-2003}).
    - `strengtheningFails` — contexts that *don't* license despite surface
      appearance (e.g., NP-comparatives that lack covert clausal structure).
      Used by study files (e.g., `KadmonLandman1993.lean`) for ungrammatical
      examples, replacing the earlier `byOtherMechanism` constructor. -/
inductive LicensingMechanism where
  | byStrengthening
  | byGenericIndefinite
  | byStrawsonDE
  | byEntropy
  | strengtheningFails
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Context Properties (single source of truth)
-- ════════════════════════════════════════════════════

/-- The bundle of theory-relevant facts about a licensing context.

    Every classification of `LicensingContext` (DE strength, K&L mechanism,
    canonical example, citation lineage) projects out of this single record.
    Per-paper classifiers (`Ladusaw1979.licensingStrength`,
    `KadmonLandman1993.klExplanation`) are derivations from `contextProperties`,
    not parallel stipulations. -/
structure ContextProperties where
  /-- Icard signature: locates the context in the natural-logic lattice. -/
  signature : Core.NaturalLogic.EntailmentSig
  /-- K&L mechanism: how this context licenses NPIs. -/
  mechanism : LicensingMechanism
  /-- A canonical English example. -/
  prototype : String
  /-- BibTeX keys for the works that established this classification. -/
  citations : List String
  /-- Strawson-DE flag (@cite{von-fintel-1999}): when `true`, the
      `signature` field over-promises classical DE — the context is in
      fact only DE under presupposition (Strawson-DE), not classically.
      Default `false` (the signature stands as a classical claim).

      Examples requiring this flag: `.onlyFocus`, `.adversative`,
      `.sinceTemporal` — classical-DE-on-paper but shown by
      @cite{von-fintel-1999} to be only Strawson-DE. The
      `byStrawsonDE` mechanism case is for items whose licensing
      *primarily* comes from Strawson-DE (e.g., superlative);
      `isStrawsonOnly` is for cases where the signature *also* needs
      qualification. -/
  isStrawsonOnly : Bool := false
  deriving Repr

/-- Canonical map from licensing contexts to their theoretical properties.

    UNVERIFIED: The "every-restrictor is LAA" result is variously
    attributed to Zwarts 1981 / van Benthem 1986 / Sánchez Valencia 1991;
    none currently in `references.bib`. The substrate uses the standard
    `.antiAdd` signature for `.universalRestrictor` without committing
    to a specific source. -/
def contextProperties : LicensingContext → ContextProperties
  | .negation =>
      { signature := .antiAddMult, mechanism := .byStrengthening
      , prototype := "Mary didn't see anyone."
      , citations := ["ladusaw-1979", "kadmon-landman-1993", "zwarts-1998"] }
  | .nobody =>
      { signature := .antiAdd, mechanism := .byStrengthening
      , prototype := "Nobody saw anyone."
      , citations := ["ladusaw-1979", "zwarts-1998"] }
  | .withoutClause =>
      { signature := .antiAdd, mechanism := .byStrengthening
      , prototype := "She left without saying anything."
      , citations := ["ladusaw-1979", "zwarts-1998"] }
  | .denyVerb =>
      { signature := .antiAdd, mechanism := .byStrengthening
      , prototype := "She denied seeing anyone."
      , citations := ["zwarts-1998"] }
  | .universalRestrictor =>
      { signature := .antiAdd, mechanism := .byStrengthening
      , prototype := "Everyone who saw anyone was questioned."
      , citations := ["ladusaw-1979", "UNVERIFIED-bib-missing:partee-westerstaahl"] }
  | .few =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "Few students saw anyone."
      , citations := ["ladusaw-1979"] }
  | .atMost =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "At most three students saw anyone."
      , citations := ["ladusaw-1979"] }
  | .conditionalAntecedent =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "If anyone calls, take a message."
      , citations := ["ladusaw-1979", "kadmon-landman-1993"] }
  | .beforeClause =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "She left before anyone arrived."
      , citations := ["ladusaw-1979"] }
  | .onlyFocus =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "Only Mary saw anyone."
      , citations := ["horn-1996", "von-fintel-1999"]
      , isStrawsonOnly := true }
  | .tooTo =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "He was too tired to say anything."
      , citations := ["ladusaw-1979"] }
  | .comparativeNP =>
      -- @cite{hoeksema-1983}: the NP-comparative is a Boolean
      -- homomorphism `Set (Set U) → Set U`, hence monotone increasing — it
      -- does *not* license NPIs. Modern interval-semantic accounts
      -- (@cite{bhatt-pancheva-2004}, @cite{heim-2006}) reduce surface
      -- "than NP" with NPI to a covert clausal source — those NPIs are
      -- licensed by `.comparativeS`, not by this slot.
      { signature := .mono, mechanism := .strengtheningFails
      , prototype := "Surface NP-comparative; no NPI licensing under genuine NP reading."
      , citations := ["hoeksema-1983", "bhatt-pancheva-2004", "heim-2006"] }
  | .comparativeS =>
      { signature := .antiAdd, mechanism := .byStrengthening
      , prototype := "Mary is taller than anyone is."
      , citations := ["ladusaw-1979", "hoeksema-1983", "bhatt-pancheva-2004"] }
  | .adversative =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "I'm sorry I said anything."
      , citations := ["kadmon-landman-1993", "von-fintel-1999"]
      , isStrawsonOnly := true }
  | .sinceTemporal =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "It's been five years since anyone visited."
      , citations := ["iatridou-2000", "von-fintel-1999"]
      , isStrawsonOnly := true }
  | .doubtVerb =>
      { signature := .anti, mechanism := .byStrengthening
      , prototype := "I doubt anyone came."
      , citations := ["zwarts-1998"] }
  | .modalPossibility =>
      { signature := .mono, mechanism := .byGenericIndefinite
      , prototype := "You may take any cookie."
      , citations := ["kadmon-landman-1993", "dayal-1996"] }
  | .modalNecessity =>
      { signature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Anyone can solve this."
      , citations := ["dayal-1996"] }
  | .imperative =>
      { signature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Pick any card."
      , citations := ["kadmon-landman-1993"] }
  | .generic =>
      { signature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Any owl hunts mice."
      , citations := ["kadmon-landman-1993", "dayal-1996"] }
  | .freeRelative =>
      { signature := .mono, mechanism := .byGenericIndefinite
      , prototype := "Pick whichever you like."
      , citations := ["dayal-1996"] }
  | .question =>
      { signature := .mono, mechanism := .byEntropy
      , prototype := "Did anyone call?"
      , citations := ["van-rooy-2003"] }
  | .superlative =>
      { signature := .mono, mechanism := .byStrawsonDE
      , prototype := "The tallest student who saw anyone..."
      , citations := ["UNVERIFIED-bib-missing:herdan-sharvit", "von-fintel-1999"]
      , isStrawsonOnly := true }

end Semantics.Polarity.Licensing
