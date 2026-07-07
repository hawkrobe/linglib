import Mathlib.Tactic.DeriveFintype

/-!
# Features.LicensingContext
[ladusaw-1979] [kadmon-landman-1993]

The 22-case enum of licensing contexts for polarity-sensitive items.
Theory-neutral data substrate: every framework that talks about polarity
licensing (Ladusaw monotonicity, K&L domain widening, Israel scalar
model, Chierchia exhaustification, Giannakidou nonveridicality) needs
to talk about these context labels.

## Provenance

Extracted from `Semantics/Polarity/Licensing.lean` after
audit consensus that `LicensingContext` is data, not theory: the
22 cases are observational labels for syntactic environments, while
only the *signatures* assigned to them in `contextProperties`
(in the Theories file) carry theoretical commitment. Co-locating the
enum here makes it Fragment-importable substrate without dragging in
the Ladusaw/K&L theoretical apparatus.

The earlier 2-way split (Theories/Polarity/Licensing.lean for the
enum + theory together; Typology/PolarityItem.lean for entry +
Israel) forced `Typology/PolarityItem.lean` to import from
`Theories/`, the only such cross-layer import in linglib. This file
breaks that inversion: `Typology/` and `Semantics/Polarity/`
both import from `Features/`, no peer-layer crossings.

## Framework commitment

The 22-case enum is theory-laden in its *naming* (constructor names
like `adversative`, `doubtVerb`, `denyVerb`, `comparativeS` reflect
specific traditions' classification of contexts), but the cases
themselves enumerate empirically-attested licensing environments any
framework needs to talk about. The DE/anti-additive/anti-morphic
*labelling* of these contexts is theory-laden and lives in
`Semantics/Polarity/Licensing.lean::contextProperties`
(Ladusaw/Zwarts canonical) — not here.

UNVERIFIED: The 22-case carve-up is English-anchored and may need
cross-linguistic restructuring (e.g., factor by veridicality + monotonicity
per Giannakidou 1998, rather than by surface construction); see the
`Semantics/Polarity/Licensing.lean` "Out of scope" section
for the documented gap.
-/

namespace Features

/-- Contexts that can license polarity-sensitive items.

    Characterized by their logical properties:
    - DE (Downward Entailing): reverses entailment direction
    - Anti-additive: DE + distributes over disjunction
    - Anti-morphic: anti-additive + distributes over conjunction (= negation)

    Per-context theoretical classifications (DE strength, K&L mechanism,
    Strawson-DE flagging) live in
    `Semantics/Polarity/Licensing.lean::contextProperties`. -/
inductive LicensingContext where
  | negation          -- "not", "never", "without"
  | nobody            -- "nobody", "nothing" (negative quantifiers)
  | few               -- "few NPs" (weak DE, controversial)
  | atMost            -- "at most n"
  | conditionalAntecedent   -- Antecedent of conditional
  | beforeClause     -- "before" clauses
  | withoutClause    -- "without" PPs
  | onlyFocus        -- Focus of "only"
  | question          -- Questions (for some NPIs)
  | comparativeNP     -- surface "taller than NP" — Boolean homomorphism, monotone increasing,
                      -- and per [hoeksema-1983] *not* an NPI environment.
                      -- Surface NPIs in "than NP" arise from a covert clausal source
                      -- (modern: [bhatt-pancheva-2004] interval reduction) — list
                      -- such NPIs under `.comparativeS`, not here.
  | comparativeS      -- "taller than S is" — anti-additive ([hoeksema-1983], refined
                      -- in interval semantics by [bhatt-pancheva-2004], [heim-2006])
  | superlative       -- "the most", "the least"
  | tooTo            -- "too ADJ to VP"
  | modalPossibility -- Possibility modals (for FCIs)
  | modalNecessity   -- Necessity modals
  | imperative        -- Imperatives (for FCIs)
  | generic           -- Generic contexts (for FCIs)
  | adversative       -- "sorry", "surprised", "regret" (factive + DE)
  | sinceTemporal    -- "it's been five years since" (Iatridou)
  | freeRelative     -- Free relatives: "whatever", "whoever"
  | universalRestrictor -- Restrictor of universal: "everyone who saw anyone"
  | doubtVerb         -- DE attitude verbs: "I doubt anyone came"
  | denyVerb          -- Anti-additive attitude verbs: "She denied seeing anyone"
  deriving DecidableEq, Fintype, Repr

end Features
