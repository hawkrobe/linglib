import Linglib.Semantics.Polarity.Licensing

/-!
# Italian Polarity-Sensitive Items
[chierchia-2006] [chierchia-2013]

Lexical entries for Italian PSIs, typed by the theory-neutral categories
from `Semantics.Polarity`.

## The Italian PSI system

Italian lexicalizes the NPI/FCI distinction that English *any* collapses:
- **nessuno/niente/mai**: Pure NPIs (negative concord, DE only)
- **qualsiasi/qualunque**: Pure universal FCIs (FC only, positive polarity)
- **un N qualsiasi**: Existential FCIs (FC under modals)
-/

namespace Italian.PolarityItems

open Semantics.Polarity

/-! ### Pure NPIs -/

/-- *nessuno/nessuna* — N-word, pure NPI.
    Requires negative concord (postverbal: *non* ... *nessuno*).
    Base existential force; negative force from concord, not lexical. -/
def nessuno : Item :=
  { form := "nessuno/nessuna"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts :=
      [.negation, .nobody, .withoutClause, .conditionalAntecedent, .question]
  , scalarDirection := .strengthening
  , alternativeType := .domain }

/-- *niente/nulla* — N-word for non-human, pure NPI. -/
def niente : Item :=
  { form := "niente/nulla"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening }

/-- *mai* — Temporal pure NPI (= English *ever*).
    Disallows FC use (contrast with English *any*). -/
def mai : Item :=
  { form := "mai"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts :=
      [.negation, .nobody, .withoutClause, .question, .conditionalAntecedent]
  , scalarDirection := .strengthening
  , alternativeType := .domain }

/-- *alcuno* — Pure NPI (formal register).
    Listed in [chierchia-2006] table (76)/(94) alongside *mai* and *ever*.
    Restricted distribution: negation + formal contexts. -/
def alcuno : Item :=
  { form := "alcuno"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening }

/-- *neanche/nemmeno/neppure* — Additive focus NPI (*not even*).
    Three near-synonymous register variants. -/
def neanche : Item :=
  { form := "neanche/nemmeno/neppure"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening }

/-- *mica* — Emphatic negation reinforcer / colloquial NPI.
    Co-occurs with *non* postverbally to add emphasis: *Non mi piace mica*
    "I don't like it AT ALL". The load-bearing diagnostic in
    [cinque-1999]'s adverb hierarchy and Zanuttini's NegP cartography:
    *mica* sits in a dedicated functional projection above the lexical-VP
    negation slot. Morphologically a frozen noun ("crumb"), grammaticalized
    into a focus particle in northern Italian especially. Distinct from
    additive *neanche* (which adds a discourse-given alternative) — *mica*
    contradicts an inferred prior expectation. -/
def mica : Item :=
  { form := "mica"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening }

/-- *pur* (in *con tutta la fantasia che pur si possa avere*, "with all the
    fantasy in the world that one could have") — weak NPI licensed in
    DE/comparative environments where the speaker presupposes a contradicted
    prior belief.

    [napoli-nespor-1976] §3.11 ex. 46–48: licensed under comparative
    *non₂* alongside subjunctive co-occurrence and *neanche*-conjunction.
    Treated by N&N as a diagnostic for underlying negation in the comparative
    clause: where *pur* surfaces, *non₂* is licensed too. -/
def pur : Item :=
  { form := "pur"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation, .comparativeS]
  , scalarDirection := .strengthening }

/-- *affatto* ("at all", "completely") — weak NPI requiring *precise*
    knowledge of the listener's belief; blocked in N&N's comparative *non₂*
    on independent precision grounds.

    [napoli-nespor-1976] §3.22 fn (i): *affatto* is *not* licensed by
    bias-conditioned negation, even though it is a weak NPI elsewhere. The
    block is semantic — *affatto* requires the listener's belief to be
    explicit, which fails N&N's "imprecise/inferred" Condition 4. The
    distributional fact is therefore *orthogonal* to NPI licensing.
    Bottom-line: *affatto* is licensed by negation in general but blocked
    by the imprecise condition that bias-conditioned negation requires. -/
def affatto : Item :=
  { form := "affatto"
  , licensor := some .weak
  , baseForce := .degree
  , licensingContexts := [.negation]  -- not .comparativeS: blocked by precision
  , scalarDirection := .strengthening }

/-- N&N's central diagnostic: *pur* is licensed in comparative-clause
    contexts (which encode bias-conditioned negation in Italian), *affatto*
    is not. The contrast is structural in the registry — *pur*'s
    `licensingContexts` includes `.comparativeS` while *affatto*'s does
    not, so the Italian Fragment alone witnesses the distributional
    contrast that motivated the *non₂* analysis.

    `.comparativeS` (clausal-comparative) is the relevant slot:
    [hoeksema-1983] establishes that surface NP-comparatives are
    Boolean homomorphisms (monotone) and not NPI environments —
    `.comparativeNP` therefore licenses nothing. -/
theorem pur_licensed_in_comparative :
    pur.licensingContexts.contains .comparativeS = true := by decide

theorem affatto_not_licensed_in_comparative :
    affatto.licensingContexts.contains .comparativeS = false := by decide

/-! ### Pure Universal FCIs -/

/-- *qualsiasi* — Pure universal FCI.
    Universal force in positive/modal contexts.
    Under negation: only rhetorical ¬∀ reading ("not just any").
    Does NOT have NPI use (unlike English *any*). -/
def qualsiasi : Item :=
  { form := "qualsiasi"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic]
  , alternativeType := .domain }

/-- *qualunque* — Pure universal FCI (post-nominal only). -/
def qualunque : Item :=
  { form := "qualunque"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic]
  , alternativeType := .domain }

/-! ### Existential FCIs -/

/-- *un N qualsiasi* — Existential FCI.
    Both domain and scalar alternatives active.
    Requires modal context; ungrammatical in plain episodic. -/
def uno_qualsiasi : Item :=
  { form := "un N qualsiasi"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative]
  , alternativeType := .domain }

/-! ### Joint -/

/-- The Italian polarity-item inventory: the Fragment-side joint listing
    every polarity item this fragment defines. Every
    `Fragments/{Lang}/PolarityItems.lean` exposes `def items` of this type
    (see the operator/lexical-reactive split in `Core/Lexical/NegMarker.lean`). -/
def items : List Item :=
  [nessuno, niente, mai, alcuno, neanche, mica, pur, affatto,
   qualsiasi, qualunque, uno_qualsiasi]

/-! ### Verification -/

/-- Every attested context of every entry is predicted licensed. -/
theorem italian_licensing_sound :
    ∀ e ∈ items, ∀ c ∈ e.licensingContexts, c.licenses e := by decide

/-- All Italian NPIs have strengthening scalar direction. -/
theorem italian_npis_strengthening :
    [nessuno, niente, mai, alcuno, neanche].all
      (λ e => e.scalarDirection == .strengthening) = true := by decide

end Italian.PolarityItems
