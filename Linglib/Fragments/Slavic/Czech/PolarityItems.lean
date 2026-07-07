import Linglib.Semantics.Polarity.Licensing

/-!
# Czech Polarity-Sensitive Items
[haspelmath-1997]

Lexical entries for Czech n-words (the *ni-* series), typed by the
theory-neutral categories from `Semantics.Polarity`. Standard
sentential negation (the *ne-* prefix) lives in the sibling
`Fragments/Czech/Negation.lean`; this file holds only the lexical
reactives (operator/lexical-reactive split documented in
`Core/Lexical/NegMarker.lean`).

## The Czech *ni-* series

Czech is a strict-NC language (Slavic pattern): every n-word obligatorily
co-occurs with the *ne-* prefixed verb form, regardless of position.
*Nikdo nepřišel* 'Nobody NEG.came'; *Neviděl nikoho* 'NEG.saw nobody'.
Both preverbal and postverbal n-words require *ne-* — unlike Italian/
Spanish position-dependent NC.
-/

namespace Czech.PolarityItems

open Semantics.Polarity

/-- *nikdo* — N-word for human ('nobody').
    Strict NC: requires the *ne-* prefix on the verb regardless of
    position. -/
def nikdo : Item :=
  { form := "nikdo"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg }

/-- *nic* — N-word for non-human ('nothing'). -/
def nic : Item :=
  { form := "nic"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg }

/-- *nikdy* — Temporal n-word ('never'). -/
def nikdy : Item :=
  { form := "nikdy"
  , licensor := some .antiMorphic
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg }

/-- *nikam* — Locative n-word ('nowhere'). -/
def nikam : Item :=
  { form := "nikam"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg }

/-- *žádný* — Determiner n-word ('no/none'). -/
def zadny : Item :=
  { form := "žádný"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening }

/-! ### Joint -/

/-- The Czech polarity-item inventory: the Fragment-side joint listing
    every polarity item this fragment defines. -/
def items : List Item :=
  [nikdo, nic, nikdy, nikam, zadny]

/-! ### Verification -/

/-- The strict-NC *ni-* series characterized exactly: clausemate negation is
    the only licensing environment. -/
theorem niSeries_licensing_characterized :
    ∀ e ∈ items, ∀ c, c.licenses e ↔ c ∈ e.licensingContexts := by decide

/-- The *ni-* series is morphologically marked as `indefPlusNeg`. -/
theorem niSeries_morphology :
    [nikdo, nic, nikdy, nikam].all (fun e => e.morphology == .indefPlusNeg) = true := by
  decide

end Czech.PolarityItems
