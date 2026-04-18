/-!
# English Future Modals: *will*, *would*

Morphological lexical entries for the English future modals *will* and
*would*. Following the typology-only Fragment discipline (cf.
`Fragments/Dutch/Modals.lean`, `Fragments/English/Conditionals.lean`),
these entries record surface form and morphological metadata only —
they do **not** commit to any particular semantic clause.

The connection to a specific theory's semantics lives in the relevant
Studies file. For example, `Phenomena/Modality/Studies/CarianiSantorio2018.lean`
binds `will` and `would` to the selectional clauses
`Semantics.Modality.Selectional.{willSem, wouldSem}`. A different
analysis (Klecha-style modal-cum-tense, Kratzerian universal *will*,
Copley future operator, …) would supply its own bridge theorem against
the same two surface entries.

## What's here

- `FutureModalEntry`: morphology + Reichenbachian past-tense flag.
- `will`: present-tense surface form.
- `would`: past-tense surface form (morphological derivative of *will*).
- `allEntries`: the two-element inventory.
-/

namespace Fragments.English.Will

/-- A morphological lexical entry for an English future modal.

    Holds surface-form metadata only — no semantic clause. The intended
    semantic interpretation is supplied by a Study file via a bridge
    theorem against this entry, so multiple competing analyses can
    cohabit without duplicating the surface-form data. -/
structure FutureModalEntry where
  /-- Surface form (e.g., "will", "would"). -/
  form : String
  /-- Whether the form is morphologically past-tense. -/
  pastTense : Bool
  /-- Free-form English gloss (typically the form itself for these
      English entries; included for cross-linguistic consistency with
      other Fragment files). -/
  gloss : String
  deriving Repr, DecidableEq

/-- English present-tense future modal *will*. -/
def will : FutureModalEntry where
  form := "will"
  pastTense := false
  gloss := "will"

/-- English past-tense future modal *would*.

    Morphologically the past-tense form of *will*. The semantic effect
    of the past-tense morphology is theory-dependent: on a selectional
    analysis the morphology shifts the modal parameter without changing
    the semantic clause; on a Kratzerian analysis it shifts the modal
    base; on a Copley-style analysis it picks out a different temporal
    relation. The Fragment stays neutral. -/
def would : FutureModalEntry where
  form := "would"
  pastTense := true
  gloss := "would"

/-- The English future-modal inventory. -/
def allEntries : List FutureModalEntry := [will, would]

/-- *will* and *would* differ in the `pastTense` field — the structural
    morphological distinction that any downstream theory must respect. -/
theorem will_would_pastTense_distinct : will.pastTense ≠ would.pastTense := by
  decide

end Fragments.English.Will
