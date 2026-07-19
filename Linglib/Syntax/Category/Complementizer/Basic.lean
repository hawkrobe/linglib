import Linglib.Data.UD.Basic
import Linglib.Features.ClauseForm
import Linglib.Features.Complementation
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# Complementizer

The lexical core of the complementizer (clause-typing morpheme) as a
grammatical object, modeled on `Syntax/Category/Pronoun/`: surface form plus the
consensus clause-typing axes, each drawn from existing substrate.
Per-language fragments instantiate it — free subordinators like *that*
and *oti*, affixal clause-typers like Buryat *-žA* and Tigrinya *zɨ-*,
grammaticalized say-roots like Buryat *gɘ* and Uyghur *de*.

## Main declarations

- `Complementizer` — the general complementizer object
- `Complementizer.Licenser` — adnominal vs adverbal licensing category
- `Complementizer.IsBound` — affixal status, derived from `position`
- `Complementizer.toWord` — the `SCONJ` word a free complementizer
  projects

## Implementation notes

Framework-specific head assignments (a cartographic Force/Fin split, a
ContP-exponence claim, an [n]-feature) are not fields; they live as
Studies-local projections over these entries, and the schema carries no
denotation (cf. `Adjective`'s deferred degree semantics). Field
conventions:

- `position = none`: unrecorded, or a bound root with no fixed
  attachment of its own (Buryat *gɘ* surfaces only suffixed).
- `clauseForm`: only `.declarative` and `.embeddedQuestion` are
  sensible values for an embedded-clause typer.
- `licenser` names the licensing projection, not the morphological
  host stem (which for a postfixed clause-typer is the verb it
  attaches to).
- `agrees`: φ-agreement with a clause-internal argument (Tigrinya
  *kɨ-* and *ʔay-…-n*; West Germanic complementizer agreement).
- `factive` records only a lexical factive presupposition carried by
  the morpheme itself (Greek *pu*, Tigrinya *kəmzi-*); leave `none`
  when factivity tracks the verb or the construction — derived in
  Studies, never stored.
-/

namespace Morphology

/-- Typological position classification for formatives.
    [bickel-nichols-2007] Table 3.2 (p. 198), flattened: the table crosses
    five positions (Prae/In/Post/Simul/Detached) with formative types; this
    enum keeps the positions, promoting circumfixation (the table's common
    Simul subtype) and endoclisis (an In subtype) to their own cases. It
    classifies [bickel-nichols-2007]'s *formatives*, which include process
    modes, not `Morph` values — `simultaneous` has no segmental carrier, so
    no projection to `Morph.Kind` exists by design. Housed with its sole
    consumer, `Complementizer.position`; a formative-grain typology arc
    would re-graduate it to substrate. -/
inductive FormativePosition where
  | praefixed     -- formative precedes host
  | postfixed     -- formative follows host
  | infixed       -- formative inserted within host
  | circumfixed   -- formative wraps host
  /-- Several tokens of one morpheme realized at different places in the
  word ([bickel-nichols-2007] p. 200, after Hagège) — NOT process
  morphology: bare ablaut, substitution, and subtraction are In-position
  formatives, reduplication is Prae/Post, in the source table. -/
  | simultaneous
  | detached      -- not attached to its host (may still be phonologically bound)
  | endoclitic    -- clitic inserted inside a word (Udi, European Portuguese)
  deriving DecidableEq, Repr

end Morphology

/-- Category of the adjacent projection licensing an affixal
clause-typer: adnominal (Buryat *-Aːša*) vs adverbal (Buryat *-žA*). -/
inductive Complementizer.Licenser where
  | nominal
  | verbal
  deriving DecidableEq, Fintype, Repr

/-- A complementizer: surface form plus the consensus clause-typing axes. -/
structure Complementizer where
  /-- Surface form (romanization; affixes hyphenated). -/
  form : String
  /-- Native script form, when distinct. -/
  script : Option String := none
  /-- Morphological attachment. -/
  position : Option Morphology.FormativePosition := none
  /-- [noonan-2007] type of the clause this morpheme types. -/
  noonanType : Option NoonanCompType := none
  /-- Surface clause form typed. -/
  clauseForm : Option Features.ClauseForm := none
  /-- Verb form derived on the host (UD). -/
  verbForm : Option UD.VerbForm := none
  /-- Category of the adjacent licensing projection. -/
  licenser : Option Complementizer.Licenser := none
  /-- Carries φ-agreement with a clause-internal argument? -/
  agrees : Option Bool := none
  /-- Lexical factive presupposition. -/
  factive : Option Bool := none
  deriving Repr, BEq, DecidableEq

namespace Complementizer


/-- Bound (affixal): recorded attachment other than `.detached`. -/
def IsBound (c : Complementizer) : Prop :=
  c.position ≠ none ∧ c.position ≠ some .detached

instance : DecidablePred IsBound := fun c => by
  unfold IsBound; infer_instance

/-- The `SCONJ` word a free complementizer projects; `none` for
affixal clause-typers. -/
def toWord (c : Complementizer) : Option Word :=
  if c.position = some .detached then
    some { form := c.form, cat := .SCONJ }
  else none

end Complementizer
