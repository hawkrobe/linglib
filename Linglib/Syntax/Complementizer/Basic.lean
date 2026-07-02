import Linglib.Data.UD.Basic
import Linglib.Features.ClauseForm
import Linglib.Features.Complementation
import Linglib.Morphology.MorphRule
import Linglib.Morphology.Word

/-!
# Complementizer

The lexical core of the complementizer (clause-typing morpheme) as a
grammatical object, modeled on `Syntax/Pronoun/`: surface form plus the
consensus clause-typing axes, each drawn from existing substrate —
morphological attachment (`Morphology.FormativePosition`), the
[noonan-2007] type of the clause it types, its `Features.ClauseForm`,
the verb form an affixal clause-typer derives on its host (UD), the
licensing host category, and factivity.

Framework-specific head assignments (a cartographic Force/Fin split, a
ContP-exponence claim, an [n]-feature) are not fields; they live as
Studies-local projections over these entries (cf. `Adjective`'s deferred
degree semantics).

## Main declarations

- `Complementizer` — the general complementizer object; per-language
  fragments instantiate it (free subordinators like *that* and *oti*,
  affixal clause-typers like Buryat *-žA* and Tigrinya *zɨ-*,
  grammaticalized say-roots like Buryat *gɘ*)
- `Complementizer.Licenser` — adnominal vs adverbal licensing category
- `Complementizer.IsBound` — affixal status, derived from `position`
- `Complementizer.toWord` — the `SCONJ` word a free complementizer
  projects
-/

/-- Category of the adjacent projection an affixal clause-typer is
licensed by: adnominal (Buryat *-Aːša*, Korean *-nun*) vs adverbal
(Buryat *-žA*). Named for the licensing projection, not the
morphological host stem (which for a postfixed clause-typer is the
verb it attaches to). -/
inductive Complementizer.Licenser where
  | nominal
  | verbal
  deriving DecidableEq, Fintype, Repr

/-- The general complementizer object: the morphosyntactic core shared by
clause-typing morphemes. Carries no denotation and no framework's head
assignment (cf. `Pronoun`, `Adjective`). -/
structure Complementizer where
  /-- Surface form (romanization; affixes hyphenated). -/
  form : String
  /-- Native script form, when distinct. -/
  script : Option String := none
  /-- Morphological attachment: `.detached` for free subordinators,
  `.praefixed` and `.postfixed` for affixal clause-typers. `none` =
  unrecorded, or a bound root with no fixed attachment of its own
  (Buryat *gɘ*, which surfaces only suffixed). -/
  position : Option Morphology.FormativePosition := none
  /-- [noonan-2007] type of the complement clause this morpheme types. -/
  noonanType : Option NoonanCompType := none
  /-- Surface clause form typed. Only `.declarative` and
  `.embeddedQuestion` are sensible values for an embedded-clause typer. -/
  clauseForm : Option Features.ClauseForm := none
  /-- Verb form an affixal clause-typer derives on its host (UD `.Part`,
  `.Conv`, `.Fin`, …). -/
  verbForm : Option UD.VerbForm := none
  /-- Category of the adjacent licensing projection, for
  adjacency-conditioned clause-typers. -/
  licenser : Option Complementizer.Licenser := none
  /-- Does the morpheme carry φ-agreement with an argument of its clause?
  (Tigrinya *kɨ-* and *ʔay-…-n* take agreement suffixes; West Germanic
  complementizer agreement.) `none` = unrecorded. -/
  agrees : Option Bool := none
  /-- Lexical factive presupposition conventionally carried by the
  morpheme itself (Greek *pu*, Tigrinya *kəmzi-*). Leave `none` when
  factivity tracks the verb or the construction (Buryat, Washo) —
  construction-level factivity is derived in Studies, never stored. -/
  factive : Option Bool := none
  deriving Repr, BEq, DecidableEq

namespace Complementizer

/-- Bound (affixal) complementizer: recorded attachment other than
`.detached`. Derived, not stored (cf. `Adjective.IsGradable`). -/
def IsBound (c : Complementizer) : Prop :=
  c.position ≠ none ∧ c.position ≠ some .detached

instance : DecidablePred IsBound := fun c => by
  unfold IsBound; infer_instance

/-- Free complementizers project a `SCONJ` word (cf. `Pronoun.toWord`);
affixal clause-typers project no word of their own. -/
def toWord (c : Complementizer) : Option Word :=
  if c.position = some .detached then
    some { form := c.form, cat := .SCONJ }
  else none

end Complementizer
