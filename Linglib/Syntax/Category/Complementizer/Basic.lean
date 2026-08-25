import Linglib.Data.UD.Basic
import Linglib.Semantics.Mood.Defs
import Linglib.Syntax.Clause.Complementation
import Linglib.Morphology.Morph
import Linglib.Morphology.Word.Basic

open Morphology (Morph Word)

/-!
# Complementizer

The lexical core of the complementizer (clause-typing morpheme) as a
grammatical object, modeled on `Syntax/Category/Pronoun/`: its exponent
as morphs plus the consensus clause-typing axes, each drawn from
existing substrate. Per-language fragments instantiate it — free
subordinators like *that* and *oti*, affixal clause-typers like Buryat
*-žA* and Tigrinya *zɨ-*, grammaticalized say-roots like Buryat *gɘ* and
Uyghur *de*.

## Main declarations

* `Complementizer` — the general complementizer object
* `Complementizer.Licenser` — adnominal vs adverbal licensing category
* `Complementizer.form` — the surface form with boundary notation
* `Complementizer.IsBound` — affixal status, read off the morphs
* `Complementizer.toWord` — the `SCONJ` word a free complementizer
  projects

## Implementation notes

Framework-specific head assignments (a cartographic Force/Fin split, a
ContP-exponence claim, an [n]-feature) are not fields; they live as
Studies-local projections over these entries, and the schema carries no
denotation (cf. `Adjective`'s deferred degree semantics). Field
conventions:

- `morphs` lists the exponent in surface order: a free word (*that*), a
  bound root that never surfaces bare (Buryat *gɘ*, Uyghur *de*), or the
  affixes of a prefix or suffix complex (Tigrinya *kɛm-zɨ-*). Attachment
  is read off the morphs' kinds rather than stored.
- `force`: only `.declarative` and `.interrogative` are attested on
  embedded-clause typers.
- `licenser` names the licensing projection, not the morphological
  host stem (which for a suffixal clause-typer is the verb it
  attaches to).
- `factive` records only a lexical factive presupposition carried by
  the morpheme itself (Greek *pu*); leave `none` when factivity tracks
  the verb or the construction — derived in Studies, never stored.
-/

/-- Category of the adjacent projection licensing an affixal
clause-typer: adnominal (Buryat *-Aːša*) vs adverbal (Buryat *-žA*). -/
inductive Complementizer.Licenser where
  | nominal
  | verbal
  deriving DecidableEq, Fintype, Repr

/-- A complementizer: its exponent as morphs plus the consensus
clause-typing axes. -/
structure Complementizer where
  /-- The exponent, in surface order. -/
  morphs : List Morph
  /-- Native script form, when distinct. -/
  script : Option String := none
  /-- [noonan-2007] coding of the clause this morpheme types. -/
  coding : Option Complement.Coding := none
  /-- Illocutionary force of the clause this morpheme types. -/
  force : Option Mood.Illocutionary := none
  /-- Verb form derived on the host (UD). -/
  verbForm : Option UD.VerbForm := none
  /-- Category of the adjacent licensing projection. -/
  licenser : Option Complementizer.Licenser := none
  /-- Lexical factive presupposition. -/
  factive : Option Bool := none
  deriving Repr, DecidableEq

namespace Complementizer

/-- The surface form: the morphs' forms with their boundary notation. -/
def form (c : Complementizer) : String := String.join (c.morphs.map toString)

/-- Bound: no morph of the exponent is a free form. -/
def IsBound (c : Complementizer) : Prop := ∀ m ∈ c.morphs, m.kind ≠ .free

instance : DecidablePred IsBound := fun c => by
  unfold IsBound; infer_instance

/-- The `SCONJ` word a free complementizer projects; `none` for bound
clause-typers. -/
def toWord (c : Complementizer) : Option Word :=
  match c.morphs with
  | [⟨.free, s⟩] => some { form := s, cat := .SCONJ }
  | _ => none

end Complementizer
