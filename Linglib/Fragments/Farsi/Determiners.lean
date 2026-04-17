import Linglib.Core.Lexical.Word
import Linglib.Theories.Semantics.Quantification.ChoiceFunction
import Mathlib.Data.Rat.Defs

/-! # Farsi Determiner and Indefinite Lexicon
@cite{mirrazi-2024} @cite{alonso-ovalle-moghiseh-2025}

## Plain Indefinites (Choice Functions)

Farsi plain indefinites *ye* (singular), *čand-ta* (plural classifier "some-CL"),
and *do-ta* (numeral classifier "two-CL") are choice-function indefinites
with an independent world/situation variable. @cite{mirrazi-2024} shows
that this world variable, when bound by an intensional operator, produces
wide pseudo-scope de dicto readings: the indefinite appears to scope above
negation (via the ∃-closure over the CF) while remaining de dicto with
respect to the intensional operator (via the bound world variable).

## EFCI: *yek-i*

*yek-i* is an Existential Free Choice Item (EFCI): uniqueness in root,
free choice under deontic, modal variation under epistemic.
@cite{alonso-ovalle-moghiseh-2025}.
-/

namespace Fragments.Farsi.Determiners


/--
EFCI rescue mechanism type.
Determines how the item rescues itself from the exhaustification contradiction.
-/
inductive EFCIRescue where
  /-- No rescue available (ungrammatical in UE root) -/
  | none
  /-- Can insert covert epistemic modal -/
  | modalInsertion
  /-- Can do partial exhaustification (prune one alternative type) -/
  | partialExhaustification
  /-- Both mechanisms available -/
  | both
  deriving DecidableEq, Repr

/--
The reading an EFCI yields in different contexts.
-/
inductive EFCIReading where
  /-- Plain existential (DE contexts) -/
  | plainExistential
  /-- Exactly one satisfies P (uniqueness) -/
  | uniqueness
  /-- For each x, it's permitted that P(x) -/
  | freeChoice
  /-- At least two x's are epistemically possible for P -/
  | modalVariation
  /-- Speaker doesn't know/care which x satisfies P -/
  | epistemicIgnorance
  deriving DecidableEq, Repr


/--
A Farsi indefinite DP entry.

Captures syntactic and semantic properties including EFCI behavior.
-/
structure IndefiniteEntry where
  /-- Surface form (Persian script) -/
  form : String
  /-- Romanization -/
  romanization : String
  /-- Gloss -/
  gloss : String
  /-- Is this an EFCI? -/
  isEFCI : Bool := false
  /-- EFCI rescue mechanism (if EFCI) -/
  efciRescue : Option EFCIRescue := none
  /-- Requires partitive 'az' construction? -/
  requiresPartitive : Bool := false
  /-- Can occur with mass nouns? -/
  allowsMass : Bool := false
  /-- Conveys speaker ignorance/indifference in root? -/
  speakerIgnorance : Bool := false
  /-- Conveys uniqueness in root? -/
  uniqueness : Bool := false
  deriving Repr, BEq


/--
*yek-i*: Farsi existential free choice item.

Key properties:
- EFCI with partial exhaustification rescue
- Requires partitive 'az NP' ("one of the NPs")
- Yields uniqueness in root contexts (no modal insertion)
- Yields free choice under deontic modals
- Yields modal variation under epistemic modals
- Plain existential in DE contexts
-/
def yeki : IndefiniteEntry :=
  { form := "یکی"
  , romanization := "yek-i"
  , gloss := "one-INDF"
  , isEFCI := true
  , efciRescue := some .partialExhaustification
  , requiresPartitive := false
  , allowsMass := false
  , speakerIgnorance := false  -- NO modal component in root
  , uniqueness := true          -- Yields "exactly one" in root
  }

/--
*yek* (plain numeral): "one"

Not an EFCI - just a numeral. Contrast with *yek-i*.
-/
def yek : IndefiniteEntry :=
  { form := "یک"
  , romanization := "yek"
  , gloss := "one"
  , isEFCI := false
  , requiresPartitive := false
  , allowsMass := false
  }

/--
Indefinite suffix *-i*: Indefiniteness marker.

Attaches to nouns to create indefinites.
-/
def indef_i : IndefiniteEntry :=
  { form := "ـی"
  , romanization := "-i"
  , gloss := "-INDF"
  , isEFCI := false
  , requiresPartitive := false
  , allowsMass := true
  }


/--
Modal flavor type for context specification.
-/
inductive ModalFlavor where
  | deontic   -- Permission, obligation
  | epistemic -- Knowledge, belief
  deriving DecidableEq, Repr

/--
Context for determining EFCI reading.
-/
structure EFCIContext where
  /-- Is the context downward-entailing? -/
  isDE : Bool
  /-- Modal flavor if under a modal -/
  modalFlavor : Option ModalFlavor
  deriving Repr, BEq

/--
Root context (no modal, not DE).
-/
def rootContext : EFCIContext :=
  { isDE := false, modalFlavor := none }

/--
Deontic modal context.
-/
def deonticContext : EFCIContext :=
  { isDE := false, modalFlavor := some .deontic }

/--
Epistemic modal context.
-/
def epistemicContext : EFCIContext :=
  { isDE := false, modalFlavor := some .epistemic }

/--
Downward-entailing context.
-/
def deContext : EFCIContext :=
  { isDE := true, modalFlavor := none }

/--
Get the reading for an EFCI in a given context.
-/
def getReading (entry : IndefiniteEntry) (ctx : EFCIContext) : Option EFCIReading :=
  if !entry.isEFCI then
    -- Non-EFCI: just plain existential everywhere
    some .plainExistential
  else if ctx.isDE then
    -- DE contexts: always plain existential
    some .plainExistential
  else match ctx.modalFlavor with
    | some .deontic => some .freeChoice
    | some .epistemic => some .modalVariation
    | none =>
      -- Root context: depends on rescue mechanism
      match entry.efciRescue with
      | some .partialExhaustification => some .uniqueness
      | some .modalInsertion => some .epistemicIgnorance
      | some .both => some .epistemicIgnorance  -- Modal insertion primary
      | some .none => none  -- Ungrammatical
      | none => some .plainExistential  -- Not EFCI


/-- Yek-i in root context yields uniqueness -/
theorem yeki_root : getReading yeki rootContext = some .uniqueness := rfl

/-- Yek-i under deontic modal yields free choice -/
theorem yeki_deontic : getReading yeki deonticContext = some .freeChoice := rfl

/-- Yek-i under epistemic modal yields modal variation -/
theorem yeki_epistemic : getReading yeki epistemicContext = some .modalVariation := rfl

/-- Yek-i in DE context yields plain existential -/
theorem yeki_de : getReading yeki deContext = some .plainExistential := rfl


/-- German *irgendein*: EFCI with modal insertion available.
Cross-linguistic comparison entry; canonical German entry in `Fragments.German.ModalIndefinites`.
@cite{kratzer-shimoyama-2002} -/
def irgendein_de : IndefiniteEntry :=
  { form := "irgendein"
  , romanization := "irgendein"
  , gloss := "IRGEND.a"
  , isEFCI := true
  , efciRescue := some .modalInsertion  -- Modal insertion only (Table 2)
  , requiresPartitive := false
  , speakerIgnorance := true   -- Has epistemic component
  , uniqueness := false
  }

/-- Romanian *vreun*: EFCI with no rescue mechanism.
Cross-linguistic comparison entry; see @cite{falaus-2014}. -/
def vreun_ro : IndefiniteEntry :=
  { form := "vreun"
  , romanization := "vreun"
  , gloss := "VREUN"
  , isEFCI := true
  , efciRescue := some .none  -- No rescue
  , requiresPartitive := false
  }

/--
Irgendein in root yields epistemic ignorance (via modal insertion).
@cite{kratzer-shimoyama-2002}
-/
theorem irgendein_root : getReading irgendein_de rootContext = some .epistemicIgnorance := rfl

/--
Vreun in root is ungrammatical (no rescue).
-/
theorem vreun_root_ungrammatical : getReading vreun_ro rootContext = none := rfl


-- ════════════════════════════════════════════════════
-- § Plain Indefinites (Choice Function Semantics)
-- ════════════════════════════════════════════════════

open Semantics.Quantification.ChoiceFunction (IndefType SkolemCF)

/-- Farsi plain indefinite entry, extending `IndefiniteEntry` with
    choice-function properties relevant to @cite{mirrazi-2024}. -/
structure PlainIndefiniteEntry extends IndefiniteEntry where
  /-- Semantic analysis: choice function or ∃-quantifier. -/
  indefType : IndefType
  /-- Does this determiner carry an independent world/situation variable?
      @cite{schwarz-2012}: cross-linguistic parameter — some determiners
      combine with a world pronoun, others do not. -/
  hasWorldVar : Bool
  /-- Number: singular or plural. -/
  isPlural : Bool
  deriving Repr

/-- *ye*: Farsi singular indefinite determiner.

    Takes wide pseudo-scope de dicto under negated intensional operators.
    @cite{mirrazi-2024} exx. (1), (4): under negated *think*, the indefinite
    is interpreted de dicto (under *think*) but above negation. -/
def ye : PlainIndefiniteEntry :=
  { form := "یه"
  , romanization := "ye"
  , gloss := "some"
  , isEFCI := false
  , indefType := .choiceFunction
  , hasWorldVar := true
  , isPlural := false
  }

/-- *čand-ta*: Farsi plural classifier indefinite ("some-CL").

    Same scope behavior as *ye*: wide pseudo-scope de dicto available.
    @cite{mirrazi-2024} exx. (1), (4): *čand-ta* alternates with *ye*
    in the key examples. -/
def candTa : PlainIndefiniteEntry :=
  { form := "چندتا"
  , romanization := "čand-ta"
  , gloss := "some.PL-CL"
  , isEFCI := false
  , indefType := .choiceFunction
  , hasWorldVar := true
  , isPlural := true
  }

/-- *do-ta*: Farsi numeral classifier indefinite ("two-CL").

    Numeral indefinites behave like other indefinites in their
    scope-taking properties. @cite{mirrazi-2024} exx. (8a), (9a):
    under negated *necessary* and *can*, *do-ta* gets wide pseudo-scope
    de dicto readings. -/
def doTa : PlainIndefiniteEntry :=
  { form := "دوتا"
  , romanization := "do-ta"
  , gloss := "two-CL"
  , isEFCI := false
  , indefType := .choiceFunction
  , hasWorldVar := true
  , isPlural := true
  }

/-- All Farsi plain indefinites are choice-functional. -/
theorem ye_is_cf : ye.indefType = .choiceFunction := rfl
theorem candTa_is_cf : candTa.indefType = .choiceFunction := rfl
theorem doTa_is_cf : doTa.indefType = .choiceFunction := rfl

/-- All Farsi plain indefinites carry a world variable. -/
theorem ye_has_world_var : ye.hasWorldVar = true := rfl
theorem candTa_has_world_var : candTa.hasWorldVar = true := rfl
theorem doTa_has_world_var : doTa.hasWorldVar = true := rfl

/-- All Farsi indefinite entries -/
def allIndefinites : List IndefiniteEntry :=
  [yeki, yek, indef_i, ye.toIndefiniteEntry, candTa.toIndefiniteEntry,
   doTa.toIndefiniteEntry]

/-- Lookup by romanization -/
def lookup (romanization : String) : Option IndefiniteEntry :=
  allIndefinites.find? λ e => e.romanization == romanization


end Fragments.Farsi.Determiners
