import Linglib.Theories.Semantics.Events.Krifka1989
import Linglib.Theories.Semantics.Events.Krifka1998
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.TenseAspect.DiagnosticsBridge

/-!
# @cite{krifka-1989} Bridge: Nominal Reference → VP Telicity
@cite{krifka-1989}

Connects @cite{krifka-1989}'s nominal reference theory (`Events/Krifka1989.lean`) to
concrete verb-NP composition and telicity diagnostics.

## What it exercises

- `MassNoun`, `CountNoun`, `BarePlural` (nominal reference types)
- `QMOD`, `qmod_qua` (measure phrase quantization)
- `measure_phrase_makes_qua` (CUM noun + measure → QUA)
- `cum_transfer`, `qua_transfer` (NP reference → VP telicity)
- `VerbIncClass` cross-reference

## Structure

1. **Nominal reference classification** — NPs classified by CUM/QUA
2. **VP telicity composition** — VerbIncClass + NP reference → VP reference
3. **Per-datum composition verification** — concrete verb-NP pairs
4. **Cross-reference with VerbIncClass** — fragment annotations match data
5. **Diagnostic bridge** — composed VP reference → for/in compatibility
-/

namespace Phenomena.TenseAspect.Bridge.Krifka1989

open Fragments.English.Predicates.Verbal
open Semantics.Events.Krifka1998 (VerbIncClass)
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction)

-- ════════════════════════════════════════════════════
-- § 1. Nominal Reference Classification
-- ════════════════════════════════════════════════════

/-- Nominal reference type, abstracting @cite{krifka-1989}'s CUM/QUA distinction
    for NPs. Mass nouns and bare plurals are CUM; count nouns, measure
    phrases, and definites are QUA. -/
inductive NomRef where
  | cum   -- mass/bare plural: cumulative reference
  | qua   -- count/measured/definite: quantized reference
  deriving DecidableEq, BEq, Repr

/-- An NP datum with its reference classification. -/
structure NPDatum where
  np : String
  refType : NomRef
  reason : String
  deriving Repr, BEq

/-- "apples" (bare plural) → CUM (algebraic closure). -/
def applesNP : NPDatum :=
  { np := "apples", refType := .cum, reason := "bare plural = AlgClosure" }

/-- "two apples" → QUA (count noun + numeral). -/
def twoApplesNP : NPDatum :=
  { np := "two apples", refType := .qua, reason := "count noun + numeral" }

/-- "water" (mass noun) → CUM. -/
def waterNP : NPDatum :=
  { np := "water", refType := .cum, reason := "mass noun" }

/-- "three kilos of water" → QUA (QMOD: CUM + extensive measure + n > 0). -/
def threeKilosWaterNP : NPDatum :=
  { np := "three kilos of water", refType := .qua, reason := "QMOD" }

/-- "a house" → QUA (singular count noun). -/
def aHouseNP : NPDatum :=
  { np := "a house", refType := .qua, reason := "singular count" }

/-- "houses" (bare plural) → CUM. -/
def housesNP : NPDatum :=
  { np := "houses", refType := .cum, reason := "bare plural" }

/-- "rice" (mass noun) → CUM. -/
def riceNP : NPDatum :=
  { np := "rice", refType := .cum, reason := "mass noun" }

/-- "the cart" → QUA (definite: unique referent). -/
def theCartNP : NPDatum :=
  { np := "the cart", refType := .qua, reason := "definite" }

-- ════════════════════════════════════════════════════
-- § 2. VP Telicity Composition
-- ════════════════════════════════════════════════════

/-- Krifka (1989/1998) composition: VerbIncClass + NP reference → VP reference.
    - sinc/inc: NP reference transfers to VP (QUA NP → QUA VP, CUM NP → CUM VP)
    - cumOnly: VP is always CUM regardless of NP
    This captures: "eat two apples" (telic) vs "eat apples" (atelic) vs
    "push the cart" (always atelic). -/
def composedRef (v : VerbIncClass) (np : NomRef) : NomRef :=
  match v with
  | .sinc => np      -- strict incrementality: NP ref transfers
  | .inc => np       -- general incrementality: NP ref transfers
  | .cumOnly => .cum -- no incrementality: always CUM

-- ════════════════════════════════════════════════════
-- § 3. Per-Datum Composition Verification
-- ════════════════════════════════════════════════════

/-- A verb-NP composition datum. -/
structure CompositionDatum where
  verb : String
  np : String
  verbIncClass : VerbIncClass
  npRef : NomRef
  expectedVPRef : NomRef
  deriving Repr, DecidableEq, BEq

def eatApples : CompositionDatum :=
  { verb := "eat", np := "apples", verbIncClass := .sinc,
    npRef := .cum, expectedVPRef := .cum }

def eatTwoApples : CompositionDatum :=
  { verb := "eat", np := "two apples", verbIncClass := .sinc,
    npRef := .qua, expectedVPRef := .qua }

def eatRice : CompositionDatum :=
  { verb := "eat", np := "rice", verbIncClass := .sinc,
    npRef := .cum, expectedVPRef := .cum }

def eat3kgRice : CompositionDatum :=
  { verb := "eat", np := "3kg of rice", verbIncClass := .sinc,
    npRef := .qua, expectedVPRef := .qua }

def buildHouses : CompositionDatum :=
  { verb := "build", np := "houses", verbIncClass := .sinc,
    npRef := .cum, expectedVPRef := .cum }

def buildAHouse : CompositionDatum :=
  { verb := "build", np := "a house", verbIncClass := .sinc,
    npRef := .qua, expectedVPRef := .qua }

def pushTheCart : CompositionDatum :=
  { verb := "push", np := "the cart", verbIncClass := .cumOnly,
    npRef := .qua, expectedVPRef := .cum }

def readTheBook : CompositionDatum :=
  { verb := "read", np := "the book", verbIncClass := .inc,
    npRef := .qua, expectedVPRef := .qua }

def compositionData : List CompositionDatum :=
  [eatApples, eatTwoApples, eatRice, eat3kgRice,
   buildHouses, buildAHouse, pushTheCart, readTheBook]

/-- Composition predictions match expected VP reference for all data. -/
theorem all_compositions_correct :
    compositionData.all (λ d =>
      composedRef d.verbIncClass d.npRef == d.expectedVPRef) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 4. Cross-Reference with VerbIncClass Annotations
-- ════════════════════════════════════════════════════

/-! Verify that the composition data's `verbIncClass` fields match the
    fragment verb entries. -/

/-- "eat" composition uses sinc, matching fragment annotation. -/
theorem eat_composition_matches :
    eat.toVerbCore.verbIncClass = some eatTwoApples.verbIncClass := rfl

/-- "build" composition uses sinc, matching fragment annotation. -/
theorem build_composition_matches :
    build.toVerbCore.verbIncClass = some buildAHouse.verbIncClass := rfl

/-- "push" composition uses cumOnly, matching fragment annotation. -/
theorem push_composition_matches :
    push.toVerbCore.verbIncClass = some pushTheCart.verbIncClass := rfl

/-- "read" composition uses inc, matching fragment annotation. -/
theorem read_composition_matches :
    read.toVerbCore.verbIncClass = some readTheBook.verbIncClass := rfl

/-- sinc verbs + QUA NP → QUA VP (telic). -/
theorem sinc_qua_yields_qua :
    composedRef .sinc .qua = .qua := rfl

/-- sinc verbs + CUM NP → CUM VP (atelic). -/
theorem sinc_cum_yields_cum :
    composedRef .sinc .cum = .cum := rfl

/-- cumOnly verbs → CUM VP regardless of NP. -/
theorem cumOnly_always_cum :
    composedRef .cumOnly .qua = .cum ∧
    composedRef .cumOnly .cum = .cum := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Diagnostic Bridge
-- ════════════════════════════════════════════════════

/-! Connect composed VP reference to for/in diagnostics.
    QUA VP → accomplishment → "in X" ✓
    CUM VP → activity → "for X" ✓ -/

/-- "eat two apples" (sinc + QUA) → QUA VP → "in two hours" ✓ -/
theorem eat_two_apples_composition :
    composedRef .sinc .qua = .qua ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl⟩

/-- "eat apples" (sinc + CUM) → CUM VP → "for an hour" ✓ -/
theorem eat_apples_composition :
    composedRef .sinc .cum = .cum ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl⟩

/-- "push the cart" (cumOnly + QUA) → CUM VP → "for an hour" ✓ -/
theorem push_cart_composition :
    composedRef .cumOnly .qua = .cum ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl⟩

/-- "3kg of rice" via QMOD (CUM + extensive measure → QUA).
    This exercises `measure_phrase_makes_qua` from Krifka1989. -/
theorem measure_phrase_qua :
    eat3kgRice.npRef = .qua ∧
    composedRef eat3kgRice.verbIncClass eat3kgRice.npRef = .qua := ⟨rfl, rfl⟩

/-- "read the book" (inc + QUA) → QUA VP → "in X" ✓ -/
theorem read_book_composition :
    composedRef .inc .qua = .qua ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl⟩

end Phenomena.TenseAspect.Bridge.Krifka1989
