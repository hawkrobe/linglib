import Linglib.Syntax.CCG.Basic
import Linglib.Syntax.CCG.Classical

/-!
# CCG Cross-Serial Dependencies

CCG derivations for Dutch cross-serial dependencies, in the rule-restricted (classical)
model `CCG.Classical` (@cite{steedman-2000}). Cross-serial dependencies are the classic
witness for CCG's super-context-free power; the derivations thread a verb's argument slots
through the cluster via generalized composition.

## The derivation pattern

For "Jan Piet zag zwemmen" (Jan saw Piet swim), with the verb-raising category
`InfSubj = (S\NP)/NP` for `zwemmen`:

- `zag >B zwemmen` : `(S\NP)/(S\NP)` ∘ `(S\NP)/NP` = `(S\NP)/NP`  (forward composition)
- `(zag zwemmen) Piet` : `(S\NP)/NP` `NP` = `S\NP`               (forward application)
- `Jan (zag zwemmen Piet)` : `NP` `S\NP` = `S`                   (backward application)

Every step has primary target `S`, so each is a valid rule instance of `CCG.Classical`.

## Implementation notes

The derivation tree's `yield` does **not** match Dutch surface order — see
`jan_zag_zwemmen_piet_yield`. The categories here encode the cross-serial *binding*
pattern (which NP binds which verb) but not the linear order; a surface-order-faithful
construction would type-raise the preverbal NPs.
-/

namespace CCG.CrossSerial

open CCG
open CCG.Classical

/-! ### Categories for Dutch verb clusters -/

/-- Verb phrase (infinitival). -/
def VP : Cat := S \ NP

/-- Control verb: takes VP, gives VP (e.g. "helpen" in 2-verb clusters). -/
def ControlV : Cat := VP / VP

/-- Perception verb: `(S\NP)/(S\NP)` (e.g. "zag" = saw). -/
def PercV : Cat := (S \ NP) / VP

/-- Infinitival transitive `VP/NP`. -/
def InfTV : Cat := VP / NP

/-- Infinitival verb needing its (raised) subject: `(S\NP)/NP`. In Dutch verb-raising the
infinitive's subject surfaces in an object-like position, picked up via composition. -/
def InfSubj : Cat := (S \ NP) / NP

/-- Verb-raising control verb `((S\NP)/NP)/(S\NP)`: each restructuring verb provides an
extra `/NP` slot for its own raised subject, in addition to its VP complement. This is
what threads multiple argument slots through a 3+-verb cluster:
- `zwemmen : (S\NP)/NP`           — base: needs subject
- `helpen  : ((S\NP)/NP)/(S\NP)`  — VR: needs complement, passes an `/NP`
- `zag     : (S\NP)/(S\NP)`       — matrix: standard perception verb -/
def ControlVR : Cat := ((S \ NP) / NP) / (S \ NP)

/-- The Dutch lexicon (reference; the derivations below select specific entries). -/
def dutchLexicon : List LexEntry := [
  ⟨"Jan", NP⟩, ⟨"Piet", NP⟩, ⟨"Marie", NP⟩, ⟨"Karel", NP⟩,
  ⟨"zag", PercV⟩,
  ⟨"helpen", ControlV⟩, ⟨"laten", ControlV⟩,
  ⟨"helpen", ControlVR⟩, ⟨"laten", ControlVR⟩,
  ⟨"zwemmen", VP⟩, ⟨"zwemmen", InfSubj⟩
]

/-! ### Lexical entries -/

def jan_lex : Derivation := .lex NP "Jan"
def piet_lex : Derivation := .lex NP "Piet"
def marie_lex : Derivation := .lex NP "Marie"
def zag_lex : Derivation := .lex PercV "zag"
/-- `zwemmen` in its verb-raising category `(S\NP)/NP`. -/
def zwemmen_vr : Derivation := .lex InfSubj "zwemmen"
/-- `helpen` in its verb-raising category `((S\NP)/NP)/(S\NP)`. -/
def helpen_vr : Derivation := .lex ControlVR "helpen"

/-! ### Derivation: "Jan Piet zag zwemmen" (2 NPs, 2 Vs) -/

/-- `zag >B zwemmen`: `(S\NP)/(S\NP) ∘ (S\NP)/NP = (S\NP)/NP`. -/
def zag_comp_zwemmen : Derivation := .fc1 zag_lex zwemmen_vr
/-- `(zag zwemmen) Piet`: `(S\NP)/NP NP = S\NP`. -/
def zag_zwemmen_piet : Derivation := .fa zag_comp_zwemmen piet_lex
/-- `Jan (zag zwemmen Piet)`: `NP S\NP = S`. -/
def jan_zag_zwemmen_piet : Derivation := .ba jan_lex zag_zwemmen_piet

/-! ### Derivation: "Jan Piet Marie zag helpen zwemmen" (3 NPs, 3 Vs)

The cross-serial bindings are Jan→zag, Piet→helpen, Marie→zwemmen. `helpen_vr` passes an
`/NP` slot (for Piet) through while taking its VP complement, so `B`/`B²` thread both
Piet's and Marie's slots through the cluster into `((S\NP)/NP)/NP`. -/

/-- `helpen >B zwemmen`: `((S\NP)/NP)/(S\NP) ∘ (S\NP)/NP = ((S\NP)/NP)/NP`. -/
def helpen_comp_zwemmen : Derivation := .fc1 helpen_vr zwemmen_vr
/-- `zag >B² (helpen zwemmen)`: `(S\NP)/(S\NP) ∘² ((S\NP)/NP)/NP = ((S\NP)/NP)/NP`. -/
def zag_comp2_helpen_zwemmen : Derivation := .fc2 zag_lex helpen_comp_zwemmen
/-- verb cluster + Marie: `((S\NP)/NP)/NP NP = (S\NP)/NP`. -/
def verbs_marie : Derivation := .fa zag_comp2_helpen_zwemmen marie_lex
/-- + Piet: `(S\NP)/NP NP = S\NP`. -/
def verbs_marie_piet : Derivation := .fa verbs_marie piet_lex
/-- + Jan: `NP S\NP = S`. -/
def jan_piet_marie_zag_helpen_zwemmen_deriv : Derivation := .ba jan_lex verbs_marie_piet

/-! ### Verification -/

/-- The 2-NP cross-serial derivation yields category `S` (under the target restriction). -/
theorem two_np_derives_S : jan_zag_zwemmen_piet.cat = some S := by decide

/-- The 3-NP cross-serial derivation yields category `S`, threading three argument slots
through the verb cluster via `B` and `B²`. -/
theorem three_np_derives_S :
    jan_piet_marie_zag_helpen_zwemmen_deriv.cat = some S := by decide

/-- The verb cluster composes into `((S\NP)/NP)/NP` — a 3-place predicate wanting Jan
(`\NP`), Piet (`/NP`) and Marie (`/NP`). -/
theorem verb_cluster_cat :
    zag_comp2_helpen_zwemmen.cat = some (((S \ NP) / NP) / NP) := by decide

/-- The 2-verb derivation's surface yield.

    **This does not match Dutch surface order** ("Jan Piet zag zwemmen"): the verb-cluster
    category `(S\NP)/NP` looks rightward for its arguments, so the derivation tree spells
    out "Jan zag zwemmen Piet". A surface-order-faithful cross-serial derivation requires
    type-raising the preverbal NPs; the categories here capture the cross-serial *binding*
    pattern but not the *linear order*. -/
theorem jan_zag_zwemmen_piet_yield :
    jan_zag_zwemmen_piet.yield = ["Jan", "zag", "zwemmen", "Piet"] := by decide

end CCG.CrossSerial
