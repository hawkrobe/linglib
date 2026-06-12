import Linglib.Syntax.CCG.Basic
import Linglib.Syntax.CCG.Classical

/-!
# CCG Cross-Serial Dependencies

CCG derivations for Dutch cross-serial dependencies, in the rule-restricted (classical)
model `CCG.Classical` ([steedman-2000]). Cross-serial dependencies are the classic
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

Two constructions are given. The *verb-raising* derivations (rightward `/NP`
slots, harmonic `B`/`B²`) encode the cross-serial binding pattern but their
`yield` does **not** match Dutch surface order — see
`jan_zag_zwemmen_piet_yield`. The *surface-faithful* derivations (leftward
`\NP` slots, forward crossed composition `fcompX1`, following the book's own
Dutch fragment) get both the binding and the attested word order — see
`two_np_sub_yield` / `three_np_sub_yield`.
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

/-- Subordinate-clause perception verb `((S\NP)\NP)/VP`: infinitival
complement to the right, object and subject NPs to the left (book:
`zag := ((S₊SUB\NP)\NP)/VP₋SUB`; the toy `Cat` drops the features).
`Sub` = subordinate-clause head — contrast `InfSubj`, whose `/NP` is a
raised-subject slot. -/
def PercVSub : Cat := ((S \ NP) \ NP) / VP

/-- Infinitival head with a raised object, `(VP\NP)/VP` (book:
`zien := (VP\NP)/VP₋SUB`). -/
def InfHeadSub : Cat := (VP \ NP) / VP

/-- The Dutch lexicon (reference; the derivations below select specific entries). -/
def dutchLexicon : List LexEntry := [
  ⟨"Jan", NP⟩, ⟨"Piet", NP⟩, ⟨"Marie", NP⟩, ⟨"Karel", NP⟩,
  ⟨"zag", PercV⟩, ⟨"zag", PercVSub⟩,
  ⟨"helpen", ControlV⟩, ⟨"laten", ControlV⟩,
  ⟨"helpen", ControlVR⟩, ⟨"laten", ControlVR⟩,
  ⟨"helpen", InfHeadSub⟩,
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
    out "Jan zag zwemmen Piet". The categories here capture the cross-serial *binding*
    pattern but not the *linear order*; the surface-faithful derivations below get both. -/
theorem jan_zag_zwemmen_piet_yield :
    jan_zag_zwemmen_piet.yield = ["Jan", "zag", "zwemmen", "Piet"] := by decide

/-! ### Surface-faithful derivations (leftward argument categories)

[steedman-2000]'s own analysis (ch. 6; appendix summary of the Dutch
fragment) gives subordinate-clause cluster verbs *leftward* NP slots and
composes the cluster by forward **crossed** composition (`fcompX1`), so the
NPs precede the whole cluster and the yield is the attested
"Jan Piet (Marie) zag (helpen) zwemmen". -/

def zag_sub : Derivation := .lex PercVSub "zag"
def helpen_sub : Derivation := .lex InfHeadSub "helpen"
def zwemmen_bare : Derivation := .lex VP "zwemmen"

/-- "(dat) Jan Piet zag zwemmen": `zag` applies to bare `zwemmen` and the
NPs attach leftward — the 2-verb cluster needs no composition. -/
def jan_piet_zag_zwemmen_sub : Derivation :=
  .ba jan_lex (.ba piet_lex (.fa zag_sub zwemmen_bare))

/-- "(dat) Jan Piet Marie zag helpen zwemmen": `helpen zwemmen : VP\NP`
forms by application, `zag >B× (helpen zwemmen)` crosses the rightward
`/VP` into a leftward-seeking cluster `((S\NP)\NP)\NP`, and the three NPs
attach leftward — Marie to `helpen`'s slot, Piet to `zag`'s object slot,
Jan as subject: the cross-serial binding falls out of the category
threading. -/
def jan_piet_marie_zag_helpen_zwemmen_sub : Derivation :=
  .ba jan_lex (.ba piet_lex (.ba marie_lex
    (.fcx1 zag_sub (.fa helpen_sub zwemmen_bare))))

theorem two_np_sub_derives_S :
    jan_piet_zag_zwemmen_sub.cat = some S := by decide

theorem three_np_sub_derives_S :
    jan_piet_marie_zag_helpen_zwemmen_sub.cat = some S := by decide

/-- The crossed cluster is a leftward-seeking 3-place predicate. -/
theorem crossed_cluster_cat :
    (Derivation.fcx1 zag_sub (.fa helpen_sub zwemmen_bare)).cat
      = some (((S \ NP) \ NP) \ NP) := by decide

/-- The surface-faithful derivations spell out the attested word order
(contrast `jan_zag_zwemmen_piet_yield`). -/
theorem two_np_sub_yield :
    jan_piet_zag_zwemmen_sub.yield = ["Jan", "Piet", "zag", "zwemmen"] := by
  decide

theorem three_np_sub_yield :
    jan_piet_marie_zag_helpen_zwemmen_sub.yield
      = ["Jan", "Piet", "Marie", "zag", "helpen", "zwemmen"] := by decide

end CCG.CrossSerial
