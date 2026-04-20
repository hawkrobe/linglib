import Linglib.Theories.Semantics.Modality.Typology

/-!
# Niuean Modal Inventory

@cite{matthewson-2016} @cite{matthewson-et-al-2012} @cite{seiter-1980}

Niuean (Polynesian, ISO 639-3 `niu`) modal system. Niuean exemplifies
a typological pattern where force distinctions are encoded in the
**circumstantial** domain (separate possibility and necessity modals)
but absent in the **epistemic** domain (a single general-purpose
epistemic modal covers both force values).

## Modal inventory

| Modal   | Domain         | Force           | Source                         |
|---------|---------------|-----------------|--------------------------------|
| liga    | epistemic     | poss + nec      | @cite{matthewson-et-al-2012}   |
| maeke   | circumstantial| possibility     | @cite{seiter-1980} p. 140      |
| lata    | circumstantial| necessity       | @cite{seiter-1980} p. 133      |

## Key data (@cite{matthewson-2016} §18.5, examples 64–68)

(64) *liga kua fano tei* — 'He might have left.'
     (@cite{matthewson-et-al-2012} p. 224)

(65) *Hí ika a Tom he aho nei ... liga malolo a ia*
     'Tom is fishing today ... he's probably well.'
     (@cite{matthewson-et-al-2012} p. 228)

(66) *ne liga kua veli hifo e tama ke he pelapela*
     'The boy must have fallen in the mud.'
     (@cite{seiter-1980} p. 13)

(67) *kua maeke he tama ia ke taute pasikala afi*
     'That child is able to fix motorbikes.'
     (@cite{seiter-1980} p. 140)

(68) *lata ke ō a tautolu he aho nei ki Queen Street*
     'We should go to Queen Street today.'
     (@cite{seiter-1980} p. 133)

## Typological significance

@cite{matthewson-2016} §18.5: Niuean tests whether epistemic modals
are more likely to lack duals than circumstantial modals. The pattern —
general-purpose epistemic + dual circumstantial — is consistent with
Gitksan (variable-force epistemics, dual circumstantials) and with the
broader cross-linguistic tendency for force distinctions to be encoded
in the root/circumstantial domain.
-/

namespace Fragments.Niuean.Modals

open Core.Modality (ForceFlavor ForceAnalysis)
open Semantics.Modality.Typology (ModalExpression satisfiesIFF satisfiesSAV)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev nc := ForceFlavor.mk .necessity .circumstantial
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

/-! ## Modal expressions -/

/-- General-purpose epistemic modal: usable in both possibility and
    necessity contexts. @cite{matthewson-et-al-2012}.
    Translatable as 'might', 'probably', 'must' depending on context. -/
def liga : ModalExpression := ⟨"liga", [pe, ne]⟩

/-- Circumstantial possibility modal ('able to', 'can').
    @cite{seiter-1980} p. 140. -/
def maeke : ModalExpression := ⟨"maeke", [pc]⟩

/-- Circumstantial necessity modal ('should', 'must').
    @cite{seiter-1980} p. 133. -/
def lata : ModalExpression := ⟨"lata", [nc]⟩

def allExpressions : List ModalExpression := [liga, maeke, lata]

/-! ## Force analysis -/

/-- Force analysis for each Niuean modal.
    liga is variable-force; maeke and lata are fixed. -/
def forceAnalysis : ModalExpression → ForceAnalysis
  | ⟨"liga", _⟩ => .variableForce
  | ⟨"maeke", _⟩ => .fixed .possibility
  | ⟨"lata", _⟩ => .fixed .necessity
  | _ => .fixed .possibility

/-! ## Background classification -/

open Core.Modality (BackgroundClass) in
/-- Background class for each Niuean modal.
    liga is epistemic (factual-evidential); maeke and lata are
    circumstantial (factual-circumstantial). -/
def backgroundClass : ModalExpression → BackgroundClass
  | ⟨"liga", _⟩ => .factualEvidential
  | _ => .factualCircumstantial

/-! ## Dual structure

The circumstantial domain has a dual pair (maeke/lata), but the
epistemic domain does not — liga covers both forces. -/

/-- liga lacks a dual: no contrasting epistemic necessity or possibility modal. -/
theorem liga_no_dual : ¬ (forceAnalysis liga).HasDual := fun h => h.elim

/-- maeke has a dual (lata). -/
theorem maeke_has_dual : (forceAnalysis maeke).HasDual := trivial

/-- lata has a dual (maeke). -/
theorem lata_has_dual : (forceAnalysis lata).HasDual := trivial

/-! ## Typological properties -/

/-- liga satisfies IFF (variable force, single flavour). -/
theorem liga_satisfies_iff : satisfiesIFF liga.meaning = true := by decide

/-- liga satisfies SAV (varies on force axis only). -/
theorem liga_satisfies_sav : satisfiesSAV liga.meaning = true := by decide

/-- All Niuean modals satisfy IFF. -/
theorem all_satisfy_iff :
    allExpressions.all (fun e => satisfiesIFF e.meaning) = true := by decide

/-- All Niuean modals satisfy SAV. -/
theorem all_satisfy_sav :
    allExpressions.all (fun e => satisfiesSAV e.meaning) = true := by decide

/-! ## Flavour–force correlation

Epistemic domain: no force distinction (liga covers both).
Circumstantial domain: force distinction encoded (maeke vs lata).
This is exactly Nauze's (2008) polyfunctionality pattern applied to
the force dimension: liga varies along the force axis within the
epistemic flavour, while circumstantial modals are fixed on force. -/

/-- The epistemic domain has a single modal covering both forces. -/
theorem epistemic_single_modal :
    (allExpressions.filter (fun e =>
      e.meaning.any (fun ff => ff.flavor == .epistemic))).length = 1 := by
  decide

/-- The circumstantial domain has separate possibility and necessity modals. -/
theorem circumstantial_has_duals :
    (allExpressions.filter (fun e =>
      e.meaning.any (fun ff => ff.flavor == .circumstantial))).length = 2 := by
  decide

end Fragments.Niuean.Modals
