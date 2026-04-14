import Linglib.Theories.Semantics.Modality.Typology

/-!
# Gitksan Modal Inventory

@cite{matthewson-2013} @cite{matthewson-2016} @cite{peterson-2010}

Gitksan (Tsimshianic, ISO 639-3 `git`) modal system, spoken in northern
British Columbia. The system shows two key typological properties:

1. **Absolute epistemic/circumstantial split**: epistemic modals cannot
   be used circumstantially and vice versa (@cite{matthewson-2016} Table 18.1).
2. **Variable-force epistemic modals**: ima('a) and gat are compatible with
   both necessity and possibility contexts, contrasting only in information
   source — not in force (@cite{peterson-2010}).
3. **Prospective aspect `dim`**: obligatorily marks future temporal orientation
   for modals; without it, epistemic ima('a) cannot be future-oriented
   (@cite{matthewson-2016} §18.4.3, examples 60–63).

## Table 18.1: Gitksan modal system

|                  | Possibility  | (Weak) Necessity |
|------------------|-------------|-----------------|
| **Circumstantial** |             |                 |
| Plain            | da'akhlxw   | sgi             |
| Deontic          | anook(xw)   | sgi             |
| **Epistemic**    |             |                 |
| Plain            | ima('a)     | ima('a)         |
| Reportative      | gat         | gat             |
-/

namespace Fragments.Gitksan.Modals

open Core.Modality (ForceFlavor ForceAnalysis BackgroundClass)
open Semantics.Modality.Typology (ModalExpression)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev nd := ForceFlavor.mk .necessity .deontic
private abbrev nc := ForceFlavor.mk .necessity .circumstantial
private abbrev pd := ForceFlavor.mk .possibility .deontic
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

/-! ## Modal expressions -/

/-- Variable-force plain epistemic modal.
    @cite{peterson-2010}: analysed as a possibility modal strengthened via
    ordering source, compatible with both necessity and possibility contexts.
    @cite{matthewson-2016} §18.3.2: not specialized for a particular force. -/
def imaa : ModalExpression := ⟨"ima('a)", [pe, ne]⟩

/-- Variable-force reportative epistemic modal.
    Distinguished from ima('a) by information source: gat requires
    reportative evidence. Under @cite{kratzer-2012}'s reclassification,
    gat is **content-evidential** (the speaker can disbelieve the report),
    while ima('a) is **factual-evidential**. -/
def gat : ModalExpression := ⟨"gat", [pe, ne]⟩

/-- Circumstantial possibility ('able to'). -/
def daakhlxw : ModalExpression := ⟨"da'akhlxw", [pc]⟩

/-- Deontic possibility ('allowed to'). -/
def anookxw : ModalExpression := ⟨"anook(xw)", [pd]⟩

/-- Circumstantial necessity: deontic, pure circumstantial, and teleological.
    @cite{matthewson-2016} Table 18.1: the only circumstantial necessity modal.
    Covers obligation ('should/must go home'), pure circumstantial, and
    goal-directed readings. -/
def sgi : ModalExpression := ⟨"sgi", [nd, nc]⟩

def allExpressions : List ModalExpression :=
  [imaa, gat, daakhlxw, anookxw, sgi]

/-! ## Force analysis

The Gitksan epistemic modals are variable-force: they do not lexically
specify necessity or possibility, but are compatible with both.
The circumstantial modals have fixed force. -/

/-- Force analysis for each Gitksan modal. -/
def forceAnalysis : ModalExpression → ForceAnalysis
  | ⟨"ima('a)", _⟩ => .variableForce
  | ⟨"gat", _⟩ => .variableForce
  | ⟨"da'akhlxw", _⟩ => .fixed .possibility
  | ⟨"anook(xw)", _⟩ => .fixed .possibility
  | ⟨"sgi", _⟩ => .fixed .necessity
  | _ => .fixed .possibility

/-! ## Three-way background classification (@cite{matthewson-2016} Table 18.3)

Gitksan lexicalizes all three background classes:
- **factual-circumstantial**: da'akhlxw, anookxw, sgi
- **factual-evidential**: ima('a) (inferential, speaker cannot disbelieve)
- **content-evidential**: gat (reportative, speaker can disbelieve) -/

def backgroundClass : ModalExpression → BackgroundClass
  | ⟨"ima('a)", _⟩ => .factualEvidential
  | ⟨"gat", _⟩ => .contentEvidential
  | _ => .factualCircumstantial

/-! ## Absolute epistemic/circumstantial split

The epistemic and circumstantial domains are strictly separated:
epistemic modals cannot be used circumstantially and vice versa.
@cite{matthewson-2016} §18.2.3, example 20. -/

/-- Epistemic modals. -/
def epistemicModals : List ModalExpression := [imaa, gat]

/-- Circumstantial modals. -/
def circumstantialModals : List ModalExpression := [daakhlxw, anookxw, sgi]

/-- No epistemic modal has a circumstantial reading. -/
theorem epistemic_no_circumstantial :
    epistemicModals.all (fun e =>
      e.meaning.all (fun ff => ff.flavor == .epistemic)) = true := by decide

/-- No circumstantial modal has an epistemic reading. -/
theorem circumstantial_no_epistemic :
    circumstantialModals.all (fun e =>
      e.meaning.all (fun ff => ff.flavor != .epistemic)) = true := by decide

/-! ## Prospective aspect marker `dim`

@cite{matthewson-2016} §18.4.3: prospective aspect marking is obligatory
for future temporal orientation in Gitksan. Without `dim`, epistemic
ima('a) can only have past or present temporal orientation (examples 60–63).
English and Gitksan are mirror images: past orientation is obligatorily
marked in English (via *have*), future orientation is obligatorily marked
in Gitksan (via *dim*). -/

/-- Temporal orientation of Gitksan epistemic modals. -/
inductive TemporalOrientation where
  | past | present | future
  deriving DecidableEq, Repr, BEq

/-- Whether prospective `dim` is required for a given temporal orientation. -/
def requiresDim : TemporalOrientation → Bool
  | .future => true
  | _ => false

/-- Without `dim`, only past and present orientations are available. -/
theorem no_dim_no_future :
    [TemporalOrientation.past, .present].all (fun o => !requiresDim o) = true := by
  decide

end Fragments.Gitksan.Modals
