import Linglib.Core.Modality.TemporalAxes
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

## @cite{matthewson-2013} Figure 1: Gitksan modal system

|                  | Possibility  | (Weak) Necessity |
|------------------|-------------|-----------------|
| **Circumstantial** |             |                 |
| Plain            | da'akhlxw   | sgi             |
| Deontic          | anook(xw)   | sgi             |
| **Epistemic**    |             |                 |
| Plain            | ima('a)     | ima('a)         |
| Reportative      | gat         | gat             |

The (WEAK) annotation in the column header is load-bearing: Gitksan has
no STRONG circumstantial necessity modal — pure-necessity cases like
"I have to sneeze" use a plain future, not sgi (@cite{matthewson-2013}
ex. 95–98). This asymmetry is the crux of Matthewson's "mixed system"
typological claim: strength is encoded in the circumstantial domain,
but only weakly.
-/

namespace Fragments.Gitksan.Modals

open Core.Modality (ForceFlavor ForceAnalysis BackgroundClass TemporalOrientation)
open Semantics.Modality.Typology (ModalExpression)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev wnd := ForceFlavor.mk .weakNecessity .deontic
private abbrev wnc := ForceFlavor.mk .weakNecessity .circumstantial
private abbrev pd := ForceFlavor.mk .possibility .deontic
private abbrev pc := ForceFlavor.mk .possibility .circumstantial
private abbrev pb := ForceFlavor.mk .possibility .bouletic

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

/-- General circumstantial possibility: pure circumstantial, ability,
    bouletic, teleological, and (in competition with `anookxw`) deontic
    permission. @cite{matthewson-2013} §4.1, ex. 63–65: da'akhlxw allows
    bouletic interpretations ('You could eat less cake'), teleological
    interpretations (subsumed under circumstantial in linglib's flavor
    inventory), and deontic permission ('My mother told me I could play').
    Listed flavors: circumstantial (covering pure circumstantial, ability,
    teleological), deontic (permission overlap with anookxw), bouletic. -/
def daakhlxw : ModalExpression := ⟨"da'akhlxw", [pc, pd, pb]⟩

/-- Specialized deontic possibility ('allowed to'). @cite{matthewson-2013}
    §4.2: anook competes with da'akhlxw in permission contexts but is
    strictly deontic — infelicitous in pure circumstantial situations
    (ex. 79). -/
def anookxw : ModalExpression := ⟨"anook(xw)", [pd]⟩

/-- Circumstantial **weak** necessity. @cite{matthewson-2013} §4.3 (and
    Figure 1: column header is "(WEAK) NECESSITY"): sgi expresses
    obligation, deontic 'should', and weak circumstantial necessity. The
    preferred English translation is 'should', a weak necessity modal.

    Caveat: Matthewson herself hedges. *sgi* is INFELICITOUS in some
    pure strong-necessity contexts (sneeze case, ex. 96–98), but IS
    felicitous in others (ex. 100, "*k'ap sgi dim gwalga daxw-'m*"
    'We must all die'). The §4.3 conclusion (p. 384) suggests the
    infelicity may be a modality-TYPE issue (perhaps *sgi* requires a
    non-empty priority ordering source) rather than a strict
    weak-necessity restriction. The Fig. 1 parenthesization of
    "(WEAK)" reflects this uncertainty. -/
def sgi : ModalExpression := ⟨"sgi", [wnd, wnc]⟩

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
  | ⟨"sgi", _⟩ => .fixed .weakNecessity
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

@cite{matthewson-2013} §3–4: prospective aspect marking with `dim` is
required *asymmetrically*. Circumstantial modals (`da'akhlxw`, `anookxw`,
`sgi`) require `dim` regardless of temporal orientation — past, present,
or future, dim must always co-occur (§4.1 ex. 51–58, §4.2 ex. 73–78,
§4.3 ex. 82–88). Epistemic modals (`imaa`, `gat`) require `dim` *only*
when the temporal orientation is future (§3.3 ex. 38–42); past and
present orientations are felicitous without dim.

The contrast with English is the central typological mirror @cite{matthewson-2013}
§3.3 draws: English obligatorily marks past orientation (via *have*),
Gitksan obligatorily marks future orientation (via *dim*) — but for
Gitksan epistemics only. Circumstantials uniformly demand the marker. -/

/-- Whether prospective `dim` is required, given a modal expression and
    the temporal orientation of its prejacent. The asymmetry follows
    the modal's flavor: circumstantials always require dim; epistemics
    only require dim when oriented to the future. -/
def requiresDim (e : ModalExpression) (orient : TemporalOrientation) : Bool :=
  if e.meaning.all (fun ff => ff.flavor == .epistemic) then
    -- Epistemic modal: dim required iff future orientation.
    orient == .future
  else
    -- Circumstantial modal: dim always required.
    true

/-! ### Per-modal dim requirements

@cite{matthewson-2013} §3.3 ex. 38–42 (`imaa`), §3.3 (`gat`):
epistemic modals are felicitous without `dim` for past/present
orientations and require `dim` for future. -/

@[simp] theorem requiresDim_imaa_past    : requiresDim imaa .past    = false := rfl
@[simp] theorem requiresDim_imaa_present : requiresDim imaa .present = false := rfl
@[simp] theorem requiresDim_imaa_future  : requiresDim imaa .future  = true  := rfl

@[simp] theorem requiresDim_gat_past    : requiresDim gat .past    = false := rfl
@[simp] theorem requiresDim_gat_present : requiresDim gat .present = false := rfl
@[simp] theorem requiresDim_gat_future  : requiresDim gat .future  = true  := rfl

@[simp] theorem requiresDim_daakhlxw (o : TemporalOrientation) :
    requiresDim daakhlxw o = true := by cases o <;> rfl

@[simp] theorem requiresDim_anookxw (o : TemporalOrientation) :
    requiresDim anookxw o = true := by cases o <;> rfl

@[simp] theorem requiresDim_sgi (o : TemporalOrientation) :
    requiresDim sgi o = true := by cases o <;> rfl

/-- Circumstantial modals require `dim` for any orientation
    (§4.1 ex. 51–58, §4.2 ex. 73–78, §4.3 ex. 82–88). -/
theorem requiresDim_circumstantial :
    circumstantialModals.all (fun e =>
      [TemporalOrientation.past, .present, .future].all (fun o =>
        requiresDim e o)) = true := by decide

/-- Epistemic modals do not uniformly require `dim`: at least one
    epistemic / past-or-present pair is felicitous without it. -/
theorem epistemics_nonuniform_dim :
    epistemicModals.any (fun e =>
      [TemporalOrientation.past, .present].any (fun o =>
        !requiresDim e o)) = true := by decide

end Fragments.Gitksan.Modals
