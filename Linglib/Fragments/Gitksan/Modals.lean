import Linglib.Semantics.Modality.Basic

/-!
# Gitksan Modal Inventory

[matthewson-2013] [matthewson-2016] [peterson-2010]

Gitksan (Tsimshianic, ISO 639-3 `git`) modal system, spoken in northern
British Columbia. The system shows two key typological properties:

1. **Absolute epistemic/circumstantial split**: epistemic modals cannot
   be used circumstantially and vice versa ([matthewson-2016] Table 18.1).
2. **Variable-force epistemic modals**: ima('a) and gat are compatible with
   both necessity and possibility contexts, contrasting only in information
   source — not in force ([peterson-2010]).
3. **Prospective aspect `dim`**: obligatorily marks future temporal orientation
   for modals; without it, epistemic ima('a) cannot be future-oriented
   ([matthewson-2016] §18.4.3, examples 60–63).

## [matthewson-2013] Figure 1: Gitksan modal system

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
"I have to sneeze" use a plain future, not sgi ([matthewson-2013]
ex. 95–98). This asymmetry is the crux of Matthewson's "mixed system"
typological claim: strength is encoded in the circumstantial domain,
but only weakly.
-/

namespace Gitksan.Modals

open Modality (ForceFlavor ForceAnalysis TemporalOrientation ModalItem)

private abbrev ne : ForceFlavor := (.necessity, .epistemic)
private abbrev pe : ForceFlavor := (.possibility, .epistemic)
private abbrev wnd : ForceFlavor := (.weakNecessity, .deontic)
private abbrev wnc : ForceFlavor := (.weakNecessity, .circumstantial)
private abbrev pd : ForceFlavor := (.possibility, .deontic)
private abbrev pc : ForceFlavor := (.possibility, .circumstantial)
private abbrev pb : ForceFlavor := (.possibility, .bouletic)

/-! ## Modal expressions -/

/-- Variable-force plain epistemic modal.
    [peterson-2010]: analysed as a possibility modal strengthened via
    ordering source, compatible with both necessity and possibility contexts.
    [matthewson-2016] §18.3.2: not specialized for a particular force. -/
def imaa : ModalItem := { form := "ima('a)", meaning := {pe, ne} }

/-- Variable-force reportative epistemic modal.
    Distinguished from ima('a) by information source: gat requires
    reportative evidence. Under [kratzer-2012]'s reclassification,
    gat is **content-evidential** (the speaker can disbelieve the report),
    while ima('a) is **factual-evidential**. -/
def gat : ModalItem := { form := "gat", meaning := {pe, ne} }

/-- General circumstantial possibility: pure circumstantial, ability,
    bouletic, teleological, and (in competition with `anookxw`) deontic
    permission. [matthewson-2013] §4.1, ex. 63–65: da'akhlxw allows
    bouletic interpretations ('You could eat less cake'), teleological
    interpretations (subsumed under circumstantial in linglib's flavor
    inventory), and deontic permission ('My mother told me I could play').
    Listed flavors: circumstantial (covering pure circumstantial, ability,
    teleological), deontic (permission overlap with anookxw), bouletic. -/
def daakhlxw : ModalItem := { form := "da'akhlxw", meaning := {pc, pd, pb} }

/-- Specialized deontic possibility ('allowed to'). [matthewson-2013]
    §4.2: anook competes with da'akhlxw in permission contexts but is
    strictly deontic — infelicitous in pure circumstantial situations
    (ex. 79). -/
def anookxw : ModalItem := { form := "anook(xw)", meaning := {pd} }

/-- Circumstantial **weak** necessity. [matthewson-2013] §4.3 (and
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
def sgi : ModalItem := { form := "sgi", meaning := {wnd, wnc} }

def allExpressions : List ModalItem :=
  [imaa, gat, daakhlxw, anookxw, sgi]

/-! ## Force analysis

The Gitksan epistemic modals are variable-force: they do not lexically
specify necessity or possibility, but are compatible with both.
The circumstantial modals have fixed force. -/

/-- Force analysis for each Gitksan modal. -/
def forceAnalysis : ModalItem → ForceAnalysis
  | ⟨"ima('a)", _, _⟩ => .variableForce
  | ⟨"gat", _, _⟩ => .variableForce
  | ⟨"da'akhlxw", _, _⟩ => .fixed .possibility
  | ⟨"anook(xw)", _, _⟩ => .fixed .possibility
  | ⟨"sgi", _, _⟩ => .fixed .weakNecessity
  | _ => .fixed .possibility

/-! ## Absolute epistemic/circumstantial split

The epistemic and circumstantial domains are strictly separated:
epistemic modals cannot be used circumstantially and vice versa.
[matthewson-2016] §18.2.3, example 20. -/

/-- Epistemic modals. -/
def epistemicModals : List ModalItem := [imaa, gat]

/-- Circumstantial modals. -/
def circumstantialModals : List ModalItem := [daakhlxw, anookxw, sgi]

/-- No epistemic modal has a circumstantial reading. -/
theorem epistemic_no_circumstantial :
    ∀ e ∈ epistemicModals, ∀ ff ∈ e.meaning, ff.flavor = .epistemic := by decide

/-- No circumstantial modal has an epistemic reading. -/
theorem circumstantial_no_epistemic :
    ∀ e ∈ circumstantialModals, ∀ ff ∈ e.meaning, ff.flavor ≠ .epistemic := by decide

/-! ## Prospective aspect marker `dim`

[matthewson-2013] §3–4: prospective aspect marking with `dim` is
required *asymmetrically*. Circumstantial modals (`da'akhlxw`, `anookxw`,
`sgi`) require `dim` regardless of temporal orientation — past, present,
or future, dim must always co-occur (§4.1 ex. 51–58, §4.2 ex. 73–78,
§4.3 ex. 82–88). Epistemic modals (`imaa`, `gat`) require `dim` *only*
when the temporal orientation is future (§3.3 ex. 38–42); past and
present orientations are felicitous without dim.

The contrast with English is the central typological mirror [matthewson-2013]
§3.3 draws: English obligatorily marks past orientation (via *have*),
Gitksan obligatorily marks future orientation (via *dim*) — but for
Gitksan epistemics only. Circumstantials uniformly demand the marker. -/

/-- Whether prospective `dim` is required, given a modal expression and
    the temporal orientation of its prejacent. The asymmetry follows
    the modal's flavor: circumstantials always require dim; epistemics
    only require dim when oriented to the future. -/
def requiresDim (e : ModalItem) (orient : TemporalOrientation) : Bool :=
  if ∀ ff ∈ e.meaning, ff.flavor = .epistemic then
    -- Epistemic modal: dim required iff future orientation.
    orient == .future
  else
    -- Circumstantial modal: dim always required.
    true

/-! ### Per-modal dim requirements

[matthewson-2013] §3.3 ex. 38–42 (`imaa`), §3.3 (`gat`):
epistemic modals are felicitous without `dim` for past/present
orientations and require `dim` for future. -/

@[simp] theorem requiresDim_imaa_past    : requiresDim imaa .past    = false := by decide
@[simp] theorem requiresDim_imaa_present : requiresDim imaa .present = false := by decide
@[simp] theorem requiresDim_imaa_future  : requiresDim imaa .future  = true  := by decide

@[simp] theorem requiresDim_gat_past    : requiresDim gat .past    = false := by decide
@[simp] theorem requiresDim_gat_present : requiresDim gat .present = false := by decide
@[simp] theorem requiresDim_gat_future  : requiresDim gat .future  = true  := by decide

@[simp] theorem requiresDim_daakhlxw (o : TemporalOrientation) :
    requiresDim daakhlxw o = true := by cases o <;> decide

@[simp] theorem requiresDim_anookxw (o : TemporalOrientation) :
    requiresDim anookxw o = true := by cases o <;> decide

@[simp] theorem requiresDim_sgi (o : TemporalOrientation) :
    requiresDim sgi o = true := by cases o <;> decide

/-- Circumstantial modals require `dim` for any orientation
    (§4.1 ex. 51–58, §4.2 ex. 73–78, §4.3 ex. 82–88). -/
theorem requiresDim_circumstantial :
    ∀ e ∈ circumstantialModals, ∀ o ∈ [TemporalOrientation.past, .present, .future],
      requiresDim e o = true := by decide

/-- Epistemic modals do not uniformly require `dim`: at least one
    epistemic / past-or-present pair is felicitous without it. -/
theorem epistemics_nonuniform_dim :
    ∃ e ∈ epistemicModals, ∃ o ∈ [TemporalOrientation.past, .present],
      requiresDim e o = false := by decide

end Gitksan.Modals
