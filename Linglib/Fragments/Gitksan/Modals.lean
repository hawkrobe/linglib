module

public import Linglib.Semantics.Modality.Basic

/-!
# Gitksan Modal Inventory

[matthewson-2013] [peterson-2010]

Gitksan (Tsimshianic, ISO 639-3 `git`) modal system, spoken in northern British Columbia. The
epistemic modals are second-position clitics, *ima('a)* and the reportative *gat*, each
compatible with necessity and possibility contexts alike ([peterson-2010]); the circumstantial
modals are verbs and predicative particles, *da'akhlxw* and *anook(xw)* for possibility and
*sgi* for weak necessity, with no strong circumstantial necessity modal ([matthewson-2013]
Fig. 1).

|                  | Possibility  | (Weak) Necessity |
|------------------|-------------|-----------------|
| **Circumstantial** |             |                 |
| Plain            | da'akhlxw   | sgi             |
| Deontic          | anook(xw)   | sgi             |
| **Epistemic**    |             |                 |
| Plain            | ima('a)     | ima('a)         |
| Reportative      | gat         | gat             |
-/

@[expose] public section

namespace Gitksan

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev wnd : ForceFlavor := (.weakNecessity, .deontic)
abbrev wnc : ForceFlavor := (.weakNecessity, .circumstantial)
abbrev pd : ForceFlavor := (.possibility, .deontic)
abbrev pc : ForceFlavor := (.possibility, .circumstantial)
abbrev pb : ForceFlavor := (.possibility, .bouletic)

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

def modals : List ModalItem :=
  [imaa, gat, daakhlxw, anookxw, sgi]

/-! ## The two domains -/

/-- Epistemic modals. -/
def epistemicModals : List ModalItem := [imaa, gat]

/-- Circumstantial modals. -/
def circumstantialModals : List ModalItem := [daakhlxw, anookxw, sgi]

end Gitksan
