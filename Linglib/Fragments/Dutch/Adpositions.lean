import Linglib.Core.Path

/-!
# Dutch Adposition Fragment
@cite{broekhuis-corver-2026} @cite{dendikken-2010}

Lexical entries for Dutch adpositions, encoding their surface distribution
(preposition, postposition, circumposition, intransitive/particle) and
core properties (R-pronominalization, complement types).

## Key Empirical Generalizations (@cite{broekhuis-corver-2026})

1. PostPs are a proper subset of prePs — every postP can also be a preP (§6)
2. PrePs are locational; postPs are directional (§2.2, ex. 21–23)
3. Morphologically complex prePs resist R-pronominalization (§2.1, ex. 20)
4. The four-way classification (preP/postP/circumP/intrP) is
   epiphenomenal — all derive from prePs via syntactic movement (§6)

## Cross-references

- `Fragments.Dutch.TemporalConnectives`: *tot* as temporal connective
- `Phenomena.Constructions.ParticleVerbs.Studies.Dendikken1995`: particles as P heads
-/

namespace Fragments.Dutch.Adpositions

open Core.Path (PathShape)

/-- Complement types attested for Dutch adpositions.
    @cite{broekhuis-corver-2026} §2.1: nominal (default), PP, adjectival,
    clausal, infinitival, small-clause, none (intransitive). -/
inductive PComplementType where
  | nominal      -- DP complement (default)
  | pp           -- PP complement (van [PP na de oorlog], tot [PP in het bos])
  | adjectival   -- AP complement (tot [AP voor kort])
  | clausal      -- dat-clause (voor [CP dat hij vertrok])
  | infinitival  -- te-infinitive (na [CP te zijn gevallen])
  | smallClause  -- subject + predicate (met [SC Jan in ons team])
  | none_        -- no complement (intransitive / verbal particle)
  deriving DecidableEq, Repr

/-- A Dutch adposition lexical entry.
    Records observable distributional properties only — no
    theoretical analysis of WHY these properties hold. -/
structure DutchAdposition where
  /-- Surface form -/
  form         : String
  /-- Attested as preposition (complement follows P) -/
  prePOk       : Bool
  /-- Attested as postposition (complement precedes P) -/
  postPOk      : Bool
  /-- Second element if this P participates in a circumposition -/
  circumPart   : Option String := none
  /-- Attested without complement (intransitive / verbal particle use) -/
  intransOk    : Bool := false
  /-- Allows R-pronominalization (er/daar/waar + P); §2.1, ex. 19–20 -/
  rPronOk      : Bool := true
  /-- Attested complement types -/
  complTypes   : List PComplementType := [.nominal]
  /-- Has locational reading (place/state) -/
  locational   : Bool := false
  /-- Has directional reading (path/change of location) -/
  directional  : Bool := false
  /-- Path shape for directional uses (if any) -/
  pathShape    : Option PathShape := none
  /-- English gloss -/
  gloss        : String
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 1. Spatial adpositions
-- ════════════════════════════════════════════════════

/-- §2.2 ex. 21: *op* is both preP (locational "on") and postP (directional
    "onto"). The clearest minimal pair in the paper: *op de heuvel* (on the
    hill) vs *de heuvel op* (onto the hill). Auxiliary selection confirms the
    semantic split: *hebben* (locational) vs *zijn* (directional, ex. 22). -/
def op : DutchAdposition :=
  { form := "op", prePOk := true, postPOk := true
  , intransOk := true
  , locational := true, directional := true
  , pathShape := some .bounded
  , gloss := "on/onto/up" }

/-- §2.1 ex. 2a, §2.2 ex. 35a/58a: *in* is preP (locational "in") and postP
    (directional "into"). *De boom in* (ex. 35a) = "into the tree". -/
def in_ : DutchAdposition :=
  { form := "in", prePOk := true, postPOk := true
  , intransOk := true
  , locational := true, directional := true
  , pathShape := some .bounded
  , gloss := "in/into" }

/-- §2.1 ex. 2b: *naar* is preP only, inherently directional.
    *Naar de garage* = "to the garage". -/
def naar : DutchAdposition :=
  { form := "naar", prePOk := true, postPOk := false
  , directional := true
  , pathShape := some .bounded
  , gloss := "to" }

/-- §2.1 ex. 6–7: *van* indicates starting point of a path.
    Takes PP complements: *van [PP na de oorlog]* (ex. 7a).
    Circumposition with *af*: *van het dak af* (ex. 59). -/
def van : DutchAdposition :=
  { form := "van", prePOk := true, postPOk := false
  , circumPart := some "af"
  , complTypes := [.nominal, .pp]
  , directional := true
  , pathShape := some .source
  , gloss := "from/of" }

/-- §2.1 ex. 6–7: *tot* indicates endpoint of a path.
    Takes PP complements: *tot [PP (diep) in het bos]* (ex. 7b).
    Takes AP complements: *tot [AP voor kort]* (ex. 8a).
    See also `Fragments.Dutch.TemporalConnectives.tot` for the temporal
    sense, which has `complementType := .nominal` — the spatial sense
    is broader. -/
def tot : DutchAdposition :=
  { form := "tot", prePOk := true, postPOk := false
  , complTypes := [.nominal, .pp, .adjectival]
  , directional := true
  , pathShape := some .bounded
  , gloss := "to/until" }

/-- §3 ex. 31a, §2.3 ex. 28b: *achter* = "behind".
    Intransitive: *Mijn fiets staat achter* (ex. 28b). -/
def achter : DutchAdposition :=
  { form := "achter", prePOk := true, postPOk := false
  , intransOk := true
  , locational := true
  , gloss := "behind" }

/-- §2.3 ex. 28a, §3 ex. 37: *boven* = "above/upstairs".
    Intransitive: *De douche bevindt zich boven* (ex. 28a). -/
def boven : DutchAdposition :=
  { form := "boven", prePOk := true, postPOk := false
  , intransOk := true
  , locational := true
  , gloss := "above" }

/-- §2.2 ex. 24a: *onder* = "under". Circumposition with *door*:
    *onder de brug door* (ex. 24a) = crossing under the bridge.
    Locational as preP, directional in circumP use. -/
def onder : DutchAdposition :=
  { form := "onder", prePOk := true, postPOk := false
  , circumPart := some "door"
  , locational := true, directional := true
  , pathShape := some .bounded
  , gloss := "under" }

/-- §2.2 ex. 24b: *over* = "over/across". Circumposition with *heen*:
    *over de heide heen* (ex. 24b) = across the heath.
    Locational as preP, directional in circumP use. -/
def over : DutchAdposition :=
  { form := "over", prePOk := true, postPOk := false
  , circumPart := some "heen"
  , intransOk := true
  , locational := true, directional := true
  , pathShape := some .bounded
  , gloss := "over/across" }

/-- §2.2 ex. 25: *tussen* = "between". Circumposition with *in*:
    *tussen de kippen in* (ex. 25). -/
def tussen : DutchAdposition :=
  { form := "tussen", prePOk := true, postPOk := false
  , circumPart := some "in"
  , locational := true
  , gloss := "between" }

/-- *bij* = "at/near". Locational only. -/
def bij : DutchAdposition :=
  { form := "bij", prePOk := true, postPOk := false
  , locational := true
  , gloss := "at/near" }

/-- *tegen* = "against". -/
def tegen : DutchAdposition :=
  { form := "tegen", prePOk := true, postPOk := false
  , locational := true
  , gloss := "against" }

/-- *langs* = "along". -/
def langs : DutchAdposition :=
  { form := "langs", prePOk := true, postPOk := false
  , locational := true
  , gloss := "along" }

/-- *uit* = "out of". Source-directional.
    Intransitive in *uitslapen* (§2.3 ex. 29b). -/
def uit : DutchAdposition :=
  { form := "uit", prePOk := true, postPOk := false
  , intransOk := true
  , directional := true
  , pathShape := some .source
  , gloss := "out of" }

/-- §2.3 ex. 28c: *om* = "around".
    Intransitive: *Marie deed een sjaal om* (ex. 28c). -/
def om : DutchAdposition :=
  { form := "om", prePOk := true, postPOk := false
  , intransOk := true
  , locational := true
  , gloss := "around" }

-- ════════════════════════════════════════════════════
-- § 2. Non-spatial adpositions
-- ════════════════════════════════════════════════════

/-- §2.1 ex. 14, 19e: *met* = "with".
    Takes small-clause complement in absolute *met*-construction:
    *Met [Jan in ons team] zullen we nooit verliezen* (ex. 14a). -/
def met : DutchAdposition :=
  { form := "met", prePOk := true, postPOk := false
  , complTypes := [.nominal, .smallClause]
  , gloss := "with" }

/-- §2.1 ex. 5, 9a: *voor* = "for/before".
    Temporal sense takes clausal complement: *voor [CP (dat) hij vertrok]*
    (ex. 9a). Also takes PP (*voor [PP bij de koffie]*, ex. 5) and
    AP (*voor [AP kort]*, ex. 8a) complements. -/
def voor : DutchAdposition :=
  { form := "voor", prePOk := true, postPOk := false
  , complTypes := [.nominal, .pp, .adjectival, .clausal]
  , locational := true
  , gloss := "for/before" }

/-- §2.1 ex. 9b, 13a, 19c: *na* = "after".
    Clausal complement with obligatory *dat*: *na [CP *(dat) hij gevallen
    was]* (ex. 9b). Infinitival: *na [CP te zijn gevallen]* (ex. 13a). -/
def na : DutchAdposition :=
  { form := "na", prePOk := true, postPOk := false
  , complTypes := [.nominal, .clausal, .infinitival]
  , gloss := "after" }

/-- §2.1 ex. 13b, 20c: *zonder* = "without".
    Infinitival complement: *zonder [CP te snurken]* (ex. 13b).
    Resists R-pronominalization: *✱er zonder* (ex. 20c). -/
def zonder : DutchAdposition :=
  { form := "zonder", prePOk := true, postPOk := false
  , rPronOk := false
  , complTypes := [.nominal, .infinitival]
  , gloss := "without" }

/-- §2.1 ex. 20a: *tijdens* = "during".
    Resists R-pronominalization: *✱er tijdens*. -/
def tijdens : DutchAdposition :=
  { form := "tijdens", prePOk := true, postPOk := false
  , rPronOk := false
  , gloss := "during" }

/-- §2.1 ex. 20b: *ondanks* = "despite".
    Resists R-pronominalization: *✱er ondanks*. -/
def ondanks : DutchAdposition :=
  { form := "ondanks", prePOk := true, postPOk := false
  , rPronOk := false
  , gloss := "despite" }

/-- §4 ex. 44d: *door* = "through/by" (causal/instrumental).
    Clausal complement: *door [CP dat de wind hard waaide]* (ex. 44d').
    Also functions as circumP second element (*onder...door*) and as
    verbal particle. -/
def door : DutchAdposition :=
  { form := "door", prePOk := true, postPOk := false
  , intransOk := true
  , complTypes := [.nominal, .clausal]
  , gloss := "through/by" }

-- ════════════════════════════════════════════════════
-- § 3. CircumP second elements / particles
-- ════════════════════════════════════════════════════

/-- *af* = "off/down". Primarily circumP second element (*van...af*, ex. 59)
    and verbal particle. Not commonly used as standalone preP
    (§2.2: "P₂ has a form that is not commonly used as a preP"). -/
def af : DutchAdposition :=
  { form := "af", prePOk := false, postPOk := false
  , intransOk := true
  , directional := true
  , pathShape := some .source
  , gloss := "off/down" }

/-- *heen* = directional particle. Primarily circumP second element
    (*over...heen*, ex. 24b). Not commonly used as standalone preP. -/
def heen : DutchAdposition :=
  { form := "heen", prePOk := false, postPOk := false
  , intransOk := true
  , directional := true
  , pathShape := some .bounded
  , gloss := "thither (directional)" }

-- ════════════════════════════════════════════════════
-- § 4. Inventory and verification
-- ════════════════════════════════════════════════════

def dutchAdpositions : List DutchAdposition :=
  [ op, in_, naar, van, tot, achter, boven, onder, over, tussen
  , bij, tegen, langs, uit, om
  , met, voor, na, zonder, tijdens, ondanks, door
  , af, heen ]

/-- Every adposition that has postP use also has preP use.
    @cite{broekhuis-corver-2026} §6: postPs derive from prePs by
    complement movement, so postP ⊆ preP. -/
theorem postP_subset_preP :
    ∀ a ∈ dutchAdpositions, a.postPOk → a.prePOk := by native_decide

/-- Morphologically complex prePs resist R-pronominalization.
    §2.1 ex. 20: *tijdens*, *ondanks*, *zonder* are diachronically
    complex and block *er*-pronominalization. -/
theorem complex_Ps_no_rPron :
    tijdens.rPronOk = false ∧ ondanks.rPronOk = false ∧
    zonder.rPronOk = false := ⟨rfl, rfl, rfl⟩

/-- CircumP second elements (af, heen) are not standalone prePs. -/
theorem circumP_parts_not_preP :
    af.prePOk = false ∧ heen.prePOk = false := ⟨rfl, rfl⟩

/-- All adpositions with directional readings have a PathShape. -/
theorem directional_has_pathShape :
    ∀ a ∈ dutchAdpositions, a.directional → a.pathShape.isSome := by native_decide

/-- PostP-capable adpositions have both locational and directional readings.
    §2.2 ex. 21: preP *op* = locational, postP *op* = directional. -/
theorem postP_has_both_readings :
    ∀ a ∈ dutchAdpositions, a.postPOk →
    a.locational ∧ a.directional := by native_decide

end Fragments.Dutch.Adpositions
