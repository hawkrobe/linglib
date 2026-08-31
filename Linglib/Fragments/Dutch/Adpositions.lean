import Linglib.Semantics.Events.Path
import Linglib.Features.Aktionsart

/-!
# Dutch adpositions

Lexical entries for the Dutch adpositions, recording for each one the orders it occurs in
(preposition, postposition, circumposition, intransitive particle), whether its complement can be
R-pronominalized, the complement types it takes, and its locational and directional readings with
the path each directional reading describes.

## References

* [broekhuis-corver-2026]
* [dendikken-2010]
-/

namespace Dutch.Adpositions

open Spatial (Path)
open Features (Telicity)

/-- The complement types Dutch adpositions are attested with. -/
inductive PComplementType where
  | nominal      -- DP complement (default)
  | pp           -- PP complement (van [PP na de oorlog], tot [PP in het bos])
  | adjectival   -- AP complement (tot [AP voor kort])
  | clausal      -- dat-clause (voor [CP dat hij vertrok])
  | infinitival  -- te-infinitive (na [CP te zijn gevallen])
  | smallClause  -- subject + predicate (met [SC Jan in ons team])
  | none_        -- no complement (intransitive / verbal particle)
  deriving DecidableEq, Repr

/-- A Dutch adposition, recorded by its attested distribution. -/
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
  /-- Allows R-pronominalization: *er*, *daar* or *waar* in place of the complement. -/
  rPronOk      : Bool := true
  /-- Attested complement types -/
  complTypes   : List PComplementType := [.nominal]
  /-- Has locational reading (place/state) -/
  locational   : Bool := false
  /-- Has directional reading (path/change of location) -/
  directional  : Bool := false
  /-- Directionality and telicity for directional uses (if any) -/
  pathType     : Option (Path.Directionality × Telicity) := none
  /-- English gloss -/
  gloss        : String
  deriving DecidableEq, Repr

/-! ### Spatial adpositions -/

/-- *Op* is locational as a preposition and directional as a postposition: *op de heuvel* 'on the
hill' against *de heuvel op* 'onto the hill', with *hebben* and *zijn* as their perfect
auxiliaries. -/
def op : DutchAdposition :=
  { form := "op", prePOk := true, postPOk := true
  , intransOk := true
  , locational := true, directional := true
  , pathType := some (.goal, .telic)
  , gloss := "on/onto/up" }

/-- *In* is locational as a preposition and directional as a postposition: *in de garage* 'in the
garage' against *de boom in* 'into the tree'. -/
def in_ : DutchAdposition :=
  { form := "in", prePOk := true, postPOk := true
  , intransOk := true
  , locational := true, directional := true
  , pathType := some (.goal, .telic)
  , gloss := "in/into" }

/-- *Naar* 'to' is inherently directional and occurs only as a preposition. -/
def naar : DutchAdposition :=
  { form := "naar", prePOk := true, postPOk := false
  , directional := true
  , pathType := some (.goal, .telic)
  , gloss := "to" }

/-- *Van* 'from' indicates the starting point of a path. It takes prepositional complements —
*van [PP na de oorlog]* 'from after the war' — and forms a circumposition with *af*: *van het dak
af* 'off the roof'. -/
def van : DutchAdposition :=
  { form := "van", prePOk := true, postPOk := false
  , circumPart := some "af"
  , complTypes := [.nominal, .pp]
  , directional := true
  , pathType := some (.source, .telic)
  , gloss := "from/of" }

/-- *Tot* 'to, until' indicates a later point on a path, not necessarily its end. It takes
prepositional as well as nominal complements: *tot [PP (diep) in het bos]*. See also
`Dutch.TemporalConnectives.tot` for the temporal sense, whose complement is nominal only. -/
def tot : DutchAdposition :=
  { form := "tot", prePOk := true, postPOk := false
  , complTypes := [.nominal, .pp]
  , directional := true
  , pathType := some (.goal, .telic)
  , gloss := "to/until" }

/-- *Achter* 'behind', also used without a complement: *mijn fiets staat achter* 'my bike is at
the back'. -/
def achter : DutchAdposition :=
  { form := "achter", prePOk := true, postPOk := false
  , intransOk := true
  , locational := true
  , gloss := "behind" }

/-- *Boven* 'above', also used without a complement: *de douche bevindt zich boven* 'the shower
is upstairs'. -/
def boven : DutchAdposition :=
  { form := "boven", prePOk := true, postPOk := false
  , intransOk := true
  , locational := true
  , gloss := "above" }

/-- *Onder* 'under' is locational as a preposition and directional in the circumposition with
*door*: *onder de brug door* 'under and past the bridge'. -/
def onder : DutchAdposition :=
  { form := "onder", prePOk := true, postPOk := false
  , circumPart := some "door"
  , locational := true, directional := true
  , pathType := some (.goal, .telic)
  , gloss := "under" }

/-- *Over* 'over' is locational as a preposition and directional in the circumposition with
*heen*: *over de heide heen* 'across the heath'. -/
def over : DutchAdposition :=
  { form := "over", prePOk := true, postPOk := false
  , circumPart := some "heen"
  , intransOk := true
  , locational := true, directional := true
  , pathType := some (.goal, .telic)
  , gloss := "over/across" }

/-- *Tussen* 'between', with the circumpositional variant *tussen de kippen in* 'in among the
chickens', which stays locational. -/
def tussen : DutchAdposition :=
  { form := "tussen", prePOk := true, postPOk := false
  , circumPart := some "in"
  , locational := true
  , gloss := "between" }

/-- *Bij* 'at, near', locational only. -/
def bij : DutchAdposition :=
  { form := "bij", prePOk := true, postPOk := false
  , locational := true
  , gloss := "at/near" }

/-- *Tegen* 'against'. -/
def tegen : DutchAdposition :=
  { form := "tegen", prePOk := true, postPOk := false
  , locational := true
  , gloss := "against" }

/-- *Langs* 'along'. -/
def langs : DutchAdposition :=
  { form := "langs", prePOk := true, postPOk := false
  , locational := true
  , gloss := "along" }

/-- *Uit* 'out of' describes a path away from a source, and is also a verbal particle: *Jan
slaapt graag uit* 'Jan likes to sleep late'. -/
def uit : DutchAdposition :=
  { form := "uit", prePOk := true, postPOk := false
  , intransOk := true
  , directional := true
  , pathType := some (.source, .telic)
  , gloss := "out of" }

/-- *Om* 'around', also used without a complement: *Marie deed een sjaal om* 'Marie put on a
scarf'. -/
def om : DutchAdposition :=
  { form := "om", prePOk := true, postPOk := false
  , intransOk := true
  , locational := true
  , gloss := "around" }

/-! ### Non-spatial adpositions -/

/-- *Met* 'with' takes a small clause in the absolute construction: *met [Jan in ons team]
zullen we nooit verliezen* 'with Jan on our team we will never lose'. -/
def met : DutchAdposition :=
  { form := "met", prePOk := true, postPOk := false
  , complTypes := [.nominal, .smallClause]
  , gloss := "with" }

/-- *Voor* 'for, before' is the widest-selecting preposition of the set: nominal, prepositional
(*voor [PP bij de koffie]*), adjectival (*voor [AP heel kort]*) and clausal (*voor [CP (dat) hij
vertrok]*) complements. -/
def voor : DutchAdposition :=
  { form := "voor", prePOk := true, postPOk := false
  , complTypes := [.nominal, .pp, .adjectival, .clausal]
  , locational := true
  , gloss := "for/before" }

/-- *Na* 'after' takes a clausal complement with obligatory *dat* — *na [CP dat hij gevallen
was]* — and a *te*-infinitive: *na [CP te zijn gevallen]* 'after falling'. -/
def na : DutchAdposition :=
  { form := "na", prePOk := true, postPOk := false
  , complTypes := [.nominal, .clausal, .infinitival]
  , gloss := "after" }

/-- *Zonder* 'without' takes a *te*-infinitive — *zonder [CP te snurken]* 'without snoring' —
and resists R-pronominalization: *\*er zonder*. -/
def zonder : DutchAdposition :=
  { form := "zonder", prePOk := true, postPOk := false
  , rPronOk := false
  , complTypes := [.nominal, .infinitival]
  , gloss := "without" }

/-- *Tijdens* 'during' resists R-pronominalization: *\*er tijdens*. -/
def tijdens : DutchAdposition :=
  { form := "tijdens", prePOk := true, postPOk := false
  , rPronOk := false
  , gloss := "during" }

/-- *Ondanks* 'despite' resists R-pronominalization: *\*er ondanks*. -/
def ondanks : DutchAdposition :=
  { form := "ondanks", prePOk := true, postPOk := false
  , rPronOk := false
  , gloss := "despite" }

/-- *Door* 'through, by' expresses cause as well as path, and takes a clausal complement: *door
[CP dat de wind hard waaide]* 'because the wind was blowing hard'. It is also the second element of
*onder … door* and a verbal particle. -/
def door : DutchAdposition :=
  { form := "door", prePOk := true, postPOk := false
  , intransOk := true
  , complTypes := [.nominal, .clausal]
  , gloss := "through/by" }

/-! ### Second elements of circumpositions, and particles -/

/-- *Af* 'off, down' is the second element of *van … af* and a verbal particle; it is not
commonly used as a preposition on its own. -/
def af : DutchAdposition :=
  { form := "af", prePOk := false, postPOk := false
  , intransOk := true
  , directional := true
  , pathType := some (.source, .telic)
  , gloss := "off/down" }

/-- *Heen* is a directional particle and the second element of *over … heen*; it is not commonly
used as a preposition on its own. -/
def heen : DutchAdposition :=
  { form := "heen", prePOk := false, postPOk := false
  , intransOk := true
  , directional := true
  , pathType := some (.goal, .telic)
  , gloss := "thither (directional)" }

/-! ### The inventory -/

/-- The Dutch adpositions covered here. -/
def dutchAdpositions : List DutchAdposition :=
  [ op, in_, naar, van, tot, achter, boven, onder, over, tussen
  , bij, tegen, langs, uit, om
  , met, voor, na, zonder, tijdens, ondanks, door
  , af, heen ]

end Dutch.Adpositions
