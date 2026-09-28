module

public import Linglib.Syntax.Case.Basic

/-!
# Telugu case

Telugu marks four cases on the noun by suffix and the other relations by postposition. The
nominative is the bare stem and the genitive the oblique stem, neither with a suffix; the
accusative suffix is *-ni* and the dative *-ki*, each also heard with *-u* for *-i* except after
an *i*. The oblique stem carries the accusative and dative suffixes and the postpositions alike,
among them *lō* 'in' and *nunci* 'from'. Dravidian grammars keep the postpositions apart from
the cases, and Aitha shows the Telugu ones to stand outside the noun's prosodic word. The forms
are those of the paradigms of *illu* 'house' and *samudram* 'ocean' that Aitha reproduces from
Krishnamurti and Gwynn's grammar; the oblique stem is the matter of `Studies/Aitha2026.lean`.

## Main definitions

* `Telugu.Case`, `Telugu.Case.suffix`: the four cases, and the suffixes of the two that have one.
* `Telugu.Postposition`: the locative *lō* and the ablative *nunci*.

## References

* [aitha-2026]
* [kolichala-2026]
-/

@[expose] public section

namespace Telugu

/-! ### Cases -/

/-- The four cases. -/
inductive Case where
  /-- The nominative, the bare stem. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The genitive, the oblique stem. -/
  | gen
  /-- The dative. -/
  | dat
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for. -/
def label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | gen => .gen
  | dat => .dat

/-- The suffix of a case, inside the noun's prosodic word: the accusative *-ni*, also *-nu*
except after an *i*, and the dative *-ki*, also *-ku* except after an *i*. The nominative and the
genitive have none. -/
def suffix : Case → Option String
  | nom | gen => none
  | acc => some "-ni/-nu"
  | dat => some "-ki/-ku"

end Case

/-! ### Postpositions -/

/-- The postpositions, separate words after the oblique stem. -/
inductive Postposition where
  /-- *lō* 'in'. -/
  | lō
  /-- *nunci* 'from'. -/
  | nunci
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a postposition is named for, the locative *lō* and the ablative
*nunci*. -/
def Postposition.label : Postposition → _root_.Case
  | lō => .loc
  | nunci => .abl

end Telugu
