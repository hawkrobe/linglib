import Linglib.Semantics.Coordination.Defs

/-!
# Hausa Coordination Morphemes
[schwartz-1989] [haspelmath-2007]

Hausa (Chadic, Nigeria) uses *da* for both comitative ("with") and
conjunction ("and") — a classic WITH-language in [stassen-2000]'s
classification. [haspelmath-2007] (12) cites [schwartz-1989]:32,36
for the data.

- *da* — J, free, prepositive medial: "A da B" = 'A and B' / 'A with B'

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.hausa`).
-/

namespace Hausa

/-- *da* — J particle, also comitative marker. Free, prepositive.
    Diachronic source: comitative ('with') → coordinator ('and'). -/
def da : Coordinator :=
  { form := "da", gloss := "and; with"
  , role := .j, kind := .free
  , note := "comitative-derived; identical form for 'with' and 'and'" }

def allEntries : List Coordinator := [da]

end Hausa
