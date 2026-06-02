import Linglib.Typology.Numeral.WALS

/-!
# Korean numeral profile (WALS Chs 53–56, 131)
@cite{wals-2013}
-/

namespace Korean

/-- Korean. Coded after @cite{wals-2013}: WALS 53A codes Korean
    "one-th, two-th, three-th" (Sino-Korean *je-* + cardinal, fully regular) →
    `allFromCardinals`; the native paradigm's *cheot-jjae* 'first' suppletion is
    a secondary system not picked up by the WALS coding. WALS 55A codes numeral
    classifiers Obligatory (counting requires a classifier: *haksaeng se myeong*
    'three CL student'). Distributive by suffix *-ssik* (*du-ssik* 'two each',
    WALS 54A). *Gwa*/*wa* (and) differs from *modu* (all). Optional plural with
    *-deul*; decimal base (WALS 131A). -/
def numeralProfile : Numeral.Profile :=
  Numeral.Profile.fromWALS "Korean" "kor" (region := .eastAsia) (pluralMarking := .optional)

end Korean
