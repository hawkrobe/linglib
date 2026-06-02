import Linglib.Typology.Color

/-!
# Japanese color profile (WALS Chs 132–135)
@cite{wals-2013}
-/

namespace Japanese

/-- Japanese: 6 non-derived basic colors, 11 total basic colors; green
    (*midori*) vs blue (*ao*) distinct in modern Japanese (though *ao*
    historically covered both — the classic Japanese green-blue case in
    the linguistic-relativity literature); red (*aka*) vs yellow (*kiiro*)
    distinct.
    Derived from the WALS Chs 132–135 rows for `jpn`. -/
def colorProfile : Typology.ColorProfile :=
  Typology.ColorProfile.fromWALS "Japanese" "jpn" "Japonic"

end Japanese
