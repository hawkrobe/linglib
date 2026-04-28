import Linglib.Typology.Color

/-!
# Mandarin color profile (WALS Chs 132–135)
@cite{wals-2013}
-/

namespace Fragments.Mandarin

/-- Mandarin Chinese: 6 non-derived basic colors, 8–8.5 total basic colors;
    green (*lü*) vs blue (*lan*) distinct; red (*hong*) vs yellow (*huang*)
    distinct. -/
def colorProfile : Typology.ColorProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , family := "Sino-Tibetan"
  , nonDerived := some .six
  , basic := some .v8to8h
  , greenBlue := some .distinct
  , redYellow := some .distinct }

end Fragments.Mandarin
