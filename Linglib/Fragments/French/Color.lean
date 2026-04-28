import Linglib.Typology.Color

/-!
# French color profile (WALS Chs 132–135)
@cite{wals-2013}
-/

namespace Fragments.French

/-- French: 6 non-derived basic colors, 11 total basic colors; green (*vert*)
    vs blue (*bleu*) distinct; red vs yellow distinct. -/
def colorProfile : Typology.ColorProfile :=
  { language := "French"
  , iso := "fra"
  , family := "Indo-European"
  , nonDerived := some .six
  , basic := some .v11
  , greenBlue := some .distinct
  , redYellow := some .distinct }

end Fragments.French
