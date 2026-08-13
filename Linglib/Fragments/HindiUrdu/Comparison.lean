import Linglib.Syntax.Comparative

/-!
# Hindi-Urdu comparative data

Hindi-Urdu marks the standard of comparison with the ablative postposition *se*
'from' (WALS Ch 121A: locational, [stassen-2013]); the free degree word
*zyaadaa* 'more' is optional. Superlative via comparative with a universal
standard (*sab se* 'than all').
-/

set_option autoImplicit false

namespace HindiUrdu.Comparison

open Comparative

/-- Optional free degree word *zyaadaa*. -/
def degreeWord : DegreeWordType := .hasDegreeWord

/-- Superlative as comparative with universal standard (*sab se*). -/
def superlative : SuperlativeStrategy := .comparativeUniversal

/-- Illustrative comparative. -/
def comparativeForm : String := "X Y se (zyaadaa) Adj hai"

/-- The ablative standard marker. -/
def standardMarker : String := "se"

/-- The free degree word. -/
def degreeMarker : String := "zyaadaa"

end HindiUrdu.Comparison
