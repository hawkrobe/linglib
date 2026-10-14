module

public import Linglib.Syntax.Negation

/-!
# Tunica negation

Tunica negates an active verb with a suffix on its semelfactive form, *-aha* in the negative of
the semelfactive and *-kʔaha* in the negative of the habitual: *lɔ'ta-wi* 'he ran' has the
negative *lɔ'ta-w-ɛhɛ* 'he did not run', and the habitual *lɔ'ta-ku* 'he runs' has the negative
*lɔ'ta-wi-kʔaha* 'he does not run', built on the semelfactive *lɔ'ta-wi*. The examples are
Miestamo's, from Haas's grammar.

## Implementation notes

The semelfactive suffix is cited as *-wi* and the semelfactive negative as *-aha* in both members
of a pair, as Miestamo cites them; the loss of *i* and the vowels of *-ɛhɛ* are
phonological.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation Morphology

namespace Tunica.Negation

/-- *-aha*, the negative suffix of the semelfactive. -/
def aha : Marker := ⟨[[.suff "aha"]]⟩

/-- *-kʔaha*, the negative suffix of the habitual. -/
def kaha : Marker := ⟨[[.suff "kʔaha"]]⟩

/-- The semelfactive and the habitual of *lɔ'ta* 'run', third person singular masculine, with
their negatives. -/
def run : List Pair :=
  [⟨aha, [.root "lɔ'ta", .suff "wi"], [.root "lɔ'ta", .suff "wi", .suff "aha"]⟩,
   ⟨kaha, [.root "lɔ'ta", .suff "ku"], [.root "lɔ'ta", .suff "wi", .suff "kʔaha"]⟩]

end Tunica.Negation
