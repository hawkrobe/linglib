import Linglib.Phonology.Prosody.Mora

/-!
# Syllables

The syllable (σ) — the second level of the prosodic hierarchy, a non-moraic
onset over a spine of `Mora`s. Weight is the number of morae, so there is no
separate weight type: `Syllable.Weight` is just `Nat`, and `Syllable.weight`
reads it off `morae.length`.

## Main definitions

* `Syllable` — a `Mora`-spine syllable, with `Syllable.moraCount` / `weight`
  and the smart constructor `Syllable.ofCV` from a segmental string.
* `Syllable.Weight` — `Nat` (the mora count), with `.light`/`.heavy`/
  `.superheavy` for readable weight profiles.

Segment sonority is a segmental property, so it lives in `Phonology.Segment`
(`Sonority` and the finer `SonorityClass`), not here.
-/

namespace Prosody

open Phonology (Segment)

/-! ### Syllables -/

/-- σ — a syllable: a non-moraic onset over a spine of morae. Weight is the
    number of morae (`moraCount`). -/
structure Syllable where
  onset : List Segment
  morae : List Mora

namespace Syllable

/-- Syllable weight is just the mora count — there is no separate weight type.
    `.light` (1μ), `.heavy` (2μ), `.superheavy` (3μ) name the common values for
    readable weight profiles in metrical and accentual computations. -/
abbrev Weight := Nat

namespace Weight
abbrev light : Weight := 1
abbrev heavy : Weight := 2
abbrev superheavy : Weight := 3
end Weight

/-- The number of morae — the syllable's weight. -/
def moraCount (σ : Syllable) : Nat := σ.morae.length

/-- The syllable's weight (= its mora count). -/
abbrev weight (σ : Syllable) : Weight := σ.moraCount

/-- Build a syllable from a segmental onset–nucleus–coda string. Each nucleus
    segment projects a mora; a coda segment projects a mora iff Weight-by-
    Position is active ([hayes-1989]), otherwise it rides on the last nucleus
    mora (a non-moraic coda). -/
def ofCV (onset nucleus coda : List Segment) (wbp : Bool := true) : Syllable :=
  let nuc := nucleus.map Mora.of
  if wbp then
    ⟨onset, nuc ++ coda.map Mora.of⟩
  else
    match nuc.reverse with
    | last :: rest => ⟨onset, rest.reverse ++ [last.attach coda]⟩
    | []           => ⟨onset, []⟩

end Syllable

end Prosody
