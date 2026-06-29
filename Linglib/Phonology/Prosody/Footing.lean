import Linglib.Phonology.Prosody.Foot

/-!
# Footings
[lamont-2022c] [kager-2007]

A **footing**: a flat parse of a syllable string into feet and stray (unfooted)
syllables — the metrical parse, with no designated head ([lamont-2022c]). It is the
canonical, headed-`Foot`-based replacement for the old weight-list `MetricalParse`:
each foot is a `Prosody.Foot` (so headedness/binarity come from `Foot.head`), and an
unfooted σ is a bare `S`.

The footing is the more primitive object in the prosodic hierarchy; the headed prosodic
word ω (`Prosody.Word`) is a footing *enriched with a head foot* (its `Word.daughters`
is the underlying footing). Quantity-sensitivity is a property of the σ-type `S`: a
quantity-insensitive footing uses `S = Unit` ([lamont-2022c]), a weight-sensitive one
`S = Syllable.Weight`.

## Main definitions

* `Footing` — a flat sequence of feet and stray syllables, `List (Foot S ⊕ S)`.
* `Footing.feet` / `strays` / `size` — the feet, the unfooted σ, the total σ count.
* `Footing.strayMarks` — the per-position unfooted-σ vector (the `Parse(σ)` profile).
-/

namespace Prosody

/-- A footing: a flat sequence of feet (`Foot S`) and stray (unfooted) syllables (`S`),
    in linear order, with zero-or-more feet and no designated head ([lamont-2022c]). -/
abbrev Footing (S : Type*) := List (Foot S ⊕ S)

namespace Footing
variable {S : Type*}

/-- The feet, left to right. -/
def feet (fc : Footing S) : List (Foot S) := fc.filterMap Sum.getLeft?

/-- The stray (unfooted) syllables, left to right. -/
def strays (fc : Footing S) : List S := fc.filterMap Sum.getRight?

/-- The total number of syllables (footed + stray). -/
def size (fc : Footing S) : Nat :=
  (fc.map (fun d => match d with | .inl f => f.syllables.length | .inr _ => 1)).sum

/-- The per-position unfooted-σ vector: `1` at each stray σ, `0` at each footed σ,
    left to right. This is the directional `Parse(σ)` violation profile
    ([lamont-2022c]). -/
def strayMarks (fc : Footing S) : List Nat :=
  fc.flatMap (fun d => match d with
    | .inl f => List.replicate f.syllables.length 0
    | .inr _ => [1])

end Footing

end Prosody
