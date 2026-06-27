import Linglib.Phonology.Prosody.Syllable

/-!
# Prosodic word (ω)
[selkirk-1984] [mccarthy-prince-1993]

The prosodic word ω, the constituent above the foot in the prosodic hierarchy
(σ < f < ω < φ < ι; the levels themselves live in `Features.Prosody`). This
module gives ω's weight profile and the minimal-word constraint. The foot-parsed
ω is `MetricalParse` (`Phonology/Prosody/Foot.lean`); the morphosyntax→prosody
mapping that fixes ω boundaries is language-specific (Telugu: `Studies/Aitha2026.lean`).

## Main definitions

* `Prosody.Word`: a prosodic word as a linear weight profile.
* `Prosody.Word.ofSyllables`: the σ → ω bridge (weight profile of a syllable list).
* `Prosody.Word.moraCount`: total mora count.
* `Prosody.Word.satisfiesMinWord`: the minimal-word constraint.
-/

namespace Prosody

/-- A prosodic word ω: a sequence of syllables by weight, forming a single
    domain for stress and word-level phonology. E.g. Telugu *samudram* 'ocean'
    has profile `[.light, .light, .heavy]` (sa.mu.dram). -/
structure Word where
  syllables : List Syllable.Weight
  deriving DecidableEq, Repr

/-- The weight profile of fully-moraified syllables — the σ → ω bridge. -/
def Word.ofSyllables (σs : List Syllable) : Word := ⟨σs.map Syllable.weight⟩

/-- Total mora count of a prosodic word (each weight *is* a mora count). -/
def Word.moraCount (w : Word) : Nat :=
  w.syllables.foldl (· + ·) 0

/-- The minimal-word constraint ([mccarthy-prince-1993]): the smallest ω must
    contain a foot — at least two morae for moraic-trochee languages (the
    default). Syllabic-trochee minima are syllable-counted, not captured by the
    default. -/
abbrev Word.satisfiesMinWord (w : Word) (minMorae : Nat := 2) : Prop :=
  w.moraCount ≥ minMorae

end Prosody
