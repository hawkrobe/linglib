/-!
# Expressive
[potts-2007] [kubota-2026]

Theory-neutral per-entry tag for **use-conditional / secondary-meaning** lexemes — the
expressive dimension of [potts-2007]. Fragments attach an `Expressive` value to mark a
lexeme as expressive and record which construction class it belongs to; theories then assign
it a denotation (`Pragmatics.Expressives.TwoDimProp`, an outlook-indexed meaning,
use-conditional types, …) and are judged on whether they predict its diagnostic behavior.

This is **object-level data** (like `Features.Person`): a tag, not
a denotation. It is `Prop`-free and depends on no theory layer, so Fragments may import it
without pulling in any account of conventional implicature. The diagnostic *fingerprint*
(`Pragmatics.Expressives.SecondaryMeaningProperties`) and the denotations live one layer up.
-/

namespace Features

/-- Construction class of a use-conditional / expressive lexeme ([potts-2007],
[kubota-2026]). The coarse, theory-neutral typology Fragments mark entries with. -/
inductive Expressive where
  /-- Epithets, slurs, and expressive adjectives — speaker-oriented affective content
      ("that bastard", "damn") ([potts-2007]). -/
  | epithet
  /-- Addressee- or referent-honorifics. -/
  | honorific
  /-- Appositives and non-restrictive modifiers — Potts's *supplements*. -/
  | supplement
  /-- Discourse-sensitive evaluative particles / outlook markers ([kubota-2026]). -/
  | outlookMarker
  deriving DecidableEq, Repr, Inhabited

end Features
