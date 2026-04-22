/-!
# Cross-linguistic conditional markers

@cite{cao-white-lassiter-2025} @cite{mizuno-2024}

Typological vocabulary for conditional markers across languages.
Some languages have distinct lexical items for hypothetical (HC) vs
premise (PC) conditionals; others use a single marker for both. This
file provides the marker-type inductive and the per-marker structure;
per-language marker entries live in `Fragments/{Language}/Conditionals.lean`.

Extracted from `Conditionals/ConditionalType.lean` (was lines 372–396).
-/

namespace Semantics.Conditionals

/-- Cross-linguistic conditional markers and their type restrictions.

Some languages have distinct lexical items for HC vs PC conditionals.
This captures the typological pattern.

Note: `pcOnly` is currently uninstantiated across known languages;
included for typological completeness. -/
inductive ConditionalMarkerType where
  /-- Only marks HCs (e.g., Japanese -ra, German falls). -/
  | hcOnly
  /-- Only marks PCs (currently uninstantiated). -/
  | pcOnly
  /-- Can mark either (e.g., English "if", German wenn). -/
  | both
  deriving DecidableEq, Repr

/-- Cross-linguistic conditional marker datum.

Per-language marker entries live in
`Fragments/{Language}/Conditionals.lean`. -/
structure ConditionalMarker where
  language : String
  marker : String
  gloss : String
  markerType : ConditionalMarkerType
  notes : String
  deriving Repr

end Semantics.Conditionals
