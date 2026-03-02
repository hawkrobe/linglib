import Lean

/-!
# @[ont_sort] — Natural Language Ontological Sort Marker
@cite{liefke-2024}

Marks a type definition as a natural language ontological category. Tagged types are the posits of semantic theory —
individuals, events, propositions, degrees, etc. — as opposed to
implementation scaffolding.

Ontological commitments of a definition emerge from which
`@[ont_sort]`-tagged types appear in its signature.

-/

namespace Linglib.Tactics

open Lean

initialize ontSortAttr : TagAttribute ←
  registerTagAttribute `ont_sort
    "Natural language ontological sort (Liefke 2024)"

end Linglib.Tactics
