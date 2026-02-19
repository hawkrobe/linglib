import Lean

/-!
# @[ont_sort] — Natural Language Ontological Sort Marker

Marks a type definition as a natural language ontological category
(Liefke 2024). Tagged types are the posits of semantic theory —
individuals, events, propositions, degrees, etc. — as opposed to
implementation scaffolding.

Ontological commitments of a definition emerge from which
`@[ont_sort]`-tagged types appear in its signature.

## Reference

- Liefke, K. (2024). Natural Language Ontology and Semantic Theory.
  Cambridge Elements in Semantics.
-/

namespace Linglib.Tactics

open Lean

initialize ontSortAttr : TagAttribute ←
  registerTagAttribute `ont_sort
    "Natural language ontological sort (Liefke 2024)"

end Linglib.Tactics
