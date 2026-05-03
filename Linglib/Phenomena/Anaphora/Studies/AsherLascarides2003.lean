import Linglib.Theories.Discourse.SDRT.Defs
import Linglib.Theories.Discourse.SDRT.RightFrontier

/-!
# Asher & Lascarides 2003: SDRT Right Frontier Constraint worked example

@cite{asher-lascarides-2003}

Example (21) from p. 149 — the discourse where the book explicitly
enumerates which attachment sites are available under the Right
Frontier Constraint, and which are excluded. We replicate it
against the SDRT substrate to verify that
`availableAttachmentPoints` returns exactly the book-predicted set.

## The example (21), p. 149

```
π₀:
  ├─ π₃, π₄
  │  ├─ π₃: K_π₃
  │  ├─ ⇓(π₃, π₄)              ← subordinating topic relation
  │  └─ π₄:
  │     ├─ π₁, π₂
  │     ├─ π₁: K_π₁
  │     ├─ π₂: K_π₂
  │     └─ Background(π₁, π₂)   ← coordinating
```

Reading the labelling F:
* F(π₀) ⊇ ⇓(π₃, π₄) — the topic relation lives at the top level
* F(π₄) ⊇ Background(π₁, π₂) — the coordinated pair lives inside π₄
* F(π₁), F(π₂), F(π₃) are atomic clausal contents K_πᵢ

## What the book asserts (p. 149)

> "assuming that π₂ in (21) is LAST, the available attachment sites
>  are π₂ (by condition 1), π₄ (by condition 2a), π₃ (by condition
>  2b and 3) and π₀ (by condition 3). But π₁ is *not* available."

## Why π₁ is not available

π₁ and π₂ are siblings under `Background`, which is **coordinating**
(not subordinating). After attaching to π₂ (LAST), the only way to
reach π₁ would be through a subordinating relation — but
`Background` doesn't qualify. Walking up via outscoping reaches π₄
(which contains both π₁ and π₂), and from π₄ we reach π₃ via the
subordinating ⇓ relation. But π₁ is on the wrong side of a
coordinating sibling boundary.

## Substrate note

@cite{asher-lascarides-2003}'s ⇓ topic-relation is not in the
substrate's `RhetoricalRelation` enum (it's a structural relation
the book uses informally; the headline truth-conditional inventory
is Narration / Elaboration / Explanation / Result / Background /
Contrast / Parallel + Consequence / Alternation / Correction). We
encode ⇓ as `.elaboration` in the example below — both are
subordinating, and the RFC's condition 2b only sees the
`isSubordinating` projection. The example would behave identically
with a hypothetical `.topic` constructor.
-/

namespace Phenomena.Anaphora.Studies.AsherLascarides2003

open Discourse.SDRT

-- ════════════════════════════════════════════════════════════════
-- § 1. The Example (21) SDRS
-- ════════════════════════════════════════════════════════════════

abbrev Label := Nat
abbrev Content := String

/-- Example (21) from @cite{asher-lascarides-2003} p. 149, with
    LAST = π₂.

    Labels: 0 = π₀, 1 = π₁, 2 = π₂, 3 = π₃, 4 = π₄.

    Edges encode the labelled-discourse-structure conjuncts:
    * `⟨0, 3, 4, .elaboration⟩` represents `⇓(π₃, π₄) ∈ F(π₀)`
      (using `.elaboration` as a stand-in for ⇓; both subordinating).
    * `⟨4, 1, 2, .background⟩` represents `Background(π₁, π₂) ∈ F(π₄)`.

    Plus container-marking edges so that iOutscopes recovers the
    box-containment structure:
    * π₀ contains π₃ and π₄
    * π₄ contains π₁ and π₂

    These containment relations are conjuncts in the parent box's
    F-content (the book's "labels A and labelling F" representation
    — being a label inside a box IS a content fact about the parent).
    We encode them as additional outscoping conjuncts using the
    same edge structure.

    For Example (21) specifically, the ⇓(π₃, π₄) and
    Background(π₁, π₂) edges already encode the containment
    (since these relations have π₃, π₄, π₁, π₂ as arguments and
    the relations themselves live in F(π₀) and F(π₄)
    respectively). No additional outscoping edges needed. -/
def example21 : SDRS Label Content where
  labels := [0, 1, 2, 3, 4]
  content
    | 0 => "π₀ (root)"
    | 1 => "K_π₁"
    | 2 => "K_π₂"
    | 3 => "K_π₃"
    | 4 => "(complex constituent containing π₁, π₂)"
    | _ => "<unknown>"
  edges := [
    ⟨0, 3, 4, .elaboration⟩,   -- ⇓(π₃, π₄) ∈ F(π₀); ⇓ acts as subordinating
    ⟨4, 1, 2, .background⟩     -- Background(π₁, π₂) ∈ F(π₄); coordinating
  ]
  root := 0
  last := 2

-- ════════════════════════════════════════════════════════════════
-- § 2. RFC verification — book p. 149's predicted set
-- ════════════════════════════════════════════════════════════════

/-- π₂ (LAST) is itself available, by condition 1 of Def 14. -/
example : availableViaChain example21 example21.last 2 0 := rfl

/-- π₄ is available from π₂ via outscoping (condition 2a):
    `Background(π₁, π₂) ∈ F(π₄)` so iOutscopes(π₄, π₂) holds. -/
example : availableViaChain example21 2 4 1 := by decide

/-- π₃ is available from π₂ via condition 2b + 3 (transitive closure):
    π₂ → π₄ (outscoping) → π₃ (subordinating ⇓ encoded as .elaboration). -/
example : availableViaChain example21 2 3 2 := by decide

/-- π₀ is available from π₂ via condition 3 (transitive closure):
    π₂ → π₄ (outscoping) → π₀ (outscoping ⇓ which contains π₄). -/
example : availableViaChain example21 2 0 2 := by decide

-- ════════════════════════════════════════════════════════════════
-- § 3. The headline negative result: π₁ is NOT available
-- ════════════════════════════════════════════════════════════════

/-- **Book p. 149 headline claim**: π₁ is NOT in the available
    attachment set from π₂ (Example 21).

    The reason: π₁ and π₂ are siblings under `Background`, which is
    coordinating (not subordinating). RFC's condition 2b only opens
    up new attachment sites via subordinating relations, so the
    sibling-via-coordinating π₁ is unreachable from π₂'s right
    frontier. -/
theorem pi_1_not_available_from_pi_2 :
    1 ∉ availableAttachmentPoints example21 := by decide

/-- The full available set from π₂ matches the book's prediction:
    {π₀, π₂, π₃, π₄}. -/
theorem available_attachment_points_match :
    availableAttachmentPoints example21 = [0, 2, 3, 4] := by decide

end Phenomena.Anaphora.Studies.AsherLascarides2003
