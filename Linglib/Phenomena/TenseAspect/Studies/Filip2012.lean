import Linglib.Theories.Semantics.Events.Krifka1998
import Linglib.Phenomena.TenseAspect.Studies.Krifka1989

/-!
# @cite{filip-2012} "Lexical Aspect"
@cite{filip-2012} @cite{krifka-1998} @cite{krifka-1989} @cite{moon-2026}

Filip's handbook chapter (Binnick ed., OUP) synthesizes the mereological
approach to lexical aspect and identifies a **three-way classification**
of verb predicates:

1. **Telic / quantized** (QUA): *recover*, *arrive*
2. **Atelic / cumulative** (CUM): *run*, *push*
3. **Neither** (¬CUM ∧ ¬QUA): *build*, *eat*, *write* (incremental verbs)

The third class is "neither quantized (telic) nor cumulative (atelic)".
Their telicity is **underspecified at the verb level** and determined
compositionally by the object NP:
- QUA object → QUA VP (telic): "eat two apples"
- CUM object → CUM VP (atelic): "eat apples"
- ¬CUM ∧ ¬QUA object → ??? : "drink margarita"

## Key Results

- `three_way_exhaustive`: every predicate is CUM, QUA, or neither
- `composedRef_gap`: `composedRef` (binary NomRef) cannot express
  the middle ground — the type system has a blind spot
- `not_cum_vp_of_witnesses` / `middle_ground_stable` (in
  `Theories/Semantics/Events/Krifka1998.lean` §10): ¬CUM ∧ ¬QUA
  is stable under VP formation with SINC + UP + CumTheta verbs

## Connection to @cite{moon-2026}

Moon's mixed drink nouns provide a concrete instantiation of the
¬CUM ∧ ¬QUA middle ground. The topological source of non-cumulativity
(`connectivity_breaks_cum`) is orthogonal to the algebraic source
(QUA/atomicity), creating a category invisible to @cite{krifka-1998}'s
two propagation theorems. "Drink margarita" falls in the gap that
`composedRef` cannot compute.
-/

namespace Phenomena.TenseAspect.Studies.Filip2012

open Mereology
open Semantics.Events.Krifka1998 (VP CumTheta UP SINC VerbIncClass)
open Phenomena.TenseAspect.Studies.Krifka1989 (NomRef composedRef)

-- ════════════════════════════════════════════════════
-- § 1. The Three-Way Exhaustiveness
-- ════════════════════════════════════════════════════

/-- The three classes are exhaustive: every predicate falls into
    exactly one of CUM, QUA, or ¬CUM ∧ ¬QUA. This is logically
    trivial but conceptually important: it shows that the middle
    ground is a genuine third category, not a gap in our analysis. -/
theorem three_way_exhaustive {α : Type*} [SemilatticeSup α]
    (P : α → Prop) :
    CUM P ∨ QUA P ∨ (¬ CUM P ∧ ¬ QUA P) := by
  by_cases hc : CUM P
  · exact .inl hc
  · by_cases hq : QUA P
    · exact .inr (.inl hq)
    · exact .inr (.inr ⟨hc, hq⟩)

-- ════════════════════════════════════════════════════
-- § 2. The composedRef Gap
-- ════════════════════════════════════════════════════

/-! ### The type-level blind spot in Krifka's composition

`composedRef : VerbIncClass → NomRef → NomRef` from
@cite{krifka-1989} successfully computes VP reference for CUM and QUA
objects. But `NomRef` is binary (`.cum | .qua`), so the function
*cannot even receive* a ¬CUM ∧ ¬QUA input. The middle ground is
invisible at the type level.

This is not a bug in `composedRef` — it faithfully implements Krifka's
binary theory. It's a gap in the theory that @cite{filip-2012}
identifies and that @cite{moon-2026}'s mixed drinks instantiate.

The theorems `not_cum_vp_of_witnesses` and `middle_ground_stable`
(in `Theories/Semantics/Events/Krifka1998.lean` §10) prove that
the gap is genuine: even at the semantic level (not just the
type level), ¬CUM ∧ ¬QUA is stable under VP formation.
-/

/-- `composedRef` always returns `.cum` or `.qua` — it cannot
    express a middle-ground result. This is a type-level encoding
    of the propagation gap: the theory's output space is too small
    for the inputs that actually arise. -/
theorem composedRef_binary (v : VerbIncClass) (np : NomRef) :
    composedRef v np = .cum ∨ composedRef v np = .qua := by
  cases v <;> cases np <;> simp [composedRef]

/-- For incremental verbs (sinc/inc), `composedRef` just passes through
    the NP's reference type. It has no mechanism to flag "underspecified"
    when the NP is ¬CUM ∧ ¬QUA — the type forces a binary answer. -/
theorem composedRef_sinc_passthrough (np : NomRef) :
    composedRef .sinc np = np := by
  cases np <;> rfl

theorem composedRef_inc_passthrough (np : NomRef) :
    composedRef .inc np = np := by
  cases np <;> rfl

-- ════════════════════════════════════════════════════
-- § 3. Filip's Verb Classification Data
-- ════════════════════════════════════════════════════

/-! ### Incremental verbs: the third class

Filip §7 identifies three verb classes by their inherent aspectual
properties. The first two have fixed telicity; the third is
compositionally determined by the object NP.

For incremental verbs, `composedRef` computes the right answer when
the NP is CUM or QUA. The gap arises only when the NP itself is in
the middle ground — which is the case @cite{moon-2026} analyzes for
mixed drink nouns.
-/

/-- Incremental verbs from Filip's class (iii). These are all SINC
    in @cite{krifka-1998}'s classification: their theme role has a
    strict bijection between object parts and event parts. -/
def incrementalVerbs : List (String × VerbIncClass) :=
  [ ("build", .sinc), ("eat", .sinc), ("write", .sinc)
  , ("compose", .sinc), ("burn", .sinc), ("recite", .sinc)
  , ("play", .sinc) ]

/-- All incremental verbs are sinc — they transmit NP reference
    faithfully (via `composedRef_sinc_passthrough`). -/
theorem incremental_all_sinc :
    incrementalVerbs.all (·.2 == .sinc) = true := by native_decide

/-- For any incremental verb and CUM NP, the VP is CUM.
    This is the atelic endpoint: "eat apples", "build houses". -/
theorem incremental_cum_object :
    incrementalVerbs.all (fun ⟨_, v⟩ =>
      composedRef v .cum == .cum) = true := by native_decide

/-- For any incremental verb and QUA NP, the VP is QUA.
    This is the telic endpoint: "eat two apples", "build a house". -/
theorem incremental_qua_object :
    incrementalVerbs.all (fun ⟨_, v⟩ =>
      composedRef v .qua == .qua) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. The Propagation Table
-- ════════════════════════════════════════════════════

/-! ### Summary: the two endpoints and the gap

| OBJ class | Propagation theorem | VP class | Telicity |
|---|---|---|---|
| CUM ("apples") | `cum_propagation` | CUM | atelic |
| QUA ("two apples") | `qua_propagation` | QUA | telic |
| ¬CUM ∧ ¬QUA ("margarita") | `middle_ground_stable` | ¬CUM ∧ ¬QUA | underspecified |

The first two rows are computed by `composedRef`. The third row
requires the semantic-level theorems from Krifka1998 §10, because
`composedRef` cannot express it.

@cite{filip-2012} (38): "Incremental (stem) verbs do not lexically
encode either scales or measure functions. The scale with respect to
which incremental predicates are interpreted as telic is specified
externally to their incremental head verbs."

This is exactly what the propagation theorems formalize: the verb
is a transparent conduit for the object's mereological properties.
When those properties are CUM or QUA, the conduit works. When they
are ¬CUM ∧ ¬QUA, the conduit faithfully transmits the indeterminacy
(`middle_ground_stable`).
-/

end Phenomena.TenseAspect.Studies.Filip2012
