import Linglib.Features.Coordination
import Linglib.Fragments.Japanese.Determiners

/-!
# Japanese Coordination Morphemes
@cite{mitrovic-sauerland-2016} @cite{haspelmath-2007}

Japanese makes the Boolean algebra foundation of coordination
morphologically transparent. Two particles systematically mark
meet (∧) and join (∨) operations across three phenomena:

| Particle | Coordination | Quantification | Focus |
|----------|-------------|----------------|-------|
| も (mo) | MU conjunction | universal (dare-mo) | additive (also) |
| か (ka) | disjunction | existential (dare-ka) | interrogative |

This is Boolean duality on the surface: "mo" marks finite meets,
"ka" marks finite joins. The same algebraic structure that makes
conjunction = universal quantification = additive checking (all
are ∧ over elements) also makes disjunction = existential
quantification = interrogative (all are ∨ over elements).

## Entries

- *to* (と) — J, bound, postpositive: "A to B". Also comitative ("with"),
  making Japanese a WITH-language in @cite{stassen-2000}'s classification
  (WALS Ch 63: `andIdenticalToWith`).
- *mo* (も) — MU, bound, postpositive: "A-mo B-mo". Also additive particle
  ("A-mo" = "A too") and universal quantifier component ("dare-mo" =
  "everyone"). The triple role is the morphological proof that MU,
  additive focus, and universal quantification are the same operation:
  finite ∧ in Boolean algebra. See `mu_is_distributive_check` in
  BillEtAl2025.lean.
- *ka* (か) — disjunction, bound, postpositive: "A ka B". Also
  interrogative and existential quantifier component ("dare-ka" =
  "someone"). Boolean dual of "mo".

## Connections

- Typology.lean: `Phenomena.Coordination.Typology.japanese`
- Determiners.lean: `dare_mo.particle = some "mo"`, `dare_ka.particle = some "ka"`
- AdditiveParticles/Data.lean: `japaneseMo`
- BillEtAl2025.lean: `mu_is_distributive_check`
-/

namespace Fragments.Japanese.Coordination

open Features.Coordination

-- ============================================================================
-- Lexical entries
-- ============================================================================

/-- *to* (と) — J particle. Bound, postpositive on first conjunct.
    "Taroo to Hanako" = "Taro and Hanako".
    Also functions as comitative marker ("with"):
    "Taroo to iku" = "go with Taro".
    This dual function is WHY Japanese is classified as a WITH-language
    in WALS Ch 63 (`andIdenticalToWith`). -/
def to_ : CoordEntry :=
  { form := "to", gloss := "and; with"
  , role := .j, boundness := .bound }

/-- *mo* (も) — MU particle. Bound, postpositive on each conjunct.
    Conjunction: "Taroo-mo Hanako-mo neta" = "both Taro and Hanako slept".
    Additive: "Taroo-mo neta" = "Taro also slept".
    Universal quantifier: "dare-mo" = "everyone" (indeterminate + mo).
    This triple role is the morphological proof that conjunction MU,
    additive focus, and universal quantification are the same operation:
    finite meet (∧) in Boolean algebra. -/
def mo : CoordEntry :=
  { form := "mo", gloss := "also, too; and (MU); every"
  , role := .mu, boundness := .bound
  , alsoAdditive := true, alsoQuantifier := true }

/-- *ka* (か) — Disjunction particle. Bound, postpositive.
    Disjunction: "Taroo ka Hanako" = "Taro or Hanako".
    Interrogative: "Taroo ka?" = "Is it Taro?".
    Existential quantifier: "dare-ka" = "someone" (indeterminate + ka).
    Boolean dual of "mo": where "mo" marks finite meets (∧),
    "ka" marks finite joins (∨). -/
def ka : CoordEntry :=
  { form := "ka", gloss := "or; question; some"
  , role := .disj, boundness := .bound
  , alsoQuantifier := true }

def allEntries : List CoordEntry :=
  [to_, mo, ka]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All Japanese coordination particles are bound (postpositive). -/
theorem all_bound :
    allEntries.all (·.boundness == .bound) = true := by
  native_decide

/-- The MU particle "mo" also serves as an additive particle. -/
theorem mu_is_additive :
    (allEntries.filter (·.role == .mu)).all (·.alsoAdditive) = true := by
  native_decide

/-- The MU particle "mo" also serves as a quantifier particle. -/
theorem mu_is_quantifier :
    (allEntries.filter (·.role == .mu)).all (·.alsoQuantifier) = true := by
  native_decide

/-- The disjunction particle "ka" also serves as a quantifier particle. -/
theorem disj_is_quantifier :
    (allEntries.filter (·.role == .disj)).all (·.alsoQuantifier) = true := by
  native_decide

-- ============================================================================
-- Determiners Bridge: Coordination ↔ Quantification
-- ============================================================================

/-!
## Boolean Duality

Japanese makes the algebraic duality between ∧ and ∨ morphologically
transparent:

- "mo" (∧ family): conjunction MU + universal quantifier + additive
- "ka" (∨ family): disjunction + existential quantifier + interrogative

The Determiners fragment independently records this: `dare_mo` (everyone)
has `particle := some "mo"`, `dare_ka` (someone) has `particle := some "ka"`.
The theorems below verify that the coordination particles and the
quantifier particles are the same morphemes.
-/

/-- The coordination "mo" (MU) is the same morpheme as the universal
    quantifier particle "mo" in dare-mo / dono-N-mo.
    The coordination "ka" (disjunction) is the same morpheme as the
    existential quantifier particle "ka" in dare-ka / nan-nin-ka. -/
theorem mo_ka_quantifier_bridge :
    -- Coordination: mo is MU, ka is disjunction
    mo.role = .mu ∧ ka.role = .disj ∧
    -- Determiners: mo-particle is universal, ka-particle is existential
    Fragments.Japanese.Determiners.dare_mo.particle = some "mo" ∧
    Fragments.Japanese.Determiners.dare_ka.particle = some "ka" ∧
    -- The coordination forms match the quantifier particles
    mo.form = "mo" ∧ ka.form = "ka" := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- "mo" marks ∧-operations (universal quantifiers), "ka" marks
    ∨-operations (existential quantifiers) — Boolean duality
    realized in the quantifier system.

    Every quantifier in the Japanese fragment built with particle "mo"
    is universal; every quantifier built with particle "ka" is
    existential. This is not a coincidence — it reflects the fact that
    ∧ (mo) and ∨ (ka) are the two operations of Boolean algebra. -/
theorem boolean_duality_in_quantifiers :
    -- All mo-particle quantifiers are universal (∧ family)
    (Fragments.Japanese.Determiners.allQuantifiers.filter
      (·.particle == some "mo")).all (·.qforce == .universal) = true ∧
    -- All ka-particle quantifiers are existential (∨ family)
    (Fragments.Japanese.Determiners.allQuantifiers.filter
      (·.particle == some "ka")).all (·.qforce == .existential) = true := by
  exact ⟨by native_decide, by native_decide⟩

end Fragments.Japanese.Coordination
