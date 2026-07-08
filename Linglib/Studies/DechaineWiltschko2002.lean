import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Déchaine & Wiltschko 2002: Decomposing Pronouns
[dechaine-wiltschko-2002]

"The notion 'pronoun' is not a primitive of linguistic theory." Pronouns
decompose into three categories by internal constituent **size** —
`proDP ⊃ prophiP ⊃ proNP` — and that size *determines* distribution, semantics,
and binding-theoretic status ([dechaine-wiltschko-2002] table (24)):

| category | internal syntax | distribution | semantics | binding |
|----------|-----------------|--------------|-----------|---------|
| pro-DP   | D; morph. complex | argument   | definite  | R-expression (Cond C) |
| pro-φP   | neither D nor N | arg or pred  | —         | variable (Cond B) |
| pro-NP   | N               | predicate    | constant  | — (inherent semantics) |

This categorial axis **cross-cuts** Cardinaletti & Starke's deficiency
hierarchy (`Pronoun.Strength`, [cardinaletti-starke-1999]): see
`strength_category_independent`. It is the structural rival to the deficiency
view that `Pronoun.Strength`'s docstring flags as orthogonal.

## Main declarations

* `Category` — pro-DP / pro-φP / pro-NP, with `hasDLayer`/`hasPhiLayer` recording
  size.
* `Category.bindingStatus` — *derived from size*, not stipulated: D&W's claim
  that the D layer yields a Condition-C R-expression, a φP-top yields a
  Condition-B variable, and a bare NP is binding-unconstrained.
* `strength_category_independent` — the C&S `Strength` and D&W `Category` axes
  are functionally independent (neither determines the other), with English
  witnesses from [dechaine-wiltschko-2002] §3.2.

## Implementation notes

The φP layer is the locus of the person/number/gender φ-features modelled in
`UD.Person` etc.; `hasPhiLayer` marks which categories project it. A full
federation of the φ-internal geometry to `UD.Person` is left to follow-up.
-/

namespace DechaineWiltschko2002

open Pronoun (Strength)

/-- [dechaine-wiltschko-2002]'s three pronoun categories, by internal
    constituent size: a full DP (`[DP D [φP φ [NP N]]]`), a φP (`[φP φ [NP N]]`),
    or a bare NP (`[NP N]`). -/
inductive Category where
  | proDP
  | prophiP
  | proNP
  deriving DecidableEq, Repr

/-- Whether the category projects a D layer (definiteness / R-expression locus). -/
def Category.hasDLayer : Category → Bool
  | .proDP => true
  | .prophiP => false
  | .proNP => false

/-- Whether the category projects a φP layer — the locus of the person/number/
    gender φ-features (cf. `UD.Person`). A bare `proNP` has none. -/
def Category.hasPhiLayer : Category → Bool
  | .proDP => true
  | .prophiP => true
  | .proNP => false

/-- Binding-theoretic status ([dechaine-wiltschko-2002] table (24)). -/
inductive BindingStatus where
  /-- Subject to Condition C (a referring expression). -/
  | rExpression
  /-- Subject to Condition B (can be a bound variable). -/
  | boundVariable
  /-- Undefined for binding theory; behaviour follows from inherent semantics. -/
  | unconstrained
  deriving DecidableEq, Repr

/-- External distribution ([dechaine-wiltschko-2002] (24)–(25)). -/
inductive Distribution where
  | argument
  | predicate
  | either
  deriving DecidableEq, Repr

/-- Inherent semantics ([dechaine-wiltschko-2002] (24)). -/
inductive Sem where
  | definite
  | const
  | underspecified
  deriving DecidableEq, Repr

/-- D&W's central thesis: binding status is **determined by size**. A D layer
    makes the proform an R-expression (Condition C); a φP top (φ-features but no
    D) makes it a bound variable (Condition B); a bare NP is unconstrained by
    binding theory. Derived from `hasDLayer`/`hasPhiLayer`, not stipulated. -/
def Category.bindingStatus (c : Category) : BindingStatus :=
  if c.hasDLayer then .rExpression
  else if c.hasPhiLayer then .boundVariable
  else .unconstrained

/-- Distribution: DPs are arguments, NPs are predicates, φPs are type-flexible
    ([dechaine-wiltschko-2002] (25): `DP → Argument`, `NP → Predicate`). -/
def Category.distribution : Category → Distribution
  | .proDP => .argument
  | .prophiP => .either
  | .proNP => .predicate

/-- Inherent semantics: definite (DP), constant (NP), or unspecified (φP). -/
def Category.semantics : Category → Sem
  | .proDP => .definite
  | .prophiP => .underspecified
  | .proNP => .const

/-! ### The size → binding-status entailment -/

/-- A proform is an R-expression (Condition C) iff it has a D layer. -/
theorem rExpression_iff_hasDLayer (c : Category) :
    c.bindingStatus = .rExpression ↔ c.hasDLayer = true := by
  cases c <;> decide

/-- A proform is a bound variable (Condition B) iff it has φ-features but no D. -/
theorem boundVariable_iff_phi_without_D (c : Category) :
    c.bindingStatus = .boundVariable ↔ (c.hasPhiLayer = true ∧ c.hasDLayer = false) := by
  cases c <;> decide

/-- The three categories yield three distinct binding statuses — the typology is
    non-degenerate. -/
theorem binding_statuses_distinct :
    Category.proDP.bindingStatus ≠ Category.prophiP.bindingStatus ∧
    Category.prophiP.bindingStatus ≠ Category.proNP.bindingStatus ∧
    Category.proDP.bindingStatus ≠ Category.proNP.bindingStatus := by decide

/-! ### Case studies ([dechaine-wiltschko-2002] table (24))

Each language's independent/personal proform instantiates a different category:
Halkomelem independent pronouns = pro-DP (R-expressions, Condition C); Shuswap
independent pronouns = pro-φP (bound variables, Condition B); Japanese *kare* =
pro-NP (a constant, binding-unconstrained). -/

theorem halkomelem_proDP_rExpression :
    Category.proDP.bindingStatus = .rExpression := rfl

theorem shuswap_prophiP_boundVariable :
    Category.prophiP.bindingStatus = .boundVariable := rfl

theorem japanese_kare_proNP_unconstrained :
    Category.proNP.bindingStatus = .unconstrained := rfl

/-! ### Orthogonality to Cardinaletti & Starke deficiency

[dechaine-wiltschko-2002] §3.2 analyses English personal pronouns as
pro-DP (1st/2nd person — they can be determiners: *we/us linguists*) and pro-φP
(3rd person — *\*they linguists*), and *one* as pro-NP. Cross-classifying those
categories with [cardinaletti-starke-1999] deficiency (`Pronoun.Strength`:
full *we/they* are strong, enclitic *'em* is a clitic) shows the two axes are
independent — neither determines the other. -/

/-- A pronoun cross-classified on both axes: D&W `Category` × C&S `Strength`. -/
structure Datum where
  form : String
  strength : Strength
  category : Category
  deriving Repr

/-- English inventory ([dechaine-wiltschko-2002] §3), each form tagged with
    its D&W category and its C&S strength. -/
def englishInventory : List Datum :=
  [ ⟨"we",   .strong, .proDP⟩    -- 1st person → pro-DP; full → strong
  , ⟨"you",  .strong, .proDP⟩    -- 2nd person → pro-DP
  , ⟨"they", .strong, .prophiP⟩  -- 3rd person → pro-φP; full → strong
  , ⟨"'em",  .clitic, .prophiP⟩  -- 3rd person → pro-φP; enclitic → clitic
  , ⟨"one",  .strong, .proNP⟩ ]  -- pro-NP

/-- `Strength` does not determine `Category`: *we* and *they* are both strong,
    yet *we* is pro-DP (1st person) and *they* is pro-φP (3rd person). -/
theorem category_not_determined_by_strength :
    ∃ p q : Datum, p.strength = q.strength ∧ p.category ≠ q.category :=
  ⟨⟨"we", .strong, .proDP⟩, ⟨"they", .strong, .prophiP⟩, rfl, by decide⟩

/-- `Category` does not determine `Strength`: *they* and *'em* are both pro-φP
    (3rd person), yet *they* is strong and *'em* is a clitic. -/
theorem strength_not_determined_by_category :
    ∃ p q : Datum, p.category = q.category ∧ p.strength ≠ q.strength :=
  ⟨⟨"they", .strong, .prophiP⟩, ⟨"'em", .clitic, .prophiP⟩, rfl, by decide⟩

/-- The Déchaine-Wiltschko categorial axis and the Cardinaletti-Starke deficiency
    axis are functionally independent — neither is a function of the other. This
    is the theorem behind `Pronoun.Strength`'s docstring claim of orthogonality. -/
theorem strength_category_independent :
    (∃ p q : Datum, p.strength = q.strength ∧ p.category ≠ q.category) ∧
    (∃ p q : Datum, p.category = q.category ∧ p.strength ≠ q.strength) :=
  ⟨category_not_determined_by_strength, strength_not_determined_by_category⟩

end DechaineWiltschko2002
