import Linglib.Theories.Semantics.Exhaustification.InnocentExclusion
/-!
# Chow & Erlewine 2022: Restrictions on the Position of *exh*
@cite{chow-erlewine-2022}

Keng Ji Chow & Michael Yoshitaka Erlewine.
Restrictions on the position of *exh*. Proceedings of SALT 32: 522--542.

## Core Contributions

1. Additive particles (*also*, *again*) diagnose the structural position of
   *exh*: the presupposition of *also* is sensitive to whether *exh* is in
   its scope.

2. **"As low as possible" generalization** (9): for certain SI triggers
   (disjunction, bare numerals, unstressed *some*, conjunction, *all*),
   *exh* must adjoin to the lowest position where it is not vacuous.

3. **Three-way lexical classification** of SI triggers by `[uexh]` feature
   (§3.3, (30)), following @cite{chierchia-2013}'s feature-checking approach:
   - `[uexh*]` (strong): *or*, bare numerals, *sm*, *and*, *all*
   - `[uexh]` (weak): stressed *SOME*
   - `[—]` (none): scalar adjectives

4. **Ignorance implicatures in embedded positions** (§4): the covert □ that
   derives ignorance can occur below the clause edge, contra
   Meyer's "Matrix K" theory.

## Formalization Strategy

Adjunction sites are derived from tree structure via `OpTree.inScopeOf`,
not stipulated as an enum. The tree determines whether *exh* must be below
a presupposition trigger (like *also*), and @cite{fox-2007}'s computable
`exhB` verifies the resulting semantic predictions on finite models.

## Related Files

- `Exhaustification/InnocentExclusion.lean`: `exhB`, innocent exclusion algorithm
- `Exhaustification/FreeChoice.lean`: feature-checking, scale reversal, FC
- `Exhaustification/InnocentExclusion.lean`: `exhB`, `ieIndices` (computable exhaustification)
- `ScalarImplicatures/ScopeExpressivity.lean`: grammatical vs pragmatic SI
-/

namespace Phenomena.ScalarImplicatures.Studies.ChowErlewine2022

-- ============================================================================
-- § 1. OpTree: Theory-Neutral Scope Tree
-- ============================================================================

/-- A tree for reasoning about operator scope and adjunction.

Operators (*exh*, *also*, *not*, □) are unary nodes; propositional content
is at the leaves. Labels are theory-neutral strings — no syntactic framework
is assumed. The tree structure alone determines scope relations. -/
inductive OpTree where
  | content (label : String)
  | op (label : String) (scope : OpTree)
  | merge (left right : OpTree)
  deriving Repr, DecidableEq

/-- Does the tree contain a node (content or operator) with the given label? -/
def OpTree.hasLabel : OpTree → String → Bool
  | .content l, target => l == target
  | .op l child, target => l == target || child.hasLabel target
  | .merge left right, target => left.hasLabel target || right.hasLabel target

/-- Is the target label in the scope of the given operator?
The scope of an operator is its child subtree. -/
def OpTree.inScopeOf : OpTree → (opLabel target : String) → Bool
  | .content _, _, _ => false
  | .op l child, opLabel, target =>
    (l == opLabel && child.hasLabel target) || child.inScopeOf opLabel target
  | .merge left right, opLabel, target =>
    left.inScopeOf opLabel target || right.inScopeOf opLabel target

-- ============================================================================
-- § 2. ExhFeature: Three-Way Classification of SI Triggers
-- ============================================================================

/-- Syntactic feature governing *exh* placement (@cite{chow-erlewine-2022} §3.3).

SI triggers bear one of three features constraining where their associated
*exh* may adjoin. This is orthogonal to `SITrigger` (which governs *when*
SIs fire); `ExhFeature` governs *where exh adjoins*.

- `strong` `[uexh*]`: *exh* as low as possible (non-vacuously)
- `weak` `[uexh]`: *exh* within local finite clause or just above embedding verb
- `none` `[—]`: no constraint on *exh* position -/
inductive ExhFeature where
  | strong  -- [uexh*]: or, bare numerals, unstressed some, and, all
  | weak    -- [uexh]: stressed SOME
  | none    -- [—]: scalar adjectives
  deriving DecidableEq, Repr

/-- An SI trigger paired with its *exh*-placement feature. -/
structure SITriggerSpec where
  trigger : String
  feature : ExhFeature
  deriving Repr

def orTrigger     : SITriggerSpec := ⟨"or",    .strong⟩
def andTrigger    : SITriggerSpec := ⟨"and",   .strong⟩
def allTrigger    : SITriggerSpec := ⟨"all",   .strong⟩
def smTrigger     : SITriggerSpec := ⟨"sm",    .strong⟩
def bareNumeral   : SITriggerSpec := ⟨"three", .strong⟩
def stressedSOME  : SITriggerSpec := ⟨"SOME",  .weak⟩
def scalarAdj     : SITriggerSpec := ⟨"cold",  .none⟩

-- ============================================================================
-- § 3. As-Low-As-Possible on Trees
-- ============================================================================

/-- Does a parse tree satisfy the `[uexh*]` constraint relative to a
presupposition trigger (*also*/*again*)?

If the SI trigger is in the presupposition trigger's scope, then the *exh*
checking `[uexh*]` must ALSO be in that scope — i.e., *exh* is below
the presupposition trigger. If the SI trigger is outside the presupposition
trigger's scope (e.g., after passivization), any *exh* position is fine. -/
def satisfiesUExhStar
    (tree : OpTree) (presupOp exhLabel triggerLabel : String) : Bool :=
  let triggerBelowPresup := tree.inScopeOf presupOp triggerLabel
  let exhBelowPresup := tree.inScopeOf presupOp exhLabel
  if triggerBelowPresup then exhBelowPresup else true

-- ============================================================================
-- § 4. Example Trees and Structural Predictions
-- ============================================================================

/-- Example (3): `[Nina]_F also teaches Arabic or Basque.`
The SI trigger "or" is inside the scope of "also". -/
def ex3_tree : OpTree :=
  .merge (.content "Nina")
    (.op "also" (.merge (.content "teaches") (.content "or")))

/-- Example (7): `Arabic or Basque is also taught by [Nina]_F.` (passive)
The SI trigger "or" has moved to subject position, outside "also"'s scope. -/
def ex7_tree : OpTree :=
  .merge (.content "or")
    (.op "also" (.merge (.content "taught-by") (.content "Nina")))

/-- In (3), "or" IS in "also"'s scope: *exh* must go below *also*. -/
theorem ex3_trigger_below_also :
    ex3_tree.inScopeOf "also" "or" = true := by native_decide

/-- In (7), "or" is NOT in "also"'s scope: *exh* goes above *also*. -/
theorem ex7_trigger_above_also :
    ex7_tree.inScopeOf "also" "or" = false := by native_decide

-- ============================================================================
-- § 5. Semantic Predictions via Fox 2007
-- ============================================================================

open Exhaustification.InnocentExclusion

/-- Exhaustified disjunction: `exh(A ∨ B)` = exclusive or.
Directly reuses @cite{fox-2007}'s `disj_exh_eq_exor`. -/
def exhDisj : PQWorld → Bool := exhB pqDomain disjAlts pOrQ

theorem exhDisj_eq_exor : ∀ w, exhDisj w = (pOrQ w && !pAndQ w) :=
  disj_exh_eq_exor

/-- Content of *also*'s scope, determined by tree structure.

- *exh* below *also*: *also*'s scope contains the exhaustified content
- *exh* above *also*: *also*'s scope contains the bare (unexhaustified) content -/
def alsoScopeContent (exhBelow : Bool) : PQWorld → Bool :=
  if exhBelow then exhDisj else pOrQ

-- ── Example (3): also > exh ──

/-- (3a) Disjunctive antecedent (Mira teaches Arabic only) is felicitous:
antecedent satisfies exclusive or. -/
theorem ex3a_felicitous :
    alsoScopeContent true .pOnly = true := by native_decide

/-- (3b) Conjunctive antecedent (Mira teaches both) is infelicitous:
antecedent does NOT satisfy exclusive or. -/
theorem ex3b_infelicitous :
    alsoScopeContent true .both = false := by native_decide

/-- Symmetric: Basque-only antecedent is also felicitous. -/
theorem ex3a_qOnly :
    alsoScopeContent true .qOnly = true := by native_decide

-- ── Counterfactual: exh > also would overgenerate ──

/-- If *exh* were above *also* in (3), (3b) would be wrongly predicted
felicitous: the conjunctive antecedent satisfies bare `A ∨ B`. -/
theorem ex3b_wrongly_ok_if_exh_above :
    alsoScopeContent false .both = true := by native_decide

-- ── Example (7): passive — exh > also ──

/-- (7) Conjunctive antecedent is felicitous in the passive:
*exh* is above *also* (the only non-vacuous position), so *also*'s
scope is unexhaustified `A ∨ B`. Conjunctive antecedent satisfies this. -/
theorem ex7_conjunctive_ok :
    alsoScopeContent false .both = true := by native_decide

-- ── End-to-end: tree → scope config → prediction ──

/-- The tree for (3) determines *exh* below *also*, which correctly predicts
(3a) felicitous and (3b) infelicitous — both in one theorem. -/
theorem ex3_end_to_end :
    let exhBelow := ex3_tree.inScopeOf "also" "or"
    alsoScopeContent exhBelow .pOnly = true
    ∧ alsoScopeContent exhBelow .both = false := by
  native_decide

/-- The tree for (7) determines *exh* above *also*, which correctly predicts
conjunctive antecedent felicitous. -/
theorem ex7_end_to_end :
    let exhBelow := ex7_tree.inScopeOf "also" "or"
    alsoScopeContent exhBelow .both = true := by
  native_decide

-- ============================================================================
-- § 6. Indirect Scalar Implicatures Under Negation
-- ============================================================================

/-- Negated propositions for indirect SI computation (§2.3). -/
def notPandQ : PQWorld → Bool := λ w => !pAndQ w
def notPorQ  : PQWorld → Bool := λ w => !pOrQ w
def notP     : PQWorld → Bool := λ w => !pProp w
def notQ     : PQWorld → Bool := λ w => !qProp w

/-- Alternatives for `¬(A ∧ B)` under scale reversal:
`{¬(A∧B), ¬A, ¬B, ¬(A∨B)}`. The scale `⟨∨, ∧⟩` reverses under negation
to `⟨¬∧, ¬∨⟩`, where `¬(A∨B)` is strongest. -/
def negConjAlts : List (PQWorld → Bool) := [notPandQ, notP, notQ, notPorQ]

/-- The indirect SI of negated conjunction equals exclusive or:
`exh(¬(A ∧ B)) = ¬(A ∧ B) ∧ (A ∨ B) = A ⊕ B`.

The same result as the direct SI of disjunction — as expected from
duality under negation. -/
theorem indirect_si_eq_exclusive_or :
    ∀ w : PQWorld, exhB pqDomain negConjAlts notPandQ w =
      (pOrQ w && !pAndQ w) := by
  intro w; cases w <;> native_decide

-- ── Vacuity: exh on conjunction is trivial ──

/-- Sauerland alternatives for conjunction: `{A∧B, A, B, A∨B}`. -/
def conjAlts : List (PQWorld → Bool) := [pAndQ, pProp, qProp, pOrQ]

/-- *exh* applied directly to conjunction is **vacuous**: A∧B entails every
Sauerland alternative, so NW = {} and I-E = {}. This is why position ③
in (19) is ruled out — *exh* there makes no contribution. -/
theorem exh_conj_vacuous :
    ∀ w : PQWorld, exhB pqDomain conjAlts pAndQ w = pAndQ w := by
  intro w; cases w <;> native_decide

-- ── Parse (18): indirect SI + also diagnostic ──

/-- Parse (18a): `exh [also [not [A∧B]]]`
*exh* above *also* — `[uexh*]` violated. The paper shows this parse
wrongly predicts (16b) felicitous. -/
def parse18a_tree : OpTree :=
  .op "exh" (.op "also" (.op "not" (.content "and")))

/-- Parse (18b): `also [exh [not [A∧B]]]`
*exh* below *also*, above *not* — `[uexh*]` satisfied. This is the
correct parse: *exh* exhaustifies ¬(A∧B) to get the indirect SI A⊕B,
and *also* presupposes a salient individual satisfying A⊕B. -/
def parse18b_tree : OpTree :=
  .op "also" (.op "exh" (.op "not" (.content "and")))

/-- Parse (18c): `also [not [exh [A∧B]]]`
*exh* below *not*, directly on conjunction — vacuous by `exh_conj_vacuous`.
`satisfiesUExhStar` passes but *exh* contributes nothing, so this parse
is equivalent to having no SI. -/
def parse18c_tree : OpTree :=
  .op "also" (.op "not" (.op "exh" (.content "and")))

theorem parse18a_violates :
    satisfiesUExhStar parse18a_tree "also" "exh" "and" = false := by native_decide

theorem parse18b_satisfies :
    satisfiesUExhStar parse18b_tree "also" "exh" "and" = true := by native_decide

/-- Parse (18c) passes the structural check but is vacuous — the "as low
as possible" generalization (9) requires the *non-vacuity* qualification
to correctly rule out this position. -/
theorem parse18c_structural_ok_but_vacuous :
    satisfiesUExhStar parse18c_tree "also" "exh" "and" = true := by native_decide

/-- (16a) `not>and` antecedent (teaches exactly one) is felicitous:
satisfies `exh(¬(A ∧ B))` = exclusive or. -/
theorem ex16a_felicitous :
    exhB pqDomain negConjAlts notPandQ .pOnly = true := by native_decide

/-- (16b) `not>or` antecedent (teaches neither) is infelicitous:
`neither` does NOT satisfy exclusive or. -/
theorem ex16b_infelicitous :
    exhB pqDomain negConjAlts notPandQ .neither = false := by native_decide

/-- End-to-end for indirect SI: parse (18b) places *exh* below *also*,
yielding `exh(¬(A∧B)) = A⊕B` as *also*'s scope content. Combined with
the structural constraint and semantic predictions, this closes the
argument chain: tree → [uexh*] satisfied → indirect SI → correct judgments. -/
theorem ex16_end_to_end :
    satisfiesUExhStar parse18b_tree "also" "exh" "and" = true
    ∧ exhB pqDomain negConjAlts notPandQ .pOnly = true
    ∧ exhB pqDomain negConjAlts notPandQ .neither = false := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- § 7. Scalar Adjectives: No Placement Constraint
-- ============================================================================

/-- Temperature scale: `freezing > cold > warm`.
Scalar adjectives bear no `[uexh]` feature (§3.1). -/
inductive TempWorld where | freezing | cold | warm
  deriving DecidableEq, Repr

def isCold     : TempWorld → Bool | .freezing | .cold => true | .warm => false
def isFreezing : TempWorld → Bool | .freezing => true  | _ => false
def tempDomain : List TempWorld := [.freezing, .cold, .warm]
def coldAlts   : List (TempWorld → Bool) := [isCold, isFreezing]

/-- `exh(cold) = cold ∧ ¬freezing`: exactly cold, not freezing. -/
def exhCold : TempWorld → Bool := exhB tempDomain coldAlts isCold

/-- If `[uexh*]` forced *exh* low (below *also*), a "freezing" antecedent
would need to satisfy `exh(cold) = cold ∧ ¬freezing`. It doesn't. -/
theorem freezing_fails_exh_cold : exhCold .freezing = false := by native_decide

/-- But (24) IS felicitous with a "freezing" antecedent, showing
scalar adjectives allow *exh* above *also*. The antecedent satisfies
unexhaustified "cold" (since freezing entails cold). -/
theorem freezing_satisfies_cold : isCold .freezing = true := by native_decide

-- ============================================================================
-- § 8. Ignorance Implicatures: Embedded □
-- ============================================================================

/-! Multiple *exh* instances + the covert necessity modal □ derive both
the scalar implicature (A ∨ B → ¬(A ∧ B)) and the ignorance implicature
(the speaker doesn't know which disjunct is true).

Three candidate parses for (32) `[Nina]_F also teaches A or B` with
ignorance inferences. The inner *exh* (exh1) must check `[uexh*]`.
The outer *exh* (exh2) applies above □ to derive ignorance.

Once `[uexh*]` is checked by exh₁, it imposes no conditions on the
placement of additional *exh* instances — this explains why both
(37a) and (37b) are grammatical despite differing in exh₂'s position. -/

/-- Parse (37a): `also [exh₂ [□ [exh₁ [A ∨ B]]]]`
exh₁ is below *also* — `[uexh*]` satisfied. -/
def parse37a : OpTree :=
  .op "also" (.op "exh2" (.op "box" (.op "exh1" (.content "or"))))

/-- Parse (37b): `exh₂ [□ [also [exh₁ [A ∨ B]]]]`
exh₁ is below *also* — `[uexh*]` satisfied.
□ is in an embedded position (contra Meyer's Matrix K). -/
def parse37b : OpTree :=
  .op "exh2" (.op "box" (.op "also" (.op "exh1" (.content "or"))))

/-- Parse (37c): `exh₂ [□ [exh₁ [also [A ∨ B]]]]`
exh₁ is ABOVE *also* — `[uexh*]` violated. -/
def parse37c : OpTree :=
  .op "exh2" (.op "box" (.op "exh1" (.op "also" (.content "or"))))

theorem parse37a_ok :
    satisfiesUExhStar parse37a "also" "exh1" "or" = true := by native_decide

/-- Parse (37b) is grammatical AND places □ in an embedded position.
This is the empirical argument against Meyer's Matrix K theory,
which requires the ignorance-generating operator to adjoin only
at the clause root. Parse (37b) is necessary to account for "split"
antecedents (33c) — the grammar must generate it. -/
theorem parse37b_ok :
    satisfiesUExhStar parse37b "also" "exh1" "or" = true := by native_decide

theorem parse37c_bad :
    satisfiesUExhStar parse37c "also" "exh1" "or" = false := by native_decide

/-- In (37b), □ is dominated by exh₂ — an embedded, non-root position.
This demonstrates that ignorance implicatures can be generated in
embedded positions, contra the Matrix K theory. -/
theorem box_embedded_in_37b :
    parse37b.inScopeOf "exh2" "box" = true := by native_decide

-- ============================================================================
-- § 9. Tree-Based *exh* Positioning
-- ============================================================================

/-! `ExhFeature` determines which tree positions are available for *exh*.

The standard M/O/I positions correspond to specific nodes in a
doubly-quantified sentence tree. The tree-based `inScopeOf` predicate
subsumes an enumeration of positions by computing them from tree structure
rather than stipulating them.

`ExhFeature` answers: "where MUST *exh* go, given the trigger's feature?" -/

/-- Doubly-quantified tree with *exh* at position I (below *also*):
`[Q₁ [also [exh [V Q₂]]]]` -/
def treeExhI : OpTree :=
  .merge (.content "Q1")
    (.op "also" (.op "exh" (.merge (.content "V") (.content "Q2"))))

/-- Doubly-quantified tree with *exh* at position M (above everything):
`[exh [Q₁ [also [V Q₂]]]]` -/
def treeExhM : OpTree :=
  .op "exh" (.merge (.content "Q1")
    (.op "also" (.merge (.content "V") (.content "Q2"))))

/-- For a `[uexh*]` trigger (e.g., "Q2") inside *also*'s scope,
the tree-based constraint forces exh below *also* — i.e., position I.
Position M (above *also*) is ruled out. This recovers the M/O/I
distinction as a special case of tree structure. -/
theorem strong_forces_inner :
    satisfiesUExhStar treeExhI "also" "exh" "Q2" = true
    ∧ satisfiesUExhStar treeExhM "also" "exh" "Q2" = false := by
  exact ⟨by native_decide, by native_decide⟩

end Phenomena.ScalarImplicatures.Studies.ChowErlewine2022
