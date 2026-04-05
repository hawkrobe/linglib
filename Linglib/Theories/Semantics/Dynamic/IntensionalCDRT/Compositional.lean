import Linglib.Theories.Semantics.Dynamic.IntensionalCDRT.Bridge

/-!
# Compositional Fragment for ICDRT

@cite{hofmann-2025} Appendix C

Type-driven compositional semantics for Intensional CDRT. Each lexical
entry is a higher-order function over dynamic meta-types; composition is
function application + sequential update. The resulting `ICDRTUpdate`
values lift to distributive CCPs via `Bridge.lean`.

## Meta-types (Definition 13)

| Paper | Lean | Interpretation |
|-------|------|----------------|
| **e** | `IVar` | Individual dref name |
| **w** | `PVar` | Propositional dref name |
| **t** | `ICDRTUpdate W E` | Static update relation |

Compositional types are functions between these: `e(wt)` = VP type,
`wt` = sentence type, etc. Lean's own type system enforces
well-typedness — no separate type-checking layer needed.

## Lexical entries

* `commonNoun` — (15) `λv.λφ.[R_φ(v)]`
* `indefinite` — (16) `a^v: λP.λP'.λφ.[φ:v]; P(v)(φ); P'(v)(φ)`
* `pronoun` — (17) `it_v: λP.λφ.P(v)(φ)`
* `properName` — (14) `Mary: λP.λφ.[v | v ≡ Mary]; P(v)(φ)`
* `semNOT` — (18a) `NOT^{φ'}: λSc.λφ.[φ' | φ ≡ φ̄']; max_{φ'}(Sc(φ'))`
* `semOR` — (18b) `OR^{φ',φ''}: λSc'.λSc''.λφ.[φ',φ'' | φ ≡ φ'⊎φ'']; ...`
* `semIF` — (18c) `IF^{φ',φ''}: λSc'.λSc''.λφ.[φ',φ'' | φ ≡ φ̄'⊎φ'']; ...`
* `semAND` — (18d) `AND^{φ',φ''}: λSc'.λSc''.λφ.[φ' | φ'⊑φ]; ...; [φ'' | φ''⊑φ']; ...`
* `semBelieved` — (18e) `believed: λv.λSc.λφ.[φ' | believe_φ(v,φ')]; max_{φ'}(Sc(φ'))`
* `semDEC` — (19) `DEC_S^φ: λSc.[φ | φ_{DC_S}⊑φ]; max_φ(Sc(φ))`

## Architecture

```
Lexical entries (this file)
    │  compose via function application + ICDRTUpdate.seq
    ↓
ICDRTUpdate W E (Operators.lean)
    │  toDynProp = lift ∘ fiberDRS
    ↓
DynProp W E = CCP (ICDRTAssignment W E × W) (Bridge.lean)
```
-/

namespace Semantics.Dynamic.IntensionalCDRT.Compositional

open Core
open Semantics.Dynamic.IntensionalCDRT


-- ════════════════════════════════════════════════════════════════
-- § 1. Dynamic Semantic Types (Appendix C, Definition 13)
-- ════════════════════════════════════════════════════════════════

variable {W E : Type*}

/-- VP / predicate type: `e(wt)` — takes individual dref and local context,
    returns an update. This is the semantic type of common nouns, VPs,
    and any expression that predicates over an individual. -/
abbrev SemE (W E : Type*) := IVar → PVar → ICDRTUpdate W E

/-- Sentence / clause type: `wt` — takes local context, returns update.
    This is the semantic type of sentences (before DEC anchoring). -/
abbrev SemW (W E : Type*) := PVar → ICDRTUpdate W E


-- ════════════════════════════════════════════════════════════════
-- § 2. Primitives
-- ════════════════════════════════════════════════════════════════

/-- Vacuous VP scope: the identity predicate `λv.λφ.idUp`.
    Used when a sentence has no VP beyond the NP (e.g., "there is a bathroom"). -/
def vacuousScope : SemE W E := λ _ _ => ICDRTUpdate.idUp


-- ════════════════════════════════════════════════════════════════
-- § 3. Lexical Entries (Appendix C, Definitions 14–19)
-- ════════════════════════════════════════════════════════════════

/--
(15) Common noun: `bathroom ⟿ λv_e.λφ_w.[bathroom_φ(v)]`

A common noun is a test update: the assignment is unchanged,
but the predication `R_φ(v)` must hold at the output.

@cite{hofmann-2025} Appendix C (15)
-/
def commonNoun (R : E → W → Prop) : SemE W E :=
  λ v φ => λ i j => i = j ∧ dynPred R φ v j

/--
Intransitive VP: structurally identical to `commonNoun`.
The distinction is syntactic category, not semantic type —
both are `SemE W E` (predicate type `e(wt)`).
-/
abbrev intransVP (R : E → W → Prop) : SemE W E := commonNoun R

/--
(16) Indefinite: `a^v ⟿ λP.λP'.λφ.[φ : v]; P(v)(φ); P'(v)(φ)`

The indefinite introduces individual dref `v` relative to
local context `φ` via relative variable update (Definition 25),
then sequences restrictor `P` and nuclear scope `P'`.

The biconditional in `relVarUp` ensures `v` has a referent
exactly in the φ-worlds, preventing scope leakage.

@cite{hofmann-2025} Appendix C (16)
-/
def indefinite (v : IVar) (P P' : SemE W E) (φ : PVar) : ICDRTUpdate W E :=
  ICDRTUpdate.seq (ICDRTUpdate.seq (λ i j => relVarUp φ v i j) (P v φ)) (P' v φ)

/--
(17) Pronoun: `it_v ⟿ λP.λφ.P(v)(φ)`

The pronoun contributes no update — it simply passes its
index `v` to the predicate `P` in local context `φ`.

@cite{hofmann-2025} Appendix C (17)
-/
def pronoun (v : IVar) (P : SemE W E) (φ : PVar) : ICDRTUpdate W E :=
  P v φ

/--
(14) Proper name: `Mary ⟿ λP.λφ.[v | v ≡ Mary_e]; P(v)(φ)`

Introduces a rigid individual dref `v` whose value is the
constant individual `name` at every world, then passes `v`
to the predicate.

@cite{hofmann-2025} Appendix C (14)
-/
def properName (name : E) (v : IVar) (P : SemE W E) (φ : PVar) :
    ICDRTUpdate W E :=
  ICDRTUpdate.seq
    (λ i j => indivVarUp v i j ∧ ∀ w : W, j.indiv v w = .some name)
    (P v φ)

/--
(18a) Sentential negation: `NOT^{φ'} ⟿ λSc.λφ.[φ' | φ ≡ φ̄']; max_{φ'}(Sc(φ'))`

Introduces fresh propositional dref `φ'` for the negated content,
constrains the matrix `φ` to be its complement, then applies
propositional maximization to the scope.

This is static complementation over propositional drefs, NOT
bilateral swap — the algebraic content of @cite{hofmann-2025}'s
key insight (§5.1.1).

@cite{hofmann-2025} Appendix C (18a)
-/
def semNOT (φ' : PVar) (Sc : SemW W E) (φ : PVar) : ICDRTUpdate W E :=
  ICDRTUpdate.seq
    (λ i j => propVarUp φ' i j ∧ isComplement φ φ' j)
    (propMaxOp φ' (Sc φ'))

/--
(18b) Disjunction: `OR^{φ',φ''} ⟿ λSc'.λSc''.λφ.[φ',φ'' | φ ≡ φ'⊎φ''];
       max_{φ'}(Sc'(φ')); max_{φ''}(Sc''(φ''))`

Introduces two fresh propositional drefs whose union equals the
matrix proposition. Each disjunct is independently maximized.

The disjuncts' local contexts (`φ'`, `φ''`) need NOT overlap —
this is how bathroom disjunctions enable cross-disjunct anaphora.

@cite{hofmann-2025} Appendix C (18b)
-/
def semOR (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) :
    ICDRTUpdate W E :=
  ICDRTUpdate.seq
    (ICDRTUpdate.seq
      (λ i j => multiVarUp [φ', φ''] [] i j ∧
        j.prop φ = j.prop φ' ∪ j.prop φ'')
      (propMaxOp φ' (Sc' φ')))
    (propMaxOp φ'' (Sc'' φ''))

/--
(18c) Conditional: `IF^{φ',φ''} ⟿ λSc'.λSc''.λφ.[φ',φ'' | φ ≡ φ̄'⊎φ''];
       max_{φ'}(Sc'(φ')); max_{φ''}(Sc''(φ''))`

Like `semOR` but the first disjunct is complemented:
`φ ≡ φ̄' ⊎ φ''`. The antecedent `Sc'` is evaluated in `φ'`,
the consequent `Sc''` in `φ''`.

@cite{hofmann-2025} Appendix C (18c)
-/
def semIF (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) :
    ICDRTUpdate W E :=
  ICDRTUpdate.seq
    (ICDRTUpdate.seq
      (λ i j => multiVarUp [φ', φ''] [] i j ∧
        j.prop φ = (j.prop φ')ᶜ ∪ j.prop φ'')
      (propMaxOp φ' (Sc' φ')))
    (propMaxOp φ'' (Sc'' φ''))

/--
(18d) Conjunction: `AND^{φ',φ''} ⟿ λSc'.λSc''.λφ.
       [φ' | φ'⊑φ]; max_{φ'}(Sc'(φ'));
       [φ'' | φ''⊑φ']; max_{φ''}(Sc''(φ''))`

Both conjuncts contribute conditions in sequenced local contexts.
The first conjunct's context `φ'` is contained in `φ`, and the
second conjunct's context `φ''` is contained in `φ'`.

@cite{hofmann-2025} Appendix C (18d)
-/
def semAND (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) :
    ICDRTUpdate W E :=
  ICDRTUpdate.seq
    (ICDRTUpdate.seq
      (ICDRTUpdate.seq
        (λ i j => propVarUp φ' i j ∧ dynInclusion φ' φ j)
        (propMaxOp φ' (Sc' φ')))
      (λ i j => propVarUp φ'' i j ∧ dynInclusion φ'' φ' j))
    (propMaxOp φ'' (Sc'' φ''))

/--
(18e) Attitude verb: `believed ⟿ λv.λSc.λφ.[φ' | believe_φ(v,φ')]; max_{φ'}(Sc(φ'))`

The attitude verb introduces a propositional dref `φ'` for the
agent's doxastic state. `dox j` returns the set of worlds
compatible with the agent's beliefs at assignment `j`.

The embedded content `Sc` is evaluated in `φ'`, which is a
nonveridical context — enabling anaphora to hypothetical drefs
without requiring veridicality relative to the speaker's DC.

@cite{hofmann-2025} Appendix C (18e)
-/
def semBelieved (φ' : PVar) (dox : ICDRTAssignment W E → Set W)
    (Sc : SemW W E) (_φ : PVar) : ICDRTUpdate W E :=
  ICDRTUpdate.seq
    (λ i j => propVarUp φ' i j ∧ believeCondition φ' dox j)
    (propMaxOp φ' (Sc φ'))

/--
(19) Declarative assertion: `DEC_S^φ ⟿ λSc.[φ | φ_{DC_S}⊑φ]; max_φ(Sc(φ))`

Introduces propositional dref `φ` for the assertion content,
constrains `φ_{DC_S} ⊆ φ` (the speaker's commitment set is
a subset of the assertion's truth conditions), and applies
propositional maximization.

This is the speech-act operator that anchors sentential content
to the discourse. Every declarative sentence is wrapped in DEC.

@cite{hofmann-2025} Appendix C (19)
-/
def semDEC (φ_DC : PVar) (φ : PVar) (Sc : SemW W E) :
    ICDRTUpdate W E :=
  ICDRTUpdate.seq
    (λ i j => propVarUp φ i j ∧ decCondition φ_DC φ j)
    (propMaxOp φ (Sc φ))


-- ════════════════════════════════════════════════════════════════
-- § 4. Structural Properties of Lexical Entries
-- ════════════════════════════════════════════════════════════════

/-- A common noun is a test: it preserves the assignment. -/
theorem commonNoun_is_test (R : E → W → Prop) (v : IVar) (φ : PVar)
    (i j : ICDRTAssignment W E) (h : commonNoun R v φ i j) : i = j := h.1

/-- `vacuousScope` is a test (identity). -/
theorem vacuousScope_is_test (v : IVar) (φ : PVar)
    (i j : ICDRTAssignment W E) (h : vacuousScope v φ i j) : i = j := h

/-- `pronoun v P φ` is just `P v φ` — the pronoun is transparent. -/
theorem pronoun_transparent (v : IVar) (P : SemE W E) (φ : PVar) :
    pronoun v P φ = P v φ := rfl

/-- Indefinite introduction implies local entailment when restrictor
    and scope are tests (preserve the assignment).

    This is the KEY structural connection between composition and
    accessibility: the biconditional in `relVarUp` (Definition 25ii)
    survives through test-like predicates, ensuring the introduced
    dref is locally entailed in its own local context.

    Combined with `accessible`, this gives: indefinite + test predicates
    → accessible (assuming discourse consistency). -/
theorem indefinite_test_entails (v : IVar) (P P' : SemE W E) (φ : PVar)
    (hP : ∀ a b, P v φ a b → a = b)
    (hP' : ∀ a b, P' v φ a b → a = b)
    (i j : ICDRTAssignment W E)
    (h : indefinite v P P' φ i j) :
    localEntailment φ v j := by
  obtain ⟨l, ⟨m, hrel, hPml⟩, hP'lj⟩ := h
  have hmj : m = j := (hP m l hPml).trans (hP' l j hP'lj)
  rw [← hmj]
  exact relVarUp_implies_localEntailment φ v i m hrel


-- ════════════════════════════════════════════════════════════════
-- § 5. Operator Decomposition Theorems
-- ════════════════════════════════════════════════════════════════

/-- DEC introduces the inclusion condition. -/
theorem semDEC_inclusion (φ_DC φ : PVar) (Sc : SemW W E)
    (i j : ICDRTAssignment W E) (h : semDEC φ_DC φ Sc i j) :
    ∃ k, propVarUp φ i k ∧ decCondition φ_DC φ k ∧
      propMaxOp φ (Sc φ) k j := by
  obtain ⟨k, hk, hmax⟩ := h
  exact ⟨k, hk.1, hk.2, hmax⟩

/-- NOT introduces the complement condition on the intermediate assignment. -/
theorem semNOT_introduces_complement (φ' : PVar) (Sc : SemW W E) (φ : PVar)
    (i j : ICDRTAssignment W E) (h : semNOT φ' Sc φ i j) :
    ∃ k, propVarUp φ' i k ∧ isComplement φ φ' k ∧
      propMaxOp φ' (Sc φ') k j := by
  obtain ⟨k, hk, hmax⟩ := h
  exact ⟨k, hk.1, hk.2, hmax⟩

/-- Double negation restores the original local context via
    double complementation.

    At the introduction level, `isComplement φ φ' k` and
    `isComplement φ' φ'' j` together yield `j.prop φ = j.prop φ''`
    by `double_complement_eq` (from Operators.lean). -/
theorem double_neg_complement (φ' φ'' : PVar) (φ : PVar)
    (k j : ICDRTAssignment W E)
    (h_outer : isComplement φ φ' k)
    (h_inner : isComplement φ' φ'' j)
    (h_prop_pres : j.prop φ = k.prop φ)
    (h_prop_pres' : j.prop φ' = k.prop φ') :
    j.prop φ = j.prop φ'' := by
  have h_outer_j : isComplement φ φ' j := by
    unfold isComplement at h_outer ⊢
    rw [h_prop_pres, h_prop_pres', h_outer]
  exact double_complement_eq φ' φ'' φ j h_inner h_outer_j


-- ════════════════════════════════════════════════════════════════
-- § 6. Definitional Unfolding
-- ════════════════════════════════════════════════════════════════

/-- `commonNoun R v φ` is a test: identity + `dynPred`. -/
theorem commonNoun_unfold (R : E → W → Prop) (v : IVar) (φ : PVar) :
    commonNoun R v φ = (λ i j => i = j ∧ dynPred R φ v j) := rfl

/-- `indefinite v P P' φ` is `relVarUp ; P ; P'`. -/
theorem indefinite_unfold (v : IVar) (P P' : SemE W E) (φ : PVar) :
    indefinite v P P' φ =
    ICDRTUpdate.seq (ICDRTUpdate.seq (λ i j => relVarUp φ v i j) (P v φ)) (P' v φ) := rfl

/-- `semNOT φ' Sc φ` is `(propVarUp + complement) ; max(scope)`. -/
theorem semNOT_unfold (φ' : PVar) (Sc : SemW W E) (φ : PVar) :
    semNOT φ' Sc φ =
    ICDRTUpdate.seq
      (λ i j => propVarUp φ' i j ∧ isComplement φ φ' j)
      (propMaxOp φ' (Sc φ')) := rfl

/-- `semDEC φ_DC φ Sc` is `(propVarUp + DEC condition) ; max(scope)`. -/
theorem semDEC_unfold (φ_DC φ : PVar) (Sc : SemW W E) :
    semDEC φ_DC φ Sc =
    ICDRTUpdate.seq
      (λ i j => propVarUp φ i j ∧ decCondition φ_DC φ j)
      (propMaxOp φ (Sc φ)) := rfl

/-- `semOR φ' φ'' Sc' Sc'' φ` is `(multiVarUp + union) ; max(Sc') ; max(Sc'')`. -/
theorem semOR_unfold (φ' φ'' : PVar) (Sc' Sc'' : SemW W E) (φ : PVar) :
    semOR φ' φ'' Sc' Sc'' φ =
    ICDRTUpdate.seq
      (ICDRTUpdate.seq
        (λ i j => multiVarUp [φ', φ''] [] i j ∧
          j.prop φ = j.prop φ' ∪ j.prop φ'')
        (propMaxOp φ' (Sc' φ')))
      (propMaxOp φ'' (Sc'' φ'')) := rfl


-- ════════════════════════════════════════════════════════════════
-- § 7. Bridge to CCP
-- ════════════════════════════════════════════════════════════════

/-- Every compositional derivation lifts to a distributive CCP.
    This is immediate from `toDynProp_isDistributive` because every
    derivation is an `ICDRTUpdate W E`. -/
theorem comp_isDistributive (D : ICDRTUpdate W E) :
    IsDistributive D.toDynProp :=
  toDynProp_isDistributive D

/-- Every compositional derivation factors through `fiberDRS`. -/
theorem comp_factorizes (D : ICDRTUpdate W E) :
    D.toDynProp = lift (fiberDRS D) :=
  toDynProp_eq_lift_fiberDRS D

/-- Sequential composition in the fragment lifts to CCP composition. -/
theorem comp_seq_lifts (D₁ D₂ : ICDRTUpdate W E) (c : IContext W E) :
    (ICDRTUpdate.seq D₁ D₂).toDynProp c = D₂.toDynProp (D₁.toDynProp c) :=
  ICDRTUpdate.seq_toDynProp D₁ D₂ c


end Semantics.Dynamic.IntensionalCDRT.Compositional
