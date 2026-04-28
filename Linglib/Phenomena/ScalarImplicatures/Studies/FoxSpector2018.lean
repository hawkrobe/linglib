import Mathlib.Tactic.DeriveFintype
import Linglib.Theories.Semantics.Exhaustification.Operators.Basic
import Linglib.Theories.Semantics.Exhaustification.Innocent

/-!
# Fox & Spector 2018: Economy and Embedded Exhaustification
@cite{fox-spector-2018}

Fox, D. & Spector, B. (2018). Economy and embedded exhaustification.
Natural Language Semantics, 26(1), 1–50.

## Empirical support: @cite{chemla-spector-2011}

The economy-condition framework predicts that embedded `exh` is
licensed precisely when its insertion is non-vacuous. CS11's §4.4.5
distributivity finding (page 20) is direct empirical support: for the
'or' item under STRONG condition, sub-cases STRONG[≠] (where
distributivity inferences are non-vacuous) are rated significantly
higher than STRONG[=] (where they are vacuous), 99.5% vs 73%, W = 78,
p < .005. See `Phenomena/ScalarImplicatures/Studies/ChemlaSpector2011.lean`
`distributivity_strong_neq_gt_strong_eq` for the captured empirical
inequality.

## Core Argument

Where can `exh` be inserted in the parse tree? Fox & Spector propose
an **economy condition**: `exh` is licensed only if it is neither
incrementally vacuous nor incrementally weakening. This single
constraint derives three previously independent generalizations:

1. **Hurford's Constraint**: disjunctions where one disjunct entails
   the other are infelicitous (unless rescued by embedded `exh`)
2. **Singh's Asymmetry**: "p or q, or both" is acceptable but
   "both, or p or q" is not (@cite{singh-2008})
3. **Implicature Focus Generalization (IFG)**: embedded `exh` under
   DE operators requires focus on the scalar item

## Formalized Results

- Economy condition (original and comparison-class formulations)
- Hurford's Constraint derived from economy (`hurford_from_economy`)
- Singh's Asymmetry from economy (`singh_weak_exh_nonvacuous`,
  `singh_strong_exh_vacuous`)
- `exh` is always globally weakening under DE (`exh_weakening_under_de`)
- More IE alternatives → stronger result (`exhIE_stronger_of_more_IE`)
- Under DE, more IE → weaker global result (`de_weakening_of_more_IE`)
- The exh–exh prediction: `exh[¬exh(p∨q)] = p∧q` (`exh_exh_conjunctive`)
- Bridge to `Symmetry.lean`: vacuous `exh` violates economy
  (`vacuous_violates_economy`)

## Connection to the Symmetry Problem

Economy interacts with the symmetry problem (`Symmetry.lean`)
indirectly. When symmetric alternatives S₁, S₂ are the only
non-weaker alternatives, `exh` is vacuous (proved by
`symmetric_exhB_vacuous`). Vacuous `exh` violates economy
(`vacuous_violates_economy`), so the grammar rejects the parse
rather than producing wrong results. But economy does not *derive*
the correct SI — that requires @cite{katzir-2007}'s structural
complexity restricting the alternative set (see
`Structural.lean`).

Economy and structural complexity are **complementary**:
- @cite{katzir-2007} determines *which* alternatives enter the set
  → breaks symmetry → `exh` derives the correct SI
- Economy determines *whether* `exh` is licensed given those
  alternatives → blocks vacuous/weakening insertions
-/

namespace Phenomena.ScalarImplicatures.Studies.FoxSpector2018

open Exhaustification


-- ============================================================
-- SECTION 1: Continuations and Parse Points
-- ============================================================

variable {World : Type*}

/-- Binary disjunction for `Prop'`. -/
private def por (φ ψ : Set World) : Set World := fun w => φ w ∨ ψ w

/-- A continuation context represents "the rest of the sentence"
    after a parse point. -/
abbrev Continuation (World : Type*) := Set World → Set World

/-- Negation continuation. -/
def negCont : Continuation World := (·)ᶜ

/-- A parse point: a proposition with alternatives and possible
    continuations. -/
structure ParsePoint (World : Type*) where
  prop : Set World
  alts : Set (Set World)
  continuations : Set (Continuation World)


-- ============================================================
-- SECTION 2: Economy Condition (definition 63)
-- ============================================================

/-- Incremental vacuity: `exh` makes no difference for ANY
    continuation. -/
def isIncrementallyVacuous (ALT : Set (Set World)) (φ : Set World)
    (conts : Set (Continuation World)) : Prop :=
  ∀ C ∈ conts, ∀ w : World, C (exhIE ALT φ) w ↔ C φ w

/-- Incremental weakening: `exh` weakens the meaning for ALL
    continuations. In DE contexts, local strengthening = global
    weakening. -/
def isIncrementallyWeakening (ALT : Set (Set World)) (φ : Set World)
    (conts : Set (Continuation World)) : Prop :=
  ∀ C ∈ conts, C φ ⊆ C (exhIE ALT φ)

/-- **Economy Condition on Exhaustification** (definition 63):
    `exh(φ)` is licensed only if it is neither incrementally
    vacuous nor incrementally weakening. -/
def economyConditionMet (ALT : Set (Set World)) (φ : Set World)
    (conts : Set (Continuation World)) : Prop :=
  ¬isIncrementallyVacuous ALT φ conts ∧
  ¬isIncrementallyWeakening ALT φ conts


-- ============================================================
-- SECTION 3: Comparison-Class Economy (definitions 85/86)
-- ============================================================

/-!
## Comparison-Class Economy

The refined economy condition compares `exh_C(φ)` not just against
`φ`, but against `exh_{C'}(φ)` for every subset C' of alternatives.
Economy bans adding alternatives that only weaken the result.
-/

/-- Global weakening (definition 84): `exh` is globally weakening
    if the sentence without `exh` entails the sentence with `exh`. -/
def isGloballyWeakening (ALT : Set (Set World)) (φ : Set World)
    (S : Continuation World) : Prop :=
  ∀ w, S φ w → S (exhIE ALT φ) w

/-- Generalized global weakening (definition 86): `exh_C` is
    globally weakening if there exists C' with strictly fewer IE
    alternatives such that S(exh_{C'}(A)) entails S(exh_C(A)).
    Using fewer alternatives gives a stronger result. -/
def isGloballyWeakeningGen (ALT : Set (Set World)) (φ : Set World)
    (S : Continuation World) : Prop :=
  ∃ ALT' : Set (Set World),
    IE ALT' φ ⊂ IE ALT φ ∧
    ∀ w, S (exhIE ALT' φ) w → S (exhIE ALT φ) w


-- ============================================================
-- SECTION 4: Hurford's Constraint from Economy
-- ============================================================

/-!
## Hurford's Constraint

"A disjunction of the form 'A or B' sounds redundant and is odd
when one of the disjuncts entails the other."

Fox & Spector derive this from economy rather than stipulating it.
-/

/-- Hurford violation: one disjunct entails the other. -/
def hurfordViolation (A B : Set World) : Prop :=
  (A ⊆ B) ∨ (B ⊆ A)

/-- A disjunction satisfies Hurford's Constraint if neither
    disjunct entails the other. -/
def satisfiesHC (A B : Set World) : Prop :=
  ¬(A ⊆ B) ∧ ¬(B ⊆ A)

/-- A Hurford disjunction can be rescued by embedding `exh` in the
    weaker disjunct if the exhaustified disjunct no longer entails
    the stronger one. -/
def isRescuedByExh (ALT : Set (Set World)) (A B : Set World) :
    Prop :=
  ¬(exhIE ALT A ⊆ B)

/-- The disjunction continuation: (λp. A ∨ p). -/
def disjCont (A : Set World) : Continuation World :=
  fun p => por A p

/-- **Hurford from Economy**: if B ⊆ A and `exh(B)` cannot break
    the entailment, then `exh(B)` is incrementally weakening in
    the disjunction context — economy blocks the parse.

    This derives Hurford's Constraint from economy rather than
    stipulating it as a surface filter. -/
theorem hurford_from_economy (ALT : Set (Set World)) (A B : Set World)
    (hBA : B ⊆ A) (_hstill : exhIE ALT B ⊆ A) :
    isIncrementallyWeakening ALT B {disjCont A} := by
  intro C hC w hCBw
  simp only [Set.mem_singleton_iff] at hC
  rw [hC] at hCBw ⊢
  simp only [disjCont, por] at hCBw ⊢
  rcases hCBw with hAw | hBw
  · left; exact hAw
  · left; exact hBA hBw


-- ============================================================
-- SECTION 5: Singh's Asymmetry from Economy
-- ============================================================

/-!
## Singh's Asymmetry (@cite{singh-2008})

"Mary read [A or B] or [A and B]" ✓ (weak first)
"Mary read [A and B] or [A or B]" # (strong first)

Economy derives this: `exh` on the weak disjunct is non-vacuous
(derives exclusive or), while `exh` on the strong disjunct is
vacuous (nothing to exclude).
-/

/-- **Singh weak-first**: `exh` on the weak disjunct is non-vacuous
    when `exh` genuinely excludes something. Economy is met.

    The hypothesis `h_excludes` says there is a world where the
    weak disjunct holds but neither the exhaustified weak nor the
    strong holds — this witnesses non-vacuity. -/
theorem singh_weak_exh_nonvacuous (ALT : Set (Set World))
    (weak strong : Set World)
    (h_excludes : ∃ w, weak w ∧ ¬exhIE ALT weak w ∧ ¬strong w) :
    ¬isIncrementallyVacuous ALT weak {disjCont strong} := by
  intro hvacuous
  have heq := hvacuous (disjCont strong) (Set.mem_singleton _)
  obtain ⟨w, hweak, hnexh, hnstrong⟩ := h_excludes
  have hright : disjCont strong weak w := Or.inr hweak
  have hleft : disjCont strong (exhIE ALT weak) w := (heq w).mpr hright
  rcases hleft with hstrong | hexh
  · exact hnstrong hstrong
  · exact hnexh hexh

/-- **Singh strong-first**: `exh` on the strong disjunct is vacuous
    when strong entails weak. The only alternative (weak) cannot be
    excluded because its negation contradicts the prejacent.
    Economy is violated.

    The proof constructs {strong} as the unique MC-set: adding
    ¬weak or ¬strong to the exclusion set makes it inconsistent
    (since strong entails weak, every strong-world is a weak-world). -/
theorem singh_strong_exh_vacuous (weak strong : Set World)
    (h_entails : strong ⊆ weak) :
    exhIE {weak, strong} strong = strong := by
  apply Set.Subset.antisymm
  · -- exhIE ⊆ strong: the prejacent is always in IE
    intro w hexh
    have hstrong_in_IE : strong ∈ IE {weak, strong} strong :=
      fun E hE_mc => hE_mc.1.1
    exact hexh strong hstrong_in_IE
  · -- strong ⊆ exhIE: construct the unique MC-set {strong}
    intro w hstrong_w ψ hψ_IE
    have hE₀_compat : IsCompatible {weak, strong} strong {strong} := by
      refine ⟨Set.mem_singleton _, ?_, ?_⟩
      · intro ψ' hψ'
        left; exact Set.mem_singleton_iff.mp hψ'
      · exact ⟨w, fun ψ' hψ' => Set.mem_singleton_iff.mp hψ' ▸ hstrong_w⟩
    have hE₀_maximal : IsMCSet {weak, strong} strong {strong} := by
      refine ⟨hE₀_compat, ?_⟩
      intro E' hE'_compat hE₀_sub_E' ψ' hψ'_E'
      rcases hE'_compat.2.1 ψ' hψ'_E' with hψ'_eq | ⟨a, ha_ALT, hψ'_neg⟩
      · exact Set.mem_singleton_iff.mpr hψ'_eq
      · exfalso
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha_ALT
        obtain ⟨u, hu⟩ := hE'_compat.2.2
        have hstrong_u : strong u := hu strong hE'_compat.1
        rcases ha_ALT with ha_weak | ha_strong
        · rw [ha_weak] at hψ'_neg
          have hneg_weak_u := hu ψ' hψ'_E'
          rw [hψ'_neg] at hneg_weak_u
          exact hneg_weak_u (h_entails hstrong_u)
        · rw [ha_strong] at hψ'_neg
          have hneg_strong_u := hu ψ' hψ'_E'
          rw [hψ'_neg] at hneg_strong_u
          exact hneg_strong_u hstrong_u
    rw [Set.mem_singleton_iff.mp (hψ_IE {strong} hE₀_maximal)]
    exact hstrong_w


-- ============================================================
-- SECTION 6: DE Operators and Economy
-- ============================================================

/-!
## DE Operators and Economy

A key observation: `exh` is **always** globally weakening under DE
operators. Since `exhIE` entails its prejacent (it can only
strengthen), DE reverses this, making the overall sentence weaker.

This means economy blocks `exh` under DE unless:
1. The DE scope is embedded under another DE operator (making the
   overall context UE), or
2. Two levels of `exh` are used: `exh[DE[exh(S)]]`, where the inner
   `exh` strengthens, DE reverses, and the outer `exh` strengthens
   again (§7, §10 of the paper)

The second mechanism requires **focus** on the scalar item to provide
the right alternatives for the inner `exh` — this derives the IFG.
-/

/-- A continuation is **downward-entailing** if it reverses
    entailment. -/
def isDECont (S : Continuation World) : Prop :=
  ∀ (p q : Set World), (∀ w, p w → q w) → ∀ w, S q w → S p w

/-- Negation is DE. -/
theorem negCont_is_DE : isDECont (Compl.compl (α := Set World)) := by
  intro p q hpq w hnq hp
  exact hnq (hpq w hp)

/-- The prejacent is always in IE (it belongs to every compatible
    set by definition, hence every MC-set). -/
theorem prejacent_mem_IE (ALT : Set (Set World)) (φ : Set World) :
    φ ∈ IE ALT φ :=
  fun _E hE => hE.1.1

/-- `exhIE` always entails its prejacent: exhaustification can
    only strengthen, never weaken. -/
theorem exhIE_entails_prejacent (ALT : Set (Set World))
    (φ : Set World) : exhIE ALT φ ⊆ φ :=
  fun _w h => h φ (prejacent_mem_IE ALT φ)

/-- **`exh` is always globally weakening under DE**: since
    `exhIE ALT φ ⊆ φ` and DE reverses entailment,
    `S(φ) ⊆ S(exhIE ALT φ)`.

    This is the core observation behind the IFG: embedded `exh`
    under DE operators is blocked by economy unless focus provides
    the right alternative set (via a two-level exh mechanism). -/
theorem exh_weakening_under_de (ALT : Set (Set World))
    (φ : Set World) (S_cont : Continuation World)
    (hDE : isDECont S_cont) :
    isGloballyWeakening ALT φ S_cont :=
  fun w => hDE (exhIE ALT φ) φ (exhIE_entails_prejacent ALT φ) w

/-- More IE alternatives means a stronger exhaustified meaning:
    if IE(ALT') ⊆ IE(ALT), then exhIE ALT φ ⊆ exhIE ALT' φ.
    More requirements to satisfy → fewer satisfying worlds. -/
theorem exhIE_stronger_of_more_IE (ALT ALT' : Set (Set World))
    (φ : Set World) (hIE : IE ALT' φ ⊆ IE ALT φ) :
    exhIE ALT φ ⊆ exhIE ALT' φ :=
  fun _w hexh ψ hψ => hexh ψ (hIE hψ)

/-- **Under DE, more IE alternatives weakens the global result**.
    If IE(ALT') ⊆ IE(ALT), then S(exhIE ALT' φ) ⊆ S(exhIE ALT φ).

    This captures the core of theorem (88): under DE operators,
    expanding the comparison class can only weaken the overall
    sentence. The full theorem (88) additionally handles the
    two-level exh structure `exh_{OP(S)}(OP[exh_C(S)])`, but this
    lemma is the key step. -/
theorem de_weakening_of_more_IE (S_cont : Continuation World)
    (hDE : isDECont S_cont) (ALT ALT' : Set (Set World))
    (φ : Set World) (hIE : IE ALT' φ ⊆ IE ALT φ) :
    ∀ w, S_cont (exhIE ALT' φ) w → S_cont (exhIE ALT φ) w :=
  fun w => hDE _ _ (exhIE_stronger_of_more_IE ALT ALT' φ hIE) w


-- ============================================================
-- SECTION 7: The exh–exh Prediction (§11.1)
-- ============================================================

/-!
## exh–exh: Conjunctive Readings Under Negation

A key prediction (§11.1): when `exh` appears both above and below
negation, the result is conjunctive:

  exh[¬exh(p ∨ q)] = p ∧ q

"Jack didn't talk to Mary OR Sue" (with focused `or`) yields "Jack
talked to both" — embedded exclusive disjunction under negation
always produces a conjunctive reading.

The derivation:
  exh(¬exh(p ∨ q))
  = ¬exh(p ∨ q) ∧ (p ∨ q)            [exh negates ¬(p∨q)]
  = [¬(p∨q) ∨ (p∧q)] ∧ (p∨q)         [expand ¬exh]
  = (p ∧ q)                           [simplify]
-/

section ExhExh

/-- Four worlds for two atomic propositions p, q. -/
inductive PQWorld where | pq | p_only | q_only | neither
  deriving Repr, DecidableEq, Inhabited, Fintype

open PQWorld
open Exhaustification (innocent predToFinset altsFromPreds)

private def p_or_q : PQWorld → Bool
  | pq | p_only | q_only => true | neither => false
private def p_and_q : PQWorld → Bool
  | pq => true | _ => false

/-- exh(p ∨ q) = exclusive or (with alternatives {p∨q, p∧q}). -/
theorem exh_p_or_q_is_exclusive :
    innocent.exh (altsFromPreds [p_or_q, p_and_q]) (predToFinset p_or_q) =
    predToFinset (fun w => p_or_q w && !p_and_q w) := by decide

/-- ¬exh(p ∨ q): "both or neither". -/
private def neg_exh_p_or_q : PQWorld → Bool :=
  fun w => decide (w ∉ innocent.exh (altsFromPreds [p_or_q, p_and_q]) (predToFinset p_or_q))

/-- ¬(p ∨ q): "neither". -/
private def neg_p_or_q : PQWorld → Bool
  | neither => true | _ => false

/-- **The exh–exh prediction**: exh[¬exh(p∨q)] = p∧q.

    The higher `exh` has alternatives {¬exh(p∨q), ¬(p∨q)}, where
    ¬(p∨q) is the version without the lower `exh`. Since ¬(p∨q) is
    strictly stronger, it is innocently excludable. Negating it
    adds (p∨q), which combined with ¬exh(p∨q) gives p∧q. -/
theorem exh_exh_conjunctive :
    innocent.exh (altsFromPreds [neg_exh_p_or_q, neg_p_or_q]) (predToFinset neg_exh_p_or_q) =
    predToFinset p_and_q := by decide

end ExhExh


-- ============================================================
-- SECTION 8: Bridge to Symmetry
-- ============================================================

/-!
## Economy and the Symmetry Problem

Economy interacts with the symmetry problem indirectly. When
symmetric alternatives S₁, S₂ are the only non-weaker alternatives,
`exh` is vacuous (`symmetric_exhB_vacuous` in `Symmetry.lean`).
Vacuous `exh` violates economy, so the grammar rejects the parse
rather than producing wrong results.

Economy and structural complexity are **complementary**:
- @cite{katzir-2007} determines *which* alternatives enter the set
  → breaks symmetry → `exh` derives the correct SI
- Economy determines *whether* `exh` is licensed given those
  alternatives → blocks vacuous/weakening insertions
-/

/-- Vacuous `exhIE` violates economy: if `exhIE = φ`, then `exh`
    is incrementally vacuous for all extensional continuations, so
    economy is not met.

    The extensionality assumption (pointwise-equivalent inputs
    produce pointwise-equivalent outputs) holds for all natural
    language continuations: negation, quantifier restrictors,
    coordination, etc. -/
theorem vacuous_violates_economy (ALT : Set (Set World))
    (φ : Set World) (conts : Set (Continuation World))
    (_hne : conts.Nonempty)
    (hvac : exhIE ALT φ = φ)
    (hext : ∀ C ∈ conts, ∀ (p q : Set World),
      (∀ w, p w ↔ q w) → ∀ w, C p w ↔ C q w) :
    ¬economyConditionMet ALT φ conts := by
  intro ⟨hnv, _⟩
  apply hnv
  intro C hC w
  exact hext C hC (exhIE ALT φ) φ (fun w => Iff.of_eq (congrFun hvac w)) w


end Phenomena.ScalarImplicatures.Studies.FoxSpector2018
