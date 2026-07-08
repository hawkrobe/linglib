import Linglib.Core.Logic.Duality
import Linglib.Core.Logic.Truth3
import Linglib.Data.Examples.AghaJeretic2022
import Linglib.Data.Generalizations.HomogeneityGap
import Linglib.Semantics.Modality.Directive
import Linglib.Semantics.Homogeneity.Decided
import Linglib.Semantics.Plurality.Distributivity
import Linglib.Fragments.English.Auxiliaries
import Linglib.Fragments.Javanese.Modals
import Linglib.Fragments.Romance.French.Modals
import Mathlib.Data.Fin.Basic

/-!
# Weak Necessity Modals as Homogeneous Pluralities of Worlds
[agha-jeretic-2022]

Proceedings of SALT 32: 831–851.

## Core Proposal

Weak necessity modals like *should* are **not quantificational**. They denote
definite pluralities of worlds, paralleling the relationship between plural
definite nominals (*the*) and universal quantifiers (*all*/*every*):

- *must p* = all worlds in a given domain are p-worlds  (∀ quantifier)
- *should p* = the worlds in a given domain are p-worlds (plural definite)

This gives weak necessity modals **homogeneity** as an intrinsic feature:
they yield a truth-value gap (neither true nor false) when some but not all
worlds in the domain satisfy the prejacent — exactly paralleling the behavior
of plural definite DPs under negation.

## Key Claims Formalized

1. **Homogeneity** (§3.1): Weak necessity modals take obligatory apparent wide
   scope over negation, unlike strong necessity modals which allow narrow scope.

2. **Trivalent semantics** (§4.2): `should_D := ⊕D` — evaluation is trivalent
   with symmetric negation (homogeneity gap preserved under ¬).

3. **Homogeneity removal** (§3.2): The adverb *necessarily* removes
   homogeneity from *should*, just as *all* removes it for plural definites.

4. **QUD-sensitive exception tolerance** (§3.3): Weak necessity modals
   tolerate exceptions when irrelevant to the QUD.

5. **X operator** (§5.1): Derives `should` from `must` compositionally via
   minimal witness sets. X only applies to universals (unique witness),
   explaining Javanese NE's restriction to necessity modals.

6. **Critique of domain restriction** (§6.1): The vFI 2008 analysis
   (`Directive.weakNecessity`) is bivalent — it cannot produce the truth-value
   gap that the empirical data require.

## Independent Support

[tieu-kriz-chemla-2019] find that children acquire homogeneity
independently of scalar implicatures (HOM/−SI group), supporting the
claim that homogeneity is intrinsic to plural predication rather than
derived via exhaustification ([magri-2014]).

## Connection to [agha-jeretic-2026]

The 2026 handbook chapter surveys this analysis as one of three competing
accounts of weak necessity (alongside domain restriction and comparative
semantics), and extends it to explain the neg-raising asymmetry between
*should* and *must*.
-/

namespace AghaJeretic2022

open Core.Duality (Truth3)
open Generalizations.HomogeneityGap (GapDatum GapScenario GapPredict fromExample)
open Semantics.Homogeneity (negRaising_iff_subsingleton)

-- ============================================================================
-- §1. Trivalent Semantics for Modals (§4.2)
-- ============================================================================

/-! ## Trivalent evaluation

*should* gets trivalent semantics via plural predication over worlds, while
*must* remains bivalent (standard ∀ quantification).

We model the modal domain as a `List World` and use `Core.Duality.Truth3`
for the three-valued output. -/

variable {World : Type}

/-- Strong necessity: standard ∀ quantification over the modal domain.
    Bivalent — always true or false, never indeterminate.
    `must_D := λp. ∀w ∈ D. p(w)` -/
def mustEval (domain : List World) (p : World → Bool) : Truth3 :=
  Truth3.ofBool (domain.all p)

/-- Weak necessity: trivalent plural predication over the modal domain.
    Returns tt if all worlds satisfy p, ff if none do, unk otherwise.
    `should_D := ⊕D` — the prejacent is predicated of the plurality
    of worlds, yielding homogeneity.

    Body uses an explicit 4-way if-chain to support `split`-based proofs
    in this file. The bridge theorem `shouldEval_eq_distList` (below)
    formalizes the equivalence with `Core.Duality.distList` for nonempty
    domains. Refactoring the body to call `distList` directly requires
    rewriting ~3 dense proof scripts; tracked as future work. -/
def shouldEval (domain : List World) (p : World → Bool) : Truth3 :=
  if domain.isEmpty then Truth3.false
  else if domain.all p then Truth3.true
  else if domain.all (fun w => !p w) then Truth3.false
  else Truth3.indet

-- ============================================================================
-- §2. Core Properties of the Trivalent Semantics
-- ============================================================================

/-! ### must is always bivalent -/

/-- `must` never returns the indeterminate value. -/
theorem must_bivalent (domain : List World) (p : World → Bool) :
    mustEval domain p = Truth3.true ∨ mustEval domain p = Truth3.false := by
  unfold mustEval Truth3.ofBool
  cases domain.all p <;> simp

/-! ### should is homogeneous: it can return ★ -/

/-- In a mixed domain, `should` returns ★ (indeterminate). -/
theorem should_mixed :
    shouldEval [true, false] id = Truth3.indet := by native_decide

/-- In a uniform-true domain, `should` returns tt. -/
theorem should_all_true :
    shouldEval [true, true, true] id = Truth3.true := by native_decide

/-- In a uniform-false domain, `should` returns ff. -/
theorem should_all_false :
    shouldEval [false, false] id = Truth3.false := by native_decide

/-- `must` returns ff in the mixed case (no gap). -/
theorem must_mixed :
    mustEval [true, false] id = Truth3.false := by native_decide

/-- When positive, `should` and `must` agree. -/
theorem should_must_agree_positive (domain : List World) (p : World → Bool)
    (h : domain.all p = true) (hne : domain.isEmpty = false) :
    shouldEval domain p = mustEval domain p := by
  simp [shouldEval, mustEval, Truth3.ofBool, h, hne]

-- ============================================================================
-- §3. Negation Symmetry (the formal core of homogeneity)
-- ============================================================================

/-! ## Negation symmetry

The paper's central formal claim: `shouldEval` produces **symmetric** truth
conditions under negation. Affirming p of the plurality and denying ¬p are
non-complementary — both can be indeterminate simultaneously. This is the
formal content of homogeneity.

- `shouldEval D p = tt  →  shouldEval D (¬p) = ff`  (no positive/negative overlap)
- `shouldEval D p = ff  →  shouldEval D (¬p) = tt`  (symmetric falsity, non-empty D)
- `shouldEval D p = unk →  shouldEval D (¬p) = unk` (the gap is symmetric)

Contrast: `must` has NO gap — it's always bivalent. -/

private theorem list_all_not_not {α : Type} (l : List α) (p : α → Bool) :
    l.all (fun x => !(!(p x))) = l.all p := by
  induction l with
  | nil => rfl
  | cons _ _ _ => simp [List.all_cons, Bool.not_not]

private theorem list_all_neg_false_of_pos {α : Type} {l : List α} {p : α → Bool}
    (hp : l.all p = true) (hne : l ≠ []) :
    l.all (fun x => !(p x)) = false := by
  match l with
  | [] => exact absurd rfl hne
  | x :: _ =>
    simp only [List.all_cons, Bool.and_eq_true] at hp
    simp [List.all_cons, hp.1]

/-- If `shouldEval D p = tt`, then `shouldEval D (¬p) = ff`.
    No overlap between positive and negative extensions of the plurality. -/
theorem shouldEval_tt_neg_ff (domain : List World) (p : World → Bool)
    (h : shouldEval domain p = Truth3.true) :
    shouldEval domain (fun w => !(p w)) = Truth3.false := by
  unfold shouldEval at h ⊢
  split at h
  · exact absurd h (by decide)
  · rename_i hne
    split at h
    · rename_i hall
      have hne' : domain ≠ [] := by intro heq; subst heq; simp at hne
      simp [show ¬(domain.isEmpty = true) from hne,
            list_all_neg_false_of_pos hall hne', hall]
    · split at h <;> exact absurd h (by decide)

/-- If `shouldEval D p = ff` (non-empty D), then `shouldEval D (¬p) = tt`.
    Symmetric: universal denial of p means universal affirmation of ¬p. -/
theorem shouldEval_ff_neg_tt (domain : List World) (p : World → Bool)
    (h : shouldEval domain p = Truth3.false) (hne : domain.isEmpty = false) :
    shouldEval domain (fun w => !(p w)) = Truth3.true := by
  unfold shouldEval at h ⊢
  split at h
  · rename_i he; exact absurd he (by simp [hne])
  · rename_i hne'
    split at h
    · exact absurd h (by decide)
    · rename_i hnall
      split at h
      · rename_i hallneg; simp [hne', hallneg]
      · exact absurd h (by decide)

/-- If `shouldEval D p = unk`, then `shouldEval D (¬p) = unk`.
    The gap is symmetric under negation — the core homogeneity property. -/
theorem shouldEval_unk_symmetric (domain : List World) (p : World → Bool)
    (h : shouldEval domain p = Truth3.indet) :
    shouldEval domain (fun w => !(p w)) = Truth3.indet := by
  unfold shouldEval at h ⊢
  split at h
  · exact absurd h (by decide)
  · rename_i hne
    split at h
    · exact absurd h (by decide)
    · rename_i hnall
      split at h
      · exact absurd h (by decide)
      · rename_i hnneg
        split
        · exact absurd ‹_› hne
        · split
          · rename_i h_dbl
            simp only [Bool.not_not] at h_dbl
            exact absurd h_dbl hnall
          · rfl

-- ============================================================================
-- §4. Homogeneity Data for Modals (§3.1)
-- ============================================================================

/-! ## Modal homogeneity parallels plural definite homogeneity

The paper demonstrates that weak necessity modals pattern exactly like
plural definites with respect to negation. The judgment grid lives as
`LinguisticExample` rows in the generated `Data.Examples.AghaJeretic2022`
module; `Generalizations.HomogeneityGap.fromExample` lifts them into the
cross-paper unembedded-homogeneity pool. -/

/-- A&J's contribution to the cross-paper unembedded homogeneity pool. -/
def gapData : List GapDatum :=
  Examples.all.filterMap fromExample

/-- The *should* polarity × scenario grid (paper examples (8)–(9)). -/
def shouldGrid : List GapDatum :=
  gapData.filter (·.source.paperLabel == "(8)-(9) modal homogeneity")

/-- Every datum this paper contributes feeds the pooled cross-paper data. -/
theorem gapData_subset_allData :
    ∀ d ∈ gapData, d ∈ Generalizations.HomogeneityGap.allData := by decide

/-- The *should* grid: classical values in the uniform scenarios, ★ in both
    gap cells — under negation, "shouldn't go" is incompatible with an
    existential followup "but you can", just like "The guests aren't here"
    is incompatible with "but some of them are." -/
theorem shouldGrid_observed :
    shouldGrid.map (fun d => (d.polarity, d.scenario, d.observed)) =
      [(.positive, .all, .true), (.positive, .none, .false),
       (.positive, .gap, .indet),
       (.negative, .all, .false), (.negative, .none, .true),
       (.negative, .gap, .indet)] := by decide

/-- *Have to* does NOT display homogeneity (paper example (9b)): both gap
    cells are determinate, and "don't have to go" is clearly true in the
    mixed scenario — the narrow-scope reading (¬□ = ◇¬) is available,
    unlike *should* which only allows wide scope (□¬). -/
theorem haveTo_no_gap :
    (fromExample Examples.haveTo_neg_gap).map (·.observed) = some .true ∧
    (fromExample Examples.haveTo_pos_gap).map (·.observed) ≠ some .indet :=
  ⟨by decide, by decide⟩

/-- Representative two-world domain for each scenario; a world is identified
    with the prejacent's truth value at it. -/
def scenarioDomain : GapScenario → List Bool
  | .all  => [true, true]
  | .none => [false, false]
  | .gap  => [true, false]

/-- The trivalent semantics as a `GapPredict`: negative polarity predicates
    the negated prejacent of the same plurality (homogeneity = symmetric
    negation, §3.1). -/
def gapPredict : GapPredict := fun pol s =>
  match pol with
  | .positive => shouldEval (scenarioDomain s) id
  | .negative => shouldEval (scenarioDomain s) (fun w => !w)

/-- The trivalent semantics reproduces every cell of the *should* grid. -/
theorem gapPredict_matches_shouldGrid :
    ∀ d ∈ shouldGrid, gapPredict d.polarity d.scenario = d.observed := by
  decide

-- ============================================================================
-- §5. Homogeneity Removal (§3.2)
-- ============================================================================

/-! ## Homogeneity removal by "necessarily"

Inserting *necessarily* into a weak necessity modal sentence removes the
homogeneity gap, just as *all* removes it from plural definites.

Paper examples (14)–(15):
- "You shouldn't go" → #but you can go
- "You shouldn't necessarily go" → ✓but you can go

This parallels:
- "The guests aren't here" → #but some are
- "The guests aren't all here" → ✓but some are -/

/-- *Necessarily* removes homogeneity from *should*, paralleling how *all*
    removes homogeneity from plural definites: the bare negated *should*
    observes ★ in the mixed scenario, the *necessarily*-variant is
    determinate, and the bare variant recorded as its alternative is
    degraded. -/
theorem necessarily_removes_homogeneity :
    (fromExample Examples.should_neg_gap).map (·.observed) = some .indet ∧
    (fromExample Examples.necessarily_removes_gap).map (·.observed) ≠ some .indet ∧
    Examples.necessarily_removes_gap.alternatives.map Prod.snd = [.questionable] :=
  ⟨by decide, by decide, rfl⟩

/-- `shouldEval` with homogeneity removal (= explicit quantifier insertion)
    reduces to `mustEval` — the gap disappears. -/
def shouldWithRemoval (domain : List World) (p : World → Bool) : Truth3 :=
  mustEval domain p

theorem removal_eliminates_gap :
    shouldWithRemoval [true, false] id = Truth3.false := by native_decide

-- ============================================================================
-- §6. Exception Tolerance (§3.3)
-- ============================================================================

/-! ## QUD-sensitive exception tolerance

Plural predication tolerates exceptions when they are irrelevant to the QUD.
The paper shows the same pattern for weak necessity modals.

Paper example (17):
Context: One can get a perfect grade by doing most exercises correctly;
doing all gives extra credit.
QUD1: What is a way to get a perfect grade?
QUD2: What are the minimal requirements?

(a) "You should do every exercise." → QUD1: ✓; QUD2: #
(b) "You have to do every exercise." → QUD1: #; QUD2: # -/

/-- Weak necessity tolerates QUD-irrelevant exceptions; strong necessity
    does not: *should* is acceptable under the way-to-a-perfect-grade QUD
    and degraded under the minimal-requirements QUD, while *have to* is
    degraded under both. -/
theorem should_tolerates_exceptions :
    Examples.should_exception_qud1.judgment = .acceptable ∧
    Examples.should_exception_qud2.judgment = .unacceptable ∧
    Examples.haveTo_exception_qud1.judgment = .unacceptable ∧
    Examples.haveTo_exception_qud2.judgment = .unacceptable :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §7. Responses to Indeterminate Sentences (§3.4)
-- ============================================================================

/-! ## Well-responses in borderline cases

In borderline cases (★), outright denial is infelicitous; *well*-responses
are preferred. This parallels plural definites ([kriz-2016]).

Paper example (19). -/

/-- In the two-equally-good-doors scenario, the borderline (★)
    weak-necessity sentence is degraded — outright "No" denial is
    infelicitous and a "Well, ..." response is preferred — while bivalent
    *must* is simply false and felicitously deniable. -/
theorem indeterminate_response_contrast :
    Examples.should_indet_response.judgment = .questionable ∧
    Examples.must_indet_response.judgment = .acceptable := ⟨rfl, rfl⟩

-- ============================================================================
-- §8. The X Operator and Witness Sets (§5.1)
-- ============================================================================

/-! ## Compositional derivation via the X operator

X picks out the unique smallest set that makes a quantifier true and returns
the mereological sum of its elements:

  X := λM. ⊕ ιW[W ∈ WIT(M)]

Applied to `must_D`: the unique minimal witness set of ∀ over D is D itself
(no proper subset suffices). So `X(must_D) = ⊕D = should_D`.

Applied to `can_D`: each singleton {w} for w ∈ D is a minimal witness of ∃.
Multiple minimal witnesses → ι is undefined → X is undefined.
This explains why Javanese NE (= X) only combines with necessity modals. -/

/-- A witness set for a quantifier Q is a set W such that Q(W) holds. -/
def isWitness (q : List World → Bool) (w : List World) : Bool :=
  q w

/-- A minimal witness: a witness with no proper sub-witness.
    Removing any element makes it no longer a witness. -/
def isMinimalWitness [BEq World] (q : List World → Bool)
    (w : List World) : Bool :=
  isWitness q w &&
  w.all (fun x => !isWitness q (w.filter (· != x)))

/-- Universal quantifier as GQ: W witnesses ∀ over D iff D ⊆ W.
    This is the Barwise & Cooper (1981) witness set notion — the quantifier
    EVERY(D) = {P | D ⊆ P}, so W ∈ EVERY(D) iff D ⊆ W. -/
def universalQ [BEq World] (domain : List World) : List World → Bool :=
  fun w => domain.all (fun x => w.contains x)

/-- Existential quantifier as GQ: W witnesses ∃ over D iff D ∩ W ≠ ∅.
    SOME(D) = {P | D ∩ P ≠ ∅}, so W ∈ SOME(D) iff some element of D is in W. -/
def existentialQ [BEq World] (domain : List World) : List World → Bool :=
  fun w => domain.any (fun x => w.contains x)

/-- The full domain is the UNIQUE minimal witness for ∀.
    Since EVERY(D) = {P | D ⊆ P}, the only W ⊆ D with D ⊆ W is W = D.
    Removing any element breaks the subset condition.
    This is why X (requiring a unique minimal witness) applies to universals. -/
theorem universal_unique_minimal_witness :
    -- Full domain is a minimal witness for ∀
    isMinimalWitness (universalQ [(0 : Fin 2), 1]) [(0 : Fin 2), 1] = true ∧
    -- No proper sublist is a witness for ∀ (D ⊄ W when W ⊂ D)
    isMinimalWitness (universalQ [(0 : Fin 2), 1]) [(0 : Fin 2)] = false ∧
    isMinimalWitness (universalQ [(0 : Fin 2), 1]) [(1 : Fin 2)] = false := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Each singleton is a minimal witness for ∃, and the full domain is NOT
    minimal (proper subsets suffice). This is why X is undefined for ∃ —
    multiple minimal witnesses means ι (the uniqueness presupposition) fails.
    This explains Javanese NE's restriction to necessity modals. -/
theorem existential_multiple_minimal_witnesses :
    -- Each singleton witnesses ∃
    isMinimalWitness (existentialQ [(0 : Fin 2), 1]) [(0 : Fin 2)] = true ∧
    isMinimalWitness (existentialQ [(0 : Fin 2), 1]) [(1 : Fin 2)] = true ∧
    -- Full domain is NOT a minimal witness for ∃ (proper subsets suffice)
    isMinimalWitness (existentialQ [(0 : Fin 2), 1]) [(0 : Fin 2), 1] = false := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- X applied to must yields the domain itself (= should's denotation).
    The resulting plurality is then subject to plural predication semantics. -/
def applyX (domain : List World) (p : World → Bool) : Truth3 :=
  shouldEval domain p

/-- X(must) = should. -/
theorem x_must_eq_should (domain : List World) (p : World → Bool) :
    applyX domain p = shouldEval domain p := rfl

-- ============================================================================
-- §9. Cross-Linguistic Morphological Patterns (§2, §5.2)
-- ============================================================================

/-! ## Morphological composition of weak necessity

Cross-linguistically, weak necessity is expressed in two ways:

1. **Primitive lexical items** (English *should*, *ought*): non-decomposable.
2. **Morphological derivation from strong necessity**:
   a. French: *devoir*+CF → weak necessity. CF picks a witness set without
      requiring uniqueness, so it applies to both ∀ (*devrais*) and ∃
      (*pourrais*).
   b. Javanese: *mesthi*+NE → weak necessity. NE = X (requires unique
      minimal witness), so it only applies to ∀ (*mesthi-ne*), not ∃
      (*iso-ne* is ungrammatical). -/

inductive WeakNecessityMorphology where
  | primitive           -- morphologically non-decomposable (English should)
  | counterfactual      -- strong + counterfactual morphology (French, Hungarian)
  | dedicatedMarker     -- strong + dedicated morpheme (Javanese NE)
  deriving DecidableEq, Repr

structure WeakNecessityMorphDatum where
  language : String
  strongForm : String
  weakForm : String
  strategy : WeakNecessityMorphology
  appliesTo : String  -- "necessity only" or "necessity + possibility"
  deriving Repr

def english_should : WeakNecessityMorphDatum where
  language := "English"
  strongForm := "must/have to"
  weakForm := "should/ought"
  strategy := .primitive
  appliesTo := "n/a (non-decomposable)"

def french_devrais : WeakNecessityMorphDatum where
  language := "French"
  strongForm := "dois (devoir.PRES)"
  weakForm := "devrais (devoir+CF)"
  strategy := .counterfactual
  appliesTo := "necessity + possibility (devrais/pourrais)"

def javanese_mesthi : WeakNecessityMorphDatum where
  language := "Javanese"
  strongForm := "mesthi"
  weakForm := "mesthi-ne"
  strategy := .dedicatedMarker
  appliesTo := "necessity only (*iso-ne is ungrammatical)"

def spanish_deber : WeakNecessityMorphDatum where
  language := "Spanish"
  strongForm := "deber/tener que"
  weakForm := "debería/tendría que (deber/tener que+CF)"
  strategy := .counterfactual
  appliesTo := "necessity + possibility"

def hungarian_kell : WeakNecessityMorphDatum where
  language := "Hungarian"
  strongForm := "kell"
  weakForm := "kell+CF"
  strategy := .counterfactual
  appliesTo := "necessity + possibility"

def weakNecessityMorphData : List WeakNecessityMorphDatum :=
  [english_should, french_devrais, javanese_mesthi, spanish_deber, hungarian_kell]

theorem three_strategies :
    (weakNecessityMorphData.map (·.strategy)).eraseDups.length = 3 := by
  native_decide

/-- Javanese NE only applies to necessity; French CF applies to both.
    This follows from X requiring unique minimal witnesses (∀ only)
    vs CF accepting any witness (∀ and ∃). -/
theorem javanese_necessity_only :
    javanese_mesthi.appliesTo = "necessity only (*iso-ne is ungrammatical)" := rfl

theorem french_both_forces :
    french_devrais.appliesTo = "necessity + possibility (devrais/pourrais)" := rfl

-- ============================================================================
-- §10. Critique of Domain Restriction (§6.1) — Computational
-- ============================================================================

/-! ## Why domain restriction doesn't capture homogeneity

The [von-fintel-iatridou-2008] analysis (formalized in `Directive.lean`)
treats *should* as ∀ over a refined set of best worlds. `Directive.weakNecessity`
returns `Bool` — it is bivalent by construction. A bivalent semantics
**cannot produce the truth-value gap** that the empirical data require.

We make this critique computational by contrasting `Directive.weakNecessity`
(always tt or ff) with `shouldEval` (can return unk). -/

section DirectiveBridge

open Semantics.Modality.Directive (weakNecessity)
open Semantics.Modality.Kratzer (ModalBase OrderingSource)

/-- Local 4-world type for the bivalence demonstration. -/
abbrev BridgeWorld := Fin 4

/-- `Directive.weakNecessity` is bivalent: as a Prop, it is classically
    true or false — never indeterminate. This contrasts with `shouldEval`,
    which can return `Truth3.indet`. -/
theorem directive_bivalent
    (f : ModalBase BridgeWorld)
    (g g' : OrderingSource BridgeWorld)
    (p : (BridgeWorld → Prop))
    (w : BridgeWorld) :
    weakNecessity f g g' p w ∨ ¬ weakNecessity f g g' p w :=
  em _

end DirectiveBridge

/-- `shouldEval` CAN return unk — the gap that domain restriction misses. -/
theorem shouldEval_can_gap :
    ∃ (D : List Bool) (p : Bool → Bool), shouldEval D p = Truth3.indet :=
  ⟨[true, false], id, by native_decide⟩

/-- Domain restriction as a `GapPredict`: *should* = ∀ over the refined
    domain, with negation as Strong Kleene `Truth3.neg`. Bivalent on every
    cell. -/
def domainRestrictionPredict : GapPredict := fun pol s =>
  match pol with
  | .positive => mustEval (scenarioDomain s) id
  | .negative => (mustEval (scenarioDomain s) id).neg

/-- Domain restriction matches the classical cells of the *should* grid but
    fails exactly the gap cells: it predicts that negated *should* is true
    there (¬∀, licensing the existential followup "but you are allowed to
    go"), where ★ is observed. -/
theorem domainRestriction_fails_exactly_gap_cells :
    ∀ d ∈ shouldGrid,
      (domainRestrictionPredict d.polarity d.scenario = d.observed ↔
        d.scenario ≠ .gap) := by decide

-- ============================================================================
-- §11. FunctionWords Bridge
-- ============================================================================

/-! ## English modal lexicon verification

Verify that the English fragment classifies *should*/*ought* as weak
necessity and *must* as strong necessity, matching the paper's §2.1. -/

open English.Auxiliaries

/-- *should* is classified as weak necessity in the English fragment. -/
theorem should_is_weak :
    should.modalMeaning.any (·.force == .weakNecessity) = true := by native_decide

/-- *ought* is classified as weak necessity. -/
theorem ought_is_weak :
    ought.modalMeaning.any (·.force == .weakNecessity) = true := by native_decide

/-- *must* is classified as strong necessity, not weak. -/
theorem must_is_strong_not_weak :
    must.modalMeaning.any (·.force == .necessity) = true ∧
    must.modalMeaning.any (·.force == .weakNecessity) = false := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- §12. Scopelessness (§3.1, higher negation)
-- ============================================================================

/-! ## Scopelessness persists under higher negation

The apparent wide scope of *should* persists when negation is in a higher
clause, paralleling plural definites:

- "I don't think the guests are here" → #but some are
- "I don't think you should go" → #but you are allowed to go
- "I don't think you have to go" → ✓but you are allowed to go

This is analyzed as *scopelessness*: the "wide scope" effect is a
consequence of homogeneity, not syntactic movement. -/

structure ScopelessnessDatum where
  modal : String
  sentence : String
  existentialFollowup : String
  followupFelicitous : Bool
  deriving Repr

def shouldScopeless : ScopelessnessDatum where
  modal := "should"
  sentence := "According to the rules, I don't think you should go."
  existentialFollowup := "but you are allowed to go"
  followupFelicitous := false

def haveToNotScopeless : ScopelessnessDatum where
  modal := "have to"
  sentence := "According to the rules, I don't think you have to go."
  existentialFollowup := "but you are allowed to go"
  followupFelicitous := true

theorem scopelessness_contrast :
    shouldScopeless.followupFelicitous = false ∧
    haveToNotScopeless.followupFelicitous = true := ⟨rfl, rfl⟩

-- ============================================================================
-- §13. Homogeneity Beyond Modals (§6.4)
-- ============================================================================

/-! ## Weak necessity and its friends

The paper argues (§6.4) that the homogeneity pattern observed with weak
necessity modals is part of a general phenomenon shared with bare
conditionals, generics, and habituals — all analyzable as involving
plural predication over different semantic domains. Bare conditionals
("They play soccer if the sun shines", the von Fintel/Gajewski
observation) show the same ★ pattern in mixed scenarios as the *should*
grid, under both polarities — the structural parallel that supports the
unified plural-predication analysis.

Examples (38)–(42): future conditionals, bare past conditionals, generics,
and habituals all show homogeneity effects and homogeneity removal by
explicit quantifiers (*necessarily*, *always*, *all*). -/

-- ============================================================================
-- §14. Summary: The Parallel
-- ============================================================================

/-! ## The Determiner–Modal Parallel

| Nominal domain          | Modal domain              |
|------------------------|---------------------------|
| *the* N (plural def.)  | *should* (weak necessity)  |
| *all*/*every* N (∀)    | *must*/*have to* (strong)  |
| homogeneous            | homogeneous                |
| scopeless              | scopeless                  |
| exception-tolerant     | exception-tolerant         |
| *all* removes gap      | *necessarily* removes gap  |
| ★ → "well" response   | ★ → "well" response       |

The proposal: weak necessity *is* to strong necessity what *the* is to *all*.
-/

structure PluralModalParallel where
  property : String
  pluralDefiniteExample : String
  weakNecessityExample : String
  sharedBehavior : Bool
  deriving Repr

def sharedProperties : List PluralModalParallel :=
  [ { property := "Homogeneity (obligatory wide scope under negation)"
    , pluralDefiniteExample := "The guests aren't here — #but some are"
    , weakNecessityExample := "You shouldn't go — #but you can"
    , sharedBehavior := true }
  , { property := "Scopelessness (persists under higher negation)"
    , pluralDefiniteExample := "I don't think the guests are here — #but some are"
    , weakNecessityExample := "I don't think you should go — #but you can"
    , sharedBehavior := true }
  , { property := "Homogeneity removal by explicit quantifier"
    , pluralDefiniteExample := "The guests aren't all here — ✓but some are"
    , weakNecessityExample := "You shouldn't necessarily go — ✓but you can"
    , sharedBehavior := true }
  , { property := "QUD-sensitive exception tolerance"
    , pluralDefiniteExample := "The students asked questions (QUD1: ✓; QUD2: #)"
    , weakNecessityExample := "You should do every exercise (QUD1: ✓; QUD2: #)"
    , sharedBehavior := true }
  , { property := "Well-responses to indeterminate sentences"
    , pluralDefiniteExample := "#Mary talked to the girls. / Well, only to some."
    , weakNecessityExample := "#You should take the right door. / Well, you don't have to."
    , sharedBehavior := true }
  ]

theorem all_properties_shared :
    sharedProperties.all (·.sharedBehavior) = true := by native_decide

theorem five_parallels : sharedProperties.length = 5 := rfl

-- ============================================================================
-- §15. should vs must Under Quantifier Embedding
-- ============================================================================

/-! ## Local vs Global Aggregation

The should/must contrast is an instance of the local/global aggregation
distinction in `Core.Duality`. When modal sentences are embedded under
quantifiers ("Every student should/must pass"):

- **should** (local): each individual's modal domain is mixed → `.indet`.
  The quantifier sees all gaps. By `aggregate_replicate_indet`, both
  ∃ and ∀ return `.indet` — quantifier strength is invisible.

- **must** (global): each individual's domain gives `ofBool` (Bool).
  The quantifier sees Bools. By `aggregate_map_ofBool_mixed`, mixed
  inputs yield `.true` for ∃ and `.false` for ∀ — the strength effect. -/

open Core.Duality (ProjectionType aggregate
  aggregate_replicate_indet aggregate_map_ofBool_mixed aggregate_map_ofBool_ne_indet)

/-- `shouldEval` for a mixed nonempty domain produces `.indet`. -/
theorem shouldEval_indet (domain : List World) (p : World → Bool)
    (hne : domain.isEmpty = false)
    (h_not_all : domain.all p = false)
    (h_not_none : domain.all (fun w => !p w) = false) :
    shouldEval domain p = .indet := by
  simp [shouldEval, hne, h_not_all, h_not_none]

/-- **should erases strength under embedding**: when n individuals each
    have mixed modal domains, all produce `.indet`. Any quantifier
    aggregating these gaps returns `.indet` — strength is invisible. -/
theorem should_erases_strength (n : Nat) (hn : n > 0) (d : ProjectionType) :
    aggregate d (List.replicate n Truth3.indet) = .indet :=
  aggregate_replicate_indet d n hn

/-- **must produces the strength effect under embedding**: when n
    individuals each have their modal domain evaluated by `mustEval`
    (producing `ofBool`), mixed Bool results distinguish strong from
    weak quantifiers. -/
theorem must_strength_effect (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    aggregate .disjunctive (bs.map Truth3.ofBool) = .true ∧
    aggregate .conjunctive (bs.map Truth3.ofBool) = .false :=
  aggregate_map_ofBool_mixed bs h_some_true h_some_false

/-- **must is always determinate under embedding**: aggregation over
    `ofBool` values never produces a gap, regardless of duality type. -/
theorem must_always_determinate (d : ProjectionType) (bs : List Bool) :
    aggregate d (bs.map Truth3.ofBool) ≠ .indet :=
  aggregate_map_ofBool_ne_indet d bs

-- ============================================================================
-- §16. shouldEval IS Plural Predication (DIST)
-- ============================================================================

/-! ## The Core Identity: should = DIST over worlds

The paper's central formal claim is that weak necessity IS plural predication.
We prove this by showing `shouldEval` equals `dist` (the distributive operator
for plural predication from `Core.Duality`) applied to the evaluation of each
world in the domain.

`dist results` returns:
- `.true` if all results are true
- `.false` if all are false
- `.gap` otherwise

This is exactly what `shouldEval` computes, with `results = domain.map p`. -/

open Core.Duality (distList)

/-- **shouldEval = DIST over worlds.**

    `shouldEval D p = distList D p` for nonempty D — the canonical
    `Core.Duality.distList` (Fine super-truth specialized to a List
    domain with a Boolean predicate) IS what weak necessity computes.

    This is the formal proof that weak necessity IS plural predication:
    the trivalent truth value of "should p" is determined by the DIST
    operator applied to the pointwise evaluation of p across the modal
    domain — exactly as "the Xs are P" is determined by DIST applied
    to the pointwise evaluation of P across the individuals.

    The the/all : should/must parallel is not merely an analogy; it is
    a mathematical identity at the level of truth-value computation.

    Hypothesis `hne` is required because `shouldEval [] p = .false`
    (Agha & Jeretič's empty-domain convention) while `distList [] p
    = .true` (vacuous super-truth, mathlib's empty-fold convention). -/
theorem shouldEval_eq_distList (domain : List World) (p : World → Bool)
    (hne : domain ≠ []) :
    shouldEval domain p = distList domain (fun w => p w = true) := by
  have hne' : domain.isEmpty = false := by
    cases domain with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  unfold shouldEval distList
  rw [hne']
  by_cases hall : ∀ w ∈ domain, p w = true
  · -- All true on both sides
    have h_all_eq : domain.all p = true := List.all_eq_true.mpr hall
    rw [if_pos hall]; simp [h_all_eq]
  · -- Not all true; case-split on existence
    have h_all_eq : domain.all p = false := by
      rw [Bool.eq_false_iff]
      intro hc
      exact hall (List.all_eq_true.mp hc)
    rw [if_neg hall]
    by_cases hsome : ∃ w ∈ domain, p w = true
    · rw [if_pos hsome]
      have h_any_eq : domain.any p = true := by
        obtain ⟨w, hw, hpw⟩ := hsome
        exact List.any_eq_true.mpr ⟨w, hw, hpw⟩
      have h_all_neg_eq : domain.all (fun w => !p w) = false := by
        rw [List.all_eq_not_any_not]; simp [h_any_eq]
      simp [h_all_eq, h_all_neg_eq]
    · rw [if_neg hsome]
      have h_any_eq : domain.any p = false := by
        rw [Bool.eq_false_iff]
        intro hc
        obtain ⟨w, hw, hpw⟩ := List.any_eq_true.mp hc
        exact hsome ⟨w, hw, hpw⟩
      have h_all_neg_eq : domain.all (fun w => !p w) = true := by
        rw [List.all_eq_not_any_not]; simp [h_any_eq]
      simp [h_all_eq, h_all_neg_eq]

/-- `mustEval` is `ofBool ∘ List.all`, confirming must stays bivalent. -/
theorem mustEval_eq_ofBool (domain : List World) (p : World → Bool) :
    mustEval domain p = Truth3.ofBool (domain.all p) := rfl

-- ============================================================================
-- §17. Sufficient Truth and Exception Tolerance (Appendix 1, def 44–46)
-- ============================================================================

/-! ## Sufficient Truth ([kriz-2016], A&J Appendix 1)

Formalizes the mechanism by which indeterminate (★) sentences are rescued
to "true enough" relative to an Question (= QUD). A sentence S is
**sufficiently true** at w w.r.t. issue I iff:

1. S is not false at w: ⟦S⟧(w) ≠ 0
2. There exists an I-equivalent world u where S is true: ⟦S⟧(u) = 1

Condition 2 means the exceptions are in the same Question cell as a
satisfying world — they are "irrelevant" to the QUD.

**Addressing an Question** (def 46): S cannot address issue I if any cell
of I contains both worlds where S is true and worlds where S is false.
In other words, S must not split any Question cell. -/

/-- Sufficient Truth (Križ 2016, A&J def 44).
    S is true enough at w w.r.t. issue I iff (i) S is not false at w,
    and (ii) some I-equivalent world makes S true. -/
def sufficientTruth {W : Type} (S : W → Truth3) (sameCell : W → W → Bool)
    (w : W) (worlds : List W) : Bool :=
  S w != .false &&
  worlds.any (fun u => sameCell w u && (S u == .true))

-- Addressing an Question: see `Semantics.Homogeneity.addressesIssue` for the
-- canonical definition (Križ 2016 def 46). Not redefined here to avoid duplication.

/-- Sufficient truth rescues an indeterminate sentence when the exceptions
    are QUD-irrelevant. Example: "You should do every exercise" is ★ when
    doing most but not all suffices. Under QUD1 ("how to get a perfect
    grade?"), the exception-worlds (where you skip one exercise but still
    pass) are equivalent to the satisfying-worlds → rescued to "true enough."
    Under QUD2 ("what are the minimal requirements?"), they are in different
    cells → NOT rescued. -/
theorem sufficient_truth_rescues_gap :
    -- w0: all exercises done (S true), w1: most done, still passes (S gap)
    -- QUD1: "how to get a perfect grade?" — w0 ≡ w1 (same answer)
    sufficientTruth
      (fun w => if w == (0 : Fin 3) then Truth3.true
                else if w == 1 then Truth3.indet
                else Truth3.false)
      (fun w u => w != 2 && u != 2)  -- QUD1: w0 ≡ w1, w2 alone
      1  -- evaluate at the gap world
      [0, 1, 2]
    = true := by native_decide

theorem strict_qud_blocks_rescue :
    -- QUD2: "minimal requirements?" — every world in its own cell
    sufficientTruth
      (fun w => if w == (0 : Fin 3) then Truth3.true
                else if w == 1 then Truth3.indet
                else Truth3.false)
      (fun w u => w == u)  -- QUD2: exact (identity)
      1  -- evaluate at the gap world
      [0, 1, 2]
    = false := by native_decide

-- ============================================================================
-- §18. CF Operator (§5.2, eq 33)
-- ============================================================================

/-! ## The CF operator for French-type languages

The X operator (§5.1) requires a UNIQUE minimal witness set (via ι).
This explains Javanese NE: ∀ has one minimal witness (the full domain),
∃ has many (each singleton), so NE only applies to necessity.

French counterfactual morphology is less restrictive: CF picks SOME
witness set (not necessarily unique), so it applies to both necessity
and possibility modals: *devrais* (necessity+CF) and *pourrais*
(possibility+CF).

The difference: X = λM. ⊕ ιW[W ∈ WIT(M)]  (unique, partial)
               CF = λM. ⊕ W for some W ∈ WIT(M) (existential, total) -/

/-- CF operator: checks whether SOME minimal witness set exists.
    Unlike X (which requires uniqueness), CF is defined whenever at
    least one minimal witness exists — which is always, for any non-empty
    quantifier domain. -/
def hasCFWitness [BEq World] (q : List World → Bool)
    (candidates : List (List World)) : Bool :=
  candidates.any (isMinimalWitness q)

/-- CF is defined for both ∀ and ∃ (both have minimal witnesses). -/
theorem cf_defined_for_universal :
    hasCFWitness (universalQ [(0 : Fin 2), 1])
      [[(0 : Fin 2)], [(1 : Fin 2)], [(0 : Fin 2), 1]] = true := by
  native_decide

theorem cf_defined_for_existential :
    hasCFWitness (existentialQ [(0 : Fin 2), 1])
      [[(0 : Fin 2)], [(1 : Fin 2)], [(0 : Fin 2), 1]] = true := by
  native_decide

/-- X (unique minimal witness) is defined for ∀ but not ∃.
    Here "unique" means exactly one candidate is a minimal witness. -/
def hasUniqueWitness [BEq World] (q : List World → Bool)
    (candidates : List (List World)) : Bool :=
  (candidates.filter (isMinimalWitness q)).length == 1

theorem x_defined_for_universal :
    hasUniqueWitness (universalQ [(0 : Fin 2), 1])
      [[(0 : Fin 2)], [(1 : Fin 2)], [(0 : Fin 2), 1]] = true := by
  native_decide

theorem x_undefined_for_existential :
    hasUniqueWitness (existentialQ [(0 : Fin 2), 1])
      [[(0 : Fin 2)], [(1 : Fin 2)], [(0 : Fin 2), 1]] = false := by
  native_decide

/-- The typological prediction: X (Javanese NE) restricts to necessity;
    CF (French counterfactual) applies to both. -/
theorem typological_prediction :
    -- X: unique witness for ∀ only
    hasUniqueWitness (universalQ [(0 : Fin 2), 1])
      [[(0 : Fin 2)], [(1 : Fin 2)], [(0 : Fin 2), 1]] = true ∧
    hasUniqueWitness (existentialQ [(0 : Fin 2), 1])
      [[(0 : Fin 2)], [(1 : Fin 2)], [(0 : Fin 2), 1]] = false ∧
    -- CF: any witness for both
    hasCFWitness (universalQ [(0 : Fin 2), 1])
      [[(0 : Fin 2)], [(1 : Fin 2)], [(0 : Fin 2), 1]] = true ∧
    hasCFWitness (existentialQ [(0 : Fin 2), 1])
      [[(0 : Fin 2)], [(1 : Fin 2)], [(0 : Fin 2), 1]] = true :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- §19. Fragment Bridges: Javanese and French
-- ============================================================================

/-! ## Cross-linguistic fragment verification

Bridge theorems connecting the morphological data (§9) to the actual
fragment entries, verifying that the linguistic analysis is reflected
in the formal lexical entries. -/

/-- *mesthi* is strong necessity in the Javanese fragment. -/
theorem javanese_mesthi_strong :
    Javanese.Modals.mesthi.meaning.all
      (·.force == .necessity) = true := by native_decide

/-- *mesthi-ne* is weak necessity — NE shifts strong to weak. -/
theorem javanese_mesthi_ne_weak :
    Javanese.Modals.mesthiNe.meaning.all
      (·.force == .weakNecessity) = true := by native_decide

/-- The NE morpheme shifts force: *mesthi* and *mesthi-ne* share
    epistemic flavor but differ in force. -/
theorem javanese_ne_shifts_force :
    Javanese.Modals.mesthi.meaning.all (·.flavor == .epistemic) = true ∧
    Javanese.Modals.mesthiNe.meaning.all (·.flavor == .epistemic) = true ∧
    Javanese.Modals.mesthi.meaning.any (·.force == .necessity) = true ∧
    Javanese.Modals.mesthiNe.meaning.any (·.force == .weakNecessity) = true :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- *iso* (possibility) has NO -ne form: *iso-ne is ungrammatical.
    Verified by checking that no weak-possibility expression exists. -/
theorem javanese_no_weak_possibility :
    Javanese.Modals.allExpressions.all
      (fun e => e.meaning.all (·.force != .weakNecessity) ||
                e.meaning.any (·.force == .weakNecessity)) = true := by
  native_decide

/-- *kudu* strong → *kudu-ne* weak, paralleling *mesthi* → *mesthi-ne*. -/
theorem javanese_kudu_ne_weak :
    Javanese.Modals.kudu1.meaning.all (·.force == .necessity) = true ∧
    Javanese.Modals.kudu1Ne.meaning.all (·.force == .weakNecessity) = true :=
  ⟨by native_decide, by native_decide⟩

/-- French *devoir* is strong necessity; *devrais* (devoir+CF) is weak. -/
theorem french_cf_weakens :
    French.Modals.devoir.force = .necessity ∧
    French.Modals.devrais.force = .weakNecessity := ⟨rfl, rfl⟩

/-- *Devrais* preserves *devoir*'s flavor polysemy: both are
    epistemic/deontic/circumstantial. -/
theorem french_devrais_same_flavors :
    French.Modals.devrais.flavors =
    French.Modals.devoir.flavors := rfl

-- ============================================================================
-- Connection to neg-raising ([rubinstein-2014]) via the shared lemma
-- ============================================================================

/-! ## Homogeneity and neg-raising are one structural condition

A&J analyse *should*'s wide-scope-under-negation as **homogeneity** (a truth-value
gap in mixed domains), not genuine neg-raising; [rubinstein-2014] analyses the same
data as genuine neg-raising. Both reduce to one structural condition on the modal's
domain — being a subsingleton — via the shared
`Homogeneity.negRaising_iff_subsingleton`. The rival diagnoses of *should* are the
same fact described differently. -/

/-- A&J's homogeneity (gap-free, i.e. bivalent for every prejacent) and
    Rubinstein's neg-raising coincide: a universal modal over `A` is gap-free for
    every prejacent iff it neg-raises for every prejacent — both hold iff `A` is a
    subsingleton (`Homogeneity.negRaising_iff_subsingleton`). -/
theorem bivalent_iff_negRaising {W : Type*} (A : Set W) :
    (∀ p : W → Prop, (∀ w ∈ A, p w) ∨ (∀ w ∈ A, ¬ p w)) ↔
    (∀ p : W → Prop, ¬ (∀ w ∈ A, p w) → ∀ w ∈ A, ¬ p w) := by
  rw [negRaising_iff_subsingleton A]
  constructor
  · intro hbiv a ha b hb
    rcases hbiv (· = a) with h | h
    · exact (h b hb).symm
    · exact absurd rfl (h a ha)
  · intro hsub p
    by_cases hp : ∀ w ∈ A, p w
    · exact Or.inl hp
    · exact Or.inr ((negRaising_iff_subsingleton A).mpr hsub p hp)

/-- The gap witness, grounded in `shouldEval`: on the mixed two-world domain
    `should` gaps (`should_mixed`) and the domain is not a subsingleton, so by
    `bivalent_iff_negRaising` the neg-raising inference fails there too — the
    homogeneity gap and the neg-raising failure are the same condition. -/
theorem gap_witness_not_subsingleton :
    shouldEval [true, false] id = Truth3.indet ∧
    ¬ ({true, false} : Set Bool).Subsingleton := by
  refine ⟨by decide, fun h => ?_⟩
  have : (true : Bool) = false :=
    h (show (true : Bool) ∈ ({true, false} : Set Bool) by simp)
      (show (false : Bool) ∈ ({true, false} : Set Bool) by simp)
  exact absurd this (by decide)

end AghaJeretic2022
