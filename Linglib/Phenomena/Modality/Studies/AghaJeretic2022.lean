import Linglib.Core.Logic.Truth3
import Linglib.Phenomena.Plurals.Homogeneity
import Linglib.Theories.Semantics.Modality.Directive
import Linglib.Fragments.English.FunctionWords

/-!
# Weak Necessity Modals as Homogeneous Pluralities of Worlds
@cite{agha-jeretic-2022}

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

@cite{tieu-kriz-chemla-2019} find that children acquire homogeneity
independently of scalar implicatures (HOM/−SI group), supporting the
claim that homogeneity is intrinsic to plural predication rather than
derived via exhaustification (@cite{magri-2014}).

## Connection to @cite{agha-jeretic-2026}

The 2026 handbook chapter surveys this analysis as one of three competing
accounts of weak necessity (alongside domain restriction and comparative
semantics), and extends it to explain the neg-raising asymmetry between
*should* and *must*.
-/

namespace Phenomena.Modality.Studies.AghaJeretic2022

open Core.Duality (Truth3)
open Phenomena.Plurals.Homogeneity (HomogeneityJudgment HomogeneityDatum
  HomogeneityRemover HomogeneityRemovalDatum conditionalExample)

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
    of worlds, yielding homogeneity. -/
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
plural definites with respect to negation. We encode the key data points
using the `HomogeneityDatum` type from `Plurals.Homogeneity`. -/

/-- *Should* displays homogeneity: under negation, "shouldn't go" is
    incompatible with an existential followup "but you can" — just like
    "The guests aren't here" is incompatible with "but some of them are."

    Paper examples (8)–(9). -/
def shouldHomogeneity : HomogeneityDatum :=
  { positiveSentence := "According to the rules, you should go."
  , negativeSentence := "According to the rules, you shouldn't go."
  , allScenario := "All best deontic worlds are go-worlds"
  , noneScenario := "No best deontic worlds are go-worlds"
  , gapScenario := "Some but not all best deontic worlds are go-worlds"
  , positiveInAll := .clearlyTrue
  , negativeInAll := .clearlyFalse
  , positiveInNone := .clearlyFalse
  , negativeInNone := .clearlyTrue
  , positiveInGap := .neitherTrueNorFalse
  , negativeInGap := .neitherTrueNorFalse
  }

/-- *Have to* does NOT display homogeneity: "don't have to go" is compatible
    with "but you are allowed to go" — narrow scope reading (¬□ = ◇¬)
    available, unlike *should* which only allows wide scope (□¬).

    Paper example (9b). -/
def haveToNoHomogeneity : HomogeneityDatum :=
  { positiveSentence := "According to the rules, you have to go."
  , negativeSentence := "According to the rules, you don't have to go."
  , allScenario := "All best deontic worlds are go-worlds"
  , noneScenario := "No best deontic worlds are go-worlds"
  , gapScenario := "Some but not all best deontic worlds are go-worlds"
  , positiveInAll := .clearlyTrue
  , negativeInAll := .clearlyFalse
  , positiveInNone := .clearlyFalse
  , negativeInNone := .clearlyTrue
  -- have-to is bivalent: dominant reading under negation is ¬□ (narrow scope)
  , positiveInGap := .clearlyFalse
  , negativeInGap := .clearlyTrue
  }

theorem should_has_gap :
    shouldHomogeneity.positiveInGap = .neitherTrueNorFalse := rfl

theorem haveTo_no_gap :
    haveToNoHomogeneity.negativeInGap = .clearlyTrue := rfl

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

/-- *Necessarily* removes homogeneity from *should*, paralleling how
    *all* removes homogeneity from plural definites. -/
def necessarilyRemovesModalHomogeneity : HomogeneityRemovalDatum :=
  { homogeneousSentence := "According to the rules, you shouldn't go."
  , precisesentence := "According to the rules, you shouldn't necessarily go."
  , remover := .necessarily  -- modal-domain counterpart of nominal .all
  , gapScenario := "Some but not all best worlds are go-worlds"
  , homogeneousJudgment := .neitherTrueNorFalse
  , preciseJudgment := .clearlyFalse
  }

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

structure ModalExceptionDatum where
  modal : String
  sentence : String
  context : String
  qud1 : String
  qud2 : String
  acceptableUnderQUD1 : Bool
  acceptableUnderQUD2 : Bool
  deriving Repr

def shouldExceptionTolerance : ModalExceptionDatum where
  modal := "should"
  sentence := "To get a perfect grade, you should do every exercise."
  context := "One can get a perfect grade by doing most exercises; doing all gives extra credit."
  qud1 := "What is a way to get a perfect grade?"
  qud2 := "What are the minimal requirements to get a perfect grade?"
  acceptableUnderQUD1 := true
  acceptableUnderQUD2 := false

def haveToExceptionTolerance : ModalExceptionDatum where
  modal := "have to"
  sentence := "To get a perfect grade, you have to do every exercise."
  context := "One can get a perfect grade by doing most exercises; doing all gives extra credit."
  qud1 := "What is a way to get a perfect grade?"
  qud2 := "What are the minimal requirements to get a perfect grade?"
  acceptableUnderQUD1 := false
  acceptableUnderQUD2 := false

theorem should_tolerates_exceptions :
    shouldExceptionTolerance.acceptableUnderQUD1 = true ∧
    haveToExceptionTolerance.acceptableUnderQUD1 = false := ⟨rfl, rfl⟩

-- ============================================================================
-- §7. Responses to Indeterminate Sentences (§3.4)
-- ============================================================================

/-! ## Well-responses in borderline cases

In borderline cases (★), outright denial is infelicitous; *well*-responses
are preferred. This parallels plural definites (@cite{kriz-2016}).

Paper example (19). -/

structure IndeterminateResponseDatum where
  sentence : String
  context : String
  noResponseFelicitous : Bool
  wellResponseFelicitous : Bool
  deriving Repr

def shouldIndeterminateResponse : IndeterminateResponseDatum where
  sentence := "You should take the right door to go to the living room."
  context := "Two doors lead to the living room; both are equally good options."
  noResponseFelicitous := false
  wellResponseFelicitous := true

def mustIndeterminateResponse : IndeterminateResponseDatum where
  sentence := "You must take the right door to go to the living room."
  context := "Two doors lead to the living room; both are equally good options."
  noResponseFelicitous := true
  wellResponseFelicitous := false

theorem should_well_not_no :
    shouldIndeterminateResponse.noResponseFelicitous = false ∧
    shouldIndeterminateResponse.wellResponseFelicitous = true := ⟨rfl, rfl⟩

theorem must_no_not_well :
    mustIndeterminateResponse.noResponseFelicitous = true ∧
    mustIndeterminateResponse.wellResponseFelicitous = false := ⟨rfl, rfl⟩

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

The @cite{von-fintel-iatridou-2008} analysis (formalized in `Directive.lean`)
treats *should* as ∀ over a refined set of best worlds. `Directive.weakNecessity`
returns `Bool` — it is bivalent by construction. A bivalent semantics
**cannot produce the truth-value gap** that the empirical data require.

We make this critique computational by contrasting `Directive.weakNecessity`
(always tt or ff) with `shouldEval` (can return unk). -/

section DirectiveBridge

open Semantics.Modality.Directive (weakNecessity)
open Semantics.Modality.Kratzer (ModalBase OrderingSource)
open Core.Proposition (BProp)

/-- `Directive.weakNecessity` is bivalent: it returns Bool, so wrapping
    in Truth3 can only yield true or false — never indet. -/
theorem directive_bivalent
    (f : ModalBase) (g g' : OrderingSource)
    (p : BProp Semantics.Attitudes.Intensional.World)
    (w : Semantics.Attitudes.Intensional.World) :
    Truth3.ofBool (weakNecessity f g g' p w) = Truth3.true ∨
    Truth3.ofBool (weakNecessity f g g' p w) = Truth3.false := by
  cases weakNecessity f g g' p w <;> simp [Truth3.ofBool]

end DirectiveBridge

/-- `shouldEval` CAN return unk — the gap that domain restriction misses. -/
theorem shouldEval_can_gap :
    ∃ (D : List Bool) (p : Bool → Bool), shouldEval D p = Truth3.indet :=
  ⟨[true, false], id, by native_decide⟩

/-- The mismatch: domain restriction predicts existential followups are
    felicitous after negated *should*, but empirically they are not. -/
structure DomainRestrictionPrediction where
  sentence : String
  existentialFollowup : String
  domainRestrictionPredicts : Bool
  empiricallyObserved : Bool
  deriving Repr

def domainRestrictionFails : DomainRestrictionPrediction where
  sentence := "According to the rules, you shouldn't go."
  existentialFollowup := "but you are allowed to go"
  domainRestrictionPredicts := true   -- ¬∀ compatible with ∃
  empiricallyObserved := false        -- actually infelicitous (#)

theorem domain_restriction_wrong :
    domainRestrictionFails.domainRestrictionPredicts ≠
    domainRestrictionFails.empiricallyObserved := by decide

-- ============================================================================
-- §11. FunctionWords Bridge
-- ============================================================================

/-! ## English modal lexicon verification

Verify that the English fragment classifies *should*/*ought* as weak
necessity and *must* as strong necessity, matching the paper's §2.1. -/

open Fragments.English.FunctionWords

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
plural predication over different semantic domains.

`Plurals.Homogeneity.conditionalExample` already captures the conditional
case: "They play soccer if the sun shines" displays the same gap as
"The switches are on" and "You should go."

Examples (38)–(42): future conditionals, bare past conditionals, generics,
and habituals all show homogeneity effects and homogeneity removal by
explicit quantifiers (*necessarily*, *always*, *all*). -/

/-- The existing `conditionalExample` from `Homogeneity.lean` shows the
    same gap pattern as `shouldHomogeneity` — both have ★ in the gap
    scenario. This structural parallel supports the unified plural
    predication analysis. -/
theorem conditional_parallel :
    conditionalExample.positiveInGap = shouldHomogeneity.positiveInGap ∧
    conditionalExample.negativeInGap = shouldHomogeneity.negativeInGap := ⟨rfl, rfl⟩

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

end Phenomena.Modality.Studies.AghaJeretic2022
