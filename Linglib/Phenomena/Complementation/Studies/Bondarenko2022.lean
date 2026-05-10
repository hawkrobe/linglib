import Linglib.Theories.Semantics.Attitudes.ClauseDenotation.Content
import Linglib.Theories.Semantics.Attitudes.ClauseDenotation.Situation

/-!
# Bondarenko 2022: Anatomy of an Attitude @cite{bondarenko-2022}

Tatiana Bondarenko (2022). MIT PhD dissertation. Thesis advisors:
P. Elliott, K. von Fintel, D. Fox, S. Iatridou, R. Schwarzschild.

## Headline thesis

Embedded CPs receive **two kinds of denotations** corresponding to a
syntactic distinction in the left periphery (§1.1.1, paper ex. 1):

- **Cont-CP** ≔ λx. CONT(x) = {s : φ(s)}  — predicate on content
  individuals (Kratzer 2006; Moulton 2009, 2015; Elliott 2020). Has an
  extra **ContP** projection that introduces the CONT function.
- **Sit-CP** ≔ λs'. s' is a minimal situation exemplifying φ —
  predicate on minimal situations (Kratzer 1989). Lacks ContP.

In some languages ContP is overtly exposed (Korean -ta declarative;
Buryat gɔ 'say'); in others (English, Russian) it is null.

## Three substantive claims this file formalizes

1. **Equality semantics** for displacement (§1.1.1.2, paper eq. 7),
   not subset semantics (eq. 10) or existential (eq. 15). The
   Cont-CP denotes equality with the embedded proposition, so CONT
   is a function rather than a downward-closed relation. Three
   arguments converge: (i) nominal CP interpretation (paper §2.4),
   (ii) impossibility of CP conjunction (Bassi & Bondarenko 2021),
   (iii) Russian NPI subjunctive distribution (paper ch. 5).

2. **Sit-CPs are referentially transparent; Cont-CPs are opaque.**
   Paper §1.1.1.1 ex. 5 vs ex. 6: under a Sit-CP, embedded
   expressions evaluate at the actual world (substitution preserves
   truth). Under a Cont-CP, they evaluate at content-related worlds
   (substitution may change truth value).

3. **Transparent Syntax-Semantics mapping thesis** (§1.1.2, ch. 4):
   bare CPs are *always* modifiers (PM via the situation argument
   path); nominalized CPs are *always* arguments (FA via the DP
   argument path). The syntactic structure of the CP determines
   the composition path. The (Sit-CP, via DP argument) cell of
   Table 1.1 is unattested by semantic triviality; the
   (bare, FA-argument) and (nominalized, PM-modifier) cells are
   ruled out by the structural correlation.

   This is the thesis @cite{angelopoulos-2026} attacks (autonomy of
   syntax: same syntactic position can yield either composition
   mode at LF). The conditional refutation theorem in
   `Phenomena.Complementation.Studies.Angelopoulos2026` cites the
   `transparentSSMapping` definition below as its premise.

## Out of scope

- Chapter 3 (clausal conjunction & disjunction): the impossibility-
  of-CP-conjunction theorem (`cont_function_blocks_conjunction`
  below) is the only fragment from ch. 3 we land here. Korean -ta
  and -ko-specific Conjunction Reduction analyses are paper-
  specific and don't generalize.
- Chapter 5 (polarity subjunctives): Russian NPI subjunctive data
  + the L-analyticity argument. Worth its own file when the
  L-analyticity substrate is in place.
- Buryat/Korean/Russian morphological exposition (ContP overt vs
  null): would belong in per-language fragment files
  (Fragments/Buryat, Fragments/Korean, Fragments/Russian) once
  those exist.
-/

namespace Phenomena.Complementation.Studies.Bondarenko2022

open Semantics.Attitudes (ContentIndividual)
open Semantics.Attitudes.ClauseDenotation.Content (compC ContentNoun)
open Semantics.Attitudes.ClauseDenotation.Situation
  (SituationIndividual SituationNoun compPu)

-- ════════════════════════════════════════════════════════════════
-- § 1. Nominal Sorts
-- ════════════════════════════════════════════════════════════════

/-- Bondarenko's typology of noun sorts that combine with embedded
    CPs. Studies-local enum per the typological-discipline rule:
    the substrate (`ContentIndividual`, `SituationIndividual`) lives
    in `Theories/Semantics/Attitudes/ClauseDenotation/`; the typology-
    level tagging stays here.

    Cross-linguistic robustness varies (English *the situation* vs
    *the case*; Korean *sanghwang*; Russian *slučaj* / *situacija*).
    This enum follows the paper's primary distinctions (§2.2). -/
inductive NominalSort where
  /-- Content nouns: *claim*, *belief*, *rumor*, *idea*, *thought*,
      *hypothesis*, non-eventive *fact*. -/
  | content
  /-- Situation nouns: *situation*, *case*, *circumstance*, *event*,
      eventive uses of *fact*. -/
  | situation
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2. Equality vs. Subset vs. Existential Semantics
-- ════════════════════════════════════════════════════════════════
--
-- Paper §1.1.1.2 states three candidate semantics for displacement
-- in attitude reports. The thesis argues for EQUALITY (paper eq. 7).
-- The substrate already exposes EQUALITY as `compC` and SUBSET as
-- `ContentIndividual.entails`; we DO NOT re-name them here (per
-- mathlib hygiene: thin aliases are bridge-lemma anti-pattern).
-- Only EXISTENTIAL is novel here — see `ExistentialContent` below.

/-- **Existential semantics** for Cont-CP (paper eq. 15).
    `CONT(x) ∩ p ≠ ∅` — content of `x` is *compatible with* `p`.

    Distinct from `compC` (equality, paper eq. 7) and
    `ContentIndividual.entails` (subset, paper eq. 10). The thesis
    argues against this candidate (§1.1.1.2). -/
def ExistentialContent {W : Type*} (xc : ContentIndividual W)
    (p : W → Prop) : Prop :=
  ∃ w : W, xc.cont w ∧ p w

/-- Equality (`compC`) is strictly stronger than subset
    (`ContentIndividual.entails`) per paper §1.1.1.2. Re-export
    of `ContentIndividual.eq_implies_entails` under the
    paper-aligned name. -/
theorem equality_implies_subset {W : Type*} (xc : ContentIndividual W)
    (p : W → Prop) : compC p xc → xc.entails p :=
  ContentIndividual.eq_implies_entails xc p

/-- Equality (`compC`) implies existential, *provided* the content is
    nonempty. The empty-content witness in `ContentIndividual` shows
    this is a real proviso. -/
theorem equality_implies_existential {W : Type*}
    (xc : ContentIndividual W) (p : W → Prop)
    (hne : ∃ w, xc.cont w) :
    compC p xc → ExistentialContent xc p := by
  intro heq
  obtain ⟨w, hw⟩ := hne
  exact ⟨w, hw, heq ▸ hw⟩

-- ════════════════════════════════════════════════════════════════
-- § 3. CP Conjunction Impossibility (Bassi & Bondarenko 2021)
-- ════════════════════════════════════════════════════════════════
--
-- Paper §1.1.1.2 argues the equality semantics predicts true CP
-- conjunction is impossible. Reasoning: if CONT is a function
-- (equality), then for any individual x, CONT(x) is a unique
-- proposition; CONT(x) = p1 AND CONT(x) = p2 forces p1 = p2.

/-- **Equality forces functionality**: if `x` has content `p1`
    under equality semantics AND `x` has content `p2` under
    equality semantics, then `p1 = p2`.

    Bassi & Bondarenko 2021 derive the impossibility of true CP
    conjunction from this functionality (paper §1.1.1.2). -/
theorem cont_function_blocks_conjunction {W : Type*}
    (xc : ContentIndividual W) (p1 p2 : W → Prop) :
    compC p1 xc → compC p2 xc → p1 = p2 := by
  intro h1 h2
  exact h1.symm.trans h2

/-- Counterpart for subset semantics (`ContentIndividual.entails`):
    subset does NOT force functionality. A *non-vacuous* content
    individual can entail multiple distinct propositions (any
    superset of the content) without being identified with them.

    Witness: a content individual whose CONT holds at exactly
    `{true}` (non-empty); it entails both `(· = true)` and
    `(fun _ => True)` — these are distinct propositions yet
    both satisfy subset semantics. -/
theorem subset_does_not_force_functionality :
    ¬ ∀ (xc : ContentIndividual Bool) (p1 p2 : Bool → Prop),
      xc.entails p1 → xc.entails p2 → p1 = p2 := by
  intro h
  -- Non-vacuous witness: content holds exactly at `true`.
  let xc : ContentIndividual Bool := ⟨fun b => b = true⟩
  have h_p1 : xc.entails (fun b => b = true) := fun _ hb => hb
  have h_p2 : xc.entails (fun _ => True) := fun _ _ => trivial
  have heq : (fun b : Bool => b = true) = (fun _ : Bool => True) :=
    h xc _ _ h_p1 h_p2
  -- The propositions disagree at `false`: `false = true` is False,
  -- but `(fun _ => True) false` is True.
  exact (iff_of_eq (congr_fun heq false)).mpr trivial |> Bool.noConfusion

-- ════════════════════════════════════════════════════════════════
-- § 4. Sit-CP Transparency vs. Cont-CP Opacity
-- ════════════════════════════════════════════════════════════════
--
-- Paper §1.1.1.1 ex. 5 (Russian Sit-NP transparency) vs ex. 6
-- (Cont-NP opacity) is the central transparency contrast. We
-- formalize the abstract content: predicates inside a Sit-CP
-- evaluate at the actual situation; predicates inside a Cont-CP
-- evaluate at content-related situations.

/-- A predicate is *referentially transparent* with respect to
    a clause iff its evaluation is at the actual situation
    (substitution under co-extensionality preserves truth). -/
def ReferentiallyTransparent {S : Type*} (clause : (S → Prop) → S → Prop)
    (s : S) : Prop :=
  ∀ p q : S → Prop, (∀ s', p s' ↔ q s') → (clause p s ↔ clause q s)

/-- A Sit-CP is referentially transparent: paper §1.1.1.1, derived
    from the Sit-CP denotation `λs'. φ(s')` evaluating predicates
    at the actual situation `s`. Witness: any clause built as a
    Sit-CP via @cite{bondarenko-2022}'s ex. 1b structure. -/
theorem sit_cp_transparent {S : Type*} (s : S) :
    ReferentiallyTransparent (fun p s' => p s') s := by
  intro p q hpq
  exact hpq s

/-- A Cont-CP is referentially OPAQUE in the sense that
    co-extensional substitution at the actual world `s` does not
    preserve truth — the relevant evaluation point is determined
    by `CONT(x)`, not by `s`.

    Witness construction (paper §1.1.1.1 ex. 6, Russian *Lena
    noticed a rumor that this woman arrived on a horse*): even if
    `this woman = the queen of Great Britain` holds at `s`, the
    rumor's content may not contain the queen.

    TODO: replace `sorry` with a concrete witness model where two
    co-extensional predicates yield different Cont-CP truth values.
    Requires distinguishing actual-world extension from CONT-internal
    extension. -/
theorem cont_cp_opaque {W : Type*} :
    ¬ ∀ (xc : ContentIndividual W) (w : W),
      ReferentiallyTransparent (fun p _ => compC p xc) w := by
  -- TODO: construct a witness ContentIndividual whose content holds
  -- exactly at one world w0 ≠ w, and two predicates that agree at
  -- w but differ at w0. Then transparency would force the Cont-CP
  -- to be insensitive to the difference, but compC's equality test
  -- detects it. Requires Bool/two-world model.
  sorry

-- ════════════════════════════════════════════════════════════════
-- § 5. Transparent Syntax-Semantics Mapping Thesis
-- ════════════════════════════════════════════════════════════════
--
-- Paper §1.1.2: only certain (CP-meaning, composition-path) pairs
-- are attested. The thesis argues this follows from a TIGHT
-- correlation between syntactic structure and integration path:
-- bare CPs MUST compose as modifiers (PM via the situation
-- argument); nominalized CPs MUST compose as arguments (FA via
-- the DP argument).
--
-- This is the thesis @cite{angelopoulos-2026} §7.3 attacks.

/-- The four logically possible (clause shape, composition path)
    combinations. -/
inductive ClauseStructurePath where
  /-- Bare CP composing via Predicate Modification (modifier path). -/
  | bareModifier
  /-- Bare CP composing via Functional Application (argument path). -/
  | bareArgument
  /-- Nominalized CP composing via Predicate Modification. -/
  | nominalizedModifier
  /-- Nominalized CP composing via Functional Application. -/
  | nominalizedArgument
  deriving DecidableEq, Repr

/-- Bondarenko's transparent Syntax-Semantics mapping thesis
    (paper §1.1.2 + ch. 4): a bare CP composes ONLY via the
    modifier path (PM via the situation argument); a nominalized
    CP composes ONLY via the argument path (FA via the DP argument).

    The two off-diagonal cells (bareArgument, nominalizedModifier)
    are predicted impossible by this thesis.

    @cite{angelopoulos-2026} attacks the bareArgument cell with
    Greek *oti*/*pu*: bare clauses pattern as internal arguments
    (clitic doubling, passivization, extraction transparency)
    while still composing via PM (the *explanans* reading).

    **Caveat (mathlib audit).** This `def`-as-table encoding is the
    paper-fidelity stub form — it lossily compresses Bondarenko's
    distinction between *situation-argument* and *DP-argument*
    composition paths into a single `bareArgument` cell. A
    genuinely structural derivation would replace this with a
    predicate `composes : ClauseShape → ArgumentSlot → Prop`
    defined over actual derivations and prove the four-cell
    pattern from a deeper claim (e.g., that bare CPs lack the
    nominal projection required to saturate a DP argument slot).
    The current encoding is honest as a paper-fidelity tag but
    should not be mistaken for a derivation. TODO: structural
    refactor when a `composes` predicate over `SyntacticObject`
    derivations is available.  -/
def transparentSSMapping : ClauseStructurePath → Prop
  | .bareModifier => True
  | .bareArgument => False
  | .nominalizedModifier => False
  | .nominalizedArgument => True

/-- Bondarenko predicts the (bare, argument) cell is empty. This
    is the EXACT cell @cite{angelopoulos-2026} attacks. The proof
    is by table-unfolding; the substantive refutation lives in
    `Phenomena.Complementation.Studies.Angelopoulos2026`. -/
theorem bare_argument_predicted_impossible :
    ¬ transparentSSMapping .bareArgument := by
  intro h; exact h

/-- Bondarenko predicts the (nominalized, modifier) cell is empty. -/
theorem nominalized_modifier_predicted_impossible :
    ¬ transparentSSMapping .nominalizedModifier := by
  intro h; exact h

/-- The diagonal cells are predicted available. -/
theorem diagonal_attested :
    transparentSSMapping .bareModifier ∧
    transparentSSMapping .nominalizedArgument :=
  ⟨trivial, trivial⟩

-- ════════════════════════════════════════════════════════════════
-- § 6. Path-of-Composition Restriction (Table 1.1)
-- ════════════════════════════════════════════════════════════════

/-- The two composition paths Bondarenko distinguishes (paper §1.1.2,
    Table 1.1): clauses can either modify a verbal situation argument
    by Predicate Modification (`viaSituation`) or saturate a DP
    argument slot by Functional Application (`viaDPArgument`). -/
inductive CompositionPath where
  | viaSituation
  | viaDPArgument
  deriving DecidableEq, Repr

/-- Paper Table 1.1: combinations of CP meanings × composition paths.
    Three of four cells are attested; the (Sit-CP, viaSituation)
    cell is unattested by semantic triviality (a Sit-CP composing
    intersectively with the situation argument always yields a
    trivially false statement, as a situation cannot be both a
    minimal exemplar of φ and the verb's situation argument). -/
def attestedCombination : NominalSort → CompositionPath → Prop
  | .content, _              => True   -- Cont-CP via either path
  | .situation, .viaDPArgument => True -- Sit-CP via DP-argument path
  | .situation, .viaSituation  => False -- Sit-CP via Situation path: ✗

/-- The (Sit-CP, viaSituation) cell is empty by semantic triviality
    (paper §1.1.2). -/
theorem sit_cp_via_situation_blocked :
    ¬ attestedCombination .situation .viaSituation := by
  intro h; exact h

-- ════════════════════════════════════════════════════════════════
-- § 7. Bridge to BondarenkoElliott2026
-- ════════════════════════════════════════════════════════════════
--
-- The mereological monotonicity apparatus in
-- `Phenomena/Attitudes/Studies/BondarenkoElliott2026.lean` (MSI,
-- MSO, TECM) presupposes the equality semantics defended here.
-- This bridge is informational; no formal dependency to chase.

/-- Bondarenko & Elliott 2026 inherit the **equality** semantics
    from this dissertation. The substantive bridge requires
    referencing a specific equality-using definition from
    `Phenomena/Attitudes/Studies/BondarenkoElliott2026.lean`
    (their `MSI`/`MSO`/`TECM` apparatus presupposes `CONT(x) = ⟦S⟧`
    rather than `CONT(x) ⊆ ⟦S⟧`). The full bridge is queued: this
    file does not yet import BE2026, and the cross-file `Iff`
    target needs to be a specific BE2026 lemma rather than the
    `compC` substrate primitive. TODO: add bridge once BE2026
    exposes a stable `equalityForm` lemma. -/
theorem be2026_inherits_equality_substrate {W : Type*}
    (xc : ContentIndividual W) (p : W → Prop) :
    compC p xc ↔ xc.cont = p := Iff.rfl

end Phenomena.Complementation.Studies.Bondarenko2022
