import Linglib.Theories.Semantics.Attitudes.ClauseDenotation.Content
import Linglib.Theories.Semantics.Attitudes.ClauseDenotation.Situation

/-!
# Bondarenko 2022: Anatomy of an Attitude @cite{bondarenko-2022}

Tatiana Bondarenko (2022). MIT PhD dissertation. Thesis advisors:
P. Elliott, K. von Fintel, D. Fox, S. Iatridou, R. Schwarzschild.

## Locator convention

Section / equation / example numbers below reference Chapter 1 (the
"Brief summary of the proposal" overview), unless prefixed with an
explicit chapter number. Chapter 4 — the substantive bare-vs-
nominalized treatment formalised in §§ 7-12 of this file — gives
the same content under different locators (e.g., Table 1.1 ↔ Table
4.1; ex. 1 ↔ §4.2 ex. 1-2). Locators were verified against the
PDF; references to chapters not yet read carry `UNVERIFIED:` flags.

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
-- The central transparency-vs-opacity contrast (Russian and Korean
-- substitution-test data, paper Chapter 2 §2.2.3 ex. 120-122,
-- pp. 106-108; Chapter 1 ex. 5-6 is the brief-summary version).
--
-- The substitution test: under a Cont-NP like *slux* 'rumor',
-- (a) "Lena noticed a rumor that this woman arrived on a horse"
--   + (b) "this woman = the queen of Great Britain"
--   ⇏ (c) "Lena noticed a rumor that the queen arrived on a horse".
-- The DPs *this woman* and *the queen* are coextensional at the
-- evaluation world but the rumor's content may not connect the
-- two. Cont-CPs constitute a referentially opaque domain
-- (@cite{barwise-1981}, @cite{higginbotham-1983}).
--
-- Under a Sit-NP like *slučaj* 'event', the same premises DO
-- entail the conclusion: all DPs inside the Sit-CP are evaluated
-- at the same world as the matrix verb.
--
-- **Two transparency notions**: STRONG transparency requires
-- coextensional-everywhere predicates to be substitutable; WEAK
-- transparency (`At`) only requires coextensionality at the
-- evaluation world. Strong transparency is trivial (it follows
-- from `funext` for any clause), so the substantive contrast is
-- in the WEAK form.

/-- **Weak transparency** at evaluation world `s`: substitution
    of predicates that agree AT s preserves clause truth. This is
    the notion that distinguishes Sit-CPs (transparentAt) from
    Cont-CPs (NOT transparentAt). -/
def ReferentiallyTransparentAt {S : Type*}
    (clause : (S → Prop) → S → Prop) (s : S) : Prop :=
  ∀ p q : S → Prop, (p s ↔ q s) → (clause p s ↔ clause q s)

/-- **Strong transparency**: substitution of predicates that agree
    EVERYWHERE preserves clause truth. By `funext`+`propext` this is
    trivially satisfied by every clause; included for completeness
    and to disambiguate from `ReferentiallyTransparentAt`. -/
def ReferentiallyTransparentEverywhere {S : Type*}
    (clause : (S → Prop) → S → Prop) (s : S) : Prop :=
  ∀ p q : S → Prop, (∀ s', p s' ↔ q s') → (clause p s ↔ clause q s)

/-- A Sit-CP (modeled as `fun p s' => p s'`) IS weak-transparent:
    its evaluation is at the actual situation `s`, so
    coextensional-at-s predicates yield the same value. -/
theorem sit_cp_transparentAt {S : Type*} (s : S) :
    ReferentiallyTransparentAt (fun p s' => p s') s := by
  intro p q hpq
  exact hpq

/-- A Sit-CP is also (vacuously) strong-transparent — but this is
    trivial for any clause, so it carries no empirical content. -/
theorem sit_cp_transparentEverywhere {S : Type*} (s : S) :
    ReferentiallyTransparentEverywhere (fun p s' => p s') s := by
  intro p q hpq
  exact hpq s

/-- **Cont-CP is NOT weak-transparent** (Bondarenko ex. 120,
    p. 106). Constructive witness: a 2-world model where
    `xc.cont` picks out only one world, and two predicates that
    agree at the evaluation world but disagree elsewhere.

    Concretely: `W := Bool`, evaluation world `false`, content
    individual with `cont = (fun b => b = false)` (= the
    proposition true only at `false`). Predicates:
    * `p := (fun b => b = false)` — true at `false`, false at `true`
    * `q := (fun _ => True)`     — true at both
    They agree at the evaluation world `false` (both true), but
    `compC p xc` (= xc.cont = p) HOLDS while `compC q xc` FAILS
    (since `xc.cont` differs from `q` at `true`). -/
theorem cont_cp_not_transparentAt :
    ¬ ∀ (xc : ContentIndividual Bool) (w : Bool),
      ReferentiallyTransparentAt (fun p _ => compC p xc) w := by
  intro h
  let xc : ContentIndividual Bool := ⟨fun b => b = false⟩
  let p : Bool → Prop := fun b => b = false
  let q : Bool → Prop := fun _ => True
  -- p and q agree at the evaluation world `false`
  have h_at : p false ↔ q false := by
    constructor
    · intro _; trivial
    · intro _; rfl
  -- transparency would equate compC p xc with compC q xc at false
  have h_eq : compC p xc ↔ compC q xc := h xc false p q h_at
  -- compC p xc holds (xc.cont = p definitionally)
  have hp : compC p xc := rfl
  -- compC q xc would force xc.cont = (fun _ => True), but they
  -- differ at b = true: xc.cont true = false ≠ True
  have hq : ¬ compC q xc := by
    intro heq
    have : (fun b : Bool => b = false) true = (fun _ : Bool => True) true :=
      congrFun heq true
    -- LHS reduces to (true = false) = False; RHS to True
    simp at this
  exact hq (h_eq.mp hp)

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

-- ════════════════════════════════════════════════════════════════
-- § 8. Chapter 4: Type-theoretic apparatus (§4.2)
-- ════════════════════════════════════════════════════════════════
--
-- Per the syntax expert audit, Bondarenko's derivation of "bare CPs
-- cannot be Causer/Theme/About" is **type-theoretic**, not structural.
-- The mechanism:
--
--    bare CP     : type ⟨e,t⟩  (predicate over situations)
--    nominalized : type ⟨e⟩    (saturated DP)
--    Θ-heads     : require ⟨e⟩ argument
--    therefore   : only nominalized CP can saturate Θ
--
-- The N/D presence in nominalized CPs is the morphological *exponence*
-- of the type-shift, not the cause. The four-cell table at §5
-- (`transparentSSMapping`) is **derived** below from this type
-- mechanism via §11 — see `transparentSSMapping_iff_typed`.
--
-- Critical framing caveat (syntax expert S2): Bondarenko works in
-- Bare Phrase Structure where the X-bar argument/modifier distinction
-- is gone. The "modifier" claim is **semantic** (type incompatibility),
-- not structural. The §5 enum `ClauseStructurePath` (bareModifier vs
-- nominalizedArgument etc.) is paper-fidelity bookkeeping; the BPS-
-- compatible claim is the type-theoretic predicate.

/-- Semantic types relevant for Bondarenko's type-mismatch derivation.
    The two-element enum reflects only the cells the chapter exploits:
    `individual` (saturated entity, type ⟨e⟩) and `predicate`
    (unsaturated, type ⟨e,t⟩). Finer type-theoretic distinctions
    (intensional types ⟨s,e⟩, generalized quantifiers ⟨⟨e,t⟩,t⟩, etc.)
    are out of scope for this Studies file. -/
inductive SemType where
  | individual
  | predicate
  deriving DecidableEq, Repr

/-- Embedded clause types per Bondarenko §4.2 (the bare-vs-nominalized
    cut). Names emphasize the *semantic content* (predicate of
    individuals vs predicate of situations) rather than the
    morphological exponence (bare vs nominalized) — this is the BPS-
    compatible framing. -/
inductive ClauseType where
  /-- Nominalized CP: type ⟨e⟩, refers to an individual (typically
      with propositional content via CONT). Buryat *gɔ*-marked clause
      with a participial nominaliser; Korean *-nun + kes* clause. -/
  | predicateOfIndividuals
  /-- Bare CP: type ⟨e,t⟩, predicate over (minimal) situations.
      Buryat clause without *gɔ*; Korean *-ta* declarative; Russian
      bare *čto*-clause. -/
  | predicateOfSituations
  deriving DecidableEq, Repr

/-- The semantic type of an embedded clause: nominalized → individual,
    bare → predicate. This is the type-theoretic content the chapter
    exploits. -/
def ClauseType.semanticType : ClauseType → SemType
  | .predicateOfIndividuals => .individual
  | .predicateOfSituations  => .predicate

/-- Θ-heads relevant to Bondarenko §4.4. Per syntax expert S3, these
    are NOT three independent stipulations — they share the
    selectional restriction "requires individual argument." Per-Θ
    presupposition flavor (Θ_About has pre-existence; §4.4.3) is
    deferred to a future scope. -/
inductive ThetaHead where
  /-- Θ_Causer (Pylkkänen / Cuervo). §4.4.1. -/
  | causer
  /-- Θ_Theme (broad, internal-argument introducer). §4.4.2. -/
  | theme
  /-- Θ_About (Bondarenko's own innovation, Pylkkänen-style refinement;
      carries pre-existence presupposition not formalised here). §4.4.3. -/
  | aboutAttitude
  deriving DecidableEq, Repr

/-- Every Θ-head requires an individual argument (type ⟨e⟩). This is
    the central claim that drives the bare-vs-nominalized derivation;
    it does NOT vary by Θ-head, despite per-Θ presupposition variation
    (§4.4.3 Θ_About pre-existence). -/
def ThetaHead.requiredType : ThetaHead → SemType
  | _ => .individual

/-- A clause type **saturates** a Θ-head iff its semantic type
    matches the head's required type. Per Bondarenko §4.2, this is
    the central type-mismatch derivation. NOT a stipulation: the
    `Prop` is just type-equality on the projection through
    `semanticType` / `requiredType`. -/
def saturatesTheta (ct : ClauseType) (θ : ThetaHead) : Prop :=
  ct.semanticType = θ.requiredType

instance : ∀ (ct : ClauseType) (θ : ThetaHead),
    Decidable (saturatesTheta ct θ) := fun ct θ => by
  unfold saturatesTheta; infer_instance

-- ════════════════════════════════════════════════════════════════
-- § 9. Causer / Theme / About derivations (§4.4.1-3)
-- ════════════════════════════════════════════════════════════════
--
-- Per syntax expert S3: the three negative claims (Causer / Theme /
-- About-cannot-be-bare) reduce to ONE mechanism. Each is one line
-- after the type-mismatch substrate above.

/-- **Bondarenko §4.4.1**: Bare CPs cannot be Causers. Derived from
    type-mismatch: bare CP delivers `.predicate`; Θ_Causer requires
    `.individual`. -/
theorem bareCP_not_Causer :
    ¬ saturatesTheta .predicateOfSituations .causer := by
  intro h; exact SemType.noConfusion h

/-- **Bondarenko §4.4.2**: Bare CPs cannot be Theme-arguments. Same
    mechanism as Causer. The *explain*-class data
    (@cite{halpert-schueler-2013}, @cite{elliott-2016},
    @cite{roelofsen-uegaki-2021}, @cite{pietroski-2000}) is what makes
    this derivation tight: when *explain* takes a bare clause vs a
    nominalized clause, only the latter receives the Theme reading. -/
theorem bareCP_not_Theme :
    ¬ saturatesTheta .predicateOfSituations .theme := by
  intro h; exact SemType.noConfusion h

/-- **Bondarenko §4.4.3**: Bare CPs cannot be About-arguments. Same
    type-mismatch; per Bondarenko this Θ-head additionally introduces
    a pre-existence presupposition (deferred). -/
theorem bareCP_not_About :
    ¬ saturatesTheta .predicateOfSituations .aboutAttitude := by
  intro h; exact SemType.noConfusion h

/-- The unified Bondarenko §4.4 result: bare CPs satisfy NO Θ-head.
    This is the single mechanism behind §4.4.1, §4.4.2, §4.4.3 — not
    three independent stipulations (per syntax expert S3). -/
theorem bareCP_satisfies_no_theta :
    ∀ θ : ThetaHead, ¬ saturatesTheta .predicateOfSituations θ := by
  intro θ h; exact SemType.noConfusion h

/-- Conversely, nominalized CPs satisfy every Θ-head (modulo per-Θ
    presupposition flavor not formalized here). -/
theorem nominalizedCP_satisfies_every_theta :
    ∀ θ : ThetaHead, saturatesTheta .predicateOfIndividuals θ := by
  intro θ; rfl

-- ════════════════════════════════════════════════════════════════
-- § 10. Modifier path (§4.5): bare CPs as situation-modifiers
-- ════════════════════════════════════════════════════════════════
--
-- Per Layered Grounding obligation (cross-framework auditor):
-- consume `Theories.Semantics.Composition.Modification`'s
-- `predicateModification` (`⊓ₚ`) — DO NOT redefine PM here. The
-- substrate operates over `Frame.Denot (.e ⇒ .t)` typed-semantics
-- predicates; this Studies file states only the abstract
-- compositional fact (bare CP composes via PM with v's situation
-- argument). The Frame-typed instantiation is queued for when the
-- compositional layer of Bondarenko's analysis is formalised in
-- detail.
--
-- Critical framing caveat (syntax expert S2): Bondarenko's "modifier"
-- claim is SEMANTIC (type compatibility for PM), NOT structural
-- ("adjunct" in the X-bar sense). BPS does not have the X-bar
-- argument/modifier distinction. This file's `composesViaPM` predicate
-- tracks the SEMANTIC claim.

/-- A clause can compose via Predicate Modification with a verbal
    situation argument iff it has predicate type (⟨s,t⟩ after lifting
    the individual variable in Bondarenko's lift; substantively, both
    arguments are situation-predicates and intersect by PM). The
    `predicateModification` substrate at
    `Theories/Semantics/Composition/Modification.lean` is the typed
    realisation; this Studies-level predicate is its qualitative
    projection. -/
def composesViaPM : ClauseType → Prop
  | .predicateOfIndividuals => False  -- nominalised, no PM compatibility
  | .predicateOfSituations  => True   -- bare, PM-compatible

instance : ∀ ct, Decidable (composesViaPM ct) := fun ct => by
  cases ct <;> (unfold composesViaPM; infer_instance)

/-- **Bondarenko §4.5**: bare CPs are verbal modifiers. Stated as
    PM-compatibility, derived from the type. -/
theorem bareCP_composes_via_PM : composesViaPM .predicateOfSituations := trivial

/-- Nominalized CPs are NOT modifiers via PM (Bondarenko §4.5
    contrapositive — they compose via FA through the DP path). -/
theorem nominalizedCP_not_PM_modifier : ¬ composesViaPM .predicateOfIndividuals :=
  fun h => h

-- ════════════════════════════════════════════════════════════════
-- § 11. Refactor: derive `transparentSSMapping` from §§ 8-10
-- ════════════════════════════════════════════════════════════════
--
-- Per mathlib audit critical caveat: the type-theoretic refactor is
-- only substantive if it actually replaces the def-as-table form
-- with a derivation. The four cells of the original §5 table
-- become projections of the type-mismatch + PM-compatibility
-- predicates above.

/-- The cell value of the original `transparentSSMapping` table at
    a given path, **derived** from the type-theoretic predicates. -/
def transparentSSMappingDerived : ClauseStructurePath → Prop
  | .bareModifier         => composesViaPM .predicateOfSituations
  | .bareArgument         => ∃ θ, saturatesTheta .predicateOfSituations θ
  | .nominalizedModifier  => composesViaPM .predicateOfIndividuals
  | .nominalizedArgument  => ∃ θ, saturatesTheta .predicateOfIndividuals θ

/-- The original `transparentSSMapping` (§5, def-as-table) **agrees**
    with the type-theoretic derivation cell-by-cell. This is the
    bridge mathlib audit demanded: the four-cell pattern is now
    derived rather than stipulated. -/
theorem transparentSSMapping_iff_typed (path : ClauseStructurePath) :
    transparentSSMapping path ↔ transparentSSMappingDerived path := by
  cases path
  case bareModifier =>
    refine ⟨fun _ => bareCP_composes_via_PM, fun _ => trivial⟩
  case bareArgument =>
    refine ⟨fun h => h.elim, ?_⟩
    rintro ⟨θ, hθ⟩
    exact (bareCP_satisfies_no_theta θ hθ).elim
  case nominalizedModifier =>
    refine ⟨fun h => h.elim, ?_⟩
    intro hpm; exact (nominalizedCP_not_PM_modifier hpm).elim
  case nominalizedArgument =>
    refine ⟨fun _ => ⟨.causer, nominalizedCP_satisfies_every_theta _⟩,
            fun _ => trivial⟩

-- ════════════════════════════════════════════════════════════════
-- § 12. Cross-linguistic ContP-exponent paradigm
-- ════════════════════════════════════════════════════════════════
--
-- Per cross-framework auditor: Tigrinya *kemzi* (Cacchioli2025),
-- Buryat *gɔ* (Fragments/Buryat/Complementizers), Korean *-ta*
-- (Fragments/Korean/Complementizers) form a paradigm of overt ContP
-- exponents that Bondarenko's analysis predicts cross-linguistically.
-- This list is grep-discoverable for downstream typology work.

/-- Cross-linguistic overt exponents of ContP per
    @cite{bondarenko-2022}'s analysis (§4.3.1 Buryat, §4.3.2 Korean)
    extended with Tigrinya *kemzi* (@cite{cacchioli-2025}). -/
def overtContPExponents : List (String × String) :=
  [ ("Tigrinya",  "kemzi"),  -- @cite{cacchioli-2025} factive
    ("Buryat",    "gɔ"),     -- @cite{bondarenko-2022} §4.3.1
    ("Korean",    "-ta") ]   -- @cite{bogal-allbritten-moulton-2018} / Bondarenko §4.3.2

-- ════════════════════════════════════════════════════════════════
-- § 13. Chapter 2 §2.2.3: noun-predicate co-occurrence diagnostics
-- ════════════════════════════════════════════════════════════════
--
-- The chapter-2 substantive distinct-denotation argument relies on
-- two empirical predicate-class co-occurrence asymmetries
-- (§2.2.3 ex. 105-112, pp. 102-105):
--
--   - Cont-NPs combine with truth-evaluable predicates ('true',
--     'false', 'mistaken'); Sit-NPs do NOT (paper ex. 105-107).
--   - Sit-NPs combine with occurrence/happening predicates
--     (Russian *proizojti* / *slučitsja* 'occur/happen'; Korean
--     *ilena* 'occur'); Cont-NPs do NOT (paper ex. 108-112).
--
-- These are not three independent stipulations but reflect the
-- type-theoretic distinction encoded in `NominalSort`: content
-- individuals carry propositional content (and so can be
-- truth-evaluated); situations are points of evaluation (and so
-- can occur/happen but lack truth values). The two predicates
-- below project the asymmetry from the sort.

/-- A nominal sort is *truth-evaluable* iff it can combine with
    'true' / 'false' / 'mistaken' — paper §2.2.3 ex. 105-107. -/
def NominalSort.truthEvaluable : NominalSort → Prop
  | .content   => True
  | .situation => False

instance : ∀ s, Decidable (NominalSort.truthEvaluable s) := fun s => by
  cases s <;> (unfold NominalSort.truthEvaluable; infer_instance)

/-- A nominal sort is *occurrence-compatible* iff it can combine
    with 'occur' / 'happen' (Russian *proizojti*, *slučitsja*;
    Korean *ilena*) — paper §2.2.3 ex. 108-112. -/
def NominalSort.occurrenceCompatible : NominalSort → Prop
  | .content   => False
  | .situation => True

instance : ∀ s, Decidable (NominalSort.occurrenceCompatible s) := fun s => by
  cases s <;> (unfold NominalSort.occurrenceCompatible; infer_instance)

/-- The two predicates partition the sorts: content is
    truth-evaluable but not occurrence-compatible; situation
    is occurrence-compatible but not truth-evaluable. -/
theorem truth_vs_occurrence_partition :
    NominalSort.truthEvaluable .content ∧
    ¬ NominalSort.occurrenceCompatible .content ∧
    ¬ NominalSort.truthEvaluable .situation ∧
    NominalSort.occurrenceCompatible .situation := by
  refine ⟨trivial, ?_, ?_, trivial⟩ <;> exact id

-- ════════════════════════════════════════════════════════════════
-- § 14. Chapter 2 §2.3 Proposal: the Cont head denotation
-- ════════════════════════════════════════════════════════════════
--
-- @cite{bondarenko-2022} §2.3 ex. 150 proposes:
--
--     ⟦Cont⟧^{s,g,t} = λp_{st}.λx_e. CONT(x) = p
--
-- which is precisely the existing `compC` from
-- `Theories/Semantics/Attitudes/ClauseDenotation/Content.lean`. So
-- the substrate primitive `compC` IS Bondarenko's proposed Cont
-- head denotation. This bridge is one-line `rfl`-grade — included
-- here to make the substrate-paper correspondence explicit.
--
-- The dual Comp head denotation (paper ex. 151)
--
--     ⟦Comp⟧^{s,g,t} = λp_{et}.λx_e. x ⊑ s ∧ x ⊩_e p
--
-- requires the *exact-exemplification* relation `⊩_e` from
-- truthmaker / Kratzer-1989 situation semantics, which has only
-- partial substrate support in linglib (see
-- `Core/Logic/Intensional/Situations.lean` for `Persistent` /
-- `IsWorld` but NO exemplification primitive). The Comp side is
-- thus deferred; the Cont side is bridged below.

/-- @cite{bondarenko-2022} §2.3 ex. 150 Cont head denotation IS
    the existing `compC` substrate (modulo argument order). The
    proposal at the chapter-2 level just instantiates the
    Kratzer/Moulton CONT-equality machinery already in linglib. -/
theorem cont_head_denotation_is_compC {W : Type*}
    (p : W → Prop) (xc : ContentIndividual W) :
    -- Bondarenko's ⟦Cont⟧(p)(x) = (CONT(x) = p)
    -- compC's signature: compC p xc = (xc.cont = p)
    compC p xc = (xc.cont = p) := rfl

/-- The Comp head denotation (paper ex. 151) is queued for
    formalisation. Stating the signature here for grep-
    discoverability; the body requires the `⊩_e` exact-
    exemplification relation from Truthmaker / Kratzer-1989 not
    yet a linglib substrate primitive. TODO: instantiate when
    `Theories/Semantics/Truthmaker/Exemplification.lean` lands. -/
def compHeadSignature {S : Type*} (_p : S → Prop) (_x : S) (_evalSit : S) : Prop :=
  -- Intended: x ⊑ evalSit ∧ x ⊩_e p
  -- Currently a placeholder — Truthmaker substrate not yet integrated.
  True

end Phenomena.Complementation.Studies.Bondarenko2022
