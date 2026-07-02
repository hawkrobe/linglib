import Linglib.Semantics.Attitudes.ClauseDenotation.Content
import Linglib.Semantics.Attitudes.ClauseDenotation.Situation
import Linglib.Fragments.Buryat.Complementizers
import Linglib.Fragments.Korean.Complementizers
import Linglib.Syntax.Clause.Complementation

/-!
# Bondarenko 2022: Anatomy of an Attitude [bondarenko-2022]

Tatiana Bondarenko (2022). MIT PhD dissertation. Thesis advisors:
P. Elliott, K. von Fintel, D. Fox, S. Iatridou, R. Schwarzschild.

## Locator convention

The §-numbers below DO NOT track a single dissertation chapter;
the file is paper-anchored as a whole and the sections were added
across multiple phases:

- §§ 1-7: reference [bondarenko-2022] Chapter 1 brief summary
  overview (locators verified at the chapter-1 level).
- §§ 8-12: reference Chapter 4 substantive bare-vs-nominalized
  treatment (Phase 2 type-theoretic refactor; §§4.2-4.5).
- §§ 13-14: reference Chapter 2 substantive distinct-denotation
  argument (Phase 3 §§2.2.3 noun-predicate co-occurrence + §2.3
  Cont/Comp head denotations).

Cross-chapter equivalence claims in the chapter-1 sections (e.g.
"Table 1.1 ↔ Table 4.1"; "ex. 1 ↔ §4.2 ex. 1-2") were noted from
context but not re-checked across chapters and carry implicit
`UNVERIFIED:` status. References to chapters not yet read carry
explicit `UNVERIFIED:` flags inline.

## Headline thesis

Embedded CPs receive **two kinds of denotations** corresponding to a
syntactic distinction in the left periphery (§1.1.1, paper ex. 1):

- **Cont-CP** ≔ λx. CONT(x) = {s : φ(s)}  — predicate on content
  individuals ([kratzer-2006]; [moulton-2009]; [moulton-2015];
  [elliott-2020-embedding]). Has an extra **ContP** projection that
  introduces the CONT function.
- **Sit-CP** ≔ λs'. s' is a minimal situation exemplifying φ —
  predicate on minimal situations ([kratzer-1989]). Lacks ContP.

In some languages ContP is overtly exposed (Korean -ta declarative;
Buryat gɘ 'say'); in others (English, Russian) it is null.

## Three substantive claims this file formalizes

1. **Equality semantics** for displacement (§1.1.1.2, paper eq. 7),
   not subset semantics (eq. 10) or existential (eq. 15). The
   Cont-CP denotes equality with the embedded proposition, so CONT
   is a function rather than a downward-closed relation. Three
   arguments converge: (i) nominal CP interpretation (paper §2.4),
   (ii) impossibility of CP conjunction ([bassi-bondarenko-2021]),
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

   This is the thesis [angelopoulos-2026] later attacks (autonomy
   of syntax: the same syntactic position can yield either
   composition mode at LF); per the chronology rule the comparison
   lives in `Studies/Angelopoulos2026.lean`
   (`transparency_conflates_axes`), which targets the
   `transparentSSMapping` definition below.

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
  null): lives in the per-language fragment files
  (`Fragments/Buryat/Complementizers.lean`,
  `Fragments/Korean/Complementizers.lean`; Russian has none yet),
  consumed by the §12 exponence projections below.
-/

namespace Bondarenko2022

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
    in `Semantics/Attitudes/ClauseDenotation/`; the typology-
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
-- § 3. CP Conjunction Impossibility ([bassi-bondarenko-2021])
-- ════════════════════════════════════════════════════════════════
--
-- Paper §1.1.1.2 argues the equality semantics predicts true CP
-- conjunction is impossible. Reasoning: if CONT is a function
-- (equality), then for any individual x, CONT(x) is a unique
-- proposition; CONT(x) = p1 AND CONT(x) = p2 forces p1 = p2.

/-- **Equality forces functionality**: if `x` has content `p1`
    under equality semantics AND `x` has content `p2` under
    equality semantics, then `p1 = p2`.

    [bassi-bondarenko-2021] derive the impossibility of true CP
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
-- ([barwise-1981], [higginbotham-1983]).
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
    Cont-CPs (NOT transparentAt).

    The everywhere-quantified variant (`∀ s', p s' ↔ q s'`) is
    `funext`+`propext`-trivial for any clause and carries no
    empirical content; only `At` is the substantive notion. -/
def ReferentiallyTransparentAt {S : Type*}
    (clause : (S → Prop) → S → Prop) (s : S) : Prop :=
  ∀ p q : S → Prop, (p s ↔ q s) → (clause p s ↔ clause q s)

/-- A Sit-CP (modeled as `fun p s' => p s'`) IS weak-transparent:
    its evaluation is at the actual situation `s`, so
    coextensional-at-s predicates yield the same value. -/
theorem sit_cp_transparentAt {S : Type*} (s : S) :
    ReferentiallyTransparentAt (fun p s' => p s') s := by
  intro p q hpq
  exact hpq

/-- **`compC` is operator-level intensional** (NOT
    weak-transparent): there exist two propositions `p, q`
    coextensional at the evaluation world such that `compC p xc`
    and `compC q xc` differ. Constructive witness via `W := Bool`:

    * `xc.cont := (fun b => b = false)` (true only at `false`)
    * `p := (fun b => b = false)` — agrees with `xc.cont`
    * `q := (fun _ => True)` — disagrees at `b = true`

    At evaluation world `false`, `p false ↔ q false` (both true);
    but `compC p xc` HOLDS (= xc.cont) while `compC q xc` FAILS
    (xc.cont differs from q at `true`).

    **Caveat (per syntax expert):** this is the *propositional-
    operator* shadow of Bondarenko's claim, not the full DP-level
    de dicto reading. Bondarenko §2.2.3 ex. 120 is specifically
    about substitution failure of two **DPs** (*this woman* /
    *the queen*) coextensional at the evaluation world but
    diverging across content-related worlds. The DP-level reading
    requires a binding-theoretic encoding of de dicto vs de re
    (an actuality-condition-style apparatus;
    [elliott-2020-embedding]'s CONT-as-content-restrictor) that is NOT yet a linglib
    substrate primitive. The theorem below establishes the
    operator-level intensionality that *underwrites* the DP-level
    de dicto reading; the DP-level theorem itself is queued. -/
theorem compC_not_transparentAt :
    ¬ ∀ (xc : ContentIndividual Bool) (w : Bool),
      ReferentiallyTransparentAt (fun p _ => compC p xc) w := by
  intro h
  let xc : ContentIndividual Bool := ⟨fun b => b = false⟩
  let p : Bool → Prop := fun b => b = false
  let q : Bool → Prop := fun _ => True
  have h_at : p false ↔ q false := by
    constructor
    · intro _; trivial
    · intro _; rfl
  have h_eq : compC p xc ↔ compC q xc := h xc false p q h_at
  have hp : compC p xc := rfl
  have hq : ¬ compC q xc := by
    intro heq
    -- xc.cont and q differ at b = true: xc.cont true = (true = false) = False
    -- but q true = True. Use congrFun + Bool.noConfusion.
    have h_true : (fun b : Bool => b = false) true = (fun _ : Bool => True) true :=
      congrFun heq true
    -- LHS reduces to `True = False` after rewriting `true = false ↔ False`.
    exact Bool.noConfusion <| (iff_of_eq h_true).mpr trivial
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
-- This is the thesis [angelopoulos-2026] §7.3 attacks.

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

    [angelopoulos-2026] attacks the bareArgument cell with
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
    is the EXACT cell [angelopoulos-2026] attacks. The proof
    is by table-unfolding; the substantive refutation lives in
    `Angelopoulos2026`. -/
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
-- `Studies/BondarenkoElliott2026.lean` (MSI,
-- MSO, TECM) presupposes the equality semantics defended here.
-- This bridge is informational; no formal dependency to chase.

/-- Bondarenko & Elliott 2026 inherit the **equality** semantics
    from this dissertation. The substantive bridge requires
    referencing a specific equality-using definition from
    `Studies/BondarenkoElliott2026.lean`
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
      with propositional content via CONT). Buryat participial
      nominalization — with or without the say-root *gɘ*
      ([bondarenko-2022] §4.3.1 ex. 31–32); Korean *-nun + kes*
      clause. -/
  | predicateOfIndividuals
  /-- Bare CP: type ⟨e,t⟩, predicate over (minimal) situations.
      Buryat *gɘžɘ*-clause; Korean *-ta* declarative; Russian
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
    ([halpert-schueler-2013], [elliott-2016],
    [roelofsen-uegaki-2021], [pietroski-2000]) is what makes
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
-- consume `Modifier.intersective` (the intersective-modification
-- substrate) — DO NOT redefine PM here. The
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
    `Modifier.intersective` substrate at
    `Semantics/Modification/Basic.lean` is the typed realisation; this
    Studies-level predicate is its qualitative projection. -/
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
-- § 12. Cross-linguistic ContP exponence
-- ════════════════════════════════════════════════════════════════
--
-- Per-language Cont-exponence analyses under [bondarenko-2022],
-- bundled with the laws tying them to the fragment inventories —
-- construction obligations discharged by `decide`, RingHom-style.
-- Buryat additionally carries the licenser-conditioned Comp
-- allomorphy (§4.3.1 ex. 33); the dissertation gives no such rule
-- for Korean, so its witness stays at `ContAnalysis`.
-- [cacchioli-2025]'s Tigrinya extension lives in
-- `Studies/Cacchioli2025.lean` per the chronology rule.

/-- A Cont-exponence analysis of one language's clause-typing
    inventory ([bondarenko-2022] ch. 4): which morpheme, if any,
    overtly expones Cont, tied by law to the fragment inventory
    (`none` = null exponence: English, Russian). A structure, not a
    class — rival frameworks construct rival witnesses. -/
structure ContAnalysis where
  /-- The fragment inventory analyzed. -/
  inventory : List Complementizer
  /-- The overt Cont exponent, if any. -/
  contExponent : Option Complementizer
  /-- The exponent is drawn from the inventory. -/
  contExponent_mem : ∀ c ∈ contExponent, c ∈ inventory

/-- A full Cont/Comp head assignment: `ContAnalysis` plus the
    licenser-conditioned Comp allomorphy and its laws. -/
structure ContCompAnalysis extends ContAnalysis where
  /-- Comp allomorph selected by the licensing category. -/
  compAllomorph : Complementizer.Licenser → Complementizer
  compAllomorph_mem : ∀ l, compAllomorph l ∈ inventory
  /-- The selected allomorph reproduces the fragment's distribution
      datum. -/
  licenser_compAllomorph : ∀ l, (compAllomorph l).licenser = some l
  /-- Head assignment is exhaustive over the inventory. -/
  cover : ∀ c ∈ inventory, c ∈ contExponent ∨ ∃ l, compAllomorph l = c

/-- Buryat (§4.3.1 ex. 33): *gɘ* expones Cont; the suffixes are Comp
    allomorphs — participial *-Aːša* next to nominal projections,
    converbial *-žA* next to verbs. -/
def buryatAnalysis : ContCompAnalysis where
  inventory := Buryat.complementizers
  contExponent := some Buryat.ge
  contExponent_mem := fun _ hc => by cases hc; exact .head _
  compAllomorph
    | .nominal => Buryat.aasha
    | .verbal  => Buryat.zha
  compAllomorph_mem := by
    intro l
    cases l
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (.head _))
  licenser_compAllomorph := by intro l; cases l <;> rfl
  cover := by
    intro c hc
    fin_cases hc
    · exact Or.inl rfl
    · exact Or.inr ⟨.nominal, rfl⟩
    · exact Or.inr ⟨.verbal, rfl⟩

/-- Korean (§4.3.2, following [bogal-allbritten-moulton-2018]): *-ta*
    expones Cont. No Comp allomorphy rule is given for Korean, so the
    witness stays at `ContAnalysis`. -/
def koreanAnalysis : ContAnalysis where
  inventory := Korean.Complementizers.complementizers
  contExponent := some Korean.Complementizers.ta
  contExponent_mem := fun _ hc => by cases hc; exact .head _

/-- Buryat-specific alignment, NOT a `ContAnalysis` law — Korean's
    Cont exponent *-ta* is itself a suffix (`verbForm = some .Fin`):
    in Buryat, the Cont exponent is exactly the non-suffixal
    say-root. -/
theorem mem_buryatContExponent_iff :
    ∀ c ∈ Buryat.complementizers,
      (c ∈ buryatAnalysis.contExponent ↔ c.verbForm = none) := by
  decide

/-- Positive-consistency check on the selection relation: each of
    *hanaxa*'s two frames (§4.4.3) is realized by exactly one member
    of the inventory — the bare-CP frame by converbial *-žA*, the
    nominalized frame by participial *-Aːša* — while the say-root *gɘ*
    (no `noonanType` of its own) realizes neither. -/
theorem hanaxa_frames_realized :
    Buryat.hanaxa.realizes Buryat.zha ∧
    Buryat.hanaxa.realizes Buryat.aasha ∧
    ¬ Buryat.hanaxa.realizes Buryat.ge :=
  ⟨⟨.finiteClause, .head _, rfl⟩, ⟨.gerund, .tail _ (.head _), rfl⟩,
    fun ⟨_, hf, h⟩ => by fin_cases hf <;> exact nomatch h⟩

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

instance : DecidablePred NominalSort.truthEvaluable
  | .content   => isTrue trivial
  | .situation => isFalse id

/-- A nominal sort is *occurrence-compatible* iff it can combine
    with 'occur' / 'happen' (Russian *proizojti*, *slučitsja*;
    Korean *ilena*) — paper §2.2.3 ex. 108-112. The footnote-28
    consultant comment ("*alachay* just does not sound good with
    'claim'") is a weaker rejection than False; the binary
    encoding here aggregates with the main paradigm. -/
def NominalSort.occurrenceCompatible : NominalSort → Prop
  | .content   => False
  | .situation => True

instance : DecidablePred NominalSort.occurrenceCompatible
  | .content   => isFalse id
  | .situation => isTrue trivial

-- The truth/occurrence partition is by-construction true (each is
-- a 2-cell `match`; the conjunction unfolds to four `rfl`s). The
-- substantive content lives in the projection definitions above,
-- not in a partition theorem; the audit-flagged
-- `truth_vs_occurrence_partition` rewrap was deleted as a vacuous
-- def-as-table tautology (mathlib + integration audit, Phase 3
-- re-audit).

-- ════════════════════════════════════════════════════════════════
-- § 14. Chapter 2 §2.3 Proposal: Cont and Comp head denotations
-- ════════════════════════════════════════════════════════════════
--
-- [bondarenko-2022] §2.3 ex. 150 proposes the Cont head
-- denotation; ex. 151 proposes the Comp head denotation. Both are
-- formalised below by consuming existing substrate (Layered
-- Grounding obligation per cross-framework audit).
--
-- **Cont head** (ex. 150): ⟦Cont⟧^{s,g,t} = λp_{st}.λx_e. CONT(x) = p
-- — IS the existing `compC` from
-- `Semantics/Attitudes/ClauseDenotation/Content.lean`.
--
-- **Comp head** (ex. 151): ⟦Comp⟧^{s,g,t} = λp_{et}.λx_e. x ⊑ s ∧ x ⊩_e p
-- — `x ⊑ s` is situation parthood (`Semantics/Intensional/
-- Situations.lean` `≼` / mathlib `≤`); `x ⊩_e p` is exact
-- exemplification (the bare verifier-membership `p x`,
-- distinguished from inexact exemplification `Truthmaker/Inexact.
-- lean inexactVer` which existentially closes over parts).
--
-- **Substantiation status (per syntax expert S6).** The
-- *justification* for the equality shape of Cont (vs subset
-- `entails` or existential) lives partly in §3 above
-- (`cont_function_blocks_conjunction` — [bassi-bondarenko-2021]
-- argument) and partly in [bondarenko-2022] §2.4 (deferred:
-- the nominal-CP-interpretation argument). One of three §2.4
-- arguments is therefore already present in this file.
--
-- **Note (per syntax expert S3).** The situation-parameter `s` in
-- ex. 150 is omitted in this Chapter-2 reduction; [bondarenko-2022]
-- footnote 37 anticipates it becoming consequential in §5.2.3
-- (clauses as restrictors of existential quantifiers). When
-- Chapter 5 is formalised, the parameter must be re-introduced.

/-- [bondarenko-2022] §2.3 ex. 150 Cont head denotation IS
    the existing `compC` substrate. The denotational identity is
    one-line — the substantive Layered-Grounding fact is that
    Bondarenko's Chapter-2 proposal does NOT introduce new
    machinery; it instantiates the Kratzer/Moulton CONT-equality
    apparatus already in linglib. -/
theorem cont_head_denotation_is_compC {W : Type*}
    (p : W → Prop) (xc : ContentIndividual W) :
    compC p xc ↔ (xc.cont = p) := Iff.rfl

/-- [bondarenko-2022] §2.3 ex. 151 Comp head denotation,
    consuming the Truthmaker substrate
    (`Semantics/Truthmaker/Basic.lean` `attHolds`-style
    parthood `s ≤ σ x`, `Semantics/Truthmaker/Inexact.lean`
    `inexactVer` for the part-existential variant) and situation
    parthood (`Semantics/Intensional/Situations.lean` `≼`).

    `compHead p x evalSit` holds iff `x` is a situation that is
    part of the evaluation situation AND `x` exactly verifies `p`
    (verifier-membership; distinguished from inexact exemplification
    where existential closure over parts is allowed).

    Type signature follows Bondarenko's `⟨e,t⟩` shape with `S` as
    the situation-typed-individual sort: `p : S → Prop` is the
    propositional argument, `x : S` is the candidate verifier,
    `evalSit : S` is the evaluation situation. -/
def compHead {S : Type*} [Preorder S]
    (p : S → Prop) (x evalSit : S) : Prop :=
  x ≤ evalSit ∧ p x

/-- Exact exemplification implies inexact exemplification (a
    verifier is a part of itself). Substrate connection to
    `Semantics/Truthmaker/Inexact.lean`'s
    `inexactVer_of_exact`. -/
theorem compHead_implies_inexactVerifier {S : Type*} [Preorder S]
    (p : S → Prop) (x evalSit : S) (h : compHead p x evalSit) :
    ∃ u, u ≤ evalSit ∧ p u :=
  ⟨x, h.1, h.2⟩

end Bondarenko2022
