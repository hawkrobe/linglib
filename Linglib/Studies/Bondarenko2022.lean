import Linglib.Semantics.Attitudes.ClauseDenotation.Content
import Linglib.Semantics.Attitudes.ClauseDenotation.Situation
import Linglib.Fragments.Buryat.Complementizers
import Linglib.Fragments.Korean.Complementizers
import Linglib.Syntax.Clause.Complementation
import Linglib.Data.Examples.Bondarenko2022

/-!
# Bondarenko 2022: Anatomy of an Attitude

[bondarenko-2022]

Embedded CPs receive two denotations, tracking a left-peripheral syntactic
distinction (§1.1.1, ex. 1): a Cont-CP denotes a predicate on content
individuals via CONT ([kratzer-2006]; [moulton-2009]; [moulton-2015];
[elliott-2020-embedding]) and projects a ContP; a Sit-CP denotes a predicate
on minimal exemplifying situations ([kratzer-1989]) and lacks one. ContP is
overt in Korean (*-ta*) and Buryat (*gɘ* 'say'), null in English and Russian.

Formalized here: equality semantics for displacement (eq. 7) against subset
(eq. 10) and existential (eq. 15), whence the impossibility of true CP
conjunction ([bassi-bondarenko-2021]); Sit-CP transparency vs Cont-CP opacity
(§1.1.1.1 ex. 5-6); and the transparent syntax-semantics mapping thesis
(§1.1.2, ch. 4) — bare CPs compose only as modifiers, nominalized CPs only as
arguments — later attacked by [angelopoulos-2026] (comparison in
`Studies/Angelopoulos2026.lean`, per the chronology rule).

## Main declarations

- `ExistentialContent` — the rejected existential semantics (eq. 15)
- `cont_function_blocks_conjunction` — equality forces CONT-functionality
- `ReferentiallyTransparentAt`, `compC_not_transparentAt` — the weak
  transparency contrast
- `saturatesTheta`, `bareCP_satisfies_no_theta` — the ch. 4 type-mismatch
  mechanism behind the Causer/Theme/About bans
- `transparentSSMapping`, `transparentSSMapping_iff_typed` — the mapping table
  and its type-theoretic derivation
- `NominalSort.truthEvaluable`, `NominalSort.occurrenceCompatible` — the ch. 2
  co-occurrence asymmetries
- `ContAnalysis`, `buryatAnalysis`, `koreanAnalysis` — per-language ContP
  exponence, tied by law to the fragment inventories
- `compHead` — the Comp head denotation (§2.3 ex. 151)

## Implementation notes

Bare `§`/`ex.`/`eq.` locators refer to the dissertation and were verified
against its text. Sections track different chapters: nominal sorts through the
BE2026 bridge follow the ch. 1 summary, the type-theoretic sections ch. 4
(§§4.2-4.5), the co-occurrence and head-denotation sections ch. 2 (§2.2.3,
§2.3). The ch. 1 summary repeats later material: Table 1.1 = Table 4.1, and
ch. 1 ex. 1 = §4.2 ex. 1-2.

Out of scope: ch. 3 clausal coordination (only the conjunction-impossibility
theorem lands here), ch. 5 polarity subjunctives (Russian NPI data,
L-analyticity), and the morphological exposition of ContP, which lives in
`Fragments/Buryat/Complementizers.lean` and
`Fragments/Korean/Complementizers.lean`.

Typed paradigm sentences (§2.2.3 ex. 105–112, 120–122; §4.3.1 ex. 30–32) live
in `Bondarenko2022.Examples`, generated from `Data/Examples/Bondarenko2022.json`.
-/

namespace Bondarenko2022

open Semantics.Attitudes (ContentIndividual)
open Semantics.Attitudes.ClauseDenotation.Content (compC ContentNoun)
open Semantics.Attitudes.ClauseDenotation.Situation
  (SituationIndividual SituationNoun compPu)

/-! ### Nominal sorts -/

/-- The dissertation's typology of nouns combining with embedded CPs (§2.2).
Studies-local: the substrate (`ContentIndividual`, `SituationIndividual`)
lives in `Semantics/Attitudes/ClauseDenotation/`. -/
inductive NominalSort where
  /-- Content nouns (§2.2): *idea*, *rumor*, *hypothesis*, *claim*, *fact*,
      *lie*. -/
  | content
  /-- Situation nouns (§2.2): *situation*, *event*, *case*, *circumstance*,
      *state of affairs*. -/
  | situation
  deriving DecidableEq, Repr

/-! ### Equality vs. subset vs. existential semantics

§1.1.1.2. The substrate exposes equality as `compC` and subset as
`ContentIndividual.entails`; only the existential candidate is new here. -/

/-- Existential semantics for a Cont-CP (eq. 15): `CONT(x) ∩ p ≠ ∅`. Rejected
by the thesis in favor of equality (`compC`, eq. 7); subset is eq. 10. -/
def ExistentialContent {W : Type*} (xc : ContentIndividual W)
    (p : W → Prop) : Prop :=
  ∃ w : W, xc.cont w ∧ p w

/-- Equality is stronger than subset (§1.1.1.2); re-export of
`ContentIndividual.eq_implies_entails`. -/
theorem equality_implies_subset {W : Type*} (xc : ContentIndividual W)
    (p : W → Prop) : compC p xc → xc.entails p :=
  ContentIndividual.eq_implies_entails xc p

/-- Equality implies existential for nonempty content; the empty-content
witness in `ContentIndividual` shows the proviso is real. -/
theorem equality_implies_existential {W : Type*}
    (xc : ContentIndividual W) (p : W → Prop)
    (hne : ∃ w, xc.cont w) :
    compC p xc → ExistentialContent xc p := by
  intro heq
  obtain ⟨w, hw⟩ := hne
  exact ⟨w, hw, heq ▸ hw⟩

/-! ### CP conjunction impossibility

Equality semantics makes CONT a function, so true CP conjunction is impossible
([bassi-bondarenko-2021], §1.1.1.2). -/

/-- Equality forces functionality: two contents assigned to the same
individual coincide. -/
theorem cont_function_blocks_conjunction {W : Type*}
    (xc : ContentIndividual W) (p1 p2 : W → Prop) :
    compC p1 xc → compC p2 xc → p1 = p2 := by
  intro h1 h2
  exact h1.symm.trans h2

/-- Subset does not force functionality: a non-vacuous content individual
entails every superset of its content. Witness over `Bool`. -/
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
  -- The propositions disagree at `false`.
  exact (iff_of_eq (congr_fun heq false)).mpr trivial |> Bool.noConfusion

/-! ### Sit-CP transparency vs. Cont-CP opacity

The substitution test (§2.2.3 ex. 120-122; summarized at ch. 1 ex. 5-6):
coextensional DPs substitute salva veritate under a Sit-NP but not under a
Cont-NP — Cont-CPs are a referentially opaque domain ([barwise-1981],
[higginbotham-1983]). Everywhere-coextensional transparency is
`funext`-trivial; the substantive notion is transparency at the evaluation
world. -/

/-- Weak transparency at `s`: substituting predicates that agree at `s`
preserves clause truth. -/
def ReferentiallyTransparentAt {S : Type*}
    (clause : (S → Prop) → S → Prop) (s : S) : Prop :=
  ∀ p q : S → Prop, (p s ↔ q s) → (clause p s ↔ clause q s)

/-- A Sit-CP evaluates at the actual situation, hence is weak-transparent. -/
theorem sit_cp_transparentAt {S : Type*} (s : S) :
    ReferentiallyTransparentAt (fun p s' => p s') s := by
  intro p q hpq
  exact hpq

/-- `compC` is not weak-transparent (witness over `Bool`). This is the
propositional-operator shadow of the §2.2.3 ex. 120 DP-level de dicto claim,
whose binding-theoretic encoding ([elliott-2020-embedding]'s
CONT-as-content-restrictor) is not yet substrate. -/
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
    -- xc.cont and q differ at `b = true`.
    have h_true : (fun b : Bool => b = false) true = (fun _ : Bool => True) true :=
      congrFun heq true
    exact Bool.noConfusion <| (iff_of_eq h_true).mpr trivial
  exact hq (h_eq.mp hp)

/-! ### The transparent syntax-semantics mapping thesis

§1.1.2: bare CPs must compose as modifiers (PM via the situation argument),
nominalized CPs as arguments (FA via the DP argument). [angelopoulos-2026]
§7.3 attacks this thesis. -/

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

/-- The mapping thesis as a four-cell table (§1.1.2, ch. 4): the off-diagonal
cells are impossible. Paper-fidelity bookkeeping —
`transparentSSMapping_iff_typed` derives the cells from the type-theoretic
apparatus; [angelopoulos-2026] attacks the `bareArgument` cell with Greek
*oti*/*pu*. -/
def transparentSSMapping : ClauseStructurePath → Prop
  | .bareModifier => True
  | .bareArgument => False
  | .nominalizedModifier => False
  | .nominalizedArgument => True

/-- The (bare, argument) cell is empty — the cell [angelopoulos-2026] attacks
(see `Angelopoulos2026`). -/
theorem bare_argument_predicted_impossible :
    ¬ transparentSSMapping .bareArgument := by
  intro h; exact h

/-- The (nominalized, modifier) cell is empty. -/
theorem nominalized_modifier_predicted_impossible :
    ¬ transparentSSMapping .nominalizedModifier := by
  intro h; exact h

/-- The diagonal cells are available. -/
theorem diagonal_attested :
    transparentSSMapping .bareModifier ∧
    transparentSSMapping .nominalizedArgument :=
  ⟨trivial, trivial⟩

/-! ### Composition paths (Table 1.1) -/

/-- Table 1.1's two composition paths: PM with the verb's situation argument,
or FA into a DP argument slot. -/
inductive CompositionPath where
  | viaSituation
  | viaDPArgument
  deriving DecidableEq, Repr

/-- Table 1.1 (attitude and speech verbs; occurrence verbs are exempt,
§4.3.3): the (Sit-CP, `viaSituation`) cell is unattested — intersective
combination yields always-trivially-false sentences. -/
def attestedCombination : NominalSort → CompositionPath → Prop
  | .content, _              => True   -- Cont-CP via either path
  | .situation, .viaDPArgument => True -- Sit-CP via DP-argument path
  | .situation, .viaSituation  => False -- Sit-CP via Situation path: ✗

/-- The (Sit-CP, viaSituation) cell is empty by semantic triviality
(§1.1.2). -/
theorem sit_cp_via_situation_blocked :
    ¬ attestedCombination .situation .viaSituation := by
  intro h; exact h

/-! ### Bridge to BondarenkoElliott2026 -/

/-- Bondarenko & Elliott 2026's MSI/MSO/TECM apparatus presupposes the
equality semantics `CONT(x) = ⟦S⟧` defended here; the cross-file bridge awaits
a stable BE2026 lemma (this file does not import BE2026). -/
theorem be2026_inherits_equality_substrate {W : Type*}
    (xc : ContentIndividual W) (p : W → Prop) :
    compC p xc ↔ xc.cont = p := Iff.rfl

/-! ### Type-theoretic apparatus (§4.2)

The §4.4 bans are type-theoretic, not structural: bare CPs are ⟨e,t⟩,
nominalized CPs ⟨e⟩, Θ-heads require ⟨e⟩; N/D presence is the exponence of the
type-shift, not its cause. In Bare Phrase Structure the X-bar
argument/modifier distinction is gone, so the "modifier" claim is semantic. -/

/-- The two semantic types the derivation uses: saturated ⟨e⟩ vs unsaturated
⟨e,t⟩. -/
inductive SemType where
  | individual
  | predicate
  deriving DecidableEq, Repr

/-- The bare-vs-nominalized cut (§4.2), named by semantic content per Bare
Phrase Structure. -/
inductive ClauseType where
  /-- Nominalized CP: type ⟨e⟩. Buryat participial nominalization, with or
      without the say-root *gɘ* (§4.3.1 ex. 31–32); Korean *-nun + kes*
      clause. -/
  | predicateOfIndividuals
  /-- Bare CP: type ⟨e,t⟩, predicate over (minimal) situations. Buryat
      *gɘžɘ*-clause; Korean *-ko*-clause; Russian bare *čto*-clause. -/
  | predicateOfSituations
  deriving DecidableEq, Repr

/-- Nominalized → individual, bare → predicate. -/
def ClauseType.semanticType : ClauseType → SemType
  | .predicateOfIndividuals => .individual
  | .predicateOfSituations  => .predicate

/-- The Θ-heads of §4.4, all sharing one selectional restriction: an
individual argument. Per-Θ presupposition flavor is deferred. -/
inductive ThetaHead where
  /-- Θ_Causer. §4.4.1. -/
  | causer
  /-- Θ_Theme (internal-argument introducer). §4.4.2. -/
  | theme
  /-- Θ_About: introduces the res-argument the attitude is about
      ([quine-1956]; [cresswell-vonstechow-1982]); carries a pre-existence
      presupposition not formalised here. §4.4.3. -/
  | aboutAttitude
  deriving DecidableEq, Repr

/-- Every Θ-head requires an individual argument. -/
def ThetaHead.requiredType : ThetaHead → SemType
  | _ => .individual

/-- A clause type saturates a Θ-head iff its semantic type matches the head's
required type (§4.2). -/
def saturatesTheta (ct : ClauseType) (θ : ThetaHead) : Prop :=
  ct.semanticType = θ.requiredType

instance : ∀ (ct : ClauseType) (θ : ThetaHead),
    Decidable (saturatesTheta ct θ) := fun ct θ => by
  unfold saturatesTheta; infer_instance

/-! ### Causer, Theme, About (§4.4)

The three bans are one type-mismatch mechanism, not three stipulations. -/

/-- §4.4.1: bare CPs cannot be Causers. -/
theorem bareCP_not_Causer :
    ¬ saturatesTheta .predicateOfSituations .causer := by
  intro h; exact SemType.noConfusion h

/-- §4.4.2: bare CPs cannot be Theme-arguments; cf. the *explain*-class data
([pietroski-2000], [halpert-schueler-2013], [elliott-2016],
[roelofsen-uegaki-2021]). -/
theorem bareCP_not_Theme :
    ¬ saturatesTheta .predicateOfSituations .theme := by
  intro h; exact SemType.noConfusion h

/-- §4.4.3: bare CPs cannot be About-arguments. -/
theorem bareCP_not_About :
    ¬ saturatesTheta .predicateOfSituations .aboutAttitude := by
  intro h; exact SemType.noConfusion h

/-- Bare CPs satisfy no Θ-head (§4.4). -/
theorem bareCP_satisfies_no_theta :
    ∀ θ : ThetaHead, ¬ saturatesTheta .predicateOfSituations θ := by
  intro θ h; exact SemType.noConfusion h

/-- Nominalized CPs satisfy every Θ-head. -/
theorem nominalizedCP_satisfies_every_theta :
    ∀ θ : ThetaHead, saturatesTheta .predicateOfIndividuals θ := by
  intro θ; rfl

/-! ### The modifier path (§4.5)

Bare CPs compose with the verb's situation argument by Predicate Modification;
`composesViaPM` is the qualitative projection of the `Modifier.intersective`
substrate (`Semantics/Modification/Basic.lean`), whose Frame-typed
instantiation is queued. -/

/-- PM-compatibility with a verbal situation argument: bare CPs qualify,
nominalized CPs do not. -/
def composesViaPM : ClauseType → Prop
  | .predicateOfIndividuals => False  -- nominalised, no PM compatibility
  | .predicateOfSituations  => True   -- bare, PM-compatible

instance : ∀ ct, Decidable (composesViaPM ct) := fun ct => by
  cases ct <;> (unfold composesViaPM; infer_instance)

/-- §4.5: bare CPs are verbal modifiers. -/
theorem bareCP_composes_via_PM : composesViaPM .predicateOfSituations := trivial

/-- Nominalized CPs compose via FA, not PM (§4.5). -/
theorem nominalizedCP_not_PM_modifier : ¬ composesViaPM .predicateOfIndividuals :=
  fun h => h

/-! ### Deriving the mapping table -/

/-- The table's cell values, derived from the type-theoretic predicates. -/
def transparentSSMappingDerived : ClauseStructurePath → Prop
  | .bareModifier         => composesViaPM .predicateOfSituations
  | .bareArgument         => ∃ θ, saturatesTheta .predicateOfSituations θ
  | .nominalizedModifier  => composesViaPM .predicateOfIndividuals
  | .nominalizedArgument  => ∃ θ, saturatesTheta .predicateOfIndividuals θ

/-- The §1.1.2 table agrees cell-by-cell with the type-theoretic derivation:
the four-cell pattern is derived, not stipulated. -/
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

/-! ### Cross-linguistic ContP exponence

Per-language Cont-exponence analyses (ch. 4), tied by law to the fragment
inventories. Buryat carries the licenser-conditioned Comp allomorphy (§4.3.1
ex. 33); Korean's parallel rule (§4.3.2 ex. 46) is not yet law-checked, so its
witness stays at `ContAnalysis`. [cacchioli-2025]'s Tigrinya extension lives
in `Studies/Cacchioli2025.lean` per the chronology rule. -/

open Buryat

/-- A Cont-exponence analysis of one language's clause-typing inventory
(ch. 4): the morpheme, if any, overtly exponing Cont (`none` = null exponence:
English, Russian). A structure, not a class — rival frameworks construct
rival witnesses. -/
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
allomorphs — participial *-Aːša* next to nominal projections, converbial
*-žA* next to verbs. -/
def buryatAnalysis : ContCompAnalysis where
  inventory := complementizers
  contExponent := some ge
  contExponent_mem := fun _ hc => by cases hc; exact .head _
  compAllomorph
    | .nominal => aasha
    | .verbal  => zha
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

/-- Korean (§4.3.2 ex. 46; cf. [bogal-allbritten-moulton-2018]): *-ta*
expones Cont; adnominal *-nun* and adverbal *-ko* are the Comp
allomorphs, parallel to Buryat ex. 33. -/
def koreanAnalysis : ContCompAnalysis where
  inventory := Korean.Complementizers.complementizers
  contExponent := some Korean.Complementizers.ta
  contExponent_mem := fun _ hc => by cases hc; exact .head _
  compAllomorph
    | .nominal => Korean.Complementizers.nun
    | .verbal  => Korean.Complementizers.ko
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

/-- In Buryat the Cont exponent is exactly the non-suffixal say-root — a
Buryat-specific alignment, not a `ContAnalysis` law (Korean's *-ta* is itself
a suffix). -/
theorem mem_buryatContExponent_iff :
    ∀ c ∈ complementizers,
      (c ∈ buryatAnalysis.contExponent ↔ c.verbForm = none) := by
  decide

/-- Each of *hanaxa*'s two frames (§4.4.3) is realized by exactly one
clause-typer — bare by converbial *-žA*, nominalized by participial *-Aːša* —
and the say-root *gɘ* realizes neither. -/
theorem hanaxa_frames_realized :
    hanaxa.realizes zha ∧
    hanaxa.realizes aasha ∧
    ¬ hanaxa.realizes ge :=
  ⟨⟨.finiteClause, .head _, rfl⟩, ⟨.gerund, .tail _ (.head _), rfl⟩,
    fun ⟨_, hf, h⟩ => by fin_cases hf <;> exact nomatch h⟩

/-! ### Noun-predicate co-occurrence (§2.2.3)

Cont-NPs combine with truth-evaluable predicates, Sit-NPs do not
(ex. 105-107); Sit-NPs combine with occurrence predicates, Cont-NPs do not
(ex. 108-112). Both asymmetries project the `NominalSort` distinction:
contents are truth-evaluated, situations occur. -/

/-- Combines with 'true' / 'false' / 'mistaken' (ex. 105-107). -/
def NominalSort.truthEvaluable : NominalSort → Prop
  | .content   => True
  | .situation => False

instance : DecidablePred NominalSort.truthEvaluable
  | .content   => isTrue trivial
  | .situation => isFalse id

/-- Combines with 'occur' / 'happen' (Russian *proizojti*, *slučit'sja*;
Korean *ilena*) — ex. 108-112. The footnote-28 hedge on *alachay* is
aggregated with the main paradigm. -/
def NominalSort.occurrenceCompatible : NominalSort → Prop
  | .content   => False
  | .situation => True

instance : DecidablePred NominalSort.occurrenceCompatible
  | .content   => isFalse id
  | .situation => isTrue trivial

/-! ### Cont and Comp head denotations (§2.3)

Ex. 150: ⟦Cont⟧ = λp.λx. CONT(x) = p — exactly the substrate `compC`.
Ex. 151: ⟦Comp⟧ = λp.λx. x ⊑ s ∧ x ⊩ p — parthood plus exact exemplification.
The dissertation's own abbreviation of ex. 151 drops the anchoring conjunct;
its footnote 37 notes the anchoring matters in §5.2.3 (clauses as restrictors
of existential quantifiers). `compHead` keeps it. -/

/-- Ex. 150 is the existing `compC` — the ch. 2 proposal introduces no new
machinery. The equality shape is further defended in §2.4 (no-stacking,
ex. 171; *the fact* definiteness, ex. 177-178; the complex-claim argument,
ex. 183-184), unformalized. -/
theorem cont_head_denotation_is_compC {W : Type*}
    (p : W → Prop) (xc : ContentIndividual W) :
    compC p xc ↔ (xc.cont = p) := Iff.rfl

/-- Ex. 151: `x` is part of the evaluation situation and exactly verifies `p`
(verifier-membership, vs the part-existential `inexactVer` of
`Semantics/Truthmaker/Inexact.lean`). -/
def compHead {S : Type*} [Preorder S]
    (p : S → Prop) (x evalSit : S) : Prop :=
  x ≤ evalSit ∧ p x

/-- Exact exemplification implies inexact: a verifier is a part of itself
(cf. `inexactVer_of_exact`). -/
theorem compHead_implies_inexactVerifier {S : Type*} [Preorder S]
    (p : S → Prop) (x evalSit : S) (h : compHead p x evalSit) :
    ∃ u, u ≤ evalSit ∧ p u :=
  ⟨x, h.1, h.2⟩

end Bondarenko2022
