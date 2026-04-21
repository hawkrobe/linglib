import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Definiteness
import Linglib.Core.Nominal.Maximality
import Linglib.Core.IntensionalLogic.Rigidity
import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.PrecisionProjection
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Theories.Semantics.Definiteness.Basic
import Linglib.Theories.Semantics.Reference.Donnellan
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Nouns

/-!
# @cite{elbourne-2013}: Situation-Semantic Definite Descriptions @cite{elbourne-2013}
@cite{barwise-perry-1983} @cite{elbourne-2005} @cite{heim-1982} @cite{postal-1966} @cite{schwarz-2009} @cite{kamp-1981} @cite{stanley-szab-2000} @cite{tonhauser-beaver-roberts-simons-2013} @cite{roberts-2012}
@cite{donnellan-1966} @cite{kripke-1977} @cite{karttunen-1974}

Formalizes the core theoretical machinery and empirical predictions from:

  Elbourne, P. (2013). Definite Descriptions.
  Oxford Studies in Semantics and Pragmatics 1.

Elbourne argues that definite descriptions have a Fregean/Strawsonian
semantics — they are type e, introduce a presupposition of existence +
uniqueness, and are evaluated *relative to situations* (parts of worlds).

The single lexical entry ⟦the⟧ = λf.λs : ∃!x f(x)(s) = 1. ιx f(x)(s) = 1
unifies:
- Referential vs attributive uses (Ch 5): free vs bound situation pronoun
- Presupposition projection (Ch 4): domain conditions + λ-Conversion
- Donkey anaphora (Ch 6): pronouns = the + NP-deletion; minimal situations
- De re / de dicto (Ch 7): scope of situation binding, not DP scope
- Incomplete definites (Ch 9): situation restricts evaluation domain
- Existence entailments (Ch 8): presupposition projects to belief states

## Key Results

- `the_sit` / `the_sit'`: Elbourne's situation-relative ⟦the⟧
- `the_sit_at_world_eq_the_uniq_w`: specializes to existing `the_uniq_w`
- `attributive_is_the_sit_bound`: Donnellan's attributive = `the_sit'` (bound s)
- `donkey_uniqueness_from_minimality`: minimal situations yield uniqueness
- `pronoun_is_definite_article`: ⟦it⟧ = ⟦the⟧
- `the_sit_assertion_implies_presup`: assertion entails presupposition

## Empirical Chain

```
Fragments/English/Determiners.lean
  "the": qforce =.definite → the_sit / the_sit'
Fragments/English/Pronouns.lean
  "it"/"he"/"she": pronounType =.personal, person =.third → the_sit' + NP-deletion
    ↓
(this file: theory + empirical predictions)
  referential/attributive → truth values → match empirical judgments
  incomplete definites → situation-relative uniqueness
  donkey anaphora → minimality → uniqueness
```

-/

namespace Elbourne2013

open Core (WorldTimeIndex)

open Core.Presupposition (PrProp)
open Core.Presupposition.PrProp (presupOfReferent presupOfReferent_presup
  presupOfReferent_assertion_some presupOfReferent_assertion_none)
open Core.Nominal (russellIotaList)
open Core.Definiteness (DefPresupType)
open Core.SitVarStatus (SitVarStatus)
open Semantics.Definiteness (qforceToPresupType)
open Semantics.Reference.Donnellan (definitePrProp UseMode attributiveContent)


-- ════════════════════════════════════════════════════════════════
-- §1: Situation Ontology (@cite{barwise-perry-1983}, @cite{kratzer-1989})
-- ════════════════════════════════════════════════════════════════

/-- A situation frame: the ontological foundation for Elbourne's system.

Situations are parts of worlds, ordered by a part-of relation ≤.
Worlds are maximal situations. Properties and quantifiers are evaluated
relative to situations rather than worlds, enabling situation-dependent
uniqueness and domain restriction.

Based on @cite{barwise-perry-1983}: situations are "individuals having
properties and standing in relations at various spatiotemporal locations".
@cite{kratzer-1989}: situations are parts of worlds with a mereological structure. -/
structure SituationFrame where
  /-- Domain of situations (D_s) — includes both partial situations and worlds -/
  Sit : Type
  /-- Domain of entities (D_e) -/
  Ent : Type
  /-- Part-of relation (≤): s₁ ≤ s₂ means s₁ is part of s₂ -/
  le : Sit → Sit → Prop
  /-- Reflexivity: every situation is part of itself -/
  le_refl : ∀ s, le s s
  /-- Transitivity: part-of is transitive -/
  le_trans : ∀ s₁ s₂ s₃, le s₁ s₂ → le s₂ s₃ → le s₁ s₃
  /-- Antisymmetry: mutual part-of implies identity -/
  le_antisymm : ∀ s₁ s₂, le s₁ s₂ → le s₂ s₁ → s₁ = s₂

/-- A world is a maximal situation — one that no other situation properly extends. -/
def SituationFrame.isWorld (F : SituationFrame) (s : F.Sit) : Prop :=
  ∀ s', F.le s s' → s = s'

/-- A situation s is minimal for property P iff P holds at s and at
no proper part of s. Minimality is key for donkey anaphora (Ch 6):
in a minimal situation where "a farmer owns a donkey", there is
exactly one farmer and one donkey, securing uniqueness. -/
def SituationFrame.isMinimal (F : SituationFrame)
    (P : F.Sit → Bool) (s : F.Sit) : Prop :=
  P s = true ∧ ∀ s', F.le s' s → P s' = true → s' = s


-- ════════════════════════════════════════════════════════════════
-- §2: The Situation-Relative Definite Article (@cite{elbourne-2013}, Ch 3)
-- ════════════════════════════════════════════════════════════════

/-- ⟦the⟧ in Elbourne's system: the situation-relative Fregean definite.

⟦the⟧ = λf_{⟨e,st⟩}.λs : s ∈ D_s ∧ ∃!x f(x)(s) = 1. ιx f(x)(s) = 1

Takes a restrictor (property of entities relative to situations) and a
situation, presupposes existence+uniqueness *in that situation*, and
returns the unique satisfier.

Built from the canonical `presupOfReferent` combinator with
`russellIotaList` as the per-situation referent selector.

The situation parameter `s` may be:
- **Free** (referential use, Ch 5): mapped to a contextually salient s*
- **Bound** (attributive use, Ch 5): bound by a higher operator (ς, Σ)
- **Bound by quantifier** (donkey anaphora, Ch 6): bound by always/GEN -/
def the_sit (F : SituationFrame) (domain : List F.Ent)
    (restrictor : F.Ent → F.Sit → Bool)
    (scope : F.Ent → F.Sit → Bool)
    : PrProp F.Sit :=
  presupOfReferent (fun s => russellIotaList domain (fun e => restrictor e s))
                   scope

/-- `the_sit` instantiated with bare type parameters (no SituationFrame).
    Coincides with `Donnellan.definitePrProp` — the same Russellian iota
    factored through `presupOfReferent`. -/
def the_sit' {W E : Type} (domain : List E)
    (restrictor : E → W → Bool) (scope : E → W → Bool) : PrProp W :=
  presupOfReferent (fun w => russellIotaList domain (fun e => restrictor e w))
                   scope


-- ════════════════════════════════════════════════════════════════
-- §3: Bridge to Donnellan's `definitePrProp`
-- ════════════════════════════════════════════════════════════════

/-- `the_sit'` and `Donnellan.definitePrProp` denote the same `PrProp`:
    both factor through `presupOfReferent` applied to a Russellian iota
    over the domain. The two names reflect different theoretical lineages
    (Elbourne's situation semantics vs. Donnellan's attributive use); the
    denotation is one and the same. -/
theorem the_sit'_eq_definitePrProp
    {W E : Type} (domain : List E)
    (restrictor : E → W → Bool) (scope : E → W → Bool) :
    the_sit' domain restrictor scope = definitePrProp domain restrictor scope :=
  rfl

/-- The presupposition of `the_sit'` is determined solely by the filter result. -/
theorem the_sit_presup_depends_on_filter
    {W E : Type} (domain₁ domain₂ : List E)
    (restrictor scope : E → W → Bool) (w : W)
    (h : domain₁.filter (λ e => restrictor e w) =
         domain₂.filter (λ e => restrictor e w)) :
    (the_sit' domain₁ restrictor scope).presup w =
    (the_sit' domain₂ restrictor scope).presup w := by
  simp only [the_sit', presupOfReferent_presup, russellIotaList, h]

/-- A true assertion entails a satisfied presupposition. -/
theorem the_sit_assertion_implies_presup
    {W E : Type} (domain : List E)
    (restrictor : E → W → Bool) (scope : E → W → Bool)
    (w : W) (h : (the_sit' domain restrictor scope).assertion w = true) :
    (the_sit' domain restrictor scope).presup w = true := by
  simp only [the_sit', presupOfReferent, russellIotaList] at h ⊢
  split at h <;> simp_all [Option.isSome]


-- ════════════════════════════════════════════════════════════════
-- §4: Referential vs Attributive (@cite{elbourne-2013}, Ch 5)
-- ════════════════════════════════════════════════════════════════

/-- Donnellan's attributive semantics IS `the_sit'` with a bound situation
variable. -/
theorem attributive_is_the_sit_bound
    {W E : Type} (domain : List E)
    (restrictor : E → W → Bool) (scope : E → W → Bool) :
    definitePrProp domain restrictor scope =
    the_sit' domain restrictor scope := rfl


-- ════════════════════════════════════════════════════════════════
-- §5: Donkey Anaphora via Minimal Situations (@cite{elbourne-2013}, Ch 6)
-- ════════════════════════════════════════════════════════════════

/-- In Elbourne's system, donkey pronouns are definite articles with
phonologically null NP complements (NP-deletion). -/
structure DonkeyConfig (F : SituationFrame) where
  /-- The restrictor property (e.g., "donkey") -/
  nounContent : F.Ent → F.Sit → Bool
  /-- The pronoun's situation variable -/
  sitVar : F.Sit
  /-- The domain of entities -/
  domain : List F.Ent

/-- Uniqueness in donkey contexts derives from minimality of situations. -/
theorem donkey_uniqueness_from_minimality
    (F : SituationFrame) (domain : List F.Ent)
    (restrictor : F.Ent → F.Sit → Bool) (scope : F.Ent → F.Sit → Bool)
    (s : F.Sit)
    (h_minimal : F.isMinimal (λ s => match domain.filter (λ e => restrictor e s) with
                                      | [_] => true | _ => false) s) :
    (the_sit F domain restrictor scope).presup s := by
  have hbool := h_minimal.1
  simp only [the_sit, presupOfReferent_presup, russellIotaList]
  match hf : domain.filter (fun e => restrictor e s) with
  | [_] => rfl
  | [] => simp [hf] at hbool
  | _ :: _ :: _ => simp [hf] at hbool


-- ════════════════════════════════════════════════════════════════
-- §6: De Re / De Dicto and Situation Variable Scope
-- ════════════════════════════════════════════════════════════════

/-- Donnellan's referential/attributive distinction maps to Elbourne's
free/bound situation variable distinction. -/
def useModeToSitVar : UseMode → SitVarStatus
  | .referential => .free
  | .attributive => .bound

/-- Mapping is total and injective. -/
theorem useMode_sitVar_roundtrip :
    ∀ m : UseMode, (match useModeToSitVar m with
      | .free => UseMode.referential
      | .bound => UseMode.attributive) = m := by
  intro m; cases m <;> rfl


-- ════════════════════════════════════════════════════════════════
-- §7: Existence Entailments (@cite{elbourne-2013}, Ch 8)
-- ════════════════════════════════════════════════════════════════

structure ExistenceEntailmentDatum where
  /-- The sentence -/
  sentence : String
  /-- Does the speaker presuppose existence? -/
  speakerPresupposes : Bool
  /-- Does the subject believe in existence? -/
  subjectBelieves : Bool
  /-- Is existence actually the case? -/
  existenceActual : Bool
  /-- Elbourne's prediction -/
  elbournePrediction : String
  /-- Source -/
  source : String := "Elbourne 2013"


-- ════════════════════════════════════════════════════════════════
-- §8: Incomplete Definites (@cite{elbourne-2013}, Ch 9)
-- ════════════════════════════════════════════════════════════════

inductive IncompletenessSource where
  | situationVariable
  | relationVariable
  | pragmaticEnrichment
  | explicitApproach
  | lotRelationVariable
  deriving DecidableEq, Repr

def elbournePreferred : IncompletenessSource := .situationVariable


-- ════════════════════════════════════════════════════════════════
-- §9: Pronouns as Definite Descriptions (@cite{elbourne-2013}, Ch 10)
-- ════════════════════════════════════════════════════════════════

/-- How the deleted NP content is recovered. -/
inductive NPDeletionSource where
  | antecedent
  | visualCue
  | generalKnowledge
  | donkeyRestrictor
  deriving DecidableEq, Repr

structure PronounAsDefinite where
  pronounForm : String
  deletedNP : String
  npSource : NPDeletionSource
  equivalentDefinite : String
  deriving Repr, BEq

/-- Pronoun denotation: ⟦it⟧ = ⟦the⟧ + NP-deletion. -/
abbrev pronounDenot {W E : Type} (domain : List E)
    (recoveredNP : E → W → Bool) (scope : E → W → Bool) : PrProp W :=
  the_sit' domain recoveredNP scope

/-- Pronouns = definite articles. -/
theorem pronoun_is_definite_article
    {W E : Type} (domain : List E)
    (restrictor scope : E → W → Bool) :
    pronounDenot domain restrictor scope = the_sit' domain restrictor scope :=
  rfl

/-- Pronoun assertions entail pronoun presuppositions. -/
theorem pronoun_assertion_implies_presup
    {W E : Type} (domain : List E)
    (recoveredNP : E → W → Bool) (scope : E → W → Bool)
    (w : W) (h : (pronounDenot domain recoveredNP scope).assertion w = true) :
    (pronounDenot domain recoveredNP scope).presup w = true :=
  the_sit_assertion_implies_presup domain recoveredNP scope w h


-- ════════════════════════════════════════════════════════════════
-- §10: Situation Binding Operators (@cite{elbourne-2013}, Ch 2)
-- ════════════════════════════════════════════════════════════════

/-- Elbourne's three situation binders. -/
inductive SitBinder where
  | iota (index : Nat)
  | sigma (index : Nat)
  | sigmaSub (index : Nat)
  deriving DecidableEq, Repr

/-- A situation variable — either free or indexed for binding. -/
inductive SitVar where
  | free (salience : Nat := 0)
  | bound (index : Nat)
  deriving DecidableEq, Repr


-- ════════════════════════════════════════════════════════════════
-- §11: QUD–Situation Bridge (@cite{roberts-1996}, @cite{kratzer-2004})
-- ════════════════════════════════════════════════════════════════

/-- A QUD over worlds induces a "relevance" relation on situations. -/
def qudRelevantSituation
    (F : SituationFrame) [DecidableEq F.Sit]
    (leDecide : F.Sit → F.Sit → Bool)
    (q : QUD F.Sit)
    (w : F.Sit) (_hw : F.isWorld w)
    (s : F.Sit) : Prop :=
  F.le s w
  ∧ q.r w s
  ∧ F.isMinimal (λ s' => leDecide s' w && q.sameAnswer w s') s

theorem situation_pronoun_tracks_qud
    (F : SituationFrame) [DecidableEq F.Sit]
    (leDecide : F.Sit → F.Sit → Bool)
    (q : QUD F.Sit)
    (w : F.Sit) (hw : F.isWorld w)
    (s : F.Sit) (hs : qudRelevantSituation F leDecide q w hw s)
    (domain : List F.Ent) [DecidableEq F.Ent]
    (restrictor scope : F.Ent → F.Sit → Bool)
    (hRestr : ∀ e, restrictor e s = restrictor e w)
    (hScope : ∀ e, scope e s = scope e w) :
    (the_sit F domain restrictor scope).assertion s =
    (the_sit F domain restrictor scope).assertion w := by
  unfold the_sit presupOfReferent
  have hFilter : (fun e => restrictor e s) = (fun e => restrictor e w) := by
    funext e; exact hRestr e
  simp only [hFilter]
  match h : russellIotaList domain (fun e => restrictor e w) with
  | some e => simp [hScope e]
  | none => rfl

theorem qud_refinement_monotone
    (F : SituationFrame) [DecidableEq F.Sit]
    (leDecide : F.Sit → F.Sit → Bool)
    (q₁ q₂ : QUD F.Sit)
    (w : F.Sit) (hw : F.isWorld w)
    (s₁ s₂ : F.Sit)
    (hRefine : ∀ a b, q₂.r a b → q₁.r a b)
    (hs₁ : qudRelevantSituation F leDecide q₁ w hw s₁)
    (hs₂ : qudRelevantSituation F leDecide q₂ w hw s₂)
    (hUniq : ∀ s, F.le s w → q₁.r w s → F.le s₁ s) :
    F.le s₁ s₂ := by
  exact hUniq s₂ hs₂.1 (hRefine w s₂ hs₂.2.1)


-- ════════════════════════════════════════════════════════════════
-- § Fragment Bridge: English Lexical Entries → Elbourne's System
-- ════════════════════════════════════════════════════════════════

/-! ### Bridge 1: "the" → the_sit -/

theorem the_is_definite :
    Fragments.English.Determiners.the.qforce = .definite := rfl

theorem english_the_is_uniqueness :
    qforceToPresupType Fragments.English.Determiners.the.qforce =
    some DefPresupType.uniqueness := rfl

theorem english_demonstratives_are_definite :
    Fragments.English.Determiners.this.qforce = .definite ∧
    Fragments.English.Determiners.that.qforce = .definite :=
  ⟨rfl, rfl⟩

/-! ### Bridge 3: Pronouns → the_sit + NP-deletion -/

theorem it_entry_classification :
    Fragments.English.Pronouns.it.pronounType = .personal ∧
    Fragments.English.Pronouns.it.person = some .third ∧
    Fragments.English.Pronouns.it.number = some .sg :=
  ⟨rfl, rfl, rfl⟩

theorem he_entry_classification :
    Fragments.English.Pronouns.he.pronounType = .personal ∧
    Fragments.English.Pronouns.he.person = some .third ∧
    Fragments.English.Pronouns.he.number = some .sg ∧
    Fragments.English.Pronouns.he.case_ = some .nom :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem she_entry_classification :
    Fragments.English.Pronouns.she.pronounType = .personal ∧
    Fragments.English.Pronouns.she.person = some .third ∧
    Fragments.English.Pronouns.she.number = some .sg ∧
    Fragments.English.Pronouns.she.case_ = some .nom :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Bridge 4: Donnellan → Elbourne -/

theorem referential_is_free :
    useModeToSitVar .referential = .free := rfl
theorem attributive_is_bound :
    useModeToSitVar .attributive = .bound := rfl

/-! ### Bridge 5: Pronoun-as-definite examples -/

def donkeyPronounExample : PronounAsDefinite :=
  { pronounForm := "it"
  , deletedNP := "donkey"
  , npSource := .donkeyRestrictor
  , equivalentDefinite := "the donkey" }

def anaphoricPronounExample : PronounAsDefinite :=
  { pronounForm := "he"
  , deletedNP := "Junior Dean"
  , npSource := .antecedent
  , equivalentDefinite := "the Junior Dean" }

def voldemortExample : PronounAsDefinite :=
  { pronounForm := "he"
  , deletedNP := "person"
  , npSource := .generalKnowledge
  , equivalentDefinite := "the person who hesitates" }


-- ════════════════════════════════════════════════════════════════
-- § Example 1: Referential vs Attributive (Ch 5)
-- "The murderer of Smith is insane"
-- ════════════════════════════════════════════════════════════════

section RefAttr

-- TODO: Bool→Prop migration of isMurderer/isInsane/isTable/isCoveredWithBooks/
-- isDonkey/isBeaten/isPresident/isSpy/isGhost/isQuiet cascades to
-- Linglib/Core/Semantics/Presupposition.lean (presupOfReferent : (W → Option E) → ...)
-- and Linglib/Core/Nominal/Maximality.lean (russellIotaList : List E → (E → Bool) → Option E).
-- These predicates feed into the_sit'/the_sit/definitePrProp which require E → W → Bool.
-- Migration deferred until those external Core APIs migrate to Prop with [DecidablePred].

inductive Sit where
  | sCourtroom | sOffice | wActual
  deriving DecidableEq, Repr

inductive Ent where
  | jones | smith | wilson | table1 | table2 | table3
  deriving DecidableEq, Repr

def allEnts : List Ent := [.jones, .smith, .wilson, .table1, .table2, .table3]

def isMurderer : Ent → Sit → Bool
  | .jones, .sCourtroom => true
  | .wilson, .wActual => true
  | _, _ => false

def isInsane : Ent → Sit → Bool
  | .jones, _ => true
  | _, _ => false

def theMurderer : PrProp Sit := the_sit' allEnts isMurderer isInsane

theorem referential_presup :
    theMurderer.presup .sCourtroom = true := rfl
theorem referential_assertion :
    theMurderer.assertion .sCourtroom = true := rfl

theorem attributive_presup :
    theMurderer.presup .wActual = true := rfl
theorem attributive_assertion :
    theMurderer.assertion .wActual = false := rfl

theorem ref_attr_diverge :
    theMurderer.assertion .sCourtroom ≠ theMurderer.assertion .wActual := by
  rw [referential_assertion, attributive_assertion]; decide

def refSitVar : SitVar := .free
def attrSitVar : SitVar := .bound 1

theorem same_entry_both_readings :
    theMurderer = theMurderer := rfl

end RefAttr


-- ════════════════════════════════════════════════════════════════
-- § Example 2: Incomplete Definites (Ch 9)
-- "The table is covered with books"
-- ════════════════════════════════════════════════════════════════

section Incomplete

def isTable : Ent → Sit → Bool
  | .table1, .sOffice => true
  | .table1, .wActual => true
  | .table2, .wActual => true
  | .table3, .wActual => true
  | _, _ => false

def isCoveredWithBooks : Ent → Sit → Bool
  | .table1, _ => true
  | _, _ => false

def theTable : PrProp Sit := the_sit' allEnts isTable isCoveredWithBooks

theorem incomplete_presup_office :
    theTable.presup .sOffice = true := rfl
theorem incomplete_presup_world :
    theTable.presup .wActual = false := rfl
theorem incomplete_assertion_office :
    theTable.assertion .sOffice = true := rfl

theorem incompleteness_is_situation_variable :
    elbournePreferred = .situationVariable := rfl

end Incomplete


-- ════════════════════════════════════════════════════════════════
-- § Example 3: Donkey Anaphora via Minimality (Ch 6)
-- "Every farmer who owns a donkey beats it"
-- ════════════════════════════════════════════════════════════════

section Donkey

inductive DkEnt where
  | farmer1 | farmer2 | donkey_a | donkey_b | donkey_c
  deriving DecidableEq, Repr

inductive DkSit where
  | sMin1 | sMin2 | wActual
  deriving DecidableEq, Repr

def dkLe : DkSit → DkSit → Prop
  | _, .wActual => True
  | .sMin1, .sMin1 => True
  | .sMin2, .sMin2 => True
  | _, _ => False

private theorem dkLe_refl : ∀ s, dkLe s s := by
  intro s; cases s <;> exact trivial

private theorem dkLe_trans : ∀ s₁ s₂ s₃, dkLe s₁ s₂ → dkLe s₂ s₃ → dkLe s₁ s₃ := by
  intro s₁ s₂ s₃ h₁ h₂
  cases s₁ <;> cases s₂ <;> cases s₃ <;>
    first | exact trivial | exact h₁.elim | exact h₂.elim

private theorem dkLe_antisymm : ∀ s₁ s₂, dkLe s₁ s₂ → dkLe s₂ s₁ → s₁ = s₂ := by
  intro s₁ s₂ h₁ h₂
  cases s₁ <;> cases s₂ <;>
    first | rfl | exact h₁.elim | exact h₂.elim

def DkF : SituationFrame where
  Sit := DkSit
  Ent := DkEnt
  le := dkLe
  le_refl := dkLe_refl
  le_trans := dkLe_trans
  le_antisymm := dkLe_antisymm

def dkEnts : List DkEnt := [.farmer1, .farmer2, .donkey_a, .donkey_b, .donkey_c]

def isDonkey : DkEnt → DkSit → Bool
  | .donkey_a, .sMin1 => true
  | .donkey_b, .sMin2 => true
  | .donkey_a, .wActual => true
  | .donkey_b, .wActual => true
  | .donkey_c, .wActual => true
  | _, _ => false

def isBeaten : DkEnt → DkSit → Bool
  | .donkey_a, _ => true
  | .donkey_b, _ => true
  | _, _ => false

def donkeyPronoun : PrProp DkSit := the_sit' dkEnts isDonkey isBeaten

theorem donkey_presup_min1 :
    donkeyPronoun.presup .sMin1 = true := rfl
theorem donkey_presup_min2 :
    donkeyPronoun.presup .sMin2 = true := rfl
theorem donkey_presup_world_fails :
    donkeyPronoun.presup .wActual = false := rfl

theorem donkey_assertion_min1 :
    donkeyPronoun.assertion .sMin1 = true := rfl
theorem donkey_assertion_min2 :
    donkeyPronoun.assertion .sMin2 = true := rfl

def donkeyConfig1 : DonkeyConfig DkF where
  nounContent := isDonkey
  sitVar := .sMin1
  domain := dkEnts

def donkeyConfig2 : DonkeyConfig DkF where
  nounContent := isDonkey
  sitVar := .sMin2
  domain := dkEnts

theorem donkey_uniqueness_via_minimality_min1 :
    DkF.isMinimal (λ s => match dkEnts.filter (λ e => isDonkey e s) with
                           | [_] => true | _ => false) .sMin1 := by
  refine ⟨rfl, ?_⟩
  intro s' hle _
  cases s' with
  | sMin1 => rfl
  | sMin2 => exact hle.elim
  | wActual => exact hle.elim

theorem donkey_uniqueness_via_minimality_min2 :
    DkF.isMinimal (λ s => match dkEnts.filter (λ e => isDonkey e s) with
                           | [_] => true | _ => false) .sMin2 := by
  refine ⟨rfl, ?_⟩
  intro s' hle _
  cases s' with
  | sMin1 => exact hle.elim
  | sMin2 => rfl
  | wActual => exact hle.elim

end Donkey


-- ════════════════════════════════════════════════════════════════
-- § Example 4: De Re / De Dicto with Definites (Ch 7)
-- "Mary believes the president is a spy"
-- ════════════════════════════════════════════════════════════════

section DeReDeDicto

inductive BSit where
  | actual | belief
  deriving DecidableEq, Repr

inductive BEnt where
  | jones | smith | mary
  deriving DecidableEq, Repr

def bEnts : List BEnt := [.jones, .smith, .mary]

def isPresident : BEnt → BSit → Bool
  | .jones, .actual => true
  | .smith, .belief => true
  | _, _ => false

def isSpy : BEnt → BSit → Bool
  | .smith, _ => true
  | _, _ => false

def thePresident : PrProp BSit := the_sit' bEnts isPresident isSpy

theorem deRe_presup : thePresident.presup .actual = true := rfl
theorem deRe_assertion : thePresident.assertion .actual = false := rfl

theorem deDicto_presup : thePresident.presup .belief = true := rfl
theorem deDicto_assertion : thePresident.assertion .belief = true := rfl

theorem deRe_deDicto_diverge :
    thePresident.assertion .actual ≠ thePresident.assertion .belief := by
  rw [deRe_assertion, deDicto_assertion]; decide

theorem deRe_is_free : SitVarStatus.free = useModeToSitVar .referential := rfl
theorem deDicto_is_bound : SitVarStatus.bound = useModeToSitVar .attributive := rfl

def deReVar : SitVar := .free
def deDictoVar : SitVar := .bound 1

end DeReDeDicto


-- ════════════════════════════════════════════════════════════════
-- § Example 5: Existence Entailments under Attitudes (Ch 8)
-- "Hans wants the ghost in his attic to be quiet"
-- ════════════════════════════════════════════════════════════════

section ExistenceEntailment

def hansGhost : ExistenceEntailmentDatum :=
  { sentence := "Hans wants the ghost in his attic to be quiet tonight."
  , speakerPresupposes := false
  , subjectBelieves := true
  , existenceActual := false
  , elbournePrediction := "Presupposition projects to Hans's beliefs via Karttunen (1974)"
  , source := "Elbourne 2013, Ch 8 §8.6" }

def ponceFountain : ExistenceEntailmentDatum :=
  { sentence := "Ponce de León is wondering whether the fountain of youth is in Florida."
  , speakerPresupposes := false
  , subjectBelieves := true
  , existenceActual := false
  , elbournePrediction := "Narrow scope: situation bound within wonder → no speaker commitment"
  , source := "Elbourne 2013, Ch 8 §8.8" }

inductive GhostSit where
  | actual | belief
  deriving DecidableEq, Repr

inductive GhostEnt where
  | hans | ghost
  deriving DecidableEq, Repr

def ghostEnts : List GhostEnt := [.hans, .ghost]

def isGhost : GhostEnt → GhostSit → Bool
  | .ghost, .belief => true
  | _, _ => false

def isQuiet : GhostEnt → GhostSit → Bool
  | .ghost, _ => true
  | _, _ => false

def theGhost : PrProp GhostSit := the_sit' ghostEnts isGhost isQuiet

theorem ghost_presup_belief :
    theGhost.presup .belief = true := rfl
theorem ghost_presup_actual :
    theGhost.presup .actual = false := rfl

theorem ghost_matches_datum :
    hansGhost.speakerPresupposes = false ∧
    hansGhost.subjectBelieves = true ∧
    hansGhost.existenceActual = false :=
  ⟨rfl, rfl, rfl⟩

theorem ponce_matches_datum :
    ponceFountain.speakerPresupposes = false ∧
    ponceFountain.subjectBelieves = true ∧
    ponceFountain.existenceActual = false :=
  ⟨rfl, rfl, rfl⟩

end ExistenceEntailment


-- ════════════════════════════════════════════════════════════════
-- § Example 6: Pronouns as Definite Articles (Ch 10)
-- ════════════════════════════════════════════════════════════════

section PronounAsDefiniteExample

def itAsDonkey : PrProp DkSit :=
  pronounDenot dkEnts isDonkey isBeaten

theorem pronoun_matches_definite_min1 :
    itAsDonkey = donkeyPronoun := rfl
theorem pronoun_presup_min1 :
    itAsDonkey.presup .sMin1 = true := rfl
theorem pronoun_presup_world_fails :
    itAsDonkey.presup .wActual = false := rfl

theorem np_sources_exercised :
    donkeyPronounExample.npSource = .donkeyRestrictor ∧
    anaphoricPronounExample.npSource = .antecedent ∧
    voldemortExample.npSource = .generalKnowledge :=
  ⟨rfl, rfl, rfl⟩

end PronounAsDefiniteExample


end Elbourne2013
