import Linglib.Features.Aktionsart
import Linglib.Features.Attitudes
import Linglib.Features.Causation
import Linglib.Semantics.Verb.Class
import Linglib.Semantics.ArgumentStructure.MeaningComponents
import Linglib.Semantics.Causation.SEM.Counterfactual

/-!
# Implicative Verbs ([nadathur-2023-implicatives])

Causal-prerequisite semantics for implicative verbs. Implicatives
(*manage*, *fail*, *dare*, *bother*, *jaksaa*, *hesitate*, ...) all
share a prerequisite-account schema (Proposal 32):

- (32i)   Presuppose: ∃ prerequisite A(x) causally necessary for P(x)
- (32ii)  Assert: x did A
- (32iii) Presuppose (two-way only): A(x) causally sufficient for P(x)

## Lexical variation

The chief dimension of variation is the type of prerequisite:

- *dare/uskaltaa* → courage
- *bother/viitsiä* → engagement/effort
- *malttaa* → patience
- *hennoa* → hard-heartedness
- *jaksaa* → strength
- *manage/onnistua* → underspecified

## V2 substrate

Polymorphic V2 forms over `SEM V α`. The legacy `ImplicativeScenario`
struct + `manageSem`/`failSem` over `CausalDynamics`,
`PrerequisiteAccount`, `ConcreteExample` (swim/manage), the
`ComplementEntailing.CausalFrame` abstraction (with abilityFrame/
viewpoint-aspect bridges), and `Implicative.toSemantics` over scenarios
were deleted in Phase D-H. The polymorphic V2 versions
(`manageSem`, `failSem`, `necessityPresup`, `Implicative.toSemantics`
dispatch) are promoted to canonical here.
-/

namespace Causation.Implicative

open Features (Implicative)
open Features
open Causation (SEM CausalGraph Valuation DecidableValuation)

/-! ### Prerequisite Types ([nadathur-2023-implicatives]) -/

/-- Lexically-specified prerequisite types for implicative verbs.

    Specific verbs (*dare*, *bother*) name their prerequisites; bleached
    verbs (*manage*, *onnistua*) leave the prerequisite underspecified. -/
inductive Prerequisite where
  | courage          -- dare, uskaltaa
  | engagement       -- bother, viitsiä
  | patience         -- malttaa
  | hardHeartedness  -- hennoa
  | strength         -- jaksaa
  | fitness          -- mahtua
  | time             -- ehtiä
  | shamelessness    -- kehdata
  | unspecified      -- manage, onnistua
  deriving DecidableEq, Repr

/-- Is the prerequisite lexically specific or underspecified? -/
def Prerequisite.isSpecific : Prerequisite → Bool
  | .unspecified => false
  | _ => true

/-! ### V2 Polymorphic Semantics -/

/-- V2 manage-sem ([nadathur-2023-implicatives] Definition 10a with the
    Definition 10 preamble, over the strict T_D development):
    prerequisite-as-`xP` is causally sufficient for complement-as-`xC` —
    the background entails neither fact, and augmenting it with the
    prerequisite causally entails the complement. Polymorphic over value
    types. -/
def manageSem {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (prerequisite : V) (xP : α prerequisite)
    (complement : V) (xC : α complement) : Prop :=
  SEM.causallyNecessary.precondition M background prerequisite xP complement xC ∧
  SEM.causallyEntails M (background.extend prerequisite xP) complement xC

noncomputable instance {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (prerequisite : V) (xP : α prerequisite)
    (complement : V) (xC : α complement) :
    Decidable (manageSem M background prerequisite xP complement xC) :=
  Classical.dec _

/-- V2 fail-sem: prerequisite-as-`xP` is NOT causally sufficient for
    complement-as-`xC`.

    TODO: this is denial of the sufficiency presupposition, which is what
    the Dreyfus infelicity judgments test, but it is NOT Proposal 32's
    semantics for negative implicative *assertions* (assert ¬A(x) with
    both presuppositions intact); the `Features.Implicative.toSemantics`
    `.negative` dispatch below inherits the same caveat. -/
abbrev failSem {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (prerequisite : V) (xP : α prerequisite)
    (complement : V) (xC : α complement) : Prop :=
  ¬ manageSem M background prerequisite xP complement xC

/-- V2 necessity presupposition: prerequisite-as-`xP` is causally
    necessary (Nadathur 2023 Def 10b) for complement-as-`xC`. -/
abbrev necessityPresup {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (prerequisite : V) (xP : α prerequisite)
    (complement : V) (xC : α complement) : Prop :=
  SEM.causallyNecessary M background prerequisite xP complement xC

/-! ### Characteristic entailments (Facts B–C) -/

/-! [nadathur-2023-implicatives] (pp. 316–317) takes Facts A–C as the
class-level data any account of implicatives must derive. On the
prerequisite account they fall out of the presupposition + assertion
split of Proposal 32, for an arbitrary deterministic SEM:

- **Fact B, positive half** (`complement_of_positive_assertion`):
  asserting the prerequisite realizes the complement — the sufficiency
  presupposition's entailment clause.
- **Fact B, negative half** (`no_complement_of_negative_assertion`):
  given the necessity presupposition, the negative assertion leaves no
  consistent completion realizing the complement.
- **Fact C** (`complement_iff_prerequisite`): in a felicitous two-way
  context the prerequisite is sufficient *and* necessary — a consistent
  completion realizes the complement exactly when it realizes the
  prerequisite.

Fact A (the existence of a potential obstacle, blocking the entailment
from complement to implicative claim) is carried by the presuppositional
preamble itself (`SEM.causallyNecessary.precondition`). -/

section CharacteristicEntailments

variable {V : Type*} {α : V → Type*}
  [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
  (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]

omit [∀ v, Fintype (α v)] in
/-- **Fact B, positive half**: a positive two-way implicative claim
    entails its complement — the background updated with the asserted
    prerequisite causally entails the complement. -/
theorem complement_of_positive_assertion
    {background : Valuation α} {p : V} {xP : α p} {c : V} {xC : α c}
    (h : manageSem M background p xP c xC) :
    SEM.causallyEntails M (background.extend p xP) c xC := h.2

/-- **Fact B, negative half**: given the necessity presupposition, a
    negative implicative claim (asserting the prerequisite took a value
    other than `xP`) leaves no consistent completion realizing the
    complement: by no-alternative, every consistent path to the
    complement runs through the prerequisite value the assertion denies. -/
theorem no_complement_of_negative_assertion
    {background : Valuation α} {p : V} {xP xP' : α p} {c : V} {xC : α c}
    (hexo : M.graph.parents p = ∅) (hp : background.get p = none)
    (hne : xP' ≠ xP)
    (hnec : necessityPresup M background p xP c xC) :
    ∀ s', SEM.IsExogenousSettlement M (background.extend p xP') s' →
      s'.get c = none → ¬ SEM.causallyEntails M s' c xC := by
  intro s' hset hc hent
  have hEntP : SEM.causallyEntails M s' p xP :=
    hnec.2.2 s' (hset.of_extend hexo hp) hc hent
  have hp' : s'.get p = some xP' :=
    hset.1 p xP' (Valuation.extend_get_same _ _ _)
  have hEntP' : SEM.causallyEntails M s' p xP' :=
    SEM.developDetVtx?_determined M hp'
  exact hne (SEM.causallyEntails_unique hEntP' hEntP)

/-- **Fact C**: in a felicitous two-way context (both presuppositions in
    force), a consistent completion of the background realizes the
    complement exactly when it realizes the prerequisite. The forward
    direction is no-alternative; the converse composes the sufficiency
    clause with `causallyEntails_mono` (determinations cannot be undone). -/
theorem complement_iff_prerequisite
    {background : Valuation α} {p : V} {xP : α p} {c : V} {xC : α c}
    (hexo : M.graph.parents p = ∅) (hp : background.get p = none)
    (hsuf : manageSem M background p xP c xC)
    (hnec : necessityPresup M background p xP c xC) :
    ∀ s', SEM.IsExogenousSettlement M background s' → s'.get c = none →
      (SEM.causallyEntails M s' c xC ↔ SEM.causallyEntails M s' p xP) := by
  intro s' hset hc
  constructor
  · exact hnec.2.2 s' hset hc
  · intro hEntP
    -- the prerequisite is exogenous, so its entailment is a syntactic fix
    have hp' : s'.get p = some xP := by
      cases hgp : s'.get p with
      | some y =>
          have := SEM.causallyEntails_unique
            (SEM.developDetVtx?_determined M hgp (x := y)) hEntP
          exact congrArg some this
      | none =>
          rw [SEM.causallyEntails, SEM.developDetVtx?_exogenous M hgp hexo] at hEntP
          simp at hEntP
    -- s' consistently extends background + prerequisite
    have hle : background.extend p xP ≤ s' := by
      intro v x hv
      by_cases hvp : v = p
      · subst hvp
        rw [Valuation.hasValue, Valuation.extend_get_same] at hv
        rw [Valuation.hasValue, hp']
        exact hv
      · rw [Valuation.hasValue, Valuation.extend_get_ne hvp] at hv
        exact hset.1 v x hv
    have hcons : SEM.isConsistentSuper M (background.extend p xP) s' := by
      refine ⟨hle, fun x xv hn hs yv _ hent => ?_⟩
      have hxp : x ≠ p := by
        intro hxp; subst hxp
        rw [Valuation.extend_get_same] at hn
        simp at hn
      have hbgx : background.get x = none := by
        rw [Valuation.extend_get_ne hxp] at hn; exact hn
      have hExoX : M.graph.parents x = ∅ :=
        hset.2 x hbgx (by rw [hs]; rfl)
      rw [SEM.causallyEntails, SEM.developDetVtx?_exogenous M hn hExoX] at hent
      simp at hent
    exact SEM.causallyEntails_mono hcons hsuf.2

/-- **The two-way entailment profile** — [karttunen-1971]'s defining
    criterion for the *manage* class — follows from the prerequisite
    account: in a context satisfying both presuppositions, the positive
    assertion entails the complement (Fact B, positive) and any negative
    assertion precludes it in every consistent completion (Fact B,
    negative). This is the derivation [nadathur-2023-implicatives]
    advertises for Facts A–C at the class level. -/
theorem twoWay_entailment_profile
    {background : Valuation α} {p : V} {xP : α p} {c : V} {xC : α c}
    (hexo : M.graph.parents p = ∅) (hp : background.get p = none)
    (hsuf : manageSem M background p xP c xC)
    (hnec : necessityPresup M background p xP c xC) :
    SEM.causallyEntails M (background.extend p xP) c xC ∧
    ∀ xP', xP' ≠ xP → ∀ s',
      SEM.IsExogenousSettlement M (background.extend p xP') s' →
      s'.get c = none → ¬ SEM.causallyEntails M s' c xC :=
  ⟨complement_of_positive_assertion M hsuf,
   fun _ hne s' h1 h2 => no_complement_of_negative_assertion M hexo hp hne hnec s' h1 h2⟩

end CharacteristicEntailments

/-! ### Directionality -/

/-- Directionality of complement entailment ([nadathur-2023-implicatives]).

    - **oneWay**: complement entailment under only one matrix polarity.
    - **twoWay**: complement entailment under both polarities. -/
inductive Directionality where
  | oneWay
  | twoWay
  deriving DecidableEq, Repr

/-! ### ImplicativeClass -/

/-- The full lexical signature of an implicative verb ([nadathur-2023-implicatives]). -/
structure ImplicativeClass where
  /-- Positive (manage, force) or negative (fail, prevent) polarity -/
  polarity : Implicative
  /-- One-way (ability) or two-way (manage) entailment -/
  directionality : Directionality
  /-- Does aspect govern the actuality inference? -/
  aspectGoverned : Bool
  /-- Lexically-specified prerequisite type (if any) -/
  prerequisite : Option Prerequisite := none
  deriving DecidableEq, Repr

def ImplicativeClass.manage : ImplicativeClass :=
  { polarity := .positive, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .unspecified }

def ImplicativeClass.fail : ImplicativeClass :=
  { polarity := .negative, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .unspecified }

def ImplicativeClass.dare : ImplicativeClass :=
  { polarity := .positive, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .courage }

def ImplicativeClass.bother : ImplicativeClass :=
  { polarity := .positive, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .engagement }

def ImplicativeClass.jaksaa : ImplicativeClass :=
  { polarity := .positive, directionality := .oneWay, aspectGoverned := false
    prerequisite := some .strength }

def ImplicativeClass.ability : ImplicativeClass :=
  { polarity := .positive, directionality := .oneWay, aspectGoverned := true }

def ImplicativeClass.enough : ImplicativeClass :=
  { polarity := .positive, directionality := .oneWay, aspectGoverned := true }

def ImplicativeClass.too : ImplicativeClass :=
  { polarity := .negative, directionality := .oneWay, aspectGoverned := true }

def ImplicativeClass.hesitate : ImplicativeClass :=
  { polarity := .negative, directionality := .oneWay, aspectGoverned := false
    prerequisite := some .courage }

-- Classification theorems (substrate-independent — about the enum)

theorem manage_fail_polarity :
    ImplicativeClass.manage.directionality = ImplicativeClass.fail.directionality ∧
    ImplicativeClass.manage.aspectGoverned = ImplicativeClass.fail.aspectGoverned ∧
    ImplicativeClass.manage.polarity ≠ ImplicativeClass.fail.polarity := by
  exact ⟨rfl, rfl, by decide⟩

theorem ability_vs_manage :
    ImplicativeClass.ability.aspectGoverned = true ∧
    ImplicativeClass.manage.aspectGoverned = false ∧
    ImplicativeClass.ability.directionality = .oneWay ∧
    ImplicativeClass.manage.directionality = .twoWay := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem enough_too_polarity :
    ImplicativeClass.enough.aspectGoverned = ImplicativeClass.too.aspectGoverned ∧
    ImplicativeClass.enough.directionality = ImplicativeClass.too.directionality ∧
    ImplicativeClass.enough.polarity ≠ ImplicativeClass.too.polarity := by
  exact ⟨rfl, rfl, by decide⟩

theorem dare_vs_manage_prerequisite :
    ImplicativeClass.dare.polarity = ImplicativeClass.manage.polarity ∧
    ImplicativeClass.dare.directionality = ImplicativeClass.manage.directionality ∧
    ImplicativeClass.dare.prerequisite ≠ ImplicativeClass.manage.prerequisite := by
  exact ⟨rfl, rfl, by decide⟩

theorem jaksaa_vs_dare_directionality :
    ImplicativeClass.jaksaa.directionality = .oneWay ∧
    ImplicativeClass.dare.directionality = .twoWay ∧
    ImplicativeClass.jaksaa.prerequisite.isSome = true ∧
    ImplicativeClass.dare.prerequisite.isSome = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem specific_vs_bleached :
    (ImplicativeClass.dare.prerequisite.bind (some ·.isSpecific)) = some true ∧
    (ImplicativeClass.manage.prerequisite.bind (some ·.isSpecific)) = some false := by
  exact ⟨rfl, rfl⟩

end Causation.Implicative

/-! ### `Features.Implicative.toSemantics` dispatch (V2 polymorphic) -/

/-! Lives here rather than in `Features/Causation.lean` because the
dispatch needs `Causation.SEM` + the `Implicative.manageSem`/`failSem`
machinery defined above; `Features/Causation.lean` is kept import-free.
Standard mathlib pattern: methods on a type may live in a sibling
file via `namespace TypeName` block when import weight matters. -/

namespace Features.Implicative

open Causation (SEM CausalGraph Valuation DecidableValuation)

/-- V2 dispatch: map an `Implicative` polarity to its V2 polymorphic
    semantic function. -/
noncomputable def toSemantics {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M] :
    Implicative → Valuation α → ∀ p : V, α p → ∀ c : V, α c → Prop
  | .positive => Causation.Implicative.manageSem M
  | .negative => Causation.Implicative.failSem M

end Features.Implicative
