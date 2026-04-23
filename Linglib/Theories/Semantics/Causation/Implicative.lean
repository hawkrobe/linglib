import Linglib.Core.Lexical.VerbClass
import Linglib.Core.Causal.SEM.Counterfactual

/-!
# Implicative Verbs (@cite{nadathur-2024})

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

namespace Semantics.Causation.Implicative

open Core.Verbs (Implicative)
open Core.Causal (SEM CausalGraph Valuation DecidableValuation)

-- ════════════════════════════════════════════════════
-- § Prerequisite Types (@cite{nadathur-2024})
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § V2 Polymorphic Semantics
-- ════════════════════════════════════════════════════

/-- V2 manage-sem: prerequisite-as-`xP` is causally sufficient for
    complement-as-`xC`. Polymorphic over value types. -/
abbrev manageSem {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (prerequisite : V) (xP : α prerequisite)
    (complement : V) (xC : α complement) : Prop :=
  SEM.causallySufficient M background prerequisite xP complement xC

/-- V2 fail-sem: prerequisite-as-`xP` is NOT causally sufficient for
    complement-as-`xC`. -/
abbrev failSem {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (prerequisite : V) (xP : α prerequisite)
    (complement : V) (xC : α complement) : Prop :=
  ¬ manageSem M background prerequisite xP complement xC

/-- V2 necessity presupposition: prerequisite-as-`xP` is causally
    necessary (Nadathur 2024 Def 10b) for complement-as-`xC`. -/
abbrev necessityPresup {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (prerequisite : V) (xP : α prerequisite)
    (complement : V) (xC : α complement) : Prop :=
  SEM.causallyNecessary M background prerequisite xP complement xC

-- ════════════════════════════════════════════════════
-- § Directionality
-- ════════════════════════════════════════════════════

/-- Directionality of complement entailment (@cite{nadathur-2024}).

    - **oneWay**: complement entailment under only one matrix polarity.
    - **twoWay**: complement entailment under both polarities. -/
inductive Directionality where
  | oneWay
  | twoWay
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § ImplicativeClass
-- ════════════════════════════════════════════════════

/-- The full lexical signature of an implicative verb (@cite{nadathur-2024}). -/
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

end Semantics.Causation.Implicative

-- ════════════════════════════════════════════════════
-- § Implicative.toSemantics dispatch (V2 polymorphic)
-- ════════════════════════════════════════════════════

namespace Core.Verbs.Implicative

open Core.Causal (SEM CausalGraph Valuation DecidableValuation)

/-- V2 dispatch: map an `Implicative` polarity to its V2 polymorphic
    semantic function. -/
noncomputable def toSemantics {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M] :
    Implicative → Valuation α → ∀ p : V, α p → ∀ c : V, α c → Prop
  | .positive => Semantics.Causation.Implicative.manageSem M
  | .negative => Semantics.Causation.Implicative.failSem M

end Core.Verbs.Implicative
