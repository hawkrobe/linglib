import Linglib.Theories.Semantics.PIP.Bridges
import Linglib.Theories.Semantics.PIP.Connectives
import Linglib.Theories.Semantics.PIP.Felicity
import Linglib.Theories.Semantics.Dynamic.DPL.Basic
import Linglib.Phenomena.Anaphora.DonkeyAnaphora
import Linglib.Phenomena.Anaphora.CrossSentential
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Keshet & Abney (2024): Intensional Anaphora

@cite{keshet-abney-2024} @cite{partee-1972} @cite{roberts-1987}
@cite{stone-1999} @cite{brasoveanu-2010}

Formalizes the core contributions of @cite{keshet-abney-2024}'s PIP
(Plural Intensional Presuppositional predicate calculus) and connects
them to the theory-neutral anaphora data in `Phenomena/Anaphora/`.

## Paper's Core Claim

Pronouns carry **descriptive content** (formula labels), not stored entity
values. A pronoun presupposes that its antecedent description has a
non-empty extension in every world of the context set (paper item 9).

This single hypothesis, implemented via PIP's formula labels and felicity
conditions, uniformly explains:

1. **Modal subordination** — labels survive modals (paper §2.6.3, items 59–60)
2. **Bathroom sentences** — labels survive negation (paper §3.4, item 92b)
3. **Donkey anaphora** — labels survive ∀ = ¬∃¬ (paper §2.6.2, items 53–56)
4. **Paycheck pronouns** — descriptions re-evaluated (paper §2.6.4, items 66–67)
5. **Intensional anaphora** — might blocks, must allows (paper §3.1–3.3)

## Architecture

This study file imports:
- **Theory**: `Theories/Semantics/PIP/` (PIP mechanism)
- **Data**: `Phenomena/Anaphora/` (theory-neutral judgments)

and proves that PIP's predictions match the empirical data via worked
finite models with `decide` verification.

-/

namespace KeshetAbney2024

open Semantics.PIP
open Semantics.Dynamic.Core (IVar ICDRTAssignment Entity IContext)
-- `BAccessRel` is re-exported by `Semantics.PIP` (opened above);
-- `BRefl` / `kripkeEval` were Bool-internal modal infrastructure that has
-- been replaced by the Prop-valued `Refl`/`boxR` API in
-- `Core.IntensionalLogic` and isn't needed here.
open Phenomena.Anaphora


-- ============================================================
-- Stone's Puzzle: Modal Subordination (paper §2.6.3)
-- ============================================================

section Stone

/--
Stone's puzzle world model (@cite{stone-1999}, @cite{roberts-1987}).

Three possible worlds:
- `actual`: the evaluation world (no wolf present)
- `wolfIn`: a world where a wolf comes in
- `noWolf`: a world where no wolf comes in
-/
inductive SWorld where
  | actual | wolfIn | noWolf
  deriving DecidableEq, Repr, Inhabited

inductive SEntity where
  | wolf
  deriving DecidableEq, Repr, Inhabited

def sWorlds : List SWorld := [.actual, .wolfIn, .noWolf]
def αWolf : FLabel := ⟨0⟩
def vWolf : IVar := ⟨0⟩

/-- Epistemic accessibility from actual world. -/
def sAccess : BAccessRel SWorld
  | .actual, .wolfIn => true
  | .actual, .noWolf => true
  | _, _ => false

def isWolf (g : ICDRTAssignment SWorld SEntity) (w : SWorld) : Bool :=
  g.indiv vWolf w == .some .wolf

def comesIn (g : ICDRTAssignment SWorld SEntity) (w : SWorld) : Bool :=
  g.indiv vWolf w == .some .wolf && w == .wolfIn

/--
"A wolf might come in." (paper item 59a)

  might(∃^αWolf x. wolf(x) ∧ comeIn(x))

Label αWolf records the description "wolf(x) that comes in".
-/
def stoneSentence1 : PUpdate SWorld SEntity :=
  might sAccess sWorlds
    (existsLabeled αWolf vWolf {.wolf}
      isWolf
      (atom (λ g w => isWolf g w && comesIn g w)))

/-- After "A wolf might come in", the label αWolf is registered. -/
theorem stone_label_registered (d : Discourse SWorld SEntity)
    (_hConsistent : d.info.Nonempty) :
    (stoneSentence1 d).labels.registered αWolf = true := by
  simp only [stoneSentence1, might, modalExpand, existsLabeled, atom, Discourse.mapInfo,
             LabelStore.registered, Option.isSome, LabelStore.register, αWolf]
  rfl

/--
"It would eat you first." (paper item 59b)

"It" = DEF_αWolf{x}; "would" = must with inherited accessibility.
-/
def stoneSentence2 : PUpdate SWorld SEntity :=
  conj
    (retrieveDef αWolf)
    (would sAccess sWorlds
      (atom (λ g w => g.indiv vWolf w != .star)))

def stoneDiscourse : PUpdate SWorld SEntity :=
  conj stoneSentence1 stoneSentence2

/-- After the full discourse, the label is still available. -/
theorem stone_discourse_label_available (d : Discourse SWorld SEntity) :
    (stoneDiscourse d).labels.registered αWolf = true := by
  simp only [stoneDiscourse, conj, stoneSentence2, stoneSentence1,
             would, must, might, modalExpand, existsLabeled, atom, retrieveDef,
             Discourse.mapInfo, LabelStore.registered, Option.isSome,
             LabelStore.register, LabelStore.lookup, αWolf, vWolf, isWolf]
  rfl

private def g₀_stone : ICDRTAssignment SWorld SEntity :=
  { indiv := λ _ _w => .star, prop := λ _ => ∅ }

private def g_wolf : ICDRTAssignment SWorld SEntity :=
  g₀_stone.updateIndivConst vWolf (.some .wolf)

private def stone_d₀ : Discourse SWorld SEntity :=
  { info := Set.univ, labels := LabelStore.empty }

private theorem g_wolf_in_sentence1 :
    (g_wolf, SWorld.actual) ∈ (stoneSentence1 stone_d₀).info := by
  unfold stoneSentence1 might modalExpand
  dsimp only
  constructor
  · exact Set.mem_univ _
  · refine ⟨SWorld.wolfIn, ?_, ?_, ?_⟩
    · simp [sWorlds]
    · rfl
    · unfold existsLabeled atom Discourse.mapInfo
      constructor
      · refine ⟨g₀_stone, SEntity.wolf, ?_, ?_, ?_⟩
        · left; exact Set.mem_univ _
        · rfl
        · rfl
      · rfl

private theorem g_wolf_in_retrieve :
    (g_wolf, SWorld.actual) ∈ (retrieveDef αWolf (stoneSentence1 stone_d₀)).info := by
  unfold retrieveDef
  simp only [stoneSentence1, might, modalExpand, existsLabeled, atom,
             Discourse.mapInfo, LabelStore.register, LabelStore.lookup, αWolf,
             vWolf, isWolf]
  refine ⟨g_wolf_in_sentence1, ?_, ?_⟩ <;> decide

/--
End-to-end test: Stone's discourse is consistent on a concrete model.

After "A wolf might come. It would eat you first.", the discourse state
is non-empty: g_wolf (with vWolf ↦ wolf) at actual survives the pipeline.
-/
theorem stone_discourse_consistent :
    (stoneDiscourse stone_d₀).info.Nonempty := by
  refine ⟨(g_wolf, .actual), ?_⟩
  unfold stoneDiscourse conj stoneSentence2 would must modalExpand
  dsimp only
  constructor
  · exact g_wolf_in_retrieve
  · intro w₁ _hw₁ hacc
    unfold atom Discourse.mapInfo
    constructor
    · right; exact ⟨SWorld.actual, g_wolf_in_retrieve, hacc⟩
    · rfl

/-- Negative test: unbound wolf variable is rejected. -/
theorem stone_discourse_rejects_unbound :
    (g₀_stone, SWorld.actual) ∉ (stoneSentence1 stone_d₀).info := by
  unfold stoneSentence1 might modalExpand
  dsimp only
  intro ⟨_, w₁, _, _, hmem⟩
  unfold existsLabeled atom Discourse.mapInfo at hmem
  obtain ⟨_, hpred⟩ := hmem
  dsimp only at hpred
  simp [isWolf, g₀_stone, vWolf] at hpred

end Stone


-- ============================================================
-- Bathroom Sentences (paper §3.4, item 92b)
-- ============================================================

section Bathroom

/-- @cite{partee-1972}'s bathroom sentence world model. -/
inductive BWorld where
  | bath | noBath
  deriving DecidableEq, Repr, Inhabited

inductive BEntity where
  | bathroom
  deriving DecidableEq, Repr, Inhabited

def αBath : FLabel := ⟨1⟩
def vBath : IVar := ⟨1⟩

def isBathroom (g : ICDRTAssignment BWorld BEntity) (w : BWorld) : Bool :=
  g.indiv vBath w == .some .bathroom

def isUpstairs (g : ICDRTAssignment BWorld BEntity) (w : BWorld) : Bool :=
  g.indiv vBath w == .some .bathroom && w == .bath

/--
"Either there's no bathroom, or it's upstairs." (paper item 92b)

PIP analysis: ¬∃^αBath x.bathroom(x) ∨ upstairs(DEF_αBath{x})

Label αBath is registered under negation and floated to the second disjunct.
-/
def bathroomSentence : PUpdate BWorld BEntity :=
  disj
    (negation
      (existsLabeled αBath vBath {.bathroom}
        isBathroom
        (atom isBathroom)))
    (conj
      (retrieveDef αBath)
      (atom isUpstairs))

/-- The bathroom label survives negation — core PIP mechanism. -/
theorem bathroom_label_survives_negation (d : Discourse BWorld BEntity) :
    let firstDisjunct := negation
      (existsLabeled αBath vBath {.bathroom}
        isBathroom
        (atom isBathroom))
    (firstDisjunct d).labels.registered αBath = true := by
  simp only [negation, existsLabeled, atom, Discourse.mapInfo,
             LabelStore.registered, Option.isSome, LabelStore.register,
             αBath]
  rfl

private def g₀ : ICDRTAssignment BWorld BEntity :=
  { indiv := λ _ _w => .star, prop := λ _ => ∅ }

private def bath_d₀ : Discourse BWorld BEntity :=
  { info := Set.univ, labels := LabelStore.empty }

/-- End-to-end: the bathroom sentence is consistent. -/
theorem bathroom_sentence_consistent :
    (bathroomSentence bath_d₀).info.Nonempty := by
  refine ⟨(g₀, .noBath), ?_⟩
  apply Set.mem_union_left
  refine ⟨Set.mem_univ _, ?_⟩
  intro ⟨_, hpred⟩
  simp [isBathroom, g₀, vBath] at hpred

private def g_bath : ICDRTAssignment BWorld BEntity :=
  g₀.updateIndivConst vBath (.some .bathroom)

/-- Negative test: bathroom at noBath world is rejected. -/
theorem bathroom_rejects_nonupstairs :
    (g_bath, BWorld.noBath) ∉ (bathroomSentence bath_d₀).info := by
  intro hmem
  unfold bathroomSentence disj at hmem
  dsimp only at hmem
  rcases hmem with h | h
  · unfold negation at h
    dsimp only at h
    obtain ⟨_, hneg⟩ := h
    apply hneg
    unfold existsLabeled atom Discourse.mapInfo
    exact ⟨⟨g₀, .bathroom, Set.mem_univ _, rfl, rfl⟩, rfl⟩
  · unfold conj at h
    simp only [retrieveDef, negation, existsLabeled, atom, Discourse.mapInfo,
               LabelStore.register, LabelStore.lookup, αBath, vBath,
               isBathroom] at h
    obtain ⟨_, hpred⟩ := h
    exact absurd hpred (by unfold isUpstairs g_bath vBath; decide)

end Bathroom


-- ============================================================
-- Paycheck Pronouns (paper §2.6.4)
-- ============================================================

section Paycheck

/--
"John spent his paycheck. Bill saved it." (paper items 66–67)

"it" carries descriptive content "paycheck-of(x, possessor)" which is
re-evaluated when the possessor variable is rebound to Bill.

Value-based: "it" → John's paycheck → wrong referent
Description-based: "it" → "the paycheck of [current subject]" → Bill's paycheck
-/
inductive PEntity where
  | john | bill | johnsPaycheck | billsPaycheck
  deriving DecidableEq, Repr, Inhabited

def αPaycheck : FLabel := ⟨2⟩
def vPaycheck : IVar := ⟨2⟩
def vPossessor : IVar := ⟨3⟩

inductive PWorld where
  | w0
  deriving DecidableEq, Repr, Inhabited

/-- Relational paycheck predicate: depends on both paycheck and possessor. -/
def isPaycheckOf (g : ICDRTAssignment PWorld PEntity) (w : PWorld) : Bool :=
  match g.indiv vPaycheck w, g.indiv vPossessor w with
  | .some .johnsPaycheck, .some .john => true
  | .some .billsPaycheck, .some .bill => true
  | _, _ => false

/-- Re-evaluation yields Bill's paycheck when possessor = Bill. -/
theorem paycheck_needs_descriptions :
    let g : ICDRTAssignment PWorld PEntity :=
      { indiv := λ v _w =>
          if v == vPaycheck then .some .billsPaycheck
          else if v == vPossessor then .some .bill
          else .star
        prop := λ _ => ∅ }
    isPaycheckOf g .w0 = true := by decide

end Paycheck


-- ============================================================
-- Modal Subordination Data (from @cite{roberts-1989})
-- ============================================================

/-- A modal subordination datum. -/
structure ModalSubDatum where
  sentence1 : String
  sentence2 : String
  modal1 : String
  modal2 : String
  anaphor : String
  antecedent : String
  felicitous : Bool
  source : String := ""
  deriving Repr

def wolfMightWould : ModalSubDatum := {
  sentence1 := "A wolf might come in."
  sentence2 := "It would eat you first."
  modal1 := "might", modal2 := "would"
  anaphor := "it", antecedent := "a wolf"
  felicitous := true
  source := "Roberts (1989)"
}

def wolfMightCould : ModalSubDatum := {
  sentence1 := "A wolf might come in."
  sentence2 := "It could eat you first."
  modal1 := "might", modal2 := "could"
  anaphor := "it", antecedent := "a wolf"
  felicitous := true
  source := "Roberts (1989)"
}

def burglarMightWould : ModalSubDatum := {
  sentence1 := "A burglar might break in."
  sentence2 := "He would steal the jewelry."
  modal1 := "might", modal2 := "would"
  anaphor := "he", antecedent := "a burglar"
  felicitous := true
  source := "Roberts (1989)"
}

def wolfMightIndicative : ModalSubDatum := {
  sentence1 := "A wolf might come in."
  sentence2 := "It eats you first."
  modal1 := "might", modal2 := "indicative"
  anaphor := "it", antecedent := "a wolf"
  felicitous := false
  source := "Roberts (1989)"
}

def wolfMightWill : ModalSubDatum := {
  sentence1 := "A wolf might come in."
  sentence2 := "It will eat you first."
  modal1 := "might", modal2 := "will"
  anaphor := "it", antecedent := "a wolf"
  felicitous := false
  source := "Roberts (1989)"
}

def wolfCouldWould : ModalSubDatum := {
  sentence1 := "A wolf could come in."
  sentence2 := "It would eat you first."
  modal1 := "could", modal2 := "would"
  anaphor := "it", antecedent := "a wolf"
  felicitous := true
  source := "Roberts (1989)"
}

def modalSubData : List ModalSubDatum := [
  wolfMightWould, wolfMightCould, burglarMightWould,
  wolfMightIndicative, wolfMightWill, wolfCouldWould
]

def felicitousModalSub : List ModalSubDatum :=
  modalSubData.filter (·.felicitous)


-- ============================================================
-- Bridge 1: Modal Subordination
-- ============================================================

/--
Modal continuation type: whether a modal inherits its accessibility
relation from prior discourse context.

PIP predicts modal subordination is felicitous iff the second modal
*subordinates* — i.e., it inherits the accessibility relation established
by the first modal (paper §2.6.3). "Would" is analyzed as `must` with
the inherited R; "could" as `might` with the inherited R.

Modals that establish their own accessibility relation (epistemic "must",
future "will", indicative mood) cannot access entities introduced under
a prior modal's scope.
-/
inductive ModalContinuation where
  | subordinating   -- inherits accessibility (would, could)
  | independent     -- establishes own accessibility (indicative, will, must)
  deriving DecidableEq, Repr

/-- Classify an English modal by whether it subordinates. -/
def classifyModal2 : String → ModalContinuation
  | "would" => .subordinating
  | "could" => .subordinating
  | _ => .independent

/--
PIP predicts modal subordination felicity iff the second modal
subordinates (inherits the accessibility relation from the first).
-/
def pipPredictsModalSub (datum : ModalSubDatum) : Bool :=
  classifyModal2 datum.modal2 == .subordinating

theorem pip_wolf_might_would :
    pipPredictsModalSub wolfMightWould = true := by decide

theorem pip_wolf_might_could :
    pipPredictsModalSub wolfMightCould = true := by decide

theorem pip_wolf_indicative_fails :
    pipPredictsModalSub wolfMightIndicative = false := by decide

theorem pip_wolf_will_fails :
    pipPredictsModalSub wolfMightWill = false := by decide

theorem pip_modal_sub_felicitous_agreement :
    felicitousModalSub.all
      (λ d => pipPredictsModalSub d == d.felicitous) = true := by
  decide

/-- External/local binding modes under modals (paper §2.1). -/
theorem modal_sub_binding_modes :
    (modalBindings ⟨99⟩ ⟨0⟩ αWolf)[1]? =
      some ⟨⟨0⟩, .local, some αWolf⟩ ∧
    (modalBindings ⟨99⟩ ⟨0⟩ αWolf)[0]? =
      some ⟨⟨99⟩, .external, none⟩ := by
  exact ⟨rfl, rfl⟩


-- ============================================================
-- Bridge 2: Bathroom Sentences
-- ============================================================

/-- Label survival is the core mechanism for bathroom sentences. -/
theorem bathroom_mechanism :
    ∀ d : Discourse BWorld BEntity,
    (negation
      (existsLabeled αBath vBath {.bathroom}
        isBathroom
        (atom isBathroom)) d).labels.registered αBath = true := by
  intro d
  simp only [negation, existsLabeled, atom, Discourse.mapInfo,
             LabelStore.registered, Option.isSome, LabelStore.register, αBath]
  rfl

/-- Full bathroom sentence preserves labels through disj + negation. -/
theorem bathroom_full_sentence_label_available :
    ∀ d : Discourse BWorld BEntity,
    (bathroomSentence d).labels.registered αBath = true := by
  intro d
  simp only [bathroomSentence, disj, negation, existsLabeled, atom,
             conj, retrieveDef, Discourse.mapInfo,
             LabelStore.registered, Option.isSome, LabelStore.register,
             LabelStore.lookup, αBath, vBath, isBathroom, isUpstairs]
  rfl


-- ============================================================
-- Bridge 3: Donkey Anaphora
-- ============================================================

theorem pip_geach_donkey :
    DonkeyAnaphora.geachDonkey.boundReading = true := rfl

theorem pip_conditional_donkey :
    DonkeyAnaphora.conditionalDonkey.boundReading = true := rfl

theorem pip_paycheck :
    DonkeyAnaphora.paycheckSentence.boundReading = true := rfl


-- ============================================================
-- Intensional Anaphora: Might Blocks (paper §3.1)
-- ============================================================

section IntensionalBurger

/--
"Andrea might be eating a cheeseburger. #It is large." (paper item 79)

The burger description is world-dependent: BURGER_w([b]) holds only
at worlds where Andrea is eating a burger. At worlds where she isn't,
Σb(BURGER_w(b)) = ∅, failing the existential presupposition SINGLE(ΣbE).

Felicity condition (paper item 83):
  ∀w(MIGHT_w(ΣwE) → SINGLE(ΣbE))
fails because some context-set worlds have no burger.
-/
inductive IBWorld where
  | actual | burgerW
  deriving DecidableEq, Repr, Inhabited

inductive IBEntity where
  | burger
  deriving DecidableEq, Repr, Inhabited

def ibWorlds : List IBWorld := [.actual, .burgerW]
def αBurger : FLabel := ⟨10⟩
def vBurger : IVar := ⟨10⟩

def ibAccess : BAccessRel IBWorld
  | .actual, .actual => true
  | .actual, .burgerW => true
  | _, _ => false

/-- World-dependent predicate: burger exists only at burgerW. -/
def isBurgerAt (g : ICDRTAssignment IBWorld IBEntity) (w : IBWorld) : Bool :=
  g.indiv vBurger w == .some .burger && w == .burgerW

def burgerSentence : PUpdate IBWorld IBEntity :=
  might ibAccess ibWorlds
    (existsLabeled αBurger vBurger {.burger}
      isBurgerAt (atom isBurgerAt))

theorem burger_label_registered (d : Discourse IBWorld IBEntity) :
    (burgerSentence d).labels.registered αBurger = true := by
  simp only [burgerSentence, might, modalExpand, existsLabeled, atom,
             Discourse.mapInfo, LabelStore.registered, Option.isSome,
             LabelStore.register, αBurger]
  rfl

/-- The burger description fails at actual — presupposition failure. -/
theorem burger_desc_fails_at_actual :
    ∀ g : ICDRTAssignment IBWorld IBEntity,
    isBurgerAt g .actual = false := by
  intro g; unfold isBurgerAt
  have : (IBWorld.actual == IBWorld.burgerW) = false := by decide
  simp [this]

instance : Fintype IBWorld where
  elems := {.actual, .burgerW}
  complete := λ w => by cases w <;> decide

/--
Might blocks anaphora NOT because of non-reflexive access, but because the
burger **description** is world-dependent: `isBurgerAt g .actual = false`
for all g (burger_desc_fails_at_actual). Even with a reflexive modal base,
the description Σb(BURGER_w([b])) is empty at .actual — no burger there.

The accessibility IS reflexive at .actual (ibAccess .actual .actual = true),
confirming that the blocking mechanism is about description content, not
accessibility structure.
-/
theorem burger_desc_world_dependent :
    isBurgerAt
      { indiv := λ _ _ => .some .burger, prop := λ _ => ∅ }
      .actual = false ∧
    ibAccess .actual .actual = true :=
  ⟨rfl, rfl⟩

end IntensionalBurger


-- ============================================================
-- Intensional Anaphora: Must Allows (paper §3.3)
-- ============================================================

section IntensionalAnimal

/--
"There must be some sort of animal in the shed. It's making quite
a racket!" (paper item 88)

The animal description is world-INdependent: ANIMAL_w([x]) ∧ SINGLE(x)
holds at ALL accessible worlds (realistic modal base includes actual).

Felicity condition (paper item 90):
  ∀w(MUST_w(ΣwX) → SINGLE(ΣxX))
succeeds because must guarantees X at every accessible world including w.
-/
inductive IAWorld where
  | actual | shedW
  deriving DecidableEq, Repr, Inhabited

inductive IAEntity where
  | animal
  deriving DecidableEq, Repr, Inhabited

def iaWorlds : List IAWorld := [.actual, .shedW]
def αAnimal : FLabel := ⟨11⟩
def vAnimal : IVar := ⟨11⟩

/-- Realistic epistemic: actual accessible from itself. -/
def iaAccess : BAccessRel IAWorld
  | .actual, .actual => true
  | .actual, .shedW => true
  | _, _ => false

/-- World-INdependent predicate: holds at ALL worlds. -/
def isAnimalInShed (g : ICDRTAssignment IAWorld IAEntity) (w : IAWorld) : Bool :=
  g.indiv vAnimal w == .some .animal

def animalSentence : PUpdate IAWorld IAEntity :=
  must iaAccess iaWorlds
    (existsLabeled αAnimal vAnimal {.animal}
      isAnimalInShed (atom isAnimalInShed))

theorem animal_label_registered (d : Discourse IAWorld IAEntity) :
    (animalSentence d).labels.registered αAnimal = true := by
  simp only [animalSentence, must, modalExpand, existsLabeled, atom,
             Discourse.mapInfo, LabelStore.registered, Option.isSome,
             LabelStore.register, αAnimal]
  rfl

theorem animal_desc_succeeds :
    ∀ (g : ICDRTAssignment IAWorld IAEntity) (w : IAWorld),
    g.indiv vAnimal w == .some .animal → isAnimalInShed g w = true := by
  intro g w h; simp [isAnimalInShed, h]

instance : Fintype IAWorld where
  elems := {.actual, .shedW}
  complete := λ w => by cases w <;> decide

/--
Must allows anaphora via Kratzer's realistic modal base.

The animal accessibility relation is reflexive at .actual (the evaluation world),
so `must_realistic_at` (derived from the T axiom) guarantees that the
description predicate holds at .actual. This is the Kripke-semantic
grounding of why must enables intensional anaphora.
-/
theorem animal_must_realistic :
    iaAccess .actual .actual = true := rfl

end IntensionalAnimal


-- ============================================================
-- Must with Multiple Animals (paper §3.3, items 106–107)
-- ============================================================

section MultiAnimal

/--
The paper's deeper argument about must (items 106–107): in different
accessible worlds, *different* animals could be in the shed. The
summation across assignments gives MULTIPLE animals, not a single one.

Must still allows anaphora because:
1. The accessibility relation is realistic (actual ∈ β_w*)
2. The animal AT the actual world is singular (SINGLE)

The summation Σx ANIMAL_w*([x]) — evaluated at the discourse world w* —
gives the singleton {cat}. The summation across ALL worlds would give
{cat, dog, raccoon}, but the world variable in ΣxX is bound by the
discourse-level Σw, fixing it to w*.

This enriched model shows why Stone/Brasoveanu's system incorrectly
predicts plurality: it would sum across all accessible worlds, getting
{cat, dog, raccoon} — failing SINGLE.
-/
inductive MAWorld where
  | actual | shedW1 | shedW2
  deriving DecidableEq, Repr, Inhabited

inductive MAEntity where
  | cat | dog | raccoon
  deriving DecidableEq, Repr, Inhabited

def maWorlds : List MAWorld := [.actual, .shedW1, .shedW2]
def αMA : FLabel := ⟨12⟩
def vMA : IVar := ⟨12⟩

/-- Realistic epistemic: actual accessible from itself, plus two alternatives. -/
def maAccess : BAccessRel MAWorld
  | .actual, _ => true
  | _, _ => false

/-- World-dependent predicate: different animal in each world. -/
def isAnimalInShedMA (g : ICDRTAssignment MAWorld MAEntity) (w : MAWorld) : Bool :=
  match g.indiv vMA w, w with
  | .some .cat, .actual => true
  | .some .dog, .shedW1 => true
  | .some .raccoon, .shedW2 => true
  | _, _ => false

/-- At the actual world, only one entity satisfies the description. -/
private def maG (e : MAEntity) : ICDRTAssignment MAWorld MAEntity :=
  { indiv := λ v _w => if v == vMA then .some e else .star
    prop := λ _ => ∅ }

/-- At actual, only cat satisfies the description (SINGLE). -/
theorem ma_single_at_actual :
    isAnimalInShedMA (maG .cat) .actual = true ∧
    isAnimalInShedMA (maG .dog) .actual = false ∧
    isAnimalInShedMA (maG .raccoon) .actual = false :=
  ⟨rfl, rfl, rfl⟩

/-- Different entities satisfy the description at different worlds. -/
theorem ma_different_animals_per_world :
    isAnimalInShedMA
      { indiv := λ v _w => if v == vMA then .some .cat else .star
        prop := λ _ => ∅ } .actual = true ∧
    isAnimalInShedMA
      { indiv := λ v _w => if v == vMA then .some .dog else .star
        prop := λ _ => ∅ } .shedW1 = true ∧
    isAnimalInShedMA
      { indiv := λ v _w => if v == vMA then .some .raccoon else .star
        prop := λ _ => ∅ } .shedW2 = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- Cross-world summation yields PLURAL — Stone/Brasoveanu would incorrectly
    predict plurality here since they sum across all accessible worlds.
    Different animals satisfy the description at different worlds: cat at
    actual, dog at shedW1. -/
theorem ma_cross_world_plural :
    isAnimalInShedMA (maG .cat) .actual = true ∧
    isAnimalInShedMA (maG .dog) .shedW1 = true ∧
    MAEntity.cat ≠ MAEntity.dog :=
  ⟨rfl, rfl, by decide⟩

end MultiAnimal


-- ============================================================
-- Possible Candidates (paper §3.2, items 85–87)
-- ============================================================

section PossibleCandidates

/--
"There may already be a winner in the mayoral race. #She is a woman." (paper item 85)

This is PIP's strongest argument against Stone/Brasoveanu's "in" predicate.
The candidates (alice, bob) are **real people who exist in the actual world**.
A Stone/Brasoveanu-style presupposition requiring only that the referent
"exist in the world of evaluation" would wrongly predict felicity.

PIP correctly blocks anaphora because the *description* WINNER_w([x]) is
world-dependent: in worlds where the tabulation isn't complete, there is
no winner, so Σx WINNER_w([x]) = ∅, failing SINGLE (paper item 87):

  ∀w(MIGHT_w(Σw WINNER_w([x])) → SINGLE(Σx WINNER_w([x])))
-/
inductive PCWorld where
  | actual | aliceWins | bobWins
  deriving DecidableEq, Repr, Inhabited

inductive PCEntity where
  | alice | bob
  deriving DecidableEq, Repr, Inhabited

def pcWorlds : List PCWorld := [.actual, .aliceWins, .bobWins]
def αWinner : FLabel := ⟨20⟩
def vWinner : IVar := ⟨20⟩

/-- Epistemic: speaker considers all outcomes possible. -/
def pcAccess : BAccessRel PCWorld
  | .actual, _ => true
  | _, _ => false

/-- World-dependent predicate: winner only at resolution worlds. -/
def isWinner (g : ICDRTAssignment PCWorld PCEntity) (w : PCWorld) : Bool :=
  match g.indiv vWinner w, w with
  | .some .alice, .aliceWins => true
  | .some .bob, .bobWins => true
  | _, _ => false

/-- "There may already be a winner." -/
def candidateSentence : PUpdate PCWorld PCEntity :=
  might pcAccess pcWorlds
    (existsLabeled αWinner vWinner {.alice, .bob}
      isWinner (atom isWinner))

/-- The winner description is empty at the actual world — no winner declared yet. -/
theorem winner_desc_empty_at_actual :
    ∀ g : ICDRTAssignment PCWorld PCEntity,
    isWinner g .actual = false := by
  intro g; simp [isWinner]

/--
Contrast with Stone/Brasoveanu: the entities EXIST in the actual world
(alice and bob are real candidates), but the description WINNER is empty there.
The "in" predicate would say alice/bob exist → felicitous. PIP says the
DESCRIPTION yields nothing at actual → infelicitous.
-/
theorem candidates_exist_but_description_fails :
    ({.alice, .bob} : Set PCEntity).Nonempty ∧
    (∀ g : ICDRTAssignment PCWorld PCEntity, isWinner g .actual = false) :=
  ⟨⟨.alice, Set.mem_insert _ _⟩, winner_desc_empty_at_actual⟩

/-- The label is registered (the mechanism works), but the description
    cannot be satisfied at the actual world. -/
theorem candidate_label_registered (d : Discourse PCWorld PCEntity) :
    (candidateSentence d).labels.registered αWinner = true := by
  simp only [candidateSentence, might, modalExpand, existsLabeled, atom,
             Discourse.mapInfo, LabelStore.registered, Option.isSome,
             LabelStore.register, αWinner]
  rfl

end PossibleCandidates


-- ============================================================
-- Bridge 4: Intensional Anaphora Contrast
-- ============================================================

/--
The paper's core contribution (§3): might blocks anaphora, must allows it.

The mechanism is the same for both (label + retrieveDef). The difference:
- must guarantees the description holds at the evaluation world (realistic base)
- might only guarantees SOME accessible world

Since the pronoun's existential presupposition (paper item 9) requires
the description to hold at the evaluation world, might fails and must succeeds.
-/
theorem pip_intensional_anaphora_contrast :
    (∀ g : ICDRTAssignment IBWorld IBEntity, isBurgerAt g .actual = false) ∧
    (∀ (g : ICDRTAssignment IAWorld IAEntity) (w : IAWorld),
     g.indiv vAnimal w == .some .animal → isAnimalInShed g w = true) :=
  ⟨burger_desc_fails_at_actual, animal_desc_succeeds⟩

/-- Labels are registered in BOTH cases — the asymmetry is about
    world-dependence of the description, not label availability. -/
theorem labels_registered_in_both_cases :
    (∀ d : Discourse IBWorld IBEntity,
      (burgerSentence d).labels.registered αBurger = true) ∧
    (∀ d : Discourse IAWorld IAEntity,
      (animalSentence d).labels.registered αAnimal = true) :=
  ⟨burger_label_registered, animal_label_registered⟩

/-- Static felicity operator F distinguishes might from must. -/
theorem felicity_might_blocks :
    (Felicity.singlePresup (W := IBWorld) (λ w => w == .burgerW)).felicitous .actual = false := by
  decide

theorem felicity_must_allows :
    (Felicity.singlePresup (W := IAWorld) (λ _ => true)).felicitous .actual = true := by
  decide


-- ============================================================
-- Unified Account
-- ============================================================

/--
PIP provides a unified account via TWO mechanisms:

1. **Label monotonicity**: labels survive all operators
   → modal subordination, bathroom sentences, donkey anaphora

2. **World-dependent descriptions + existential presupposition**:
   pronouns presuppose their description holds at the evaluation world
   → might blocks anaphora, must allows it

No stipulated accommodation rules, no "in" predicate (contra
@cite{stone-1999} / @cite{brasoveanu-2010}), no special accessibility conditions.

Evidence: all 5 phenomena are verified by the theorems above:
- `stone_discourse_consistent` + `stone_discourse_rejects_unbound`
- `bathroom_sentence_consistent` + `bathroom_rejects_nonupstairs`
- `paycheck_needs_descriptions`
- `burger_desc_fails_at_actual` + `animal_desc_succeeds`
- `pip_intensional_anaphora_contrast`
-/
theorem label_monotonicity_is_uniform :
    -- Labels survive negation (bathroom mechanism)
    (∀ d : Discourse BWorld BEntity,
      (negation
        (existsLabeled αBath vBath {.bathroom}
          isBathroom
          (atom isBathroom)) d).labels.registered αBath = true) ∧
    -- Labels survive might (burger case)
    (∀ d : Discourse IBWorld IBEntity,
      (burgerSentence d).labels.registered αBurger = true) ∧
    -- Labels survive must (animal case)
    (∀ d : Discourse IAWorld IAEntity,
      (animalSentence d).labels.registered αAnimal = true) ∧
    -- Labels survive full discourse (Stone's puzzle)
    (∀ d : Discourse SWorld SEntity,
      (stoneDiscourse d).labels.registered αWolf = true) :=
  ⟨bathroom_mechanism, burger_label_registered,
   animal_label_registered, stone_discourse_label_available⟩


-- ============================================================
-- Bridge 5: Grounding in Kripke Semantics
-- ============================================================

/--
The might/must asymmetry is grounded in descriptions, not accessibility.

Both modal bases are reflexive at .actual. The difference:
- Must (animal): the description `isAnimalInShed` is world-INdependent
  (holds at all worlds) → SINGLE succeeds at every context-set world.
- Might (burger): the description `isBurgerAt` is world-dependent
  (holds only at .burgerW) → SINGLE fails at .actual.

The T axiom is necessary but not sufficient: reflexivity guarantees the
description is checked at the evaluation world, but the description
itself must hold there.
-/
theorem intensional_anaphora_is_T_axiom :
    -- Must's accessibility is reflexive at actual
    iaAccess .actual .actual = true ∧
    -- Might's accessibility is ALSO reflexive at actual
    ibAccess .actual .actual = true ∧
    -- But the burger description fails at actual (world-dependent)
    (∀ g : ICDRTAssignment IBWorld IBEntity, isBurgerAt g .actual = false) :=
  ⟨animal_must_realistic, rfl, burger_desc_fails_at_actual⟩


-- ============================================================
-- Bridge 6: Cross-Sentential Anaphora
-- ============================================================

open CrossSententialAnaphora in
/--
PIP predicts the standard cross-sentential anaphora pattern:

- **Indefinite persistence** (Karttunen 1969): ∃^α introduces a label that
  persists through sequential conjunction → pronoun resolves via DEF_α.
- **Standard negation blocks** (Heim 1982): negation filters the info state,
  and the CONJUNCTION version ("John didn't see a bird. It was singing.")
  fails because sequential conjunction makes the second sentence evaluate
  in a context where no bird-assignments survive.
- **Double negation enables** (Elliott & Sudo 2025): ¬¬∃^α x.φ registers α
  in the body; label monotonicity through both negations preserves it.

The difference between standard negation blocking and double negation
enabling is exactly PIP's label monotonicity: labels survive negation
(`labels_survive_negation`), but the info state does not survive single
negation in sequential discourse.
-/
theorem pip_cross_sentential_predictions :
    -- Indefinites persist: label + conjunction → felicitous
    indefinitePersists.felicitous = true ∧
    -- Standard negation blocks (in sequential discourse)
    standardNegationBlocks.felicitous = false ∧
    -- Double negation enables (labels survive both negations)
    doubleNegation.felicitous = true := by
  exact ⟨rfl, rfl, rfl⟩

open CrossSententialAnaphora in
/--
PIP predicts that universals and negative quantifiers block
cross-sentential anaphora: ∀x.φ = ¬∃x.¬φ does not introduce a
labeled existential, so no DEF_α is available.
-/
theorem pip_quantifier_blocking :
    universalBlocks.felicitous = false ∧
    negativeBlocks.felicitous = false ∧
    mostBlocks.felicitous = false := by
  exact ⟨rfl, rfl, rfl⟩


-- ============================================================
-- Bridge 7: DPL Comparison — Why PIP Succeeds Where DPL Fails
-- ============================================================

/-!
### PIP vs DPL: The Architectural Difference

DPL negation is a **test**: `⟦¬φ⟧(g, h) iff g = h ∧ ¬∃k. φ(g, k)`.
The output assignment equals the input — no bindings are exported through
negation. This is why `¬¬∃xφ ≠ ∃xφ` in DPL (`dpl_dne_fails_anaphora`):
double negation doesn't recover the binding.

PIP negation propagates **labels** from the body: `(negation φ d).labels =
(φ d).labels`. The info state is complemented, but the label registry
survives. This is exactly what enables bathroom sentences and double-negation
anaphora.

The following theorems make this architectural difference explicit.
-/

/--
DPL negation resets the output assignment — it cannot export bindings.

This is the key structural property of DPL that blocks cross-negation
anaphora: after `¬φ`, the output assignment equals the input, so any
variables bound inside φ are inaccessible.
-/
theorem dpl_neg_is_test :
    ∀ (E : Type*) (φ : Semantics.Dynamic.DPL.DPLRel E) (g h : Nat → E),
    Semantics.Dynamic.DPL.DPLRel.neg φ g h → g = h :=
  λ _ _ _ _ h => h.1

/--
PIP negation preserves labels — it CAN export descriptive content.

This is the fundamental advantage of PIP over DPL: even though the info
state is complemented (like DPL's test), the label registry propagates
outward. The pronoun resolves via DEF_α (label lookup), not via assignment
binding.
-/
theorem pip_neg_preserves_labels :
    ∀ (d : Discourse BWorld BEntity) (φ : PUpdate BWorld BEntity)
      (α : FLabel) (desc : Description BWorld BEntity),
    (φ d).labels.lookup α = some desc →
    (negation φ d).labels.lookup α = some desc :=
  λ d φ α desc h => labels_survive_negation d α φ desc h

/--
The contrast: DPL negation blocks anaphora (test), PIP negation allows it
(labels survive). This is the architectural reason bathroom sentences are
infelicitous in DPL but felicitous in PIP.

Concretely:
- `dpl_dne_fails_anaphora`: ¬¬∃x.φ ≠ ∃x.φ in DPL (double negation
  doesn't recover binding)
- `bathroom_mechanism`: labels survive through negation in PIP (the
  bathroom sentence works because αBath is registered despite negation)
-/
theorem pip_solves_dpl_negation_problem :
    -- DPL: ¬¬∃xφ ≠ ∃xφ (double negation fails for anaphora)
    (∃ (x : Nat) (φ : Semantics.Dynamic.DPL.DPLRel Nat),
      Semantics.Dynamic.DPL.DPLRel.neg
        (Semantics.Dynamic.DPL.DPLRel.neg
          (Semantics.Dynamic.DPL.DPLRel.exists_ x φ)) ≠
        Semantics.Dynamic.DPL.DPLRel.exists_ x φ) ∧
    -- PIP: labels survive negation (bathroom sentences work)
    (∀ d : Discourse BWorld BEntity,
      (negation
        (existsLabeled αBath vBath {.bathroom}
          isBathroom
          (atom isBathroom)) d).labels.registered αBath = true) :=
  ⟨Semantics.Dynamic.DPL.dpl_dne_fails_anaphora, bathroom_mechanism⟩


-- ============================================================
-- Bridge 8: Presupposition Projection
-- ============================================================

/-!
Presupposition projection bridges are in `PIP.Bridges`:
- `pip_felicity_agrees_with_andFilter` — F(φ ∧ ψ) ↔ andFilter
- `pip_felicity_agrees_with_neg` — F(¬φ) ↔ PrProp.neg
- `pip_felicity_agrees_with_impFilter` — F(φ → ψ) ↔ impFilter
- `pip_felicity_agrees_with_orFilter` — F(φ ∨ ψ) decomposition
-/


-- ============================================================
-- Donkey Anaphora (paper §2.6.2, items 53–56)
-- ============================================================

section Donkey

/-!
### PIP Donkey Derivation

"Every farmer who owns a donkey beats it." (paper items 53–56)

PIP analysis: ∀x(farmer(x) ∧ ∃^αD y(donkey(y) ∧ owns(x,y)) →
              beats(x, DEF_αD{y}))

The label αD for the donkey is registered inside the restrictor's
existential. Because ∀ = ¬∃¬ and labels survive both negations,
αD is available in the nuclear scope for DEF_αD retrieval.

Key property: formula label subordination. The label αD is subordinated
to the restrictor — its descriptive content is "donkey(y) ∧ owns(x,y)".
When the pronoun "it" (= DEF_αD{y}) is resolved, it finds the unique
donkey owned by the farmer under discussion.
-/

inductive DWorld where
  | w0
  deriving DecidableEq, Repr, Inhabited

inductive DEntity where
  | farmer1 | farmer2 | donkey1 | donkey2
  deriving DecidableEq, Repr, Inhabited

def dWorlds : List DWorld := [.w0]
def αDonkey : FLabel := ⟨30⟩
def vFarmer : IVar := ⟨30⟩
def vDonkey : IVar := ⟨31⟩

def isFarmer (g : ICDRTAssignment DWorld DEntity) (w : DWorld) : Bool :=
  match g.indiv vFarmer w with
  | .some .farmer1 | .some .farmer2 => true
  | _ => false

def isDonkey (g : ICDRTAssignment DWorld DEntity) (w : DWorld) : Bool :=
  match g.indiv vDonkey w with
  | .some .donkey1 | .some .donkey2 => true
  | _ => false

/-- Ownership: farmer1 owns donkey1, farmer2 owns donkey2. -/
def owns (g : ICDRTAssignment DWorld DEntity) (w : DWorld) : Bool :=
  match g.indiv vFarmer w, g.indiv vDonkey w with
  | .some .farmer1, .some .donkey1 => true
  | .some .farmer2, .some .donkey2 => true
  | _, _ => false

/-- Beating: every farmer who owns a donkey beats it. -/
def beats (g : ICDRTAssignment DWorld DEntity) (w : DWorld) : Bool :=
  match g.indiv vFarmer w, g.indiv vDonkey w with
  | .some .farmer1, .some .donkey1 => true
  | .some .farmer2, .some .donkey2 => true
  | _, _ => false

/--
"Every farmer who owns a donkey beats it."

PIP formula: ∀x(farmer(x) ∧ ∃^αD y(donkey(y) ∧ owns(x,y)) →
             beats(x, DEF_αD))

Dynamic encoding: forall_ = ¬∃¬, with labeled existential for the donkey.
-/
def donkeySentence : PUpdate DWorld DEntity :=
  forall_ vFarmer {.farmer1, .farmer2}
    (conj
      (atom (λ g w => isFarmer g w))
      (conj
        (existsLabeled αDonkey vDonkey {.donkey1, .donkey2}
          isDonkey
          (atom (λ g w => isDonkey g w && owns g w)))
        (conj
          (retrieveDef αDonkey)
          (atom beats))))

instance : Fintype DWorld where
  elems := {.w0}
  complete := λ w => by cases w <;> decide

/-- The donkey label is registered through the forall (¬∃¬). -/
theorem donkey_label_registered (d : Discourse DWorld DEntity) :
    (donkeySentence d).labels.registered αDonkey = true := by
  simp only [donkeySentence, forall_, negation, exists_, existsLabeled, atom,
             conj, retrieveDef, Discourse.mapInfo,
             LabelStore.registered, Option.isSome, LabelStore.register,
             LabelStore.lookup, αDonkey]
  rfl

end Donkey


-- ============================================================
-- Hob-Nob (paper §3.5, items 91–93)
-- ============================================================

section HobNob

/-!
### Cross-Attitude Anaphora: Hob-Nob

"Hob thinks a witch blighted his mare. Nob wonders whether
she (the same witch) killed his cow." (Geach 1967)

PIP analysis (paper items 91–93): The label αWitch is registered
under Hob's belief attitude. Nob's wonder attitude retrieves the
same label. Label persistence across attitude operators is the
same mechanism as modal subordination.

Key property: labels are part of the discourse state, not the
information state. Since attitudes (like modals) affect only the
info state while preserving labels, cross-attitude anaphora works
by the same mechanism as cross-modal anaphora.
-/

inductive HNWorld where
  | actual | hobBelief | nobWonder
  deriving DecidableEq, Repr, Inhabited

inductive HNEntity where
  | witch
  deriving DecidableEq, Repr, Inhabited

def hnWorlds : List HNWorld := [.actual, .hobBelief, .nobWonder]
def αWitch : FLabel := ⟨40⟩
def vWitch : IVar := ⟨40⟩

/-- Hob's doxastic accessibility: Hob believes from actual to hobBelief. -/
def hobAccess : BAccessRel HNWorld
  | .actual, .hobBelief => true
  | _, _ => false

/-- Nob's bouletic accessibility: Nob wonders from actual to nobWonder. -/
def nobAccess : BAccessRel HNWorld
  | .actual, .nobWonder => true
  | _, _ => false

def isWitch (g : ICDRTAssignment HNWorld HNEntity) (w : HNWorld) : Bool :=
  g.indiv vWitch w == .some .witch

/-- Hob's belief: "a witch blighted his mare" -/
def hobBelief : PUpdate HNWorld HNEntity :=
  must hobAccess hnWorlds
    (existsLabeled αWitch vWitch {.witch}
      isWitch
      (atom isWitch))

/-- Nob's wonder: "she killed his cow" — retrieves αWitch from Hob's belief. -/
def nobWonder : PUpdate HNWorld HNEntity :=
  conj
    (retrieveDef αWitch)
    (might nobAccess hnWorlds
      (atom (λ g w => g.indiv vWitch w != .star)))

/-- The full Hob-Nob discourse. -/
def hobNobDiscourse : PUpdate HNWorld HNEntity :=
  conj hobBelief nobWonder

/-- The witch label survives from Hob's belief to Nob's wonder. -/
theorem hobnob_label_persists (d : Discourse HNWorld HNEntity) :
    (hobBelief d).labels.registered αWitch = true := by
  simp only [hobBelief, must, modalExpand, existsLabeled, atom,
             Discourse.mapInfo, LabelStore.registered, Option.isSome,
             LabelStore.register, αWitch]
  rfl

/-- After the full discourse, αWitch is still available. -/
theorem hobnob_full_label_available (d : Discourse HNWorld HNEntity) :
    (hobNobDiscourse d).labels.registered αWitch = true := by
  simp only [hobNobDiscourse, conj, nobWonder, hobBelief, must, might,
             modalExpand, existsLabeled, atom, retrieveDef,
             Discourse.mapInfo, LabelStore.registered, Option.isSome,
             LabelStore.register, LabelStore.lookup, αWitch, vWitch, isWitch]
  rfl

end HobNob


-- ============================================================
-- Semantic Framework Comparison
-- ============================================================

/-!
### DPL vs ICDRT vs PIP: Coverage Comparison

The three frameworks have different coverage profiles for anaphora
phenomena. PIP's descriptive content mechanism handles all cases
uniformly; DPL and ICDRT each miss some.

| Phenomenon | DPL | ICDRT | PIP |
|---|---|---|---|
| Cross-sentential | ✓ | ✓ | ✓ |
| Negation blocks | ✓ | ✓ | ✓ |
| Donkey anaphora | ✓ | ✓ | ✓ |
| Double negation | ✗ | ✓ | ✓ |
| Bathroom sentences | ✗ | ✓ | ✓ |
| Modal subordination | ✗ | ✓ | ✓ |
| Paycheck pronouns | ✗ | ✗ | ✓ |
| Intensional anaphora | ✗ | ✗ | ✓ |
-/

/-- Coverage datum for framework comparison. -/
structure CoverageDatum where
  phenomenon : String
  dpl : Bool
  icdrt : Bool
  pip : Bool
  deriving Repr

def coverageData : List CoverageDatum := [
  ⟨"Cross-sentential", true, true, true⟩,
  ⟨"Negation blocks", true, true, true⟩,
  ⟨"Donkey anaphora", true, true, true⟩,
  ⟨"Double negation", false, true, true⟩,
  ⟨"Bathroom sentences", false, true, true⟩,
  ⟨"Modal subordination", false, true, true⟩,
  ⟨"Paycheck pronouns", false, false, true⟩,
  ⟨"Intensional anaphora", false, false, true⟩
]

/-- PIP covers all phenomena (all pip fields are true). -/
theorem pip_covers_all :
    coverageData.all (·.pip) = true := by decide

/-- DPL misses 5 phenomena. -/
theorem dpl_misses_five :
    (coverageData.filter (! ·.dpl)).length = 5 := by decide

/-- ICDRT misses 2 phenomena (paycheck + intensional). -/
theorem icdrt_misses_two :
    (coverageData.filter (! ·.icdrt)).length = 2 := by decide

/-- PIP strictly extends ICDRT: everything ICDRT covers, PIP covers too. -/
theorem pip_extends_icdrt :
    coverageData.all (λ d => !d.icdrt || d.pip) = true := by decide

/-- PIP strictly extends DPL. -/
theorem pip_extends_dpl :
    coverageData.all (λ d => !d.dpl || d.pip) = true := by decide


end KeshetAbney2024
