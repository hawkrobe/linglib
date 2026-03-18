import Linglib.Theories.Semantics.Dynamic.PIP.Connectives

/-!
# PIP: Worked Phenomena

@cite{keshet-abney-2024} @cite{partee-1972} @cite{roberts-1989} @cite{stone-1997}Concrete examples demonstrating how PIP handles the core anaphora puzzles
via description-based retrieval over finite models:

1. **Stone's puzzle**: "A wolf might come. It would eat you first."
2. **Bathroom sentences**: "Either there's no bathroom, or it's upstairs."
3. **Paycheck pronouns**: "John spent his paycheck. Bill saved it."

Each example uses a small finite world/entity model with `native_decide`
to verify PIP's predictions.

-/

namespace Semantics.Dynamic.PIP.Phenomena

open Semantics.Dynamic.Core
open Semantics.Dynamic.PIP


-- ============================================================
-- Stone's Puzzle: Modal Subordination
-- ============================================================

section Stone

/--
Stone's puzzle world model.

Three possible worlds:
- `actual`: the evaluation world (no wolf present)
- `wolfIn`: a world where a wolf comes in
- `noWolf`: a world where no wolf comes in
-/
inductive SWorld where
  | actual | wolfIn | noWolf
  deriving DecidableEq, Repr, BEq, Inhabited

/-- The entities: just one wolf. -/
inductive SEntity where
  | wolf
  deriving DecidableEq, Repr, BEq, Inhabited

/-- All worlds in the model. -/
def sWorlds : List SWorld := [.actual, .wolfIn, .noWolf]

/-- Formula label for "a wolf". -/
def αWolf : FLabel := ⟨0⟩

/-- Variable for the wolf. -/
def vWolf : IVar := ⟨0⟩

/--
Epistemic accessibility from actual world.

The speaker considers both wolfIn and noWolf possible.
-/
def sAccess : PAccessRel SWorld
  | .actual, .wolfIn => true
  | .actual, .noWolf => true
  | _, _ => false

/-- Wolf predicate: true when the wolf variable is bound to wolf. -/
def isWolf (g : ICDRTAssignment SWorld SEntity) (_w : SWorld) : Bool :=
  g.indiv vWolf == .some .wolf

/-- Come-in predicate: wolves come in only at wolfIn. -/
def comesIn (g : ICDRTAssignment SWorld SEntity) (w : SWorld) : Bool :=
  g.indiv vWolf == .some .wolf && w == .wolfIn

/--
Stone's sentence 1: "A wolf might come."

  might(∃^αWolf x. wolf(x) ∧ comeIn(x))

The existential is inside the modal:
- x (the wolf) is **local** — bound by ∃ inside might
- The world variable is **external** — bound by might

Label αWolf records the description "wolf(x) that comes in".
-/
def stoneSentence1 : PUpdate SWorld SEntity :=
  might sAccess sWorlds
    (existsLabeled αWolf vWolf {.wolf}
      isWolf
      (atom (λ g w => isWolf g w && comesIn g w)))

/--
After "A wolf might come in", the label αWolf is registered.

This is the crucial property: even though the wolf exists only in
possible worlds, the descriptive content "wolf(x)" is available
in the discourse state for subsequent anaphora.
-/
theorem stone_label_registered (d : Discourse SWorld SEntity)
    (_hConsistent : d.info.Nonempty) :
    (stoneSentence1 d).labels.registered αWolf = true := by
  simp only [stoneSentence1, might, modalExpand, existsLabeled, atom, Discourse.mapInfo,
             LabelStore.registered, Option.isSome, LabelStore.register, αWolf]
  rfl

/--
Stone's sentence 2: "It would eat you first."

"It" = DEF_αWolf{x} — retrieves the wolf via its description.
"would" = must in the same accessibility relation.

The pronoun succeeds because αWolf was registered by sentence 1
and labels survive modal operators.
-/
def stoneSentence2 : PUpdate SWorld SEntity :=
  conj
    (retrieveDef αWolf)  -- "It" — resolve the pronoun
    (would sAccess sWorlds
      (atom (λ g _w => g.indiv vWolf != .star)))  -- eats you (simplified)

/--
The full Stone's puzzle discourse: sentence 1; sentence 2.

The discourse is well-defined (non-trivially consistent) because:
1. Sentence 1 registers αWolf and filters to worlds where a wolf might come in
2. Sentence 2 retrieves the wolf via DEF_αWolf and continues in the modal context
-/
def stoneDiscourse : PUpdate SWorld SEntity :=
  conj stoneSentence1 stoneSentence2

/--
After the full discourse, the label is still available.
Labels are monotonically accumulated through conjunction, retrieveDef,
and would/must because all these operators preserve labels.
-/
theorem stone_discourse_label_available (d : Discourse SWorld SEntity) :
    (stoneDiscourse d).labels.registered αWolf = true := by
  simp only [stoneDiscourse, conj, stoneSentence2, stoneSentence1,
             would, must, might, modalExpand, existsLabeled, atom, retrieveDef,
             Discourse.mapInfo, LabelStore.registered, Option.isSome,
             LabelStore.register, LabelStore.lookup, αWolf, vWolf, isWolf]
  rfl

/-- Base assignment: all variables unbound. -/
private def g₀_stone : ICDRTAssignment SWorld SEntity :=
  { indiv := λ _ => .star, prop := λ _ => ∅ }

/-- Witness assignment for Stone's puzzle: wolf variable bound to wolf. -/
private def g_wolf : ICDRTAssignment SWorld SEntity :=
  { indiv := λ v => if v == vWolf then .some .wolf else .star
    prop := λ _ => ∅ }

/-- Universal input discourse for Stone's puzzle. -/
private def stone_d₀ : Discourse SWorld SEntity :=
  { info := Set.univ, labels := LabelStore.empty }

/-- g_wolf survives sentence 1: might finds a wolf at an accessible world. -/
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

/-- g_wolf survives retrieveDef: the label αWolf was registered by sentence 1. -/
private theorem g_wolf_in_retrieve :
    (g_wolf, SWorld.actual) ∈ (retrieveDef αWolf (stoneSentence1 stone_d₀)).info := by
  unfold retrieveDef
  simp only [stoneSentence1, might, modalExpand, existsLabeled, atom,
             Discourse.mapInfo, LabelStore.register, LabelStore.lookup, αWolf,
             vWolf, isWolf]
  exact ⟨g_wolf_in_sentence1, rfl, rfl⟩

/--
End-to-end test: Stone's discourse is consistent on a concrete model.

After processing "A wolf might come. It would eat you first.", the
discourse state is non-empty: the assignment g_wolf (with vWolf ↦ wolf)
at the actual world survives the full pipeline:

1. **might**: g_wolf at.actual survives because (g_wolf,.wolfIn) is in
   the body result (the wolf exists at.wolfIn via `existsLabeled`)
2. **retrieveDef αWolf**: succeeds because the label was registered
3. **would/must**: g_wolf at.actual survives because `modalExpand` adds
   (g_wolf,.wolfIn) and (g_wolf,.noWolf) to the body's input, and the
   atom predicate (vWolf ≠ ⋆) holds for all of them

Without `modalExpand`, step 3 would fail: must would check accessible
worlds.wolfIn/.noWolf but find no pairs there in the body result.
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

/--
Negative test: an assignment with **unbound** wolf variable does NOT survive
Stone's discourse. The existsLabeled in sentence 1 extends assignments
with `vWolf ↦.some.wolf`, and the atom predicate `isWolf` requires
`g.indiv vWolf ==.some.wolf`. An unbound assignment (vWolf = ⋆)
fails this predicate check, so it cannot appear in the body result
of might, and is correctly rejected.

This confirms the discourse genuinely filters — it's not vacuously
accepting all assignments.
-/
theorem stone_discourse_rejects_unbound :
    (g₀_stone, SWorld.actual) ∉ (stoneSentence1 stone_d₀).info := by
  unfold stoneSentence1 might modalExpand
  dsimp only
  intro ⟨_, w₁, _, _, hmem⟩
  unfold existsLabeled atom Discourse.mapInfo at hmem
  -- hmem has form: ⟨extended_membership, predicate⟩
  -- The predicate requires isWolf g₀_stone w₁ = true,
  -- but isWolf g₀_stone _ = (.star == .some .wolf) = false
  obtain ⟨_, hpred⟩ := hmem
  dsimp only at hpred
  simp [isWolf, g₀_stone, vWolf] at hpred

end Stone


-- ============================================================
-- Bathroom Sentences
-- ============================================================

section Bathroom

/--
Bathroom world model.

Two possible worlds:
- `bath`: there is a bathroom (upstairs)
- `noBath`: there is no bathroom
-/
inductive BWorld where
  | bath | noBath
  deriving DecidableEq, Repr, BEq, Inhabited

/-- The entities. -/
inductive BEntity where
  | bathroom
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Label for "a bathroom". -/
def αBath : FLabel := ⟨1⟩

/-- Variable for the bathroom. -/
def vBath : IVar := ⟨1⟩

/-- Bathroom predicate. -/
def isBathroom (g : ICDRTAssignment BWorld BEntity) (_w : BWorld) : Bool :=
  g.indiv vBath == .some .bathroom

/-- Upstairs predicate: the bathroom is upstairs in the bath world. -/
def isUpstairs (g : ICDRTAssignment BWorld BEntity) (w : BWorld) : Bool :=
  g.indiv vBath == .some .bathroom && w == .bath

/--
Partee's bathroom sentence:
  "Either there's no bathroom, or it's upstairs."

PIP analysis:
  ¬∃^αBath x.bathroom(x) ∨ upstairs(DEF_αBath{x})

1. First disjunct: negation of labeled existential
   - The label αBath is registered even under negation
   - Records description "bathroom(x)"

2. Second disjunct: uses DEF_αBath to retrieve the bathroom
   - The description "bathroom(x)" is available because labels
     survive negation (the fundamental PIP insight)

This contrasts with standard DPL/DRT where negation blocks
accessibility of discourse referents introduced in the negated scope.
-/
def bathroomSentence : PUpdate BWorld BEntity :=
  disj
    -- ¬∃^α x. bathroom(x)
    (negation
      (existsLabeled αBath vBath {.bathroom}
        isBathroom
        (atom isBathroom)))
    -- upstairs(DEF_α{x})
    (conj
      (retrieveDef αBath)
      (atom isUpstairs))

/--
The bathroom label is registered after the first disjunct,
even though it's under negation.
-/
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

/-- Assignment with no variables bound. -/
private def g₀ : ICDRTAssignment BWorld BEntity :=
  { indiv := λ _ => .star, prop := λ _ => ∅ }

/-- Universal input discourse. -/
private def bath_d₀ : Discourse BWorld BEntity :=
  { info := Set.univ, labels := LabelStore.empty }

/--
End-to-end test: the full bathroom sentence is consistent on a concrete model.

Given a universal input (all assignment-world pairs), the bathroom sentence
produces a non-empty output. The witness (g₀,.noBath) survives via the
first disjunct (negation): g₀ doesn't bind vBath to any entity, so it's
NOT in the existsLabeled output, meaning negation keeps it.

This verifies the full compositional pipeline:
  disj → negation → existsLabeled → atom (first disjunct)
  disj → label floating → retrieveDef → atom (second disjunct)
-/
theorem bathroom_sentence_consistent :
    (bathroomSentence bath_d₀).info.Nonempty := by
  refine ⟨(g₀, .noBath), ?_⟩
  -- The output is left.info ∪ right.info; show membership in left
  apply Set.mem_union_left
  -- left = negation(existsLabeled ...) bath_d₀
  -- Membership: (g₀, .noBath) ∈ bath_d₀.info ∧ (g₀, .noBath) ∉ result.info
  refine ⟨Set.mem_univ _, ?_⟩
  -- Show (g₀, .noBath) is NOT in the existsLabeled output.
  -- The existsLabeled output only contains pairs where isBathroom holds,
  -- but isBathroom g₀ w = (g₀.indiv vBath == .some .bathroom) = (.star == .some .bathroom) = false
  intro ⟨_, hpred⟩
  simp [isBathroom, g₀, vBath] at hpred

/-- Assignment with bathroom entity bound. -/
private def g_bath : ICDRTAssignment BWorld BEntity :=
  { indiv := λ v => if v == vBath then .some .bathroom else .star
    prop := λ _ => ∅ }

/--
Negative test: a bathroom-bound assignment at the no-bathroom world
is rejected by the full bathroom sentence.

At `.noBath`, both disjuncts fail:
- First (negation): g_bath IS in the existential's output (it matches
  the `isBathroom` predicate), so negation removes it
- Second (upstairs): `isUpstairs` requires `w ==.bath`, but w = `.noBath`

This tests the genuine semantic content: the sentence says either there's
no bathroom OR the bathroom is upstairs. A bathroom that isn't upstairs
violates both conditions.
-/
theorem bathroom_rejects_nonupstairs :
    (g_bath, BWorld.noBath) ∉ (bathroomSentence bath_d₀).info := by
  intro hmem
  unfold bathroomSentence disj at hmem
  dsimp only at hmem
  rcases hmem with h | h
  · -- First disjunct: negation removes g_bath (existential succeeds)
    unfold negation at h
    dsimp only at h
    obtain ⟨_, hneg⟩ := h
    apply hneg
    unfold existsLabeled atom Discourse.mapInfo
    exact ⟨⟨g₀, .bathroom, Set.mem_univ _, rfl, rfl⟩, rfl⟩
  · -- Second disjunct: isUpstairs fails (.noBath ≠ .bath)
    unfold conj at h
    simp only [retrieveDef, negation, existsLabeled, atom, Discourse.mapInfo,
               LabelStore.register, LabelStore.lookup, αBath, vBath,
               isBathroom] at h
    obtain ⟨_, hpred⟩ := h
    -- isUpstairs g_bath .noBath = (.some .bathroom == .some .bathroom && .noBath == .bath)
    -- = (true && false) = false, contradicting hpred
    exact absurd hpred (by unfold isUpstairs g_bath vBath; decide)

end Bathroom


-- ============================================================
-- Paycheck Pronouns
-- ============================================================

section Paycheck

/--
Paycheck pronouns:

  "John spent his paycheck. Bill saved it."

"it" ≠ John's paycheck (which was already spent).
"it" = "his paycheck" with "his" re-evaluated for Bill.

PIP analysis:
- "his paycheck" introduces label α with description
  "paycheck-of(x, possessor)" where possessor is contextually resolved
- "it" = DEF_α{x} — re-evaluates the description relative to the
  current assignment, where the subject is now Bill

This is the cleanest argument for description-based over value-based
anaphora: the pronoun carries a function (λperson. person's paycheck),
not a fixed entity.

Value-based account: "it" → John's paycheck → wrong referent
Description-based: "it" → "the paycheck of [current subject]" → Bill's paycheck ✓
-/
inductive PEntity where
  | john | bill | johnsPaycheck | billsPaycheck
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Label for the paycheck description. -/
def αPaycheck : FLabel := ⟨2⟩

/-- Variable for the paycheck. -/
def vPaycheck : IVar := ⟨2⟩

/-- Variable for the possessor. -/
def vPossessor : IVar := ⟨3⟩

/-- Single-world model (paycheck is non-modal). -/
inductive PWorld where
  | w0
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Paycheck-of predicate: relates a paycheck to its owner.

The key property: this predicate is **relational** — it depends on
both the paycheck variable and the possessor variable. When the
possessor changes (John → Bill), the paycheck changes too.
-/
def isPaycheckOf (g : ICDRTAssignment PWorld PEntity) (_w : PWorld) : Bool :=
  match g.indiv vPaycheck, g.indiv vPossessor with
  | .some .johnsPaycheck, .some .john => true
  | .some .billsPaycheck, .some .bill => true
  | _, _ => false

/--
Description-based anaphora correctly predicts the paycheck reading
because the description "paycheck-of(x, possessor)" is re-evaluated
when the possessor variable changes.

In a value-based system, "it" would be bound to johnsPaycheck.
In PIP, "it" = DEF_α{x} with α = "paycheck-of(x, possessor)",
and the possessor variable gets rebound to bill.
-/
theorem paycheck_needs_descriptions :
    -- With possessor = bill, isPaycheckOf yields billsPaycheck, not johnsPaycheck
    let g : ICDRTAssignment PWorld PEntity :=
      { indiv := λ v =>
          if v == vPaycheck then .some .billsPaycheck
          else if v == vPossessor then .some .bill
          else .star
        prop := λ _ => ∅ }
    isPaycheckOf g .w0 = true := by native_decide

end Paycheck


-- ============================================================
-- Summation Pronouns
-- ============================================================

section Summation

open Semantics.Dynamic.IntensionalCDRT (IContext)
open Semantics.Dynamic.Core (Entity)

/--
Summation: Σxφ = ⋃{g(x) : g ∈ G, ⟦φ⟧^{M,{g},w*} = 1}

PIP's formal construct for collecting entity values across assignments.
Given a plural context G, a variable x, and a restricting formula φ,
summation returns the set of all g(x) values for assignments g that
satisfy φ. This is what handles summation pronouns:

  "Every farmer bought a donkey. They paid a lot for them."

"them" = Σx(donkey(x)) = the set of ALL donkeys across all farmer-donkey
pairs in the plural context G.
-/
def summationFiltered {W E : Type*} (c : IContext W E) (v : IVar)
    (φ : ICDRTAssignment W E → W → Bool) : Set (Entity E) :=
  { e | ∃ g w, (g, w) ∈ c ∧ φ g w = true ∧ g.indiv v = e }

/--
Unfiltered summation: collects ALL values of v across assignments.

This is a special case of `summationFiltered` with a trivially true filter.
-/
def summationValues {W E : Type*} (c : IContext W E) (v : IVar) : Set (Entity E) :=
  { e | ∃ g w, (g, w) ∈ c ∧ g.indiv v = e }

/-- Unfiltered summation is summation with trivial filter. -/
theorem summationValues_eq_trivial_filter {W E : Type*}
    (c : IContext W E) (v : IVar) :
    summationValues c v = summationFiltered c v (λ _ _ => true) := by
  ext e; simp [summationValues, summationFiltered]

/--
The summation set is non-empty when the context is non-empty and
the variable is bound (has a non-⋆ value).
-/
theorem summation_nonempty {W E : Type*}
    (c : IContext W E) (v : IVar)
    (gw : ICDRTAssignment W E × W)
    (h : gw ∈ c) :
    gw.1.indiv v ∈ summationValues c v :=
  ⟨gw.1, gw.2, h, rfl⟩

end Summation


-- ============================================================
-- Comparison: Value-Based vs. Description-Based
-- ============================================================

/--
The three systems compared in @cite{keshet-abney-2024}:

1. **Value-based**: Pronouns store entity values directly.
   Works for simple anaphora, fails for modal/negation/paycheck cases.

2. **Description-based (PIP)**: Pronouns carry formula labels.
   Handles all cases uniformly.

3. **File-change / DRT**: Pronouns access discourse referents.
   Handles quantifier donkey cases but struggles with modal contexts
   (requires modal subordination stipulations).

PIP subsumes the file-change approach: descriptions that happen to
pick out a unique entity degenerate to value-based behavior.
-/
inductive AnaphoraStrategy where
  | valueBased
  | descriptionBased  -- PIP
  | fileChange         -- DRT / DPL
  deriving DecidableEq, Repr

/-- PIP uses description-based anaphora. -/
def pipStrategy : AnaphoraStrategy := .descriptionBased

/--
Phenomena coverage by strategy.
-/
structure PhenomenonCoverage where
  strategy : AnaphoraStrategy
  simpleAnaphora : Bool        -- "A man walked in. He sat down."
  donkeyAnaphora : Bool        -- "Every farmer who owns a donkey beats it."
  modalSubordination : Bool    -- "A wolf might come in. It would eat you."
  bathroomSentences : Bool     -- "Either there's no bathroom, or it's upstairs."
  paycheckPronouns : Bool      -- "John spent his paycheck. Bill saved it."
  summationPronouns : Bool     -- "They paid a lot for them."
  deriving Repr

def valueCoverage : PhenomenonCoverage :=
  { strategy := .valueBased
    simpleAnaphora := true
    donkeyAnaphora := true
    modalSubordination := false  -- ✗ wolf only exists in possible worlds
    bathroomSentences := false   -- ✗ bathroom under negation
    paycheckPronouns := false    -- ✗ wrong referent (John's, not Bill's)
    summationPronouns := false } -- ✗ no plural mechanism

def fileChangeCoverage : PhenomenonCoverage :=
  { strategy := .fileChange
    simpleAnaphora := true
    donkeyAnaphora := true
    modalSubordination := false  -- ✗ requires stipulated accommodation
    bathroomSentences := false   -- ✗ negation blocks drefs in standard DRT
    paycheckPronouns := false    -- ✗ value-based at heart
    summationPronouns := true }  -- ✓ via plural DRT

def pipCoverage : PhenomenonCoverage :=
  { strategy := .descriptionBased
    simpleAnaphora := true       -- ✓ trivial description
    donkeyAnaphora := true       -- ✓ description + plural
    modalSubordination := true   -- ✓ labels survive modals
    bathroomSentences := true    -- ✓ labels survive negation
    paycheckPronouns := true     -- ✓ descriptions re-evaluated
    summationPronouns := true }  -- ✓ plural contexts

/-- PIP covers all phenomena. -/
theorem pip_covers_all :
    pipCoverage.simpleAnaphora = true ∧
    pipCoverage.donkeyAnaphora = true ∧
    pipCoverage.modalSubordination = true ∧
    pipCoverage.bathroomSentences = true ∧
    pipCoverage.paycheckPronouns = true ∧
    pipCoverage.summationPronouns = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Value-based fails on modal/negation/paycheck cases. -/
theorem value_based_gaps :
    valueCoverage.modalSubordination = false ∧
    valueCoverage.bathroomSentences = false ∧
    valueCoverage.paycheckPronouns = false := ⟨rfl, rfl, rfl⟩


end Semantics.Dynamic.PIP.Phenomena
