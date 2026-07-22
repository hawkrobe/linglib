import Linglib.Semantics.Alternatives.AltMeaning
import Linglib.Semantics.Focus.Interpretation
import Linglib.Semantics.Focus.Control
import Linglib.Semantics.Focus.Particles
import Linglib.Semantics.Composition.Tree
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Data.Examples.Rooth1992

/-!
# Alternative-semantics focus interpretation

Formalises [rooth-1992] over the example rows in
`Data/Examples/Rooth1992.json` and the formal theory in
`Focus/Interpretation.lean` (FIP, Q-A congruence), with a full
compositional derivational chain through Montague semantics and
connection to English fragment entries.

## Pipeline

```
Fragments/English/Nouns ──▷ Montague Lexicon ──▷ Tree
                                                        │
                                                    interp
                                                        │
                                                        ▼
                              propositions (Set QAWorld)
                                                        │
                                                   set literals
                                                        │
                                                        ▼
                                              PropFocusValue = Set (Set QAWorld)
                                                        │
                                                   FIP / qaCongruent
                                                        │
                                                        ▼
                                              Bridge theorems ↔ Data
```

## Model

- Q-A congruence: 4 worlds crossing subject (Fred/Mary) × object
  (beans/rice). Subject focus matches "Who ate the beans?";
  object focus does not.
- "Only" association: 3 worlds for who Mary introduced to Sue.

## What's exercised

- `AltMeaning`, `AltMeaning.unfeatured` — O/A-value computation (§3)
- `fipPrediction` — row adapter over `Data/Examples/Rooth1992.json` (§8)
- `Tree`, `interp` — compositional derivation (§10–§11)
- `Derivation` — derivation bundles (§13)
- `English.Nouns`, `.Predicates.Verbal` — fragment entries (§14)

-/

namespace Rooth1992

open Alternatives
open Focus.Interpretation (fip PropFocusValue qaCongruent qaCongruentWeak)

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Q-A Congruence World Model
-- ═══════════════════════════════════════════════════════════════════════

/-- Worlds crossing subject (Fred/Mary) × object (beans/rice).
    Sufficient to distinguish subject-focus from object-focus
    alternative sets. -/
inductive QAWorld where
  | fredBeans | fredRice | maryBeans | maryRice
  deriving DecidableEq, Repr

open QAWorld

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Propositions
-- ═══════════════════════════════════════════════════════════════════════

/-- "Fred ate the beans" — true exactly at the world `fredBeans`. -/
def fredAteBeans : Set QAWorld := {fredBeans}

/-- "Mary ate the beans" — true exactly at the world `maryBeans`. -/
def maryAteBeans : Set QAWorld := {maryBeans}

/-- "Fred ate the rice" — true exactly at the world `fredRice`. -/
def fredAteRice  : Set QAWorld := {fredRice}

-- ═══════════════════════════════════════════════════════════════════════
-- §3  AltMeaning: Focused vs. Unfeatured
-- ═══════════════════════════════════════════════════════════════════════

/-- Focused "FRED" in "FRED ate the beans" (Rooth §2.4, ex. 23a):
    O-value = "Fred"; A-value = {"Fred", "Mary"}. -/
def altSubjectFocused : AltMeaning String :=
  { oValue := "Fred", aValue := ["Fred", "Mary"] }

/-- Non-focused "ate the beans": singleton A-value (no alternatives).
    Exercises `AltMeaning.unfeatured`. -/
def altPredicateUnfeatured : AltMeaning String :=
  AltMeaning.unfeatured "ate the beans"

/-- Unfeatured O-value equals the input. -/
theorem unfeatured_preserves_oValue :
    altPredicateUnfeatured.oValue = "ate the beans" := rfl

/-- Unfeatured A-value is a singleton containing the O-value.
    Non-focused expressions evoke no alternatives ([rooth-1992] §1). -/
theorem unfeatured_singleton_aValue :
    altPredicateUnfeatured.aValue = ["ate the beans"] := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Q-A Congruence: FIP at the Propositional Level
-- ═══════════════════════════════════════════════════════════════════════

/-! [rooth-1992] §2.4, constraint (26d):
    In a Q-A pair ⟨ψ, α⟩, ⟦ψ⟧° ⊆ ⟦α⟧f.
    The ordinary semantic value of the question is a subset of the
    focus semantic value of the answer. -/

/-- "Who ate the beans?" — Hamblin question with subject alternatives.
    ⟦Q⟧° = {fredAteBeans, maryAteBeans} (Rooth §2.4, ex. 24). -/
def q_whoAteBeans : PropFocusValue QAWorld :=
  {fredAteBeans, maryAteBeans}

/-- Focus value of "[FRED]_F ate the beans" — same subject alternatives.
    ⟦A⟧f = {fredAteBeans, maryAteBeans} (Rooth §2.4, ex. 25a). -/
def fv_subjectFocus : PropFocusValue QAWorld :=
  {fredAteBeans, maryAteBeans}

/-- Focus value of "Fred ate the [BEANS]_F" — object alternatives.
    ⟦A⟧f = {fredAteBeans, fredAteRice} (varies object, not subject). -/
def fv_objectFocus : PropFocusValue QAWorld :=
  {fredAteBeans, fredAteRice}

-- ───────────────────────────────────────────────────────────────────
-- §6a  Congruent Case
-- ───────────────────────────────────────────────────────────────────

/-- Q-A congruence: subject focus value = question denotation.
    ⟦[FRED]_F ate the beans⟧f = ⟦Who ate the beans?⟧ (Rooth §2.4). -/
theorem qa_subject_focus_congruent :
    qaCongruent fv_subjectFocus q_whoAteBeans := rfl

/-- FIP (27) holds: question alternatives ⊆ focus value.
    Trivially satisfied when the sets are equal. -/
theorem fip_congruent :
    fip q_whoAteBeans fv_subjectFocus :=
  fun _ h => h

-- ───────────────────────────────────────────────────────────────────
-- §6b  Incongruent Case
-- ───────────────────────────────────────────────────────────────────

/-- "maryAteBeans" is in the question alternatives... -/
theorem maryAteBeans_in_question :
    maryAteBeans ∈ q_whoAteBeans := by
  right; rfl

/-- ...but it is NOT in the object-focus alternative set... -/
theorem maryAteBeans_not_in_objectFocus :
    maryAteBeans ∉ fv_objectFocus := by
  intro h
  -- maryAteBeans = {maryBeans}; the alts in fv_objectFocus are {fredBeans}, {fredRice}.
  -- Set equality forces maryBeans to be equal to fredBeans or fredRice (contradictions).
  have key : maryBeans ∈ maryAteBeans := rfl
  rcases h with h | h
  · rw [h] at key
    -- key : maryBeans ∈ fredAteBeans = {fredBeans}, so maryBeans = fredBeans
    have : maryBeans = fredBeans := key
    exact absurd this (by decide)
  · rw [h] at key
    have : maryBeans = fredRice := key
    exact absurd this (by decide)

/-- ...so FIP fails for object focus, explaining why "#Fred ate the BEANS"
    is not a congruent answer to "Who ate the beans?" -/
theorem fip_fails_object_focus :
    ¬ fip q_whoAteBeans fv_objectFocus :=
  fun h => maryAteBeans_not_in_objectFocus (h maryAteBeans_in_question)

-- ───────────────────────────────────────────────────────────────────
-- §6c  The Question as a Focus Antecedent
-- ───────────────────────────────────────────────────────────────────

/-- 'Who ate the beans?' as a focus antecedent
    (`Focus.Antecedent`): the anaphoric source of the
    squiggle's contrast set. -/
def qaAntecedent : Focus.Antecedent QAWorld := .question q_whoAteBeans

/-- Question antecedents license the new-information use. -/
theorem qaAntecedent_use : qaAntecedent.use = .newInfo := rfl

/-- The antecedent admits subject focus — FIP routed through the
    antecedent layer. -/
theorem qaAntecedent_admits_subjectFocus :
    qaAntecedent.Admits fv_subjectFocus := fip_congruent

/-- The antecedent rejects object focus. -/
theorem qaAntecedent_rejects_objectFocus :
    ¬ qaAntecedent.Admits fv_objectFocus := fip_fails_object_focus

/-- The question antecedent *fully* resolves against the subject-focus
    meaning: all three clauses of the squiggle presupposition, not just
    FIP — the contrast set contains the ordinary value `fredAteBeans`
    and the distinct alternative `maryAteBeans`. -/
theorem qaAntecedent_resolves :
    qaAntecedent.Resolves fredAteBeans fv_subjectFocus :=
  ⟨fip_congruent, Or.inl rfl,
    maryAteBeans, Or.inr rfl,
    fun h => by
      have : maryBeans ∈ fredAteBeans := h ▸ (rfl : maryBeans ∈ maryAteBeans)
      exact absurd this (by simp [fredAteBeans, maryAteBeans])⟩

/-- A focus-free answer cannot resolve any antecedent: its focus value
    is the unit set `{fredAteBeans}`, defeating the contrast clause —
    "the argument must contain a focus". -/
theorem focusFree_answer_cannot_resolve (Γ : PropFocusValue QAWorld) :
    ¬ Focus.SquiggleSet fredAteBeans {fredAteBeans} Γ :=
  Focus.not_squiggleSet_singleton fredAteBeans Γ

/-- Contrasting phrases (Rooth's symmetric-contrast joke opening, his
    rule construing α as contrasting with β via ⟦β⟧ᵒ ∈ ⟦α⟧f): *Canadian
    farmer*'s ordinary value is a member of *[American]F farmer*'s focus
    value distinct from its ordinary value. -/
theorem farmer_contrast :
    Focus.SquiggleInd "American farmer"
      ({"American farmer", "Canadian farmer"} : Set String)
      "Canadian farmer" :=
  ⟨Or.inr rfl, by decide⟩

-- ───────────────────────────────────────────────────────────────────
-- §6d  Strong vs Direct Association ("The Recognitions")
-- ───────────────────────────────────────────────────────────────────

/-! With a focused transitive verb, the full focus value contains
    "even trivial relations", so fixing *only*'s domain to it yields
    unsatisfiable truth conditions — while intuitively *Mary only READ
    The Recognitions* can be true. The strong theory's separately
    resolved `C` "might be quite a small set"; a lexically carried
    alternative list cannot be pragmatically narrowed. -/

/-- Worlds tracking Mary's relation to *The Recognitions*. -/
inductive RWorld where
  | readOnly      -- read it, nothing more
  | readAndGrasp  -- read and understood it
  | neither
  deriving DecidableEq, Repr

/-- 'reading The Recognitions'. -/
def reading : Set RWorld := {.readOnly, .readAndGrasp}
/-- 'understanding The Recognitions'. -/
def grasping : Set RWorld := {.readAndGrasp}
/-- A trivial property of the same semantic type — a member of the
    full focus value. -/
def trivialR : Set RWorld := Set.univ

/-- With the pragmatically restricted domain, *only READ* is
    satisfiable: true where Mary read without understanding. -/
theorem restricted_only_satisfiable :
    RWorld.readOnly ∈
      Focus.onlyVia {reading, grasping} reading := by
  intro q hq hw
  rcases hq with rfl | rfl
  · rfl
  · exact absurd hw (by simp [grasping])

/-- With the domain fixed to the full focus value (trivial property
    included), *only READ* is unsatisfiable — direct association
    over-generates exclusions. -/
theorem direct_only_unsatisfiable :
    Focus.onlyVia {reading, grasping, trivialR} reading = ∅ := by
  have hne : trivialR ≠ reading := fun h =>
    (by simp [reading] : RWorld.neither ∉ reading)
      (h ▸ Set.mem_univ RWorld.neither)
  ext w
  simp only [Focus.mem_onlyVia, Set.mem_empty_iff_false, iff_false]
  exact fun hw => hne (hw trivialR (by simp) (Set.mem_univ w))

private def readingB : RWorld → Bool
  | .readOnly | .readAndGrasp => true
  | .neither => false
private def graspingB : RWorld → Bool
  | .readAndGrasp => true
  | _ => false
private def trivialB : RWorld → Bool := fun _ => true

/-- The direct-association operator with its lexically carried full
    alternative list is the same over-generation, exhibited on
    `TraditionalOnly` itself: its assertion is everywhere false in this
    model. No pragmatic narrowing is possible — the list is fixed in
    the lexical entry, which is the strong theory's objection. -/
theorem traditional_only_unsatisfiable (w : RWorld) :
    (Focus.Particles.TraditionalOnly.mk
      readingB [graspingB, trivialB]).assertion w = false := by
  cases w <;> rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §7  "Only" Association ([rooth-1992] §2.1)
-- ═══════════════════════════════════════════════════════════════════════

/-! Rooth §2.1, constraint (26a): the domain of quantification C of
    a focusing adverb is a subset of the focus semantic value ⟦α⟧f.

    Rooth's formalization (30b): only(C) introduces
      ∀P[P ∈ C ∧ P(m) → P = VP']
    where C is constrained by the FIP to be a set of properties
    matching the focus semantic value. -/

/-- Worlds for the "only" model: who Mary introduced to Sue. -/
inductive OnlyWorld where
  | billOnly   -- Mary introduced only Bill to Sue
  | johnOnly   -- Mary introduced only John to Sue
  | both       -- Mary introduced both Bill and John
  deriving DecidableEq, Repr

open OnlyWorld

def onlyWorlds : List OnlyWorld := [billOnly, johnOnly, both]

/-- "Mary introduced Bill to Sue" -/
def introBill : OnlyWorld → Bool
  | billOnly => true | johnOnly => false | both => true

/-- "Mary introduced John to Sue" -/
def introJohn : OnlyWorld → Bool
  | billOnly => false | johnOnly => true | both => true

/-- Focus on BILL (Rooth §2.1, ex. 3a):
    O-value = introBill; A-value = {introBill, introJohn}.
    Focus determines the domain of "only". -/
def altBillFocused : AltMeaning (OnlyWorld → Bool) :=
  { oValue := introBill, aValue := [introBill, introJohn] }

/-- "Only Bill" = Mary introduced Bill but not John (Rooth §2.1). -/
def onlyBill : OnlyWorld → Bool
  | billOnly => true | _ => false

/-- "Only John" = Mary introduced John but not Bill. -/
def onlyJohn : OnlyWorld → Bool
  | johnOnly => true | _ => false

/-- "Only" with focus on BILL: O-value holds and all non-actual
    alternatives are excluded (Rooth §2.1, (30b)). -/
theorem only_bill_semantics :
    (onlyWorlds.all fun w =>
      onlyBill w == (introBill w && !introJohn w)) = true := by
  decide

/-- "Only" with focus on JOHN: symmetric case. -/
theorem only_john_semantics :
    (onlyWorlds.all fun w =>
      onlyJohn w == (introJohn w && !introBill w)) = true := by
  decide

/-- Different focus → different "only" meaning.
    Focus on BILL excludes John; focus on JOHN excludes Bill
    (Rooth §2.1, exs. 3a vs 3b). -/
theorem only_focus_determines_meaning :
    onlyBill ≠ onlyJohn := by
  intro h; exact absurd (congrFun h billOnly) (by decide)

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Bridge: Data Rows ↔ Theory
-- ═══════════════════════════════════════════════════════════════════════

/-! The rows (`Data/Examples/Rooth1992.json`) record that "FRED ate the
    beans" is congruent and "#Fred ate the BEANS" is incongruent with
    "Who ate the beans?". The theory (FIP, §6) explains:

    - Subject focus produces a focus value equal to the question
      denotation (§6a), so FIP is satisfied.
    - Object focus produces a focus value that differs (§6b):
      maryAteBeans ∈ ⟦Q⟧° but maryAteBeans ∉ ⟦A⟧f, so FIP fails.

    For "only" (§7), the rows say focus determines what "only"
    excludes. The theory confirms: the FIP constrains the domain C
    of "only" to be a subset of the focus value, so different focus
    positions yield different exclusion domains. -/

open _root_.Rooth1992

/-- The FIP prediction for a row, read off its `focus` feature: subject
    focus ("Fred") evokes the subject-alternative focus value, object
    focus ("beans") the object-alternative one (§6). -/
def fipPrediction (row : Data.Examples.LinguisticExample) : Prop :=
  match row.feature? "focus" with
  | some "Fred"  => fip q_whoAteBeans fv_subjectFocus
  | some "beans" => fip q_whoAteBeans fv_objectFocus
  | _ => False

/-- **Transfer**: a Q-A row is acceptable iff its focus value satisfies
    the FIP against "Who ate the beans?" ([rooth-1992] (26d)). Subject
    focus passes (§6a); object focus fails (§6b). -/
theorem qa_acceptable_iff_fip :
    ∀ row ∈ Examples.all,
      row.feature? "fip_application" = some "qaCongruence" →
      (row.judgment = .acceptable ↔ fipPrediction row) := by
  intro row hrow happ
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl
  · exact absurd happ (by decide)
  · exact absurd happ (by decide)
  · exact ⟨fun _ => fip_congruent, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide),
           fun h => absurd h fip_fails_object_focus⟩

/-- Distinct focusing-adverb rows carry distinct `focus` features: the
    rows form an association-with-focus minimal pair. -/
theorem focusingAdverb_rows_differ_in_focus :
    ∀ r₁ ∈ Examples.all, ∀ r₂ ∈ Examples.all,
      r₁.feature? "fip_application" = some "focusingAdverb" →
      r₂.feature? "fip_application" = some "focusingAdverb" →
      r₁.id ≠ r₂.id → r₁.feature? "focus" ≠ r₂.feature? "focus" := by
  decide

/-- Bridge: the focusing-adverb rows differ only in focus position, and
    the theory maps distinct focus positions to distinct "only"
    meanings (§7). -/
theorem bridge_only_association :
    Examples.only_bill.feature? "focus" ≠
      Examples.only_sue.feature? "focus" ∧
    onlyBill ≠ onlyJohn :=
  ⟨by decide, only_focus_determines_meaning⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §10  Montague Model and Compositional Lexicon
-- ═══════════════════════════════════════════════════════════════════════

/-! The propositions in §2 were hand-defined. Here we derive them
    compositionally: entity denotations + a world-indexed verb meaning
    are combined via direct function application and Heim & Kratzer's
    `interp` to produce the same truth conditions.

    The derivational chain is:
      Fragment entry → Montague LexEntry → Tree → interp → Bool
    run once per world to yield a world-indexed proposition. -/

open Intensional
-- (open removed: Assignment alias eliminated upstream)
open Semantics.Montague (Lexicon)
open Syntax
open Semantics.Composition.Tree

/-- Entity domain for the focus model. -/
inductive E where
  | fred | mary | beans | rice
  deriving DecidableEq, Repr

/-- World-indexed verb semantics for "ate".
    `ateInWorld w obj subj` follows Montague's argument order
    (object first, then subject). -/
def ateInWorld (w : QAWorld) : Denot E Unit (.e ⇒ .e ⇒ .t) :=
  fun obj subj => match w, subj, obj with
  | .fredBeans, .fred, .beans => True
  | .fredRice,  .fred, .rice  => True
  | .maryBeans, .mary, .beans => True
  | .maryRice,  .mary, .rice  => True
  | _, _, _ => False

/-- Montague lexicon parameterized by world.
    Maps surface forms to typed denotations. -/
def focusLex (w : QAWorld) : Lexicon E Unit := fun word =>
  match word with
  | "Fred"  => some ⟨.e, E.fred⟩
  | "Mary"  => some ⟨.e, E.mary⟩
  | "ate"   => some ⟨.e ⇒ .e ⇒ .t, ateInWorld w⟩
  | "beans" => some ⟨.e, E.beans⟩
  | "rice"  => some ⟨.e, E.rice⟩
  | _ => none

-- ═══════════════════════════════════════════════════════════════════════
-- §11  Syntax Trees and Compositional Interpretation
-- ═══════════════════════════════════════════════════════════════════════

/-- Syntax tree: [S [NP Fred] [VP [V ate] [NP beans]]] -/
def tree_fredAteBeans : Tree Unit String :=
  .bin (.leaf "Fred") (.bin (.leaf "ate") (.leaf "beans"))

/-- Syntax tree: [S [NP Mary] [VP [V ate] [NP beans]]] -/
def tree_maryAteBeans : Tree Unit String :=
  .bin (.leaf "Mary") (.bin (.leaf "ate") (.leaf "beans"))

/-- Syntax tree: [S [NP Fred] [VP [V ate] [NP rice]]] -/
def tree_fredAteRice : Tree Unit String :=
  .bin (.leaf "Fred") (.bin (.leaf "ate") (.leaf "rice"))

/-- Default assignment for binding-free trees. -/
private def g₀ : Core.Assignment E := λ _ => E.fred

/-- Extract the Prop truth value from a tree interpretation.
    Returns `none` if the tree is uninterpretable or has non-`t` type. -/
def treeResult (lex : Lexicon E Unit) (t : Tree Unit String) : Option Prop :=
  match interp E Unit lex g₀ t with
  | some ⟨.t, p⟩ => some p
  | _ => none

-- ═══════════════════════════════════════════════════════════════════════
-- §12  Grounding: Compositional Meaning = Hand-Defined Propositions
-- ═══════════════════════════════════════════════════════════════════════

/-! The propositions from §2 were stipulated directly. Here we show
    they are derivable: running `interp` at each world produces
    the same truth values. -/

/-- Compositionally derived "Fred ate beans" proposition. -/
def fredAteBeans_comp : QAWorld → Prop :=
  fun w => (treeResult (focusLex w) tree_fredAteBeans).getD False

/-- Compositionally derived "Mary ate beans" proposition. -/
def maryAteBeans_comp : QAWorld → Prop :=
  fun w => (treeResult (focusLex w) tree_maryAteBeans).getD False

/-- Compositionally derived "Fred ate rice" proposition. -/
def fredAteRice_comp : QAWorld → Prop :=
  fun w => (treeResult (focusLex w) tree_fredAteRice).getD False

/-- Direct function application matches tree interpretation. -/
theorem direct_eq_interp (w : QAWorld) :
    treeResult (focusLex w) tree_fredAteBeans =
    some (ateInWorld w E.beans E.fred) := by
  cases w <;> rfl

/-- Grounding: compositional "Fred ate beans" agrees with hand-defined
    proposition at each world. -/
theorem comp_grounds_fredAteBeans :
    fredAteBeans_comp = fun w => ateInWorld w E.beans E.fred := by
  funext w; cases w <;> rfl

/-- Grounding: compositional "Mary ate beans" = direct function application. -/
theorem comp_grounds_maryAteBeans :
    maryAteBeans_comp = fun w => ateInWorld w E.beans E.mary := by
  funext w; cases w <;> rfl

/-- Grounding: compositional "Fred ate rice" = direct function application. -/
theorem comp_grounds_fredAteRice :
    fredAteRice_comp = fun w => ateInWorld w E.rice E.fred := by
  funext w; cases w <;> rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §12b  The Focus Dimension Through the Same Engine
-- ═══════════════════════════════════════════════════════════════════════

/-! F-marking is a non-`pure` lexicon entry: the same `interp` that
    computes ordinary values at `M = Id` computes focus values at
    `M = AltMeaning` (`pure = AltMeaning.unfeatured` lifts the
    focus-free entries), with `applyForward`'s `<*>` doing Hamblin
    functional application. -/

/-- Alternatives do not distribute through predicate abstraction —
    the honest `none`. -/
instance (E W : Type) : PredAbs AltMeaning E W := ⟨none⟩

/-- The focus lexicon at `M = AltMeaning`: every entry `pure`-lifts
    except focused *[Fred]F*, whose entry carries the subject
    alternatives. -/
def focusLexF (w : QAWorld) : Lexicon E Unit AltMeaning := fun word =>
  match word with
  | "Fred" => some ⟨.e, (⟨E.fred, [E.fred, E.mary]⟩ : AltMeaning _)⟩
  | w' => Lexicon.lift AltMeaning (focusLex w) w'

/-- Focus-dimension tree interpretation. -/
def treeResultF (lex : Lexicon E Unit AltMeaning) (t : Tree Unit String) :
    Option (AltMeaning Prop) :=
  match interp E Unit lex g₀ t with
  | some ⟨.t, p⟩ => some p
  | _ => none

/-- The engine at `M = AltMeaning` computes the two-dimensional meaning
    of *[FRED]F ate the beans*: the O-value is the ordinary
    interpretation and the A-value is the subject-alternative family —
    the focus value is computed, not stipulated. -/
theorem treeResultF_fredAteBeans (w : QAWorld) :
    treeResultF (focusLexF w) tree_fredAteBeans =
      some ⟨ateInWorld w E.beans E.fred,
            [ateInWorld w E.beans E.fred, ateInWorld w E.beans E.mary]⟩ := by
  cases w <;> rfl

/-- O-projection through the engine: mapping `oValue` over the
    `AltMeaning` run recovers the `Id` run. -/
theorem treeResultF_oValue (w : QAWorld) :
    (treeResultF (focusLexF w) tree_fredAteBeans).map (·.oValue) =
      treeResult (focusLex w) tree_fredAteBeans := by
  cases w <;> rfl

/-- The stipulated `fv_subjectFocus` of §6 is exactly the engine's
    computed alternative family, read as proposition sets. -/
theorem fv_subjectFocus_computed :
    fv_subjectFocus =
      {{w | ateInWorld w E.beans E.fred}, {w | ateInWorld w E.beans E.mary}} := by
  have h1 : ({w | ateInWorld w E.beans E.fred} : Set QAWorld) = fredAteBeans := by
    ext w; cases w <;> simp [ateInWorld, fredAteBeans]
  have h2 : ({w | ateInWorld w E.beans E.mary} : Set QAWorld) = maryAteBeans := by
    ext w; cases w <;> simp [ateInWorld, maryAteBeans]
  rw [h1, h2]
  rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §13  Fragment Connection
-- ═══════════════════════════════════════════════════════════════════════

/-! Connect the model's lexicon to English fragment entries. Fragment
    entries provide morphological and syntactic properties; the bridge
    verifies that these properties are consistent with the model and
    that fragment surface forms feed the compositional lexicon. -/

section FragmentNouns
open English.Nouns

/-- Fred is a proper name in the English fragment. -/
theorem fragment_fred_proper : fred.proper = true := rfl

/-- Mary is a proper name in the English fragment. -/
theorem fragment_mary_proper : mary.proper = true := rfl

/-- "bean" is countable in the English fragment. -/
theorem fragment_bean_countable : bean.countable = .count := rfl

/-- Fragment surface forms feed the Montague lexicon.
    The form field of each fragment entry matches a lexicon key. -/
theorem fragment_fred_in_lexicon :
    (focusLex .fredBeans fred.formSg).isSome = true := rfl

theorem fragment_mary_in_lexicon :
    (focusLex .fredBeans mary.formSg).isSome = true := rfl

theorem fragment_bean_pl_in_lexicon :
    (focusLex .fredBeans (bean.formPl.getD "")).isSome = true := rfl

end FragmentNouns

section FragmentVerbs
open English.Predicates.Verbal

/-- "eat" is transitive (NP complement). -/
theorem fragment_eat_transitive : eat.complementType = .np := rfl

/-- "eat" has past tense "ate" matching the lexicon entry. -/
theorem fragment_eat_past_form : eat.formPast = "ate" := rfl

/-- The past form of "eat" is in the Montague lexicon. -/
theorem fragment_eat_past_in_lexicon :
    (focusLex .fredBeans eat.formPast).isSome = true := rfl

end FragmentVerbs

-- ═══════════════════════════════════════════════════════════════════════
-- §15  Full End-to-End Chain
-- ═══════════════════════════════════════════════════════════════════════

/-! The complete derivational chain from fragments to FIP:

    1. Fragment entries (§14) provide surface forms and properties
    2. Surface forms feed the Montague lexicon (§10)
    3. Tree derivations compose meanings via interp (§11)
    4. Running at each world yields propositions grounding §2 (§12)
    5. Propositions build Hamblin questions and focus values (§6)
    6. FIP/qaCongruent proves congruence (§6a) or incongruence (§6b)
    7. Theoretical predictions match empirical judgments (§9) -/

/-- End-to-end: the compositional derivation produces the same truth values
    as the hand-defined propositions used to build the Hamblin question.
    At each world, the tree interp matches the hand-defined proposition. -/
theorem endToEnd_question_grounded :
    (∀ w, treeResult (focusLex w) tree_fredAteBeans = some (ateInWorld w E.beans E.fred)) ∧
    (∀ w, treeResult (focusLex w) tree_maryAteBeans = some (ateInWorld w E.beans E.mary)) := by
  exact ⟨fun w => by cases w <;> rfl, fun w => by cases w <;> rfl⟩

end Rooth1992
