import Linglib.Studies.Ginzburg2012.InquiryCycle
import Linglib.Semantics.Questions.Partition.QUD

/-!
# KOS: Worked Examples
[ginzburg-2012] Ch. 4 ex. 66, ex. 68

Public worked examples demonstrating the substrate operations on concrete
inputs. Earlier these lived inline in `Gameboard/Rules.lean` as `private` defs;
they are public here so consumers (study files, the TTR-typed counterpart
in `Austinian.lean`) can reference them.

## Sections

- §1. Inquiry cycle (Bo): A asks "Is Bo here?", B asserts, A accepts
- §2. Check/Confirm cycle: A asserts, B checks, A confirms
- §3. AssertWithQUD cycle: full Assert protocol on the Bo example
- §4. Partition-based answerhood (RainWorld): typed propositions
       resolving a partition QUD via `PropResolvesQUD`

The string-based examples use a generic `DecidableSupport String String`
instance (string equality as answerhood), and instantiate Cont = String
for utterance content (since the worked examples don't exercise the
LocProp Pending pipeline). See `Austinian.lean` for the TTR-typed
counterpart over `BCheckableAustinian S` and `TTRQuestionB R`.

-/

namespace Ginzburg2012.Examples

open Discourse.Gameboard Question

-- ════════════════════════════════════════════════════
-- § 1. Inquiry Cycle Example (Bo)
-- ════════════════════════════════════════════════════

section InquiryExample

/-- String-based answerhood: a fact resolves a question if they match. -/
instance : DecidableSupport String String where
  supports fact question := fact = question
  decSupports a b := decEq a b

/-- Start: empty TIS. -/
def tis₀ : TIS String String String String := TIS.initial

/-- Step 1: A asks "Is Bo here?" -/
def tis₁ : TIS String String String String := tis₀.ask "Bo is here"

/-- Step 2: B asserts "Bo is here." -/
def tis₂ : TIS String String String String := tis₁.assertRule "Bo is here"

/-- Step 3: A accepts B's assertion. -/
def tis₃ : TIS String String String String := tis₂.accept "Bo is here"

/-- After Ask, QUD contains the question (wrapped as an InfoStruc with no FECs). -/
theorem inquiry_step1_qud :
    tis₁.dgb.qud = [(InfoStruc.fromQuestion "Bo is here" : InfoStruc String String)] := rfl

/-- After Ask, FACTS are unchanged. -/
theorem inquiry_step1_facts : tis₁.dgb.facts = [] := rfl

/-- After Ask, the move is recorded. -/
theorem inquiry_step1_moves : tis₁.dgb.moves = [.ask "Bo is here"] := rfl

/-- After Assert, the fact is in FACTS. -/
theorem inquiry_step2_has_fact : "Bo is here" ∈ tis₂.dgb.facts := by
  simp [tis₂, TIS.assertRule, DGB.assertFact, DGB.addFact, DGB.downdateQud, DGB.recordMove]

/-- After Assert, QUD is empty (the question was resolved). -/
theorem inquiry_step2_qud_empty : tis₂.dgb.qud = [] := by decide

/-- After Accept, the fact appears twice (once from assert, once from accept). -/
theorem inquiry_step3_facts : tis₃.dgb.facts = ["Bo is here", "Bo is here"] := by
  decide

/-- Moves accumulate through the inquiry cycle. -/
theorem inquiry_cycle_moves :
    tis₃.dgb.moves = [.ask "Bo is here", .assert "Bo is here", .accept "Bo is here"] := by
  decide

end InquiryExample

-- ════════════════════════════════════════════════════
-- § 2. Check / Confirm Example
-- ════════════════════════════════════════════════════

section CheckExample

/-- A(1): Bo is in Essen. (Assert) -/
def checkTIS₀ : TIS String String String String := TIS.initial
def checkTIS₁ : TIS String String String String :=
  checkTIS₀.assertRule "Bo is in Essen"

/-- B(1b): Is he? (Check) -/
def checkTIS₂ : TIS String String String String :=
  checkTIS₁.check "Bo is in Essen" "Bo is in Essen"

/-- A(2): Confirm. -/
def checkTIS₃ : TIS String String String String :=
  checkTIS₂.confirm "Bo is in Essen"

/-- After Check, QUD has the polar question. -/
theorem check_pushes :
    checkTIS₂.dgb.qud =
      [(InfoStruc.fromQuestion "Bo is in Essen" : InfoStruc String String)] := by
  decide

/-- After Confirm, the fact is in FACTS and QUD is resolved. -/
theorem confirm_resolves : checkTIS₃.dgb.qud = [] := by decide

end CheckExample

-- ════════════════════════════════════════════════════
-- § 3. AssertWithQUD Example
-- ════════════════════════════════════════════════════

section AssertWithQUDExample

/-- Full inquiry cycle using the Ginzburg 2012 Assert protocol.

A: "Is Bo here?"  (Ask)
B: "Bo is here."  (AssertWithQUD — pushes About("Bo is here") onto QUD)
A: accepts         (Accept + factUpdateQudDowndate) -/
def awq₀ : TIS String String String String := TIS.initial
def awq₁ := awq₀.ask "Bo is here"
def awq₂ := awq₁.assertWithQUD "Bo is here" "Bo is here"

/-- After assertWithQUD, the question from Ask is resolved (fact matches). -/
theorem awq_resolves_original_question : awq₂.dgb.qud = [] := by decide

/-- The fact is in FACTS after assertWithQUD. -/
theorem awq_has_fact : "Bo is here" ∈ awq₂.dgb.facts := by
  simp [awq₂, awq₁, awq₀, TIS.assertWithQUD, TIS.ask, DGB.addFact, DGB.pushQud,
    DGB.downdateQud, DGB.recordMove]

end AssertWithQUDExample

-- ════════════════════════════════════════════════════
-- § 4. Partition-Based Answerhood (RainWorld)
-- ════════════════════════════════════════════════════

section PartitionExample

/-- Three-world scenario: is it raining? -/
inductive RainWorld where
  | sunny | rainy | cloudy
  deriving Repr, DecidableEq

/-- "Is it raining?" — partition into rainy vs non-rainy. -/
def isRainingQ : QUD RainWorld :=
  QUD.ofProject (fun w => match w with | .rainy => true | _ => false) "raining?"

/-- A tagged proposition for the rain example: pairs a `Set RainWorld`
    with a tag enabling decidable equality and Bool-valued resolution. -/
inductive RainProp where
  | raining
  | sunny
  deriving DecidableEq, Repr

def RainProp.toProp : RainProp → Set RainWorld
  | .raining => fun w => w = .rainy
  | .sunny   => fun w => w = .sunny

instance (rp : RainProp) : DecidablePred rp.toProp := fun w => by
  cases rp <;> simp only [RainProp.toProp] <;> exact inferInstance

/-- "It is raining" — true only in the rainy world. -/
def itIsRaining : Set RainWorld := fun w => w = .rainy

instance : DecidablePred itIsRaining := fun w => by
  unfold itIsRaining; exact inferInstance

/-- "It is sunny" — true only in the sunny world. -/
def itIsSunny : Set RainWorld := fun w => w = .sunny

instance : DecidablePred itIsSunny := fun w => by
  unfold itIsSunny; exact inferInstance

def rainWorlds : List RainWorld := [.sunny, .rainy, .cloudy]

/-- "It is raining" resolves "Is it raining?" -/
theorem raining_resolves_raining :
    PropResolvesQUD rainWorlds itIsRaining isRainingQ := by
  unfold PropResolvesQUD itIsRaining
  decide

/-- "It is sunny" also resolves "Is it raining?" -/
theorem sunny_resolves_raining :
    PropResolvesQUD rainWorlds itIsSunny isRainingQ := by
  unfold PropResolvesQUD itIsSunny
  decide

/-- Full inquiry cycle with partition-based support (via `RainProp` tags). -/
def rainTIS₀ : TIS String RainProp (QUD RainWorld) Unit := TIS.initial

instance rainSupport : DecidableSupport RainProp (QUD RainWorld) where
  supports rp q := PropResolvesQUD rainWorlds rp.toProp q
  decSupports rp q := inferInstanceAs (Decidable (PropResolvesQUD _ _ _))

def rainTIS₁ : TIS String RainProp (QUD RainWorld) Unit :=
  rainTIS₀.ask isRainingQ

/-- After asking, QUD has the partition question. -/
theorem rain_ask_qud :
    rainTIS₁.dgb.qud = [(InfoStruc.fromQuestion isRainingQ : InfoStruc (QUD RainWorld) Unit)] :=
  rfl

def rainTIS₂ : TIS String RainProp (QUD RainWorld) Unit :=
  rainTIS₁.assertRule .raining

/-- After asserting "It is raining", QUD is empty (resolved). -/
theorem rain_assert_resolves : rainTIS₂.dgb.qud = [] := by
  unfold rainTIS₂ rainTIS₁ rainTIS₀ TIS.assertRule TIS.ask DGB.assertFact
    DGB.addFact DGB.downdateQud DGB.recordMove DGB.pushQud
  simp only [List.filter, List.any]
  decide

end PartitionExample

end Ginzburg2012.Examples
