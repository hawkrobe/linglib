import Linglib.Data.Examples.Jenks2018
import Linglib.Semantics.Definiteness.Interpret
import Linglib.Semantics.Genericity.MeaningPreservation
import Linglib.Fragments.Mandarin.Determiners
import Linglib.Fragments.Cantonese.Determiners
import Linglib.Fragments.German.Determiners

/-!
# Jenks (2018): Articulated Definiteness without Articles

This file formalizes [jenks-2018], the claim that Mandarin, without a definite article,
distinguishes the two definites of [schwarz-2009]: unique definites are bare nouns, read by
[chierchia-1998]'s covert ι, and anaphoric definites are demonstrative descriptions, the
demonstrative supplying the index of ι^x, (22). The distribution follows from three principles
over a language's declared determiner inventory. The Blocking Principle, (23), makes the covert
ι available exactly when no overt determiner marks uniqueness (`IotaAvailable`), which is how
Mandarin bare nouns can be definite and Cantonese ones, whose [Clf-N] marks both
presuppositions, cannot (`selectShift_mandarin`). Index!, (50), an instance of Maximize
Presupposition, requires the indexed form wherever an index is available, so bare nouns are
excluded from anaphoric, donkey and producer-product bridging environments and demonstratives
from the unique ones (`BareLicit`, `MarkedLicit`); and a bare anaphoric subject survives as a
continuing topic, Section 5.3, but not as a new one. The paper's data, (10) to (20), (49) and
(51) to (56), agree with the prediction row by row (`rows_agree`). A demonstrative denotes its
index's value in every situation where it is defined, so it cannot covary through the situation
pronoun as a bare noun does, Section 4.3; and Table 2's cells are the marking strategies the
fragments derive, marked-unique being the unattested fourth (`table2`).

## Implementation notes

* The environments are the paper's six, mapped to [schwarz-2013]'s presupposition types by
  `useTypeToPresupType` and `bridgingPresupType`; the marked form is the language's obligatory
  exponent of the environment's presupposition, the demonstrative in Mandarin and [Clf-N] in
  Cantonese, so Cantonese's restricted demonstrative, (57), is not modelled.
* [jenks-2018] types the index of ι^x as a property, Section 4.4; the substrate's
  `Description.anaphoric` carries an individual index, so Section 4.4 is not formalized.

## References

* [jenks-2018]
* [schwarz-2009]
* [schwarz-2013]
* [chierchia-1998]
-/

namespace Jenks2018

open Data.Examples Definiteness Determiner Semantics.Composition Semantics.Kinds.MeaningPreservation

/-! ### Environments and principles -/

/-- The definite environments of Sections 3 and 6. -/
inductive Environment
  | largerSituation
  | immediateSituation
  | partWholeBridging
  | producerBridging
  | anaphoric
  | donkey
  deriving DecidableEq, Repr

/-- The presupposition an environment licenses, [schwarz-2013]'s split of bridging included. -/
def Environment.presup : Environment → DefPresupType
  | .largerSituation => useTypeToPresupType .largerSituation
  | .immediateSituation => useTypeToPresupType .immediateSituation
  | .partWholeBridging => bridgingPresupType .partWhole
  | .producerBridging => bridgingPresupType .relational
  | .anaphoric => useTypeToPresupType .anaphoric
  | .donkey => useTypeToPresupType .donkey

/-- A description's discourse status, Section 5.3: no topic, a continuing topic or a new one. -/
inductive Topic
  | none
  | continuing
  | new
  deriving DecidableEq, Repr

/-- The Blocking Principle, (23): the covert ι is available exactly when no overt determiner
marks uniqueness. -/
def IotaAvailable (inv : Inventory) : Prop := ¬ inv.MarksPresup .uniqueness

/-- An index is available exactly in the environments licensed by familiarity, Section 5.1:
prior mention of the referent or, in producer-product bridging, of its argument. -/
def IndexAvailable (env : Environment) : Prop := env.presup = .familiarity

/-- The bare noun is licit: ι is available and, by Index!, (50), no indexed form competes, or the
description is a continuing topic, Section 5.3. -/
def BareLicit (inv : Inventory) (env : Environment) (t : Topic) : Prop :=
  IotaAvailable inv ∧ (¬ (IndexAvailable env ∧ inv.MarksPresup .familiarity) ∨ t = .continuing)

/-- The marked form is licit: the inventory marks the environment's presupposition. -/
def MarkedLicit (inv : Inventory) (env : Environment) : Prop := inv.MarksPresup env.presup

instance (inv : Inventory) : Decidable (IotaAvailable inv) := by
  unfold IotaAvailable; infer_instance

instance (env : Environment) : Decidable (IndexAvailable env) := by
  unfold IndexAvailable; infer_instance

instance (inv : Inventory) (env : Environment) (t : Topic) : Decidable (BareLicit inv env t) := by
  unfold BareLicit; infer_instance

instance (inv : Inventory) (env : Environment) : Decidable (MarkedLicit inv env) := by
  unfold MarkedLicit; infer_instance

/-- Index!: with an index available and an indexed form in the inventory, a bare noun that is
not a continuing topic is out. -/
theorem not_bareLicit_of_indexAvailable {inv : Inventory} {env : Environment} {t : Topic}
    (h : IndexAvailable env) (hm : inv.MarksPresup .familiarity) (ht : t ≠ .continuing) :
    ¬ BareLicit inv env t :=
  λ ⟨_, h'⟩ => h'.elim (λ h'' => h'' ⟨h, hm⟩) ht

/-! ### Type-shifting under blocking -/

/-- The type-shift context a declared inventory induces: each covert shift is blocked by an
overt exponent of its meaning, (23). -/
def shiftContext (inv : Inventory) : TypeShiftContext where
  number := .neutral
  downDefined := false
  iotaBlocked := decide (inv.MarksPresup .uniqueness)
  iotaAnaphoricBlocked := decide (inv.MarksPresup .familiarity)
  existsBlocked := decide (inv.Realizes .indefinite)
  instantiationAccessible := true

/-- Mandarin bare nouns type-shift by ι, and ι^x is unavailable to them: bare nouns are unique
definites and never anaphoric ones. -/
theorem selectShift_mandarin :
    selectShift (shiftContext Mandarin.Determiners.inventory) = some .iota ∧
      .iotaAnaphoric ∉ availableShifts (shiftContext Mandarin.Determiners.inventory) := by
  decide

/-- Cantonese [Clf-N] marks uniqueness, so its bare nouns have no definite shift. -/
theorem not_iotaAvailable_cantonese : ¬ IotaAvailable Cantonese.Determiners.inventory := by
  decide

/-! ### The data -/

/-- A row: the language's inventory, the environment, the discourse status, and the judgments on
the bare and the marked form where the paper gives them. -/
structure Row where
  inventory : Inventory
  env : Environment
  topic : Topic
  bare : Option Bool
  marked : Option Bool

private def envOf : String → Option Environment
  | "largerSituation" => some .largerSituation
  | "immediateSituation" => some .immediateSituation
  | "partWholeBridging" => some .partWholeBridging
  | "producerBridging" => some .producerBridging
  | "anaphoric" => some .anaphoric
  | "donkey" => some .donkey
  | _ => none

private def topicOf : String → Option Topic
  | "none" => some .none
  | "continuing" => some .continuing
  | "new" => some .new
  | _ => none

/-- A row from the paper's features. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let inv ← match e.language with
    | "mand1415" => some Mandarin.Determiners.inventory
    | "cant1236" => some Cantonese.Determiners.inventory
    | _ => none
  let env ← (e.feature? "environment").bind envOf
  let t ← (e.feature? "topic").bind topicOf
  some ⟨inv, env, t, (e.feature? "bare").map (· == "ok"), (e.feature? "marked").map (· == "ok")⟩

/-- The Mandarin data of Sections 3 and 5 and the Cantonese data of Section 6. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- A judgment, where the paper gives one, agrees with a prediction. -/
def Agrees (p : Prop) : Option Bool → Prop
  | none => True
  | some b => p ↔ b = true

instance (p : Prop) [Decidable p] : ∀ o, Decidable (Agrees p o)
  | none => inferInstanceAs (Decidable True)
  | some _ => inferInstanceAs (Decidable (_ ↔ _))

/-- The paper's data row by row: the bare noun is judged licit exactly when `BareLicit` and the
marked form exactly when `MarkedLicit`. -/
theorem rows_agree :
    ∀ r ∈ rows, Agrees (BareLicit r.inventory r.env r.topic) r.bare ∧
      Agrees (MarkedLicit r.inventory r.env) r.marked := by
  decide

/-! ### Demonstratives are strict (Section 4.3) -/

/-- A demonstrative description denotes the value of its index in every situation where its
restrictor holds of it: it cannot covary through the situation pronoun as the bare unique
definite does, (27) to (30). -/
theorem interpret_demonstrative_eq_some_iff {E W : Type} (R : DenotGS E W .et)
    (δ : Features.Deixis.Feature) (s d : Nat) (g : Assignment E) (gs : SitAssignment W) (x : E) :
    interpret (.demonstrative R δ s d) g gs = some x ↔ R g gs (g d) ∧ x = g d := by
  rw [interpret_demonstrative]
  split_ifs with h <;> simp [h, eq_comm]

/-! ### The typology (Table 2) -/

/-- Table 2's attested cells: bipartite (German, Lakhota), marked anaphoric (Mandarin, Akan, Wu)
and generally marked (Cantonese, English); the marked-unique cell is unattested. -/
def attested : List DefMarkingStrategy := [.bipartite, .markedAnaphoric, .generallyMarked]

/-- The fragments derive Table 2's columns: German bipartite, Mandarin marked anaphoric,
Cantonese and English generally marked. -/
theorem table2 :
    German.Determiners.inventory.markingStrategy = .bipartite ∧
      Mandarin.Determiners.inventory.markingStrategy = .markedAnaphoric ∧
      Cantonese.Determiners.inventory.markingStrategy = .generallyMarked ∧
      English.Determiners.inventory.markingStrategy = .generallyMarked := by
  decide

end Jenks2018
