module

public import Linglib.Fragments.Guebie.ParticleVerbs
public import Linglib.Studies.Casali2003
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Syntax.Minimalist.Linearization.Cyclic
public import Linglib.Syntax.Minimalist.Movement.Remnant
public import Linglib.Syntax.Minimalist.SyntacticObject.Derivation
public import Linglib.Data.Examples.SandeClemDabkowski2026

/-!
# Sande, Clem & Dąbkowski (2026): Discontinuous Vowel Harmony in Guébie

This file formalizes the paper's account of discontinuous ATR harmony in Guébie particle-verb
focus constructions, where a fronted particle harmonizes with the clause-final verb across the
intervening subject, auxiliary and object. The syntax is remnant-VP fronting after
[koopman-1997]: the object shifts out of the VP, the verb raises to T unless an auxiliary
occupies T, in which case it stays in v, and the remnant VP fronts to Spec,CP, so two
parameters derive the four attested orders (`ClauseConfig`, `WordOrder`). Harmony is local at
the spell-out of the vP phase, which contains the particle and, exactly when an auxiliary blocks
verb raising, the verb, and the particle keeps the value it received when the remnant later
fronts (`ClauseConfig.harmony`, `surfaceATR`); this derives the paper's correlation between
harmony and the verb's spell-out position (`harmony_eq_hasAux`) and the surface discontinuity
(`discontinuous_harmony`). The local harmony is the ranking of [sande-2019] in Agreement by
Projection ([hansson-2014]) (`optimal_eq_surfaceATR`), the fronting is narrow-syntactic remnant
movement on the Minimalist carrier (`guebie_remnant_fronting`), and spelled-out material stays
accessible to later movement, as Cyclic Linearization ([fox-pesetsky-2005]) allows for the
leftmost element of a phase (`all_clauses_consistent`). The rows are the paper's examples, and
their particle forms and word orders follow from the two parameters (`harmony_rows`,
`order_rows`). Wolof relative clauses ([sy-2005], [martinovic-2019]) show the same profile with
the trigger rather than the target moving (`wolof_rows`, `wolof_profile`). Guébie's ten
vowels make a five-height system in [casali-2003]'s typology, so its System-Dependent [ATR]
Dominance specifies [+ATR]; the particle's [−ATR] default outside harmony is then the weak
assimilatory [+ATR] dominance that account predicts, and its surface value is what the
root-control ranking there derives (`casali_weakAssimilatory`, `surfaceATR_eq_casali`).

## Implementation notes

Spell-out snapshots are lists of terminal labels, and the rows omit the paper's tone numerals.
The paper deems the implementation of local harmony inessential, so the tableau renders only
the ranking of its two constraints. The verb-doubling orders of plain verb focus, the
diagnostics of successive cyclicity and island sensitivity, and the Atchan nasal harmony the
paper leaves open are not formalized.

## References

* [sande-clem-dabkowski-2026]
* [casali-2003]
* [koopman-1997]
* [fox-pesetsky-2005]
* [sande-2019]
* [hansson-2014]
* [sy-2005]
* [martinovic-2019]
-/

@[expose] public section

namespace SandeClemDabkowski2026

open List Data.Examples
open Minimalist.Linearization (Consistent)
open Constraints (Constraint)
open OptimalityTheory

/-- The particle's lexical [ATR] value (`true` = [+ATR]), surfacing when no harmony trigger is
local; the model is the particle /jɔkʊ/ of the fragment. -/
def particleDefaultATR : Bool := Guebie.jOkU.atr

/-! ### The two parameters of predicate fronting -/

/-- The two parameters of the predicate-fronting analysis: an auxiliary in T blocks verb
raising, and the remnant VP containing the particle may front to Spec,CP. -/
structure ClauseConfig where
  hasAux : Bool
  fronted : Bool
  deriving DecidableEq, Repr

/-- The verb stays in v, inside the vP spell-out, exactly when an auxiliary occupies T. -/
def ClauseConfig.verbInVP (c : ClauseConfig) : Bool := c.hasAux

/-- The overt terminals spelled out within vP: the particle, and the verb when it has not
raised; the object has shifted out. -/
def ClauseConfig.vPSpellOut (c : ClauseConfig) : List String :=
  "Part" :: if c.verbInVP then ["V"] else []

/-- The surface clause: the fronted particle, the subject, the auxiliary or raised verb, the
object, the in-situ particle, and the clause-final verb. -/
def ClauseConfig.surfaceOrder (c : ClauseConfig) : List String :=
  (if c.fronted then ["Part"] else []) ++ ["S"]
    ++ (if c.hasAux then ["Aux"] else ["V"]) ++ ["O"]
    ++ (if c.fronted then [] else ["Part"])
    ++ (if c.hasAux then ["V"] else [])

/-- The two-phase derivation: the vP spell-out, then the surface clause. -/
def ClauseConfig.derivation (c : ClauseConfig) : List (List String) :=
  [c.vPSpellOut, c.surfaceOrder]

/-- The four attested word orders. -/
inductive WordOrder where
  | SVOPart
  | SAuxOPartV
  | PartSVO
  | PartSAuxOV
  deriving DecidableEq, Repr

/-- The parameter setting behind each order. -/
def WordOrder.config : WordOrder → ClauseConfig
  | .SVOPart => ⟨false, false⟩
  | .SAuxOPartV => ⟨true, false⟩
  | .PartSVO => ⟨false, true⟩
  | .PartSAuxOV => ⟨true, true⟩

/-- Every parameter setting linearizes consistently across the two phases. -/
theorem all_clauses_consistent :
    ∀ aux fronted : Bool, Consistent (ClauseConfig.derivation ⟨aux, fronted⟩) := by
  decide

/-- The particle can front because it is the leftmost overt element of the vP at spell-out: a
vP that spelled it out after the verb could not front it without an ordering conflict. -/
theorem nonedge_particle_fronting_crashes :
    ¬ Consistent [["V", "Part"], ["Part", "S", "Aux", "O", "V"]] := by
  decide

/-! ### Harmony at the spell-out of vP -/

/-- Harmony applies exactly when the trigger verb is spelled out within vP. -/
def ClauseConfig.harmony (c : ClauseConfig) : Bool := c.vPSpellOut.contains "V"

/-- The paper's correlation: harmony iff an auxiliary keeps the verb in vP, whether or not the
particle fronts. -/
theorem harmony_eq_hasAux (aux fronted : Bool) :
    (ClauseConfig.mk aux fronted).harmony = aux := by
  decide +revert

/-- In the fronted clause with an auxiliary the particle and the verb are not adjacent on the
surface in either order, yet harmony applies. -/
theorem discontinuous_harmony :
    (ClauseConfig.mk true true).harmony = true ∧
      ¬ (["Part", "V"] <:+: (ClauseConfig.mk true true).surfaceOrder ∨
        ["V", "Part"] <:+: (ClauseConfig.mk true true).surfaceOrder) := by
  decide

/-- The particle's surface value: the verb root's under harmony, its lexical default
otherwise. -/
def surfaceATR (c : ClauseConfig) (vRoot : Bool) : Bool :=
  if c.harmony then vRoot else particleDefaultATR

/-- An output candidate for the particle at vP spell-out: its lexical value, the domain-local
trigger when the verb is in the domain, and its output value. -/
structure HarmonyCand where
  lexical : Bool
  trigger : Option Bool
  out : Bool
  deriving DecidableEq, Repr

/-- Faithfulness to the input value. -/
def identIO : Constraint HarmonyCand := Constraint.binary fun c ↦ c.out ≠ c.lexical

/-- Agreement with a domain-local trigger. -/
def atrHarm : Constraint HarmonyCand := Constraint.binary fun c ↦ ∃ t ∈ c.trigger, t ≠ c.out

/-- The domain-local trigger: the verb root's value when the verb is spelled out in vP. -/
def vPTrigger (c : ClauseConfig) (vRoot : Bool) : Option Bool :=
  if c.harmony then some vRoot else none

/-- The vP-domain tableau over the two output values, harmony ranked above faithfulness. -/
def harmonyTableau (lex : Bool) (trig : Option Bool) : Tableau HarmonyCand 2 :=
  Tableau.ofRanking [⟨lex, trig, true⟩, ⟨lex, trig, false⟩] [atrHarm, identIO]
    (List.cons_ne_nil _ _)

/-- The unique winner under the ranking surfaces with exactly the value harmony assigns:
agreeing when a trigger is local, faithful to the default otherwise. -/
theorem optimal_eq_surfaceATR (aux fronted : Bool) (vRoot : Bool) :
    (harmonyTableau particleDefaultATR (vPTrigger ⟨aux, fronted⟩ vRoot)).optimal
      = {⟨particleDefaultATR, vPTrigger ⟨aux, fronted⟩ vRoot,
          surfaceATR ⟨aux, fronted⟩ vRoot⟩} := by
  cases aux <;> cases fronted <;> cases vRoot <;> decide

/-- Guébie's inventory is a five-height system, whose System-Dependent [ATR] Dominance
specifies [+ATR]; the particle's [−ATR] default outside harmony is the weak assimilatory
[+ATR] dominance [casali-2003] predicts for harmonizing affixes in non-harmonic contexts. -/
theorem casali_weakAssimilatory :
    Casali2003.inventoryType? Guebie.inventory = some .fiveHeight ∧
      particleDefaultATR = !Casali2003.InventoryType.fiveHeight.specifiedValue := by
  decide

/-- The particle's surface value is what [casali-2003]'s root-control ranking derives for a
five-height language: the root's value under harmony, the unspecified value in isolation
(`Casali2003.rootControl_optimal`, `Casali2003.isolated_optimal`). -/
theorem surfaceATR_eq_casali (c : ClauseConfig) (vRoot : Bool) :
    surfaceATR c vRoot =
      if c.harmony then vRoot else !Casali2003.InventoryType.fiveHeight.specifiedValue := by
  obtain ⟨aux, fronted⟩ := c
  cases aux <;> cases fronted <;> cases vRoot <;> decide

/-! ### Predicate fronting is narrow-syntactic movement -/

open Minimalist (SyntacticObject LIToken PlanarSyntacticObject)
open Minimalist.SyntacticObject

def V₀ : LIToken := ⟨.simple .V [], 1⟩
def Part₀ : LIToken := ⟨.simple .P [], 2⟩
def T₀ : LIToken := ⟨.simple .T [], 3⟩
def C₀ : LIToken := ⟨.simple .C [], 4⟩

/-- The remnant VP: the particle over the verb's trace. -/
def remnantVP : PlanarSyntacticObject :=
  {PlanarSyntacticObject.leaf Part₀, PlanarSyntacticObject.traceOf V₀}

/-- The derivation of a fronted clause: the verb merges with the particle and raises to T, and
the remnant VP fronts to Spec,CP. -/
def guebieFronting : Derivation :=
  ⟨V₀, [.em .left Part₀, .em .left T₀, .im V₀, .em .left C₀, .im remnantVP]⟩

/-- The verb is a mover and the VP fronts as a remnant, so the fronting configuration is built
in the narrow syntax. -/
theorem guebie_remnant_fronting :
    (V₀ : SyntacticObject) ∈ guebieFronting.movedItems ∧ guebieFronting.IsRemnantStep 4 := by
  decide

/-! ### The paper's examples -/

def orders : List (String × WordOrder) :=
  [("SVOPart", .SVOPart), ("SAuxOPartV", .SAuxOPartV), ("PartSVO", .PartSVO),
    ("PartSAuxOV", .PartSAuxOV)]

def verbs : List (String × Guebie.Morpheme) :=
  [("ni", Guebie.ni), ("ngwOsa", Guebie.ngwOsa)]

def atrs : List (String × Bool) := [("plus", true), ("minus", false)]

def patterns : List (String × List String) :=
  [("S Aux O Part V", ["S", "Aux", "O", "Part", "V"]), ("S V O Part", ["S", "V", "O", "Part"]),
    ("Part S V O", ["Part", "S", "V", "O"]), ("Part S Aux O V", ["Part", "S", "Aux", "O", "V"]),
    ("S Part V O", ["S", "Part", "V", "O"]), ("Part V S V O", ["Part", "V", "S", "V", "O"]),
    ("V S V O Part", ["V", "S", "V", "O", "Part"]), ("V S O Part", ["V", "S", "O", "Part"]),
    ("Part S V O Part", ["Part", "S", "V", "O", "Part"])]

/-- The rows in a language. -/
def rowsIn (lang : String) : List LinguisticExample := Examples.all.filter (·.language == lang)

/-- The Guébie rows' particles surface with the value harmony assigns from the row's order and
verb root. -/
theorem harmony_rows :
    ∀ x ∈ rowsIn "gabo1234", ∀ o ∈ x.parse? "order" orders, ∀ v ∈ x.parse? "verb" verbs,
      ∀ a ∈ x.parse? "particleATR" atrs, a = surfaceATR o.config v.atr := by
  decide +kernel

/-- A Guébie row's word order is acceptable exactly when some parameter setting derives it. -/
theorem order_rows :
    ∀ x ∈ rowsIn "gabo1234", ∀ p ∈ x.parse? "pattern" patterns,
      (x.judgment = .acceptable ↔
        ∃ aux fronted : Bool, (⟨aux, fronted⟩ : ClauseConfig).surfaceOrder = p) := by
  decide +kernel

/-! ### The prediction beyond Guébie -/

/-- The prediction schema: trigger and target are spelled out together in a low phase, and the
two-phase derivation linearizes consistently. -/
def HarmonyProfile (low surface : List String) (trigger target : String) : Prop :=
  trigger ∈ low ∧ target ∈ low ∧ Consistent [low, surface]

instance (low surface : List String) (trigger target : String) :
    Decidable (HarmonyProfile low surface trigger target) := by
  unfold HarmonyProfile; infer_instance

/-- The fronted clause with an auxiliary instantiates the schema: verb and particle are spelled
out together in vP, and the surface clause linearizes consistently. -/
theorem guebie_profile :
    HarmonyProfile (ClauseConfig.mk true true).vPSpellOut
      (ClauseConfig.mk true true).surfaceOrder "V" "Part" := by
  decide

/-- The Wolof shapes: a bare noun and demonstrative, or a relative clause with the head noun
moved past the stative verb. -/
inductive WolofShape where
  | localDP
  | relClause
  deriving DecidableEq, Repr

/-- The head noun and the demonstrative are spelled out together at the DP phase in both
shapes. -/
def WolofShape.dpSpellOut : WolofShape → List String := λ _ => ["head", "dem"]

/-- The surface strings of the two shapes. -/
def WolofShape.surfaceOrder : WolofShape → List String
  | .localDP => ["head", "dem"]
  | .relClause => ["head", "rel", "stative", "dem"]

/-- Both Wolof shapes instantiate the schema, with the trigger rather than the target
moving. -/
theorem wolof_profile (sh : WolofShape) :
    HarmonyProfile sh.dpSpellOut sh.surfaceOrder "head" "dem" := by
  cases sh <;> decide

/-- In the Wolof rows the demonstrative bears the head noun's value, whether or not the stative
verb between them shares it. -/
theorem wolof_rows :
    ∀ x ∈ rowsIn "nucl1347", ∀ h ∈ x.parse? "headATR" atrs, ∀ d ∈ x.parse? "demATR" atrs,
      d = h := by
  decide +kernel

end SandeClemDabkowski2026
