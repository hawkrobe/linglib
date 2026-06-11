import Linglib.Syntax.ConstructionGrammar.Basic
import Mathlib.Tactic.NormNum
import Linglib.Studies.FillmoreKayOConnor1988
import Linglib.Studies.GoldbergShirtz2025
import Linglib.Studies.KayFillmore1999

/-!
# Slot/Filler Verification

[dunn-2025] [kay-fillmore-1999] [goldberg-shirtz-2025]

[dunn-2025]'s variationist CxG treats abstraction as continuous — the
proportion of open slots in a construction's typed form
(`abstractionLevel`). This file computes the measure for constructions
across the constructicon (ditransitive, must-V, *let alone*, WXDY) and
verifies the structural properties of WXDY's flat slot projection:
coreference grouping (X–Y coinstantiation via shared `refIdx`) and
per-slot syntactic constraints ([loc -], [neg -], [ref ∅]).
-/

namespace Dunn2025

open ConstructionGrammar

/-! ### Abstraction levels

The continuous measure on the typed forms of constructions defined in
their owning study files. -/

/-- Ditransitive: 4/4 open slots → abstraction level 1. -/
theorem ditransitive_abstraction :
    abstractionLevel ditransitive.slots = 1 := by
  norm_num [abstractionLevel, ArgStructureConstruction.slots, ditransitive,
    List.filter, SlotFiller.isOpen]

/-- must-V: 2/3 open slots → abstraction level 2/3. -/
theorem mustVerb_abstraction :
    abstractionLevel (_root_.GoldbergShirtz2025.mustVerbConstruction).form
      = 2 / 3 := by
  norm_num [abstractionLevel, GoldbergShirtz2025.mustVerbConstruction,
    List.filter, SlotFiller.isOpen]

/-- *Let alone*: 2/4 open slots → abstraction level 1/2. -/
theorem letAlone_abstraction :
    abstractionLevel (_root_.FillmoreKayOConnor1988.letAloneConstruction).form
      = 1 / 2 := by
  norm_num [abstractionLevel, FillmoreKayOConnor1988.letAloneConstruction,
    List.filter, SlotFiller.isOpen]

/-- Veggie-wrap: a fully lexically specified compound ([goldberg-2003]:220). -/
def veggieWrapForm : TypedForm String :=
  [ { filler := .fixed "veggie" }
  , { filler := .fixed "wrap", isHead := true } ]

/-- Veggie-wrap: 0/2 open slots → abstraction level 0. -/
theorem veggieWrap_abstraction :
    abstractionLevel veggieWrapForm = 0 := by
  norm_num [abstractionLevel, veggieWrapForm, List.filter, SlotFiller.isOpen]

/-- Veggie-wrap: derived `.lexicallySpecified` (all fixed). -/
theorem veggieWrap_is_lexicallySpecified :
    derivedSpecificity veggieWrapForm = .lexicallySpecified := by decide

/-! ### WXDY ([kay-fillmore-1999], Figure 12)

`wxdyConstruction.form` (in `Studies/KayFillmore1999.lean`) is the flat
projection of the paper's hierarchical AVM: valence sets, grammatical
functions, coreference indices (#1, #2), and feature constraints
([loc -], [neg -], [ref ∅]), with the nesting lost.

**Coinstantiation** (Figure 13, §4.2) is a general construction
expressing subject control: the matrix subject and the complement's
subject share a coreference index. WXDY's X–Y coindexation is an
instance of this pattern. -/

/-- WXDY's typed form, from its owning study file. -/
private def wxdyForm : TypedForm String :=
  KayFillmore1999.wxdyConstruction.form

/-- Coinstantiation construction ([kay-fillmore-1999], Figure 13, §4.2).

"She tried to leave": the subject of *try* (#1) = the understood
subject of *leave* (#1). This is the mechanism underlying WXDY's X–Y
coindexation. -/
def coinstantiationForm : TypedForm String :=
  [ { filler := .open_ .NOUN, role := some "subject", gf := some .subj
    , refIdx := some 1 }
  , { filler := .open_ .VERB, role := some "predicate", isHead := true }
  , { filler := .open_ .VERB, role := some "complement", gf := some .comp
    , refIdx := some 1 } ]

/-- WXDY: 2/5 open slots → abstraction level 2/5. -/
theorem wxdy_abstraction :
    abstractionLevel wxdyForm = 2 / 5 := by
  norm_num [abstractionLevel, wxdyForm,
    KayFillmore1999.wxdyConstruction,
    List.filter, SlotFiller.isOpen]

/-- WXDY is partiallyOpen: mix of open, headed, and fixed slots. -/
theorem wxdy_specificity :
    derivedSpecificity wxdyForm = .partiallyOpen := by decide

/-- Coinstantiation is fully abstract (all slots open). -/
theorem coinstantiation_specificity :
    derivedSpecificity coinstantiationForm = .fullyAbstract := by decide

/-! ### Coreference constraints -/

/-- WXDY has exactly one coreference group (the X–Y coinstantiation). -/
theorem wxdy_coreference_count :
    refGroupCount wxdyForm = 1 := by decide

/-- X (first slot) and Y (last slot) share coreference index 2:
X is the understood subject of Y. -/
theorem wxdy_coinstantiation :
    wxdyForm.head?.bind (·.refIdx) = some 2 ∧
    wxdyForm.getLast?.bind (·.refIdx) = some 2 := by decide

/-- Coinstantiation has exactly one coreference group. -/
theorem coinstantiation_coreference :
    refGroupCount coinstantiationForm = 1 := by decide

/-! ### Syntactic constraints -/

/-- WXDY-what is left-isolated ([loc -]) and nonreferential ([ref ∅]).
These two constraints together explain why WXDY-what cannot take
*else* modification and is not a true interrogative pronoun. -/
theorem wxdy_what_constraints :
    hasConstraint wxdyForm .locMinus = true ∧
    hasConstraint wxdyForm .refEmpty = true := by decide

/-- WXDY-doing cannot be negated ([neg -]): "*What's X not doing Y?"
is ungrammatical on the incredulity reading. -/
theorem wxdy_doing_negMinus :
    hasConstraint wxdyForm .negMinus = true := by decide

/-- Neither the ditransitive nor *let alone* bear any slot constraints —
the enriched constraint machinery is specific to constructions like
WXDY that have fine-grained syntactic restrictions. -/
theorem basic_forms_no_constraints :
    hasConstraint ditransitive.slots .locMinus = false ∧
    hasConstraint ditransitive.slots .negMinus = false ∧
    hasConstraint (_root_.FillmoreKayOConnor1988.letAloneConstruction).form
      .locMinus = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Dunn2025
