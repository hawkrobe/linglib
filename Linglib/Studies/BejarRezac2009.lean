import Linglib.Syntax.Minimalist.Agree.Cyclic
import Linglib.Fragments.Basque.Agreement
import Linglib.Fragments.Georgian.Agreement
import Linglib.Data.Examples.BejarRezac2009

/-!
# Béjar & Rezac (2009): Cyclic Agree

Person-hierarchy-driven agreement displacement falls out of Agree over
articulated π-probes in a cyclic syntax: the probe on v meets the IA
first, checks whatever segments it can, and any active residue meets the
EA on the next projection. The probe's articulation — flat [u-3], partial
[u-3-2], full [u-3-1-2] ((7)–(9)) — fixes a language's hierarchy
sensitivity, and the derivations split into direct contexts, where the EA
checks residue, and inverse contexts, where the EA never Agrees (22).
Inverse contexts violate the Person-Licensing Condition
(`Minimalist.CyclicAgree.plc_violation_iff_inverse`) and are repaired by
an added probe (Mohawk, Nishnaabemwin, Basque) or R-Case on the IA
(Kashmiri) — one mechanism, property P (23), with parametric spell-out.

## Main statements

* `basque_indexed_iff_always_inverse`, `georgian_indexed_iff_always_inverse`:
  the Fragment paradigms index an object iff cyclic Agree puts every
  EA→IA combination into an inverse context.
* `nishnaabemwin_direct_contexts`, `basque_direct_contexts`,
  `swahili_all_inverse`: the (22) direct/inverse classifications, derived
  from the three probe articulations.
* `repairs_identically_distributed`, `repair_iff_inverse`: Mohawk's
  added-probe cells (Table 7) and Kashmiri's R-Case cells (Table 11) are
  the same cells, and they are exactly the inverse contexts of the
  [u-3-2-1] system — disparately realized, identically distributed (§4).

## References

* [bejar-rezac-2009]: Cyclic Agree. *Linguistic Inquiry* 40.
* [bejar-rezac-2003]: Person licensing and the derivation of PCC effects.
* [bejar-2003]: Phi-syntax: A theory of agreement.
* [harley-ritter-2002]: Person and number in pronouns: A feature-geometric
  analysis.
-/

namespace BejarRezac2009

open Minimalist.CyclicAgree
open Agreement

/-- Person level of a φ-cell (`Agreement.Cell`); Basque and Georgian share
the same map. -/
def toLevel (c : Cell) : Person :=
  match c.person with
  | some .first => .first
  | some .second => .second
  | _ => .third

/-- The three core person values the paper's paradigms range over. -/
def corePersons : List Person := [.first, .second, .third]

/-! ### Basque: ergative displacement ((2)) -/

/-- The (2) paradigm: the core slot tracks the IA in (2a–c) and displaces
to the EA only when the 3rd-person IA leaves the [u2] residue (2d) — no
ranking of person values covers both (2a) 1>2 = 2 and (2c) 2>1 = 1. -/
theorem basque_displacement_paradigm :
    basque.value .first .second = .second ∧   -- (2a) 1>2 = 2
    basque.value .third .first = .first ∧     -- (2b) 3>1 = 1
    basque.value .second .first = .first ∧    -- (2c) 2>1 = 1
    basque.value .first .third = .first := by -- (2d) 1>3 = 1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Basque's direct contexts (22b): exactly a SAP EA over a 3rd-person IA
— the only cells where the [u-3-2] probe keeps a residue the EA can
check. -/
theorem basque_direct_contexts :
    ∀ ea ∈ corePersons, ∀ ia ∈ corePersons,
      (isDirectContext .standard partialProbe ea ia = true ↔
        (ea = .first ∨ ea = .second) ∧ ia = .third) := by decide

/-- Differential object indexing: the Fragment's `pIsIndexed` (SAP objects
indexed, textbook Basque) holds of a φ-cell iff cyclic Agree puts *every*
EA→IA combination with that object into an inverse context — a SAP IA
fully checks [u-3-2], leaving no residue for any EA. -/
theorem basque_indexed_iff_always_inverse : ∀ c ∈ Cell.pnCells,
    (Basque.Agreement.pIsIndexed c = true ↔
      ∀ ea : Person, basque.isInverse ea (toLevel c) = true) := by decide

/-! ### Georgian: the same [u-3-2] system, plus second-cycle morphology -/

/-- Georgian's paradigm-derived object indexing (`objectAgr` has an
exponent for a cell or not) matches the inverse classification of the
shared standard-geometry [u-3-2] system, exactly as in Basque. -/
theorem georgian_indexed_iff_always_inverse : ∀ c ∈ Cell.pnCells,
    (Georgian.Agreement.isIndexed c = true ↔
      ∀ ea ∈ corePersons,
        isInverseContext .standard partialProbe ea (toLevel c) = true) := by
  decide

/-- 1sg *m-* is first-cycle morphology (18a): whenever the IA is 1st
person the probe is fully valued on cycle I, whatever the EA. -/
theorem georgian_m_is_cycle_I :
    Georgian.Agreement.objectAgr.realize (.pn .first .Sing) = some "m-" ∧
    ∀ ea ∈ corePersons,
      hasSecondCycleEffect .standard partialProbe ea .first = false := by
  refine ⟨rfl, ?_⟩; decide

/-- 1sg *v-* is second-cycle morphology (18b): with a 3rd-person IA the
[u2] residue is valued by the SAP EA on cycle II — the same person value,
spelled by the cycle that valued it. -/
theorem georgian_v_is_cycle_II :
    hasSecondCycleEffect .standard partialProbe .first .third = true ∧
    hasSecondCycleEffect .standard partialProbe .second .third = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### Nishnaabemwin: the fully articulated probe ((17), Tables 4–5) -/

/-- The (17) core-slot paradigm under the [u-3-1-2] probe (2nd person most
specified, addressee geometry): the 2nd-person IA wins in (17a), the
2nd-person EA checks the [u2] residue over a 1st-person IA in (17b), and
3rd-person EAs never displace ((17c–d)). -/
theorem nishnaabemwin_controllers :
    nishnaabemwin.value .first .second = .second ∧   -- (17a) 1>2 = 2
    nishnaabemwin.value .second .first = .second ∧   -- (17b) 2>1 = 2
    nishnaabemwin.value .third .first = .first ∧     -- (17c) 3>1 = 1
    nishnaabemwin.value .third .second = .second := by -- (17d) 3>2 = 2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Nishnaabemwin's direct contexts (22b): 2>1, 2>3, and 1>3 — the EA
checks residue exactly when it is more specified than the IA on the
2>1>3 geometry. -/
theorem nishnaabemwin_direct_contexts :
    ∀ ea ∈ corePersons, ∀ ia ∈ corePersons,
      (isDirectContext .addressee fullProbeAddr ea ia = true ↔
        (ea = .second ∧ ia ≠ .second) ∨ (ea = .first ∧ ia = .third)) := by
  decide

/-- A flat-probe language has no direct contexts at all (22a): any IA
fully checks [u-3], so subject and object agreement never interact
((10), Swahili). -/
theorem swahili_all_inverse :
    ∀ ea ∈ corePersons, ∀ ia ∈ corePersons,
      swahili.isInverse ea ia = true := by decide

/-! ### Repairs: added probe and R-Case (§4, Tables 7 and 11)

Inverse contexts leave the EA without π-Agree, violating the PLC
(`plc_violation_iff_inverse`); property P (23) adds a probe on vII, spelled
out as extra EA agreement (Mohawk, Bizkaian Basque INV, the Nishnaabemwin
theme suffix) or, with the alternative spell-out choice (24), as the
special R-Case on the IA (Kashmiri). -/

/-- The seven attested transitive cells of the paper's [u-3-2-1] paradigms
(1>1 and 2>2 are systematic gaps; 3>3 is attested with differently
specified 3rd persons). -/
def attestedCells : List (Person × Person) :=
  [(.first, .second), (.first, .third), (.second, .first), (.second, .third),
   (.third, .first), (.third, .second), (.third, .third)]

/-- Mohawk's added-probe cells (Table 7): the extra agreement slot appears
in 2>1, 3>1, 3>2, and 3>3. -/
def mohawkAddedProbe : Person × Person → Bool
  | (.second, .first) | (.third, .first)
  | (.third, .second) | (.third, .third) => true
  | _ => false

/-- Kashmiri's R-Case cells (Table 11): the IA bears the dative-shaped
structural Case in 2>1, 3>1, 3>2, and 3>3, and only there. -/
def kashmiriRCase : Person × Person → Bool
  | (.second, .first) | (.third, .first)
  | (.third, .second) | (.third, .third) => true
  | _ => false

/-- The two repairs are identically distributed (§4.1): Mohawk's extra
agreement and Kashmiri's special Case mark the same cells — one mechanism,
two spell-outs. -/
theorem repairs_identically_distributed :
    ∀ c ∈ attestedCells, mohawkAddedProbe c = kashmiriRCase c := by decide

/-- The repair cells are exactly the inverse contexts of the [u-3-2-1]
standard-geometry system: repair appears where the EA fails to Agree with
the core probe. -/
theorem repair_iff_inverse :
    ∀ c ∈ attestedCells,
      kashmiriRCase c = isInverseContext .standard fullProbeStd c.1 c.2 := by
  decide

/-- The repair cells are exactly those where the EA is not person-licensed
by the core probe — the PLC connection (13): repair is EA licensing. -/
theorem repair_marks_unlicensed_ea :
    ∀ c ∈ attestedCells,
      (kashmiriRCase c = true ↔
        eaIsLicensed .standard fullProbeStd c.1 c.2 = false) := by decide

/-- Basque's added probe appears in more cells than Mohawk's because its
probe is shallower: 1>2 is inverse for [u-3-2] (Bizkaian INV *iñdd*,
Table 9) but direct for [u-3-2-1] (Mohawk's portmanteau *ku*, Table 7). -/
theorem shallower_probe_more_inverse :
    isInverseContext .standard partialProbe .first .second = true ∧
    isDirectContext .standard fullProbeStd .first .second = true := by
  refine ⟨?_, ?_⟩ <;> decide

end BejarRezac2009
