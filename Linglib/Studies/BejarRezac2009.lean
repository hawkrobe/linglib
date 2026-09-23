module

public import Linglib.Syntax.Minimalist.Agree.Cyclic
public import Linglib.Fragments.Basque.Agreement
public import Linglib.Fragments.Georgian.Agreement
public import Linglib.Data.Examples.BejarRezac2009

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

* `controller_rows`, `context_rows`: the controller of the core slot and the direct or inverse
  context the paper reports for each example are those of the language's probe.
* `basque_not_hierarchy`: no ranking of the persons picks the controllers of (2).
* `basque_prefix_rows`: the auxiliaries of (2) begin with the Fragment's absolutive prefix for
  the person cyclic Agree values the probe with.
* `georgian_prefix_rows`: the 1st person singular of (18) is spelled by the Fragment's Set B
  when the IA values the probe and by its Set A when the EA does.
* `basque_hasPersonPrefix_iff_always_inverse`, `georgian_hasObjectPrefix_iff_always_inverse`:
  the Fragment paradigms have a marker for an object iff cyclic Agree puts every
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

@[expose] public section

namespace BejarRezac2009

open Minimalist.CyclicAgree
open Agreement Data.Examples

/-- The three core person values the paper's paradigms range over. -/
def corePersons : List Person := [.first, .second, .third]

/-- The flat system of Swahili and Abkhaz ((7)), the probe `[u-3]` with no person-hierarchy
sensitivity. -/
def swahili : AgreementSystem := ⟨.standard, flatProbe⟩

/-- The partial system of Basque and Georgian ((8)), the probe `[u-3-2]` under the standard
geometry. -/
def basque : AgreementSystem := ⟨.standard, partialProbe⟩

/-- The full system of Nishnaabemwin and Mohawk ((9)), the probe `[u-3-1-2]` under the addressee
geometry, second person the most specified. -/
def nishnaabemwin : AgreementSystem := ⟨.addressee, fullProbeAddr⟩

/-- The full system of Mohawk and Kashmiri, the probe `[u-3-2-1]` under the standard geometry. -/
def kashmiri : AgreementSystem := ⟨.standard, fullProbeStd⟩

/-! ### The examples -/

/-- The person a feature of an example names. -/
def person? (e : LinguisticExample) (key : String) : Option Person :=
  e.parse? key [("1", .first), ("2", .second), ("3", .third)]

/-- The agreement system of an example's language. -/
def system? (e : LinguisticExample) : Option AgreementSystem :=
  [("basq1248", basque), ("nucl1302", basque), ("otta1242", nishnaabemwin),
    ("kash1277", kashmiri)].lookup e.language

/-- The person cyclic Agree gives the core slot in an example. -/
def value? (e : LinguisticExample) : Option Person := do
  (← system? e).value (← person? e "ea") (← person? e "ia")

/-- Whether cyclic Agree makes an example's context inverse. -/
def isInverse? (e : LinguisticExample) : Option Bool := do
  (← system? e).isInverse (← person? e "ea") (← person? e "ia")

/-- The Basque paradigm (2), where the core slot tracks the IA in (2a–c) and displaces to the EA
only when the 3rd-person IA leaves the [u2] residue (2d). -/
def basqueRows : List LinguisticExample :=
  [Examples.br2009_2a, Examples.br2009_2b, Examples.br2009_2c, Examples.br2009_2d]

/-- The examples the paper annotates with the controller of the core slot. They are the Basque
paradigm (2) and (3), the Nishnaabemwin paradigm (17) under the [u-3-1-2] probe of the addressee
geometry, and the Georgian pair (18). -/
def controllerRows : List LinguisticExample :=
  basqueRows ++ [Examples.br2009_3, Examples.br2009_17a, Examples.br2009_17b,
    Examples.br2009_17c, Examples.br2009_17d, Examples.br2009_18a, Examples.br2009_18b]

/-- The controller the paper reports for each example is the person cyclic Agree gives the
core slot. -/
theorem controller_rows : ∀ e ∈ controllerRows,
    (value? e).isSome ∧ value? e = person? e "controller" := by
  decide +kernel

/-- The direct and inverse contexts of (22) the paper reports for the Basque, Nishnaabemwin and
Kashmiri examples are those of cyclic Agree. -/
theorem context_rows : ∀ e ∈ Examples.all, ∀ c ∈ e.feature? "context",
    isInverse? e = some (c == "inverse") := by
  decide +kernel

/-! ### Basque: ergative displacement ((2)) -/

/-- No ranking of the persons picks the controllers of (2). The 2nd person wins over the 1st in
(2a) and the 1st over the 2nd in (2c), so a hierarchy under which the higher-ranked argument
controls would rank the two persons alike. -/
theorem basque_not_hierarchy (r : Person → ℕ) (hr : r .first ≠ r .second) :
    ¬ ∀ ea ia, basque.value ea ia = if r ia < r ea then ea else ia := by
  intro h
  have h12 := h .first .second
  have h21 := h .second .first
  rw [show basque.value .first .second = .second by decide] at h12
  rw [show basque.value .second .first = .first by decide] at h21
  split_ifs at h12 h21
  omega

/-- The first morph of an example's last word, a prefix. -/
def slotPrefix? (e : LinguisticExample) : Option Morphology.Morph :=
  e.surfaceTokens.getLast?.map fun w ↦ .pref (String.ofList (w.toList.takeWhile (· ≠ '-')))

/-- The auxiliaries of (2) begin with the Fragment's absolutive prefix for the person cyclic
Agree values the probe with, in some number: *z-* in (2a), and *n-* in (2b–d), where in (2d) it
cross-references the EA. -/
theorem basque_prefix_rows : ∀ e ∈ basqueRows, ∃ v ∈ value? e,
    ∃ n ∈ [Number.singular, .plural],
      (Basque.absolutive.realize (.pn v n)).bind (·.head?) = slotPrefix? e := by
  decide +kernel

/-- Basque's direct contexts (22b) are exactly a SAP EA over a 3rd-person IA, the only cells
where the [u-3-2] probe keeps a residue the EA can check. -/
theorem basque_direct_contexts :
    ∀ ea ∈ corePersons, ∀ ia ∈ corePersons,
      (isDirectContext .standard partialProbe ea ia = true ↔
        (ea = .first ∨ ea = .second) ∧ ia = .third) := by decide

/-- The absolutive slot of the Fragment has a prefix for a person and number iff cyclic Agree
puts every EA→IA combination with that object into an inverse context, since a SAP IA fully
checks [u-3-2] and leaves no residue for any EA. -/
theorem basque_hasPersonPrefix_iff_always_inverse : ∀ c ∈ Bundle.pnCells,
    (Basque.HasPersonPrefix c ↔ ∀ ea : Person, basque.isInverse ea c.person = true) := by decide

/-! ### Georgian: the same [u-3-2] system, plus second-cycle morphology -/

/-- The Fragment's Set B has a prefix for a direct object of a person and number iff cyclic
Agree puts every EA→IA combination with that object into an inverse context, exactly as in
Basque. -/
theorem georgian_hasObjectPrefix_iff_always_inverse : ∀ c ∈ Bundle.pnCells,
    (Georgian.HasObjectPrefix c ↔ ∀ ea : Person, basque.isInverse ea c.person = true) := by
  decide

/-- The set of affixes that spells the core probe, Set B when the IA values it on the first
cycle and Set A when the EA values it on the second. -/
def affixSet : Controller → Georgian.AffixSet
  | .ia => .B
  | .ea => .A

/-- The argument cyclic Agree makes the controller of the core slot in an example. -/
def controller? (e : LinguisticExample) : Option Controller := do
  (← system? e).controller (← person? e "ea") (← person? e "ia")

/-- Second-cycle morphology in (18). The 1st person singular is spelled by the Fragment's Set B
*m-* in (18a), where the IA values the probe, and by its Set A *v-* in (18b), where the EA
does. -/
theorem georgian_prefix_rows : ∀ e ∈ [Examples.br2009_18a, Examples.br2009_18b],
    ∃ v ∈ value? e, ∃ c ∈ controller? e,
      ((affixSet c).paradigm.realize (.pn v .singular)).bind (·.head?) = slotPrefix? e := by
  decide +kernel

/-- A 1st-person IA is spelled by first-cycle morphology whatever the EA (18a), since it values
the probe fully on cycle I. -/
theorem georgian_m_is_cycle_I :
    ∀ ea : Person, hasSecondCycleEffect .standard partialProbe ea .first = false := by
  decide

/-- 1sg *v-* is second-cycle morphology (18b), since with a 3rd-person IA the [u2] residue is
valued by the SAP EA on cycle II, the same person value spelled by the cycle that valued it. -/
theorem georgian_v_is_cycle_II :
    hasSecondCycleEffect .standard partialProbe .first .third = true ∧
    hasSecondCycleEffect .standard partialProbe .second .third = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### Nishnaabemwin: the fully articulated probe ((17), Tables 4–5) -/

/-- Nishnaabemwin's direct contexts (22b) are 2>1, 2>3 and 1>3, since the EA checks residue
exactly when it is more specified than the IA on the 2>1>3 geometry. -/
theorem nishnaabemwin_direct_contexts :
    ∀ ea ∈ corePersons, ∀ ia ∈ corePersons,
      (isDirectContext .addressee fullProbeAddr ea ia = true ↔
        (ea = .second ∧ ia ≠ .second) ∨ (ea = .first ∧ ia = .third)) := by
  decide

/-- A flat-probe language has no direct contexts at all (22a), since any IA fully checks [u-3],
so subject and object agreement never interact ((10), Swahili). -/
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

/-- Mohawk's added-probe cells (Table 7), where the extra agreement slot appears, 2>1, 3>1, 3>2
and 3>3. -/
def mohawkAddedProbe : Person × Person → Bool
  | (.second, .first) | (.third, .first)
  | (.third, .second) | (.third, .third) => true
  | _ => false

/-- Kashmiri's R-Case cells (Table 11), where the IA bears the dative-shaped structural Case,
2>1, 3>1, 3>2 and 3>3, and only there. -/
def kashmiriRCase : Person × Person → Bool
  | (.second, .first) | (.third, .first)
  | (.third, .second) | (.third, .third) => true
  | _ => false

/-- The two repairs are identically distributed (§4.1). Mohawk's extra agreement and Kashmiri's
special Case mark the same cells, one mechanism with two spell-outs. -/
theorem repairs_identically_distributed :
    ∀ c ∈ attestedCells, mohawkAddedProbe c = kashmiriRCase c := by decide

/-- The repair cells are exactly the inverse contexts of the [u-3-2-1] standard-geometry system,
so repair appears where the EA fails to Agree with the core probe. -/
theorem repair_iff_inverse :
    ∀ c ∈ attestedCells,
      kashmiriRCase c = isInverseContext .standard fullProbeStd c.1 c.2 := by
  decide

/-- The repair cells are exactly those where the EA is not person-licensed by the core probe,
the PLC connection (13), so repair is EA licensing. -/
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
