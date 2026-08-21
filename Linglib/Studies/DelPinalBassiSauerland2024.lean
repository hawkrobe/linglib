import Linglib.Semantics.Exhaustification.Presuppositional
import Linglib.Semantics.Presupposition.BeliefEmbedding
import Linglib.Studies.BarLevFox2020

/-!
# Del Pinal, Bassi & Sauerland (2024): free choice and presuppositional exhaustification

[delpinal-bassi-sauerland-2024] derive free choice with `pex^{IE+II}`
(`Exhaustification.Presuppositional.pexIEII`), which asserts its prejacent and
*presupposes* the negation of the innocently excludable alternatives together with
homogeneity over the innocently includable ones. On `◇(p ∨ q)` this is (14): the
presupposed `◇p ↔ ◇q` with the asserted disjunction entails `◇p ∧ ◇q` (`pex_fc`), and the
same structure gives double prohibition under negation (16) (`pex_double_prohibition`) and,
with the necessity alternatives relabelled, negative free choice (19a)–(20)
(`pex_negative_fc`, `pex_double_requirement`). The split is what flat `exh^{IE+II}`
lacks, and the paper's embedded puzzles turn on it. Under a negative factive (§3), the
factive presupposes the whole `pex` output, so free choice is presupposed
(`fc_presupposed_under_neg_factive`), while the assertion denies belief in the bare
prejacent, which denies belief in either disjunct (`pex_unaware_target`); a flat `exh`
complement yields only denial of belief in the exhaustified conjunction, which a believer
in free choice can satisfy (`exh_unaware_too_weak`). In a disjunction (§4) the homogeneity
presupposition of the second disjunct is filtered in its local context
([schlenker-2009]) and free choice follows there (`filtering_fc`), whereas flat `exh`
leaves nothing to project (`exh_filtering_trivial`). Under quantifiers (§5.1) universal
projection of the presupposition gives universal, universal-negative, and existential
free choice, (62), (63), (75) (`universal_fc`, `universal_negative_fc`, `existential_fc`),
and under *exactly one* (§5.2) the salient readings of (76)–(77) of
[gotzner-romoli-santorio-2020] (`exactly_one_fc`, `exactly_one_double_prohibition`).
The five-world model and alternative set are [bar-lev-fox-2020]'s.
-/

namespace DelPinalBassiSauerland2024

open Semantics.Presupposition (PartialProp)
open CommonGround (ContextSet)
open Exhaustification Exhaustification.Presuppositional BarLevFox2020 ModalLogic
open Semantics.Presupposition.Context (presupSatisfied localCtxSecondDisjunct)

/-! ### `pex^{IE+II}` on `◇(p ∨ q)` (§2) -/

/-- (14): `pex^{IE+II}[◇(p ∨ q)]` on the five-world model. -/
def pexFC : PartialProp FCWorld := pexIEII_full fcALT fcPrejacent

theorem permA_mem_II : IsInnocentlyIncludable fcALT fcPrejacent permA :=
  mem_II_of_cell_witness fcALT fcPrejacent (by simp [fcALT]) .separatelyAB separatelyAB_in_cell
    trivial

theorem permB_mem_II : IsInnocentlyIncludable fcALT fcPrejacent permB :=
  mem_II_of_cell_witness fcALT fcPrejacent (by simp [fcALT]) .separatelyAB separatelyAB_in_cell
    trivial

theorem permAorB_iff (w : FCWorld) : permAorB w ↔ permA w ∨ permB w := by
  cases w <;> simp [permAorB, permA, permB]

variable {w : FCWorld}

/-- (14): the presupposed homogeneity `◇p ↔ ◇q` with the asserted `◇(p ∨ q)` gives free
choice. -/
theorem pex_fc (h : pexFC.holds w) : permA w ∧ permB w := by
  have hiff : permA w ↔ permB w :=
    h.1.2 permA ⟨permA_mem_II, by simp [fcALT]⟩ permB ⟨permB_mem_II, by simp [fcALT]⟩
  rcases (permAorB_iff w).1 h.2 with hA | hB
  exacts [⟨hA, hiff.1 hA⟩, ⟨hiff.2 hB, hB⟩]

/-- (16): negation denies the prejacent and leaves the presupposition, so `¬pex[◇(p ∨ q)]`
is double prohibition. -/
theorem pex_double_prohibition (h : pexFC.neg.holds w) : ¬ permA w ∧ ¬ permB w :=
  ⟨fun hA => h.2 ((permAorB_iff w).2 (.inl hA)), fun hB => h.2 ((permAorB_iff w).2 (.inr hB))⟩

/-- `¬□T`, read on the five-world model: the alternatives to `¬□(T ∧ B)` — `¬□T`, `¬□B`,
`¬□(T ∨ B)` — have the same innocent-exclusion/inclusion structure as those to `◇(p ∨ q)`,
with `¬□T` in the place of `◇q` and `¬□B` in the place of `◇p`. -/
abbrev notReqT : Set FCWorld := permB

/-- `¬□B` on the five-world model. -/
abbrev notReqB : Set FCWorld := permA

/-- (19a): `pex^{IE+II}[¬□(T ∧ B)]` gives negative free choice. -/
theorem pex_negative_fc (h : pexFC.holds w) : notReqT w ∧ notReqB w := (pex_fc h).symm

/-- (20): `¬pex^{IE+II}[□(T ∧ B)]` gives double requirement. -/
theorem pex_double_requirement (h : pexFC.neg.holds w) : ¬ notReqT w ∧ ¬ notReqB w :=
  (pex_double_prohibition h).symm

/-! ### Free choice under negative factives (§3) -/

variable (believes : (FCWorld → Prop) → FCWorld → Prop)

/-- Under a negative factive the whole `pex` output is presupposed, so free choice is
presupposed, (21a). -/
theorem fc_presupposed_under_neg_factive
    (h : (PartialProp.negFactive pexFC believes).presup w) : permA w ∧ permB w :=
  pex_fc h

/-- The factive's assertion denies belief in the prejacent `◇(p ∨ q)`, hence belief in either
disjunct, (21b). -/
theorem pex_unaware_target (R : FCWorld → FCWorld → Prop)
    (h : (PartialProp.negFactive pexFC (box R)).assertion w) :
    ¬ box R permA w ∧ ¬ box R permB w :=
  ⟨fun hA => h (box_mono R (by intro v hv; exact (permAorB_iff v).2 (.inl hv)) w hA),
   fun hB => h (box_mono R (by intro v hv; exact (permAorB_iff v).2 (.inr hv)) w hB)⟩

/-- `exh^{IE+II}[◇(p ∨ q)]`, fully assertive. -/
def flatExhFC : Set FCWorld := exhIEII fcALT fcPrejacent

/-- With a flat `exh` complement the factive's assertion only denies belief in the
exhaustified conjunction, which an attitude holder who believes free choice but not
exclusivity satisfies (§3.1). -/
theorem exh_unaware_too_weak :
    ∃ R : FCWorld → FCWorld → Prop, (box R permA w ∧ box R permB w) ∧ ¬ box R flatExhFC w :=
  ⟨fun _ v => v = .both, ⟨fun _ hv => hv ▸ trivial, fun _ hv => hv ▸ trivial⟩,
   fun h => (h .both rfl).2.1 permAandB permAandB_is_ie trivial⟩

/-! ### Filtering free choice (§4) -/

/-- In `A or pex[◇(p ∨ q)]` the homogeneity presupposition is satisfied in the second
disjunct's local context `c ∧ ¬A`, and free choice follows there. -/
theorem filtering_fc (c : ContextSet FCWorld) (A : PartialProp FCWorld) (hc : w ∈ c)
    (hA : ¬ A.assertion w) (hf : presupSatisfied (localCtxSecondDisjunct c A) pexFC)
    (hassert : pexFC.assertion w) : permA w ∧ permB w :=
  pex_fc ⟨hf ⟨hc, hA⟩, hassert⟩

/-- A flat `exh` second disjunct has nothing to filter: its free-choice content is
assertive and stays inside the disjunct (§4.1). -/
theorem exh_filtering_trivial (c : ContextSet FCWorld) (A : PartialProp FCWorld) :
    presupSatisfied (localCtxSecondDisjunct c A) (PartialProp.ofProp flatExhFC) :=
  fun _ _ => trivial

/-! ### Free choice under quantifiers (§5) -/

variable {Student : Type*} (S : Student → Prop)

/-- (62): universal projection of homogeneity and the universal assertion give universal free
choice. -/
theorem universal_fc (permC permIC : Student → Prop)
    (hassert : ∀ x, S x → permC x ∨ permIC x) (hhomog : ∀ x, S x → (permC x ↔ permIC x)) :
    (∀ x, S x → permC x) ∧ ∀ x, S x → permIC x :=
  ⟨fun x hx => (hassert x hx).elim id (hhomog x hx).2,
   fun x hx => (hassert x hx).elim (hhomog x hx).1 id⟩

/-- (63): with a negated existential assertion, universal negative free choice. -/
theorem universal_negative_fc (reqA reqB : Student → Prop)
    (hassert : ¬ ∃ x, S x ∧ reqA x ∧ reqB x) (hhomog : ∀ x, S x → (reqA x ↔ reqB x)) :
    (¬ ∃ x, S x ∧ reqA x) ∧ ¬ ∃ x, S x ∧ reqB x :=
  ⟨fun ⟨x, hx, hA⟩ => hassert ⟨x, hx, hA, (hhomog x hx).1 hA⟩,
   fun ⟨x, hx, hB⟩ => hassert ⟨x, hx, (hhomog x hx).2 hB, hB⟩⟩

/-- (75): with an existential assertion, existential free choice. -/
theorem existential_fc (permC permIC : Student → Prop)
    (hassert : ∃ x, S x ∧ (permC x ∨ permIC x)) (hhomog : ∀ x, S x → (permC x ↔ permIC x)) :
    ∃ x, S x ∧ permC x ∧ permIC x :=
  let ⟨x, hx, h⟩ := hassert
  ⟨x, hx, h.elim (fun hC => ⟨hC, (hhomog x hx).1 hC⟩) fun hIC => ⟨(hhomog x hx).2 hIC, hIC⟩⟩

/-- (76a): under *exactly one*, the witness has free choice and every other student double
prohibition. -/
theorem exactly_one_fc (permL permC : Student → Prop) (x₀ : Student) (hx₀ : S x₀)
    (hpos : permL x₀ ∨ permC x₀) (hneg : ∀ x, S x → x ≠ x₀ → ¬ (permL x ∨ permC x))
    (hhomog : ∀ x, S x → (permL x ↔ permC x)) :
    (permL x₀ ∧ permC x₀) ∧ ∀ x, S x → x ≠ x₀ → ¬ permL x ∧ ¬ permC x :=
  ⟨hpos.elim (fun h => ⟨h, (hhomog x₀ hx₀).1 h⟩) fun h => ⟨(hhomog x₀ hx₀).2 h, h⟩,
   fun x hx hne => ⟨fun h => hneg x hx hne (.inl h), fun h => hneg x hx hne (.inr h)⟩⟩

/-- (77a): under *exactly one … can't*, the witness has double prohibition and every other
student free choice. -/
theorem exactly_one_double_prohibition (permL permC : Student → Prop) (x₀ : Student)
    (hneg : ¬ (permL x₀ ∨ permC x₀)) (hpos : ∀ x, S x → x ≠ x₀ → permL x ∨ permC x)
    (hhomog : ∀ x, S x → (permL x ↔ permC x)) :
    (¬ permL x₀ ∧ ¬ permC x₀) ∧ ∀ x, S x → x ≠ x₀ → permL x ∧ permC x :=
  ⟨⟨fun h => hneg (.inl h), fun h => hneg (.inr h)⟩,
   fun x hx hne => (hpos x hx hne).elim (fun h => ⟨h, (hhomog x hx).1 h⟩)
     fun h => ⟨(hhomog x hx).2 h, h⟩⟩

end DelPinalBassiSauerland2024
