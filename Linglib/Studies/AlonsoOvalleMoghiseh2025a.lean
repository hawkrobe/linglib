import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Linglib.Semantics.Exhaustification.DomainAlternatives
import Linglib.Semantics.Exhaustification.Finite
import Linglib.Data.Examples.AlonsoOvalleMoghiseh2025a

/-!
# Alonso-Ovalle & Moghiseh (2025): existential free choice items

Farsi *yek-i* DPs are existential free choice items: plain existentials in downward
entailing contexts, free choice under deontic modals and modal variation under epistemic
ones (§2), but, unlike *irgendein* or *vreun*, grammatical and non-modal when unembedded,
where they convey uniqueness (§2.4). In [chierchia-2013]'s framework the DP introduces the
scalar alternative *at least two* and the pre-exhaustified domain alternatives
(`preExhaustified`, computed by innocent exclusion as in (56f)). Under a modal, negating the
domain alternatives gives free choice (`deontic_tolerant`, the general
`freeChoice_of_proper`), but negating the scalar alternative too is too strong
under ◇ and too weak under □ (`deontic_tolerant_box`); in a conditional antecedent
exhaustification is vacuous (`conditional_vacuous`). Unembedded, the contradiction-tolerant
operator yields ⊥ (`root_tolerant`, (92)); modal insertion (85)–(87) rescues *irgendein*
(`modal_insertion`), while *yek-i* prunes the domain alternatives, and partial scalar
exhaustification gives uniqueness (`root_scalar`) where partial domain exhaustification
returns the scalar alternative itself, which the Economy Principle (94) blocks
(`root_domain`). Fox's contradiction-free operator does not deliver (103): the paper's (101)
omits the maximal exclusion `{¬(b₁∧¬b₂), ¬(b₂∧¬b₁)}`, so no alternative is innocently
excludable and exhaustification is vacuous (`root_innocent`).

The embedded uniqueness of §5 needs split exhaustification, scalar below the modal and domain
above it (113): `split_diamond` and `split_box` derive (119)–(120), leaving ◇(b₁∧b₂) open,
while the single-operator LFs (143)–(146) are too weak or too strong (`single_below`,
`single_above`, `two_innocent`). Below *if*, scalar exhaustification weakens the sentence
(`conditional_weakening`), so Maximize Strength (132) prunes it. The scenario verdicts of
§§2–5 are checked in `rows_agree` on five-book models, and Table 2's typology in
`table2_rows`.

## References

* [alonso-ovalle-moghiseh-2025a]
* [chierchia-2013]
* [kratzer-shimoyama-2002]
* [alonso-ovalle-menendez-benito-2010]
* [falaus-2014]
* [fox-2007]
* [bar-lev-fox-2020]
* [aloni-port-2015]
-/

namespace AlonsoOvalleMoghiseh2025a

open Exhaustification ModalLogic Data.Examples Finset

/-! ### The two-book model (§3) -/

/-- A world records which of the two books Forood bought. -/
abbrev Buy := Finset (Fin 2)

/-- Book `i` is bought at `v`. -/
def buys (v : Buy) (i : Fin 2) : Prop := i ∈ v

instance (v : Buy) : DecidablePred (buys v) := fun i => inferInstanceAs (Decidable (i ∈ v))

/-- The proposition denoted by a decidable predicate on worlds. -/
abbrev prop {W : Type*} [Fintype W] (p : W → Prop) [DecidablePred p] : Finset W :=
  univ.filter p

/-- The assertion (56c): Forood bought a book. -/
def assertion : Finset Buy := prop (claim buys univ)

/-- The scalar alternative (54): Forood bought at least two books. -/
def scalar : Finset Buy := prop (2 ≤ ·.card)

/-- Exactly one book is bought. -/
def exactlyOne : Finset Buy := prop (·.card = 1)

/-- The domain alternatives (55): the claim restricted to each proper subdomain. -/
def domainAlts : Finset (Finset Buy) :=
  (subdomainAlternatives .proper univ).image fun S => prop (claim buys S)

/-- The pre-exhaustified alternatives (56f): each alternative strengthened by innocent
exclusion of the others. -/
def preExhaustified {W : Type*} [Fintype W] [DecidableEq W] (ALT : Finset (Finset W)) :
    Finset (Finset W) :=
  ALT.image (innocent.exh ALT)

/-- (56f): the pre-exhaustified domain alternatives are *only b₁* and *only b₂*. -/
theorem preExhaustified_domainAlts :
    preExhaustified domainAlts = {prop (· = {0}), prop (· = {1})} := by decide

/-! ### Modal contexts (§3, §5) -/

/-- A nonempty modal base: the permitted (or epistemically possible) buy-worlds. -/
abbrev Base := {A : Finset Buy // A.Nonempty}

instance : Fintype Base := Subtype.fintype fun A : Finset Buy => A.Nonempty
instance : DecidableEq Base := Subtype.instDecidableEq

/-- A modal world pairs a modal base with the actual buy-world; accessibility keeps the base
and moves to one of its worlds, so the frame is serial. -/
abbrev Modal := Base × Buy

instance : DecidableEq Modal := instDecidableEqProd
instance : Fintype Modal := instFintypeProd Base Buy

/-- Accessibility: an accessible world has the same modal base and lies in it. -/
def acc (m m' : Modal) : Prop := m'.1 = m.1 ∧ m'.2 ∈ m.1.1

instance : DecidableRel acc := fun m m' => inferInstanceAs (Decidable (m'.1 = m.1 ∧ m'.2 ∈ m.1.1))

/-- The modal world with base `A` and actual buy-world `v`. -/
def world (A : Finset Buy) (v : Buy) (h : A.Nonempty := by decide) : Modal := (⟨A, h⟩, v)

/-- Book `i` is bought at the modal world `m`. -/
def buysM (m : Modal) (i : Fin 2) : Prop := i ∈ m.2

instance (m : Modal) : DecidablePred (buysM m) := fun i => inferInstanceAs (Decidable (i ∈ m.2))

/-- A proposition about the buy-world, evaluated at a modal world. -/
def at' (p : Finset Buy) : Finset Modal := prop (·.2 ∈ p)

/-- ◇ as an operation on propositions. -/
def dia (p : Finset Modal) : Finset Modal := prop (◇[acc] (· ∈ p))

/-- □ as an operation on propositions. -/
def box' (p : Finset Modal) : Finset Modal := prop (□[acc] (· ∈ p))

/-- The alternatives of a modalized clause: the modal applied pointwise (fn. 15). -/
def lift (M : Finset Modal → Finset Modal) (ALT : Finset (Finset Buy)) :
    Finset (Finset Modal) :=
  ALT.image (M ∘ at')

/-- Free choice at a modal world: each book is permitted. -/
def fc (m : Modal) : Prop := FreeChoice acc m univ buysM

instance : DecidablePred fc := fun m => inferInstanceAs (Decidable (FreeChoice acc m univ buysM))

/-- (61): exhaustifying ◇(b₁∨b₂) over all alternatives at once gives free choice together
with the unattested ¬◇(b₁∧b₂). -/
theorem deontic_tolerant :
    tolerant.exh ({dia (at' scalar)} ∪ preExhaustified (lift dia domainAlts))
        (dia (at' assertion)) = prop fc \ dia (at' scalar) := by decide +kernel

/-- (67)–(68): under □ the same exhaustification is too weak — it holds where Forood may buy
more than one book. -/
theorem deontic_tolerant_box :
    world {{0}, {1}, {0, 1}} {0} ∈
      tolerant.exh ({box' (at' scalar)} ∪ preExhaustified (lift box' domainAlts))
        (box' (at' assertion)) := by decide +kernel

/-- (85)–(87): modal insertion rescues an unembedded *irgendein* — the result is
contingent and conveys ignorance about each book. -/
theorem modal_insertion :
    let φ := tolerant.exh ({box' (at' scalar)} ∪ preExhaustified (lift box' domainAlts))
      (box' (at' assertion))
    φ.Nonempty ∧ φ ⊆ dia (prop (buysM · 0)) ∩ dia (prop (buysM · 1)) ∩
      dia (prop (¬ buysM · 0)) ∩ dia (prop (¬ buysM · 1)) := by decide +kernel

/-! ### Unembedded *yek-i* DPs (§4) -/

/-- (92): unembedded, the contradiction-tolerant operator yields ⊥. -/
theorem root_tolerant :
    tolerant.exh ({scalar} ∪ preExhaustified domainAlts) assertion = ∅ := by decide

/-- (93a): partial scalar exhaustification gives uniqueness. -/
theorem root_scalar : innocent.exh {scalar} assertion = exactlyOne := by decide

/-- (93b)–(94): partial domain exhaustification returns the scalar alternative itself, so the
Exhaustification Economy Principle blocks it. -/
theorem root_domain : innocent.exh (preExhaustified domainAlts) assertion = scalar := by decide

/-- (101)–(103) do not go through: `{¬(b₁∧¬b₂), ¬(b₂∧¬b₁)}` is a third maximal consistent
exclusion, so no alternative is innocently excludable and the contradiction-free operator
is vacuous rather than delivering uniqueness. -/
theorem root_innocent :
    innocent.exh ({scalar} ∪ preExhaustified domainAlts) assertion = assertion := by decide

/-! ### Split exhaustification (§5) -/

/-- (119): scalar exhaustification below ◇ and domain exhaustification above it give
free choice with embedded uniqueness, compatible with ◇(b₁∧b₂). -/
theorem split_diamond :
    innocent.exh (preExhaustified (lift dia domainAlts)) (dia (at' exactlyOne)) =
      prop fc ∩ dia (at' exactlyOne) ∧
    world {{0}, {1}, {0, 1}} {0} ∈
      innocent.exh (preExhaustified (lift dia domainAlts)) (dia (at' exactlyOne)) := by
  decide +kernel

/-- (120): under □, every permitted world has exactly one book bought and each book is
permitted. -/
theorem split_box :
    innocent.exh (preExhaustified (lift box' domainAlts)) (box' (at' exactlyOne)) =
      prop fc ∩ box' (at' exactlyOne) := by decide +kernel

/-- (143): a single contradiction-free operator below ◇ is vacuous (`root_innocent`), so the
result is ◇(b₁∨b₂) — too weak for free choice. -/
theorem single_below :
    world {{0}} {0} ∈ dia (at' (innocent.exh ({scalar} ∪ preExhaustified domainAlts) assertion)) ∧
      ¬ fc (world {{0}} {0}) := by decide +kernel

/-- (146): a single contradiction-free operator above ◇ negates the scalar alternative,
forbidding ◇(b₁∧b₂). -/
theorem single_above :
    innocent.exh ({dia (at' scalar)} ∪ preExhaustified (lift dia domainAlts))
        (dia (at' assertion)) = prop fc \ dia (at' scalar) := by decide +kernel

/-- (144)–(145): two contradiction-free operators, below and above ◇, also forbid
◇(b₁∧b₂). -/
theorem two_innocent :
    innocent.exh ({dia (at' scalar)} ∪ preExhaustified (lift dia domainAlts))
        (dia (at' exactlyOne)) = (prop fc ∩ dia (at' exactlyOne)) \ dia (at' scalar) := by decide +kernel

/-! ### Downward entailing contexts (§3, §5) -/

/-- A world of the conditional (77): the books read and whether Forood gets a gift. -/
abbrev Cond := Buy × Bool

/-- *If Forood reads a book, he gets a gift* (78b). -/
def conditional : Finset Cond := prop fun c => claim buys univ c.1 → c.2 = true

/-- The conditional with scalar exhaustification in its antecedent (130e). -/
def conditionalUnique : Finset Cond := prop fun c => c.1.card = 1 → c.2 = true

/-- The domain alternatives of the conditional (78d). -/
def condAlts : Finset (Finset Cond) :=
  (subdomainAlternatives .proper (univ : Finset (Fin 2))).image fun S =>
    prop fun c => claim buys S c.1 → c.2 = true

/-- (78)–(80): the scalar alternative is entailed and the domain alternatives are vacuous,
so the plain existential reading survives; likewise for (135). -/
theorem conditional_vacuous :
    tolerant.exh {prop fun c : Cond => 2 ≤ c.1.card → c.2 = true} conditional = conditional ∧
      innocent.exh (preExhaustified condAlts) conditional = conditional ∧
      innocent.exh (preExhaustified condAlts) conditionalUnique = conditionalUnique := by
  decide

/-- (131): scalar exhaustification inside the antecedent weakens the conditional, which
Maximize Strength (132) forbids. -/
theorem conditional_weakening : conditional ⊂ conditionalUnique := by decide

/-! ### The paper's verdicts -/

/-- Five books; a scenario fixes the permitted or epistemically possible buy-worlds. -/
abbrev Buy₅ := Finset (Fin 5)

def buys₅ (v : Buy₅) (i : Fin 5) : Prop := i ∈ v

instance (v : Buy₅) : DecidablePred (buys₅ v) := fun i => inferInstanceAs (Decidable (i ∈ v))

/-- Accessibility from any world to the scenario's possibilities. -/
def scenarioAcc (A : Finset Buy₅) : Buy₅ → Buy₅ → Prop := fun _ v => v ∈ A

instance (A : Finset Buy₅) : DecidableRel (scenarioAcc A) :=
  fun _ v => inferInstanceAs (Decidable (v ∈ A))

/-- The possibilities a row's `scenario` feature names. -/
def scenario : String → Option (Finset Buy₅)
  | "permitted24" | "required28" | "known34" => some {{0}, {1}, {2}}
  | "known31" => some {∅, {0}, {1}, {2}}
  | "anyNumber104" => some (univ.filter (·.Nonempty))
  | "twoBooks108" => some (univ.filter (·.card = 2))
  | _ => none

/-- The verdict of an item under a modal over the possibilities `A`: a plain existential
needs the claim under the modal, *irgendein* free choice, *algún* modal variation, and
*yek-i* free choice or modal variation by flavor together with embedded uniqueness. -/
def verdict (A : Finset Buy₅) : String → String → Option Bool
  | "yek", "deontic possibility" => some (decide (◇[scenarioAcc A] (claim buys₅ univ) ∅))
  | "yek", "deontic necessity" => some (decide (□[scenarioAcc A] (claim buys₅ univ) ∅))
  | "irgendein", _ => some (decide (FreeChoice (scenarioAcc A) ∅ univ buys₅))
  | "algún", _ => some (decide (ModalVariation (scenarioAcc A) ∅ univ buys₅))
  | "yek-i", "deontic possibility" =>
    some (decide (FreeChoice (scenarioAcc A) ∅ univ buys₅ ∧ ◇[scenarioAcc A] (·.card = 1) ∅))
  | "yek-i", "deontic necessity" =>
    some (decide (FreeChoice (scenarioAcc A) ∅ univ buys₅ ∧ □[scenarioAcc A] (·.card = 1) ∅))
  | "yek-i", "epistemic possibility" =>
    some (decide (ModalVariation (scenarioAcc A) ∅ univ buys₅ ∧ ◇[scenarioAcc A] (·.card = 1) ∅))
  | "yek-i", "epistemic necessity" =>
    some (decide (ModalVariation (scenarioAcc A) ∅ univ buys₅ ∧ □[scenarioAcc A] (·.card = 1) ∅))
  | _, _ => none

/-- A row's predicted verdict from its `scenario`, `item`, and `modal` features. -/
def predicted (row : LinguisticExample) : Option Bool :=
  match row.feature? "scenario", row.feature? "item", row.feature? "modal" with
  | some s, some i, some m => scenario s >>= fun A => verdict A i m
  | _, _, _ => none

/-- Every scenario row carries the predicted verdict. -/
theorem rows_agree :
    ∀ row ∈ Examples.all, ∀ b, predicted row = some b →
      row.feature? "verdict" = some (if b then "true" else "false") := by decide +kernel

example : (Examples.all.filter fun row => (predicted row).isSome).length = 10 := by
  decide +kernel

/-- Table 2: an unembedded EFCI is ungrammatical exactly when it allows neither modal
insertion nor partial exhaustification. -/
theorem table2_rows :
    ∀ row ∈ Examples.all, (row.feature? "modalInsertion").isSome →
      (row.feature? "partialExhaustification").isSome →
      (row.judgment = .ungrammatical ↔
        row.feature? "modalInsertion" = some "no" ∧
          row.feature? "partialExhaustification" = some "no") := by decide +kernel

end AlonsoOvalleMoghiseh2025a
