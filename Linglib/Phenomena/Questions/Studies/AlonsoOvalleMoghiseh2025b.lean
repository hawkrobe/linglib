import Linglib.Core.Logic.Quantification.Generators

/-!
# Alonso-Ovalle & Moghiseh (2025): Number Marking in *What* Interrogatives
@cite{alonso-ovalle-moghiseh-2025b}

Luis Alonso-Ovalle and Esmail Moghiseh. Number marking in interrogative
phrases: *What* interrogatives in Farsi. In: *Proceedings of Sinn und
Bedeutung 29*, pp. 1–16.

## Overview

Farsi *what* interrogatives display a distinctive number-marking pattern:
singular *what* CIs (`che ketab-i`, "what book") allow both singular and
plural answers, unlike English where singular CIs restrict to singular
answers only. This divergence is derived from four assumptions:

1. Interrogatives range over generalized quantifiers — conjunctions (⊓)
   and disjunctions (⊔) built from non-empty subsets of an entity domain
   (@cite{xiang-2016}, @cite{elliott-nicolae-sauerland-2022}).
2. Singular marking on bare interrogatives is a morphological default
   with no semantic import (@cite{maldonado-2020}).
3. Singular marking on complex interrogatives has semantic import: SING
   restricts the domain to atoms (@cite{scontras-2022}).
4. Differential object marker *-ro* restricts the subset selection
   function to singletons, signaling specificity (@cite{karimi-2003}).

## Predictions

| Type | ±ro | Sg | Pl | Ex. |
|------|-----|----|----|-----|
| SBI  | −   | ✓  | ✓  | 20  |
| PBI  | −   | ✗  | ✓  | 21  |
| SCI  | −   | ✓  | ✓  | 23  |
| PCI  | −   | ✗  | ✓  | 25  |
| SBI  | +   | ✓  | ✓  | 26  |
| SCI  | +   | ✓  | ✗  | 27  |
| PCI  | +   | ✗  | ✓  | 28  |

## Connection to *yek-i* DPs

Farsi interrogative forms (`chi`, `che`) are homophonous with indefinites
(@cite{alonso-ovalle-moghiseh-2025}, §5). The interrogative and indefinite
share the same domain-building mechanism (⊓ ∪ ⊔ over GQs), but
interrogatives compose with ANS while indefinites compose with existential
closure. See `Fragments.Farsi.Determiners` and
`Phenomena.FreeChoice.FarsiYekI` for the indefinite paradigm.
-/

set_option autoImplicit false

namespace AlonsoOvalleMoghiseh2025b

open Core.Quantification (NPQ conjGQ disjGQ conjGQs disjGQs nonemptySubsets
  conjGQ_iff_forall disjGQ_iff_exists conjGQ_le_individual individual_le_disjGQ
  conjGQ_le_disjGQ' individual)

-- ============================================================================
-- § 1. Model
-- ============================================================================

/-- Entity domain: two atomic individuals and their mereological join.
    `t12 = t1 ⊕ t2` in the sense of @cite{link-1983}. -/
inductive Entity where | t1 | t2 | t12
  deriving DecidableEq, BEq, Repr

/-- Evaluation worlds: what did Roya buy? -/
inductive World where | w1 | w2 | w12
  deriving DecidableEq, BEq, Repr

def allEntities : List Entity := [.t1, .t2, .t12]
def allWorlds : List World := [.w1, .w2, .w12]

/-- Mereological atom predicate. Corresponds to `[+atomic]` in
    @cite{harbour-2014} (`Features.Number`) and `Mereology.Atom`. -/
def isAtom : Entity → Prop
  | .t1 | .t2 => True
  | .t12 => False

instance : DecidablePred isAtom := fun x => by unfold isAtom; cases x <;> infer_instance

/-- Distributive predicate: `bought(e, roya, w)`.
    Distributivity: `bought t12 w = bought t1 w ∧ bought t2 w`. -/
def bought : Entity → World → Bool
  | .t1,  .w1  | .t1,  .w12 => true
  | .t2,  .w2  | .t2,  .w12 => true
  | .t12, .w12 => true
  | _,    _    => false

/-- Distributivity holds for the join entity at all worlds. -/
theorem bought_distributive (w : World) :
    bought .t12 w = (bought .t1 w && bought .t2 w) := by cases w <;> rfl

-- ============================================================================
-- § 2. Hamblin Sets, ANS, EXH_P
-- ============================================================================

/-! The GQ generators `conjGQs`/`disjGQs` and their underlying lattice
    operations (`conjGQ`/`disjGQ`) are imported from
    `Core.Logic.Quantification.Generators`, where they are defined as
    iterated meets/joins of Montagovian individual quantifiers.

    - `conjGQ X P = X.all P` — universal quantification over X
    - `disjGQ X P = X.any P` — existential quantification over X
    - `conjGQs dom` — all ⊓(X) for ∅ ≠ X ⊆ dom (@cite{xiang-2016})
    - `disjGQs dom` — all ⊔(X) for ∅ ≠ X ⊆ dom -/

/-- Hamblin set: propositions from applying each GQ in ⊓(dom) ∪ ⊔(dom)
    to the VP `bought`. Implements eq. (29) for the buy predicate.

    ⟦Q⟧(dom) = {λw. Q(λe. bought(e, w)) | Q ∈ ⊓(dom) ∪ ⊔(dom)}

    Since `NPQ Entity = (Entity → Prop) → Prop`, we use the propositional
    characterization `conjGQ_iff_forall` / `disjGQ_iff_exists` to compute
    a Bool result from the Bool predicate `bought`. -/
def hamblinSet (dom : List Entity) : List (World → Bool) :=
  (nonemptySubsets dom).map (λ X w => X.all (λ e => bought e w)) ++
  (nonemptySubsets dom).map (λ X w => X.any (λ e => bought e w))

/-- Hamblin set with *-ro*: restricted to singleton subsets (eq. 52).
    *-ro* imposes |f(P)| = 1, so each entity contributes exactly one
    proposition, eliminating conjunctive and disjunctive GQs.

    Also serves as the individual-level Hamblin set for EXH_P
    competition: the singular alternative ranges over individual GQs
    (singletons), which is exactly what *-ro* does. The coincidence
    is structural — both operations restrict to |X| = 1. -/
def hamblinSetRo (dom : List Entity) : List (World → Bool) :=
  dom.map (λ e => λ w => bought e w)

/-- Propositional entailment over the finite world set. -/
def entails (p q : World → Bool) : Bool :=
  allWorlds.all (λ w => !p w || q w)

/-- Dayal's Exhaustivity Presupposition: does ANS find a strongest true
    answer at `w`? (@cite{dayal-1996}, eq. 8)

    EP(H, w) = ∃p ∈ H. p(w) ∧ ∀q ∈ H. q(w) → p ⊆ q

    Corresponds to `dayalEP` in
    `Theories.Semantics.Questions.Exhaustivity`. -/
def epHolds (hamblin : List (World → Bool)) (w : World) : Bool :=
  let trueProps := hamblin.filter (· w)
  trueProps.any (λ p => trueProps.all (λ q => entails p q))

/-- EXH_P anti-uniqueness (@cite{marty-2017}, @cite{elliott-sauerland-2019},
    eq. 15). For plural interrogatives competing with singular alternatives:
    the question is felicitous at `w` only if more than one individual-level
    proposition in the singular alternative's Hamblin set is true.

    Connects to `pexIEII` in
    `Theories.Semantics.Exhaustification.PresuppositionalExhaustification`. -/
def exhPAntiUniq (singularIndivH : List (World → Bool)) (w : World) : Bool :=
  (singularIndivH.filter (· w)).length > 1

-- ============================================================================
-- § 4. Interrogative Domains
-- ============================================================================

/-- BI domain: atoms + pluralities. Singular marking on BIs is a default
    with no semantic import (§4, assumption 2). -/
def biDomain : List Entity := allEntities

/-- CI domain: atoms only. ⟦SING⟧ = λP.λx: ATOM(x). P(x) (eq. 42,
    @cite{scontras-2022}). Implements the semantic content of singular
    marking on CIs. -/
def ciDomain : List Entity := allEntities.filter (fun e => decide (isAtom e))


-- ============================================================================
-- § 5. Entailment Structure
-- ============================================================================

/-! The model's predictions derive from three structural facts about
    propositional entailment under the `bought` predicate:

    1. **Conjunction strength**: ⊓({t1,t2}) yields B(t1) ∧ B(t2), which
       entails both B(t1) and B(t2). This creates strongest answers at
       plural worlds — the mechanism behind Farsi SCIs accepting plurals.

    2. **Atomic independence**: B(t1) and B(t2) are logically independent.
       Without conjunction GQs, no strongest answer exists at plural worlds.

    3. **Singleton absorption**: At singular worlds (one atom bought),
       the unique true atomic proposition entails every true disjunction
       (by disjunction introduction), so EP always holds.

    The entailment facts in (1) and (3) are derived from the lattice
    structure of GQ generators in `Core.Logic.Quantification.Generators`:
    - `conjGQ_le_individual`: ⊓(X) ≤ individual(a) for a ∈ X
    - `individual_le_disjGQ`: individual(a) ≤ ⊔(X) for a ∈ X
    - `conjGQ_le_disjGQ'`: ⊓(X) ≤ ⊔(X) for non-empty X

    The bridge `npq_le_entails` lifts NPQ lattice `≤` to the study's
    propositional `entails`, connecting the abstract lattice structure
    to the concrete model. -/

/-- NPQ lattice ordering lifts to propositional entailment via `bought`.
    If Q₁ ≤ Q₂ in the NPQ lattice, and p₁/p₂ are the propositions
    obtained by applying Q₁/Q₂ to `bought` at each world, then p₁
    entails p₂.

    This is the key bridge connecting the lattice-theoretic GQ
    infrastructure to the study's propositional entailment relation. -/
private theorem npq_le_entails {Q₁ Q₂ : NPQ Entity}
    {p₁ p₂ : World → Bool}
    (hp₁ : ∀ w, p₁ w = true ↔ Q₁ (λ e => bought e w = true))
    (hp₂ : ∀ w, p₂ w = true ↔ Q₂ (λ e => bought e w = true))
    (h : Q₁ ≤ Q₂) :
    entails p₁ p₂ = true := by
  simp only [entails, allWorlds, List.all_eq_true]
  intro w _
  rcases Bool.eq_false_or_eq_true (p₁ w) with hp1 | hp1
  · have hQ₁ := (hp₁ w).mp hp1
    have hQ₂ := h _ hQ₁
    have hp2 := (hp₂ w).mpr hQ₂
    rw [hp1, hp2]; rfl
  · rw [hp1]; rfl

/-- B(t1)∧B(t2) = ⊓({t1,t2})(bought): the conjunction proposition is
    the conjGQ of atoms applied to the buy predicate. -/
private theorem conj_eq_conjGQ_iff (w : World) :
    (bought .t1 w && bought .t2 w) = true ↔
    conjGQ [.t1, .t2] (λ e => bought e w = true) := by
  cases w <;> simp [conjGQ_iff_forall]

/-- B(t1)∨B(t2) = ⊔({t1,t2})(bought): the disjunction proposition is
    the disjGQ of atoms applied to the buy predicate. -/
private theorem disj_t1t2_eq_disjGQ_iff (w : World) :
    (bought .t1 w || bought .t2 w) = true ↔
    disjGQ [.t1, .t2] (λ e => bought e w = true) := by
  cases w <;> simp [disjGQ_iff_exists]

/-- B(t1)∨B(t12) = ⊔({t1,t12})(bought). -/
private theorem disj_t1t12_eq_disjGQ_iff (w : World) :
    (bought .t1 w || bought .t12 w) = true ↔
    disjGQ [.t1, .t12] (λ e => bought e w = true) := by
  cases w <;> simp [disjGQ_iff_exists]

/-- B(t1) and B(t2) are logically independent.
    - w1 witnesses B(t1) ⊬ B(t2): Roya bought t1 but not t2
    - w2 witnesses B(t2) ⊬ B(t1): Roya bought t2 but not t1
    This is why EP fails for individual-only Hamblin sets at w12:
    neither individual proposition can serve as the strongest true answer. -/
theorem atoms_independent :
    entails (bought .t1) (bought .t2) = false ∧
    entails (bought .t2) (bought .t1) = false :=
  ⟨rfl, rfl⟩

/-- B(t1) ∧ B(t2) entails each atom individually (conjunction elimination).
    Structural proof: ⊓({t1,t2}) ≤ individual(tᵢ) in the NPQ lattice
    (`conjGQ_le_individual`), lifted to propositional entailment via
    `npq_le_entails`. -/
theorem conj_entails_atoms :
    entails (λ w => bought .t1 w && bought .t2 w) (bought .t1) = true ∧
    entails (λ w => bought .t1 w && bought .t2 w) (bought .t2) = true :=
  ⟨npq_le_entails conj_eq_conjGQ_iff (fun _ => Iff.rfl)
    (conjGQ_le_individual .t1 _ (List.mem_cons_self ..)),
   npq_le_entails conj_eq_conjGQ_iff (fun _ => Iff.rfl)
    (conjGQ_le_individual .t2 _ (List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))))⟩

/-- B(t1) entails any disjunction containing it (disjunction introduction).
    Structural proof: individual(t1) ≤ ⊔(X) for t1 ∈ X in the NPQ lattice
    (`individual_le_disjGQ`), lifted to propositional entailment. -/
theorem atom_entails_containing_disj :
    entails (bought .t1) (λ w => bought .t1 w || bought .t2 w) = true ∧
    entails (bought .t1) (λ w => bought .t1 w || bought .t12 w) = true :=
  ⟨npq_le_entails (fun _ => Iff.rfl) disj_t1t2_eq_disjGQ_iff
    (individual_le_disjGQ .t1 _ (List.mem_cons_self ..)),
   npq_le_entails (fun _ => Iff.rfl) disj_t1t12_eq_disjGQ_iff
    (individual_le_disjGQ .t1 _ (List.mem_cons_self ..))⟩

/-- The conjunction also entails the disjunction of its conjuncts.
    Structural proof: ⊓(X) ≤ ⊔(X) for non-empty X (`conjGQ_le_disjGQ'`),
    lifted to propositional entailment.
    Combined with `conj_entails_atoms`, this makes ⊓({t1,t2}) the strongest
    element in any Hamblin set built from {t1, t2}. -/
theorem conj_entails_disj :
    entails (λ w => bought .t1 w && bought .t2 w)
            (λ w => bought .t1 w || bought .t2 w) = true :=
  npq_le_entails conj_eq_conjGQ_iff disj_t1t2_eq_disjGQ_iff
    (conjGQ_le_disjGQ' (by decide))

/-- EP holds at w12 for GQ-ranging over atoms: ⊓({t1,t2}) = B(t1) ∧ B(t2)
    is true at w12 and entails every other proposition in the Hamblin set
    (by `conj_entails_atoms` and `conj_entails_disj`). -/
theorem ep_gq_atoms_w12 :
    epHolds (hamblinSet ciDomain) .w12 = true := by decide

/-- EP fails at w12 for individual-ranging over atoms: the Hamblin set
    is {B(t1), B(t2)}, both true at w12, but independent by
    `atoms_independent`. Neither can be strongest → no ANS → EP fails.
    This is the English SCI pattern. -/
theorem ep_indiv_atoms_w12 :
    epHolds (hamblinSetRo ciDomain) .w12 = false := rfl

/-- At w1 (only t1 bought), EP holds for any Hamblin set containing B(t1).
    B(t1) is the unique true atomic proposition, and it entails every true
    disjunction via `atom_entails_containing_disj`. The proof covers both
    the full GQ Hamblin set and the individual Hamblin set. -/
theorem ep_at_singular_world :
    epHolds (hamblinSet biDomain) .w1 = true ∧
    epHolds (hamblinSet ciDomain) .w1 = true ∧
    epHolds (hamblinSetRo biDomain) .w1 = true ∧
    epHolds (hamblinSetRo ciDomain) .w1 = true := by
  exact ⟨by decide, by decide, rfl, rfl⟩

/-- At w12 (both atoms bought), EP holds for GQ-ranging over the full
    domain: ⊓({t1,t2,t12}) = B(t1) ∧ B(t2) ∧ B(t12) is the strongest
    true proposition (entails all others by conjunction elimination). -/
theorem ep_gq_full_w12 :
    epHolds (hamblinSet biDomain) .w12 = true := by decide

/-- Anti-uniqueness at w1: only one individual proposition true (B(t1)),
    so the count is 1, not > 1. Plural marking's presupposition fails →
    singular answer blocked for all PL-marked interrogatives at w1. -/
theorem antiUniq_w1 :
    exhPAntiUniq (hamblinSetRo biDomain) .w1 = false ∧
    exhPAntiUniq (hamblinSetRo ciDomain) .w1 = false :=
  ⟨rfl, rfl⟩

/-- Anti-uniqueness at w12: both B(t1) and B(t2) true (count = 2 > 1).
    Plural marking's presupposition holds → plural answers allowed. -/
theorem antiUniq_w12 :
    exhPAntiUniq (hamblinSetRo biDomain) .w12 = true ∧
    exhPAntiUniq (hamblinSetRo ciDomain) .w12 = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 6. Interrogative Types
-- ============================================================================

/-- The seven interrogative configurations from the Farsi paradigm. -/
inductive IntType where
  | sbi | pbi | sci | pci | sbiRo | sciRo | pciRo
  deriving DecidableEq, BEq, Repr

/-- Predicted singular answer availability.
    For base types, singular = EP holds at w1 (a world where one atom bought).
    For plural types, additionally requires EXH_P anti-uniqueness. -/
def predictSg : IntType → Bool
  | .sbi   => epHolds (hamblinSet biDomain) .w1
  | .sci   => epHolds (hamblinSet ciDomain) .w1
  | .pbi   => epHolds (hamblinSet biDomain) .w1 && exhPAntiUniq (hamblinSetRo biDomain) .w1
  | .pci   => epHolds (hamblinSet biDomain) .w1 && exhPAntiUniq (hamblinSetRo ciDomain) .w1
  | .sbiRo => epHolds (hamblinSetRo biDomain) .w1
  | .sciRo => epHolds (hamblinSetRo ciDomain) .w1
  | .pciRo => epHolds (hamblinSetRo biDomain) .w1 && exhPAntiUniq (hamblinSetRo ciDomain) .w1

/-- Predicted plural answer availability.
    Plural = EP holds at w12 (a world where both atoms bought). -/
def predictPl : IntType → Bool
  | .sbi   => epHolds (hamblinSet biDomain) .w12
  | .sci   => epHolds (hamblinSet ciDomain) .w12
  | .pbi   => epHolds (hamblinSet biDomain) .w12 && exhPAntiUniq (hamblinSetRo biDomain) .w12
  | .pci   => epHolds (hamblinSet biDomain) .w12 && exhPAntiUniq (hamblinSetRo ciDomain) .w12
  | .sbiRo => epHolds (hamblinSetRo biDomain) .w12
  | .sciRo => epHolds (hamblinSetRo ciDomain) .w12
  | .pciRo => epHolds (hamblinSetRo biDomain) .w12 && exhPAntiUniq (hamblinSetRo ciDomain) .w12

-- ============================================================================
-- § 7. Core Predictions
-- ============================================================================

/-! Each prediction derives from the structural lemmas in § 5. The proofs
    explicitly chain the relevant structural facts via `simp only`.

    ### Bare Interrogatives

    BIs range over GQs from the FULL entity domain (atoms + pluralities).
    Singular marking on BIs is a morphological default (no semantic import). -/

/-- SBI (`chi`, what.SG): allows singular answers. (ex. 20a)
    EP holds at w1 by `ep_at_singular_world`: B(t1) is the strongest
    true answer in the full GQ Hamblin set. -/
theorem sbi_singular : predictSg .sbi = true := by
  show epHolds (hamblinSet biDomain) .w1 = true
  exact ep_at_singular_world.1

/-- SBI: allows plural answers. (ex. 20b)
    EP holds at w12 by `ep_gq_full_w12`: ⊓({t1,t2,t12}) produces a
    conjunction proposition that entails all others. -/
theorem sbi_plural : predictPl .sbi = true := by
  show epHolds (hamblinSet biDomain) .w12 = true
  exact ep_gq_full_w12

/-- PBI (`chi-a`, what.PL): blocks singular via EXH_P. (ex. 21a)
    EP itself holds at w1 (`ep_at_singular_world`), but EXH_P
    anti-uniqueness fails: only B(t1) is true among individual
    propositions at w1 (`antiUniq_w1`), so count = 1, not > 1. -/
theorem pbi_blocks_singular : predictSg .pbi = false := by
  show (epHolds (hamblinSet biDomain) .w1 && exhPAntiUniq (hamblinSetRo biDomain) .w1) = false
  simp only [ep_at_singular_world.1, antiUniq_w1.1, Bool.true_and]

/-- PBI: allows plural. (ex. 21b)
    EP holds at w12 (`ep_gq_full_w12`) and anti-uniqueness holds
    (`antiUniq_w12`): both B(t1) and B(t2) true → count = 2 > 1. -/
theorem pbi_plural : predictPl .pbi = true := by
  show (epHolds (hamblinSet biDomain) .w12 && exhPAntiUniq (hamblinSetRo biDomain) .w12) = true
  simp only [ep_gq_full_w12, antiUniq_w12.1, Bool.true_and]

/-! ### Complex Interrogatives

    CIs range over GQs from the ATOM domain ({t1, t2}).
    SING restricts the domain to atoms — this is the semantic content
    of singular marking on CIs, unlike BIs where it's vacuous. -/

/-- SCI (`che ketab-i`, what book.SG.INDEF): allows singular. (ex. 23a)
    EP holds at w1 by `ep_at_singular_world`. -/
theorem sci_singular : predictSg .sci = true := by
  show epHolds (hamblinSet ciDomain) .w1 = true
  exact ep_at_singular_world.2.1

/-- SCI: allows plural answers — the key Farsi innovation. (ex. 23b)
    Unlike English SCIs (individual-ranging → independent propositions →
    EP fails at plural worlds by `atoms_independent`), Farsi SCIs range
    over GQs. The conjunction GQ ⊓({t1, t2}) produces B(t1) ∧ B(t2),
    which entails both atomic propositions (`conj_entails_atoms`) and
    the disjunction (`conj_entails_disj`) → EP holds by
    `ep_gq_atoms_w12`. -/
theorem sci_plural : predictPl .sci = true := by
  show epHolds (hamblinSet ciDomain) .w12 = true
  exact ep_gq_atoms_w12

/-- PCI (`che ketab-a-i`, what book.PL.INDEF): blocks singular. (ex. 25a)
    EP holds but anti-uniqueness fails at w1 (`antiUniq_w1`). -/
theorem pci_blocks_singular : predictSg .pci = false := by
  show (epHolds (hamblinSet biDomain) .w1 && exhPAntiUniq (hamblinSetRo ciDomain) .w1) = false
  simp only [ep_at_singular_world.1, antiUniq_w1.2, Bool.true_and]

/-- PCI: allows plural. (ex. 25b)
    EP holds at w12 and anti-uniqueness holds (`antiUniq_w12`). -/
theorem pci_plural : predictPl .pci = true := by
  show (epHolds (hamblinSet biDomain) .w12 && exhPAntiUniq (hamblinSetRo ciDomain) .w12) = true
  simp only [ep_gq_full_w12, antiUniq_w12.2, Bool.true_and]

/-! ### With Differential Object Marker *-ro*

    *-ro* restricts the selection function to singletons, eliminating
    conjunctive and disjunctive GQs. The Hamblin set reduces to
    individual propositions {B(e) | e ∈ dom}. -/

/-- SBI + *-ro* (`chi ro`): allows singular. (ex. 26a)
    EP holds at w1 by `ep_at_singular_world`. -/
theorem sbi_ro_singular : predictSg .sbiRo = true := by
  show epHolds (hamblinSetRo biDomain) .w1 = true
  exact ep_at_singular_world.2.2.1

/-- SBI + *-ro*: allows plural. (ex. 26b)
    BI domain includes t12, so the Hamblin set is {B(t1), B(t2), B(t12)}.
    B(t12) = B(t1) ∧ B(t2) by distributivity (`bought_distributive`),
    so at w12 it entails both → EP holds. -/
theorem sbi_ro_plural : predictPl .sbiRo = true := rfl

/-- SCI + *-ro* (`che ketab-i ro`): allows singular. (ex. 27a)
    EP holds at w1 by `ep_at_singular_world`. -/
theorem sci_ro_singular : predictSg .sciRo = true := by
  show epHolds (hamblinSetRo ciDomain) .w1 = true
  exact ep_at_singular_world.2.2.2

/-- SCI + *-ro*: blocks plural. (ex. 27b)
    SING restricts domain to atoms {t1, t2}. *-ro* restricts to
    singletons, giving Hamblin = {B(t1), B(t2)}.
    At w12: both true but neither entails the other
    (`atoms_independent`) → EP fails (`ep_indiv_atoms_w12`).
    This recovers the English SCI pattern, only with *-ro*. -/
theorem sci_ro_blocks_plural : predictPl .sciRo = false := by
  show epHolds (hamblinSetRo ciDomain) .w12 = false
  exact ep_indiv_atoms_w12

/-- PCI + *-ro* (`che ketab-a-i ro`): blocks singular. (ex. 28a)
    EP holds at w1 but anti-uniqueness fails (`antiUniq_w1`). -/
theorem pci_ro_blocks_singular : predictSg .pciRo = false := by
  show (epHolds (hamblinSetRo biDomain) .w1 && exhPAntiUniq (hamblinSetRo ciDomain) .w1) = false
  simp only [ep_at_singular_world.2.2.1, antiUniq_w1.2, Bool.true_and]

/-- PCI + *-ro*: allows plural. (ex. 28b)
    EP holds at w12 (BI domain includes t12, giving strongest answer)
    and anti-uniqueness holds (`antiUniq_w12`). -/
theorem pci_ro_plural : predictPl .pciRo = true := by
  show (epHolds (hamblinSetRo biDomain) .w12 && exhPAntiUniq (hamblinSetRo ciDomain) .w12) = true
  have hEP : epHolds (hamblinSetRo biDomain) .w12 = true := rfl
  simp only [hEP, antiUniq_w12.2, Bool.true_and]

/-- All 14 predictions verified in aggregate. Each case is proved
    individually above via structural lemmas; this theorem confirms
    they compose correctly into the full paradigm table. -/
theorem full_paradigm :
    [predictSg .sbi, !predictSg .pbi, predictSg .sci, !predictSg .pci,
     predictSg .sbiRo, predictSg .sciRo, !predictSg .pciRo,
     predictPl .sbi, predictPl .pbi, predictPl .sci, predictPl .pci,
     predictPl .sbiRo, !predictPl .sciRo, predictPl .pciRo].all id = true := by
  simp only [sbi_singular, pbi_blocks_singular, sci_singular, pci_blocks_singular,
             sbi_ro_singular, sci_ro_singular, pci_ro_blocks_singular,
             sbi_plural, pbi_plural, sci_plural, pci_plural,
             sbi_ro_plural, sci_ro_blocks_plural, pci_ro_plural,
             Bool.not_false, List.all, id, Bool.and_self]

-- ============================================================================
-- § 8. Bridge Theorems
-- ============================================================================

/-- CI domain = atom filter of all entities. Connects SING (eq. 42) to
    `Features.Number.Category.singular` ([+atomic]). -/
theorem ciDomain_is_atoms : ciDomain = allEntities.filter (fun e => decide (isAtom e)) := rfl

/-- The Farsi/English SCI divergence in one theorem.
    Both use atoms-only domain (SING). The difference: Farsi ranges over
    GQs (`hamblinSet`), English over individuals (`hamblinSetRo`). Only
    GQ-ranging allows plural answers at w12.

    Farsi side: ⊓({t1,t2}) creates B(t1)∧B(t2), which entails both
    B(t1) and B(t2) (`conj_entails_atoms`) → strongest answer → EP holds.
    English side: {B(t1), B(t2)} are independent (`atoms_independent`)
    → no strongest answer → EP fails. -/
theorem farsi_vs_english :
    epHolds (hamblinSet ciDomain) .w12 = true ∧
    epHolds (hamblinSetRo ciDomain) .w12 = false :=
  ⟨ep_gq_atoms_w12, ep_indiv_atoms_w12⟩

/-- *-ro* eliminates disjunctive propositions from the Hamblin set,
    blocking free choice interpretations (§4, eqs. 62–63).

    Full Hamblin set includes ⊔({t1,t2}) = B(t1) ∨ B(t2), which
    enables free choice readings. *-ro* restricts to singletons,
    so only B(t1), B(t2), B(t12) remain — no disjunctions. -/
theorem ro_eliminates_disjunction :
    let disj := λ w => bought .t1 w || bought .t2 w
    -- Present in full Hamblin set
    (hamblinSet biDomain).any
      (λ p => allWorlds.all (λ w => p w == disj w)) = true ∧
    -- Absent from -ro Hamblin set
    (hamblinSetRo biDomain).any
      (λ p => allWorlds.all (λ w => p w == disj w)) = false :=
  ⟨by decide, rfl⟩

/-- The Hamblin set decomposes into conjGQ and disjGQ applications.
    Each proposition in `hamblinSet dom` is `conjGQ X (bought · w)` or
    `disjGQ X (bought · w)` for some non-empty X ⊆ dom. This connects
    the study's concrete Hamblin set to the lattice-theoretic GQ
    generators in `Core.Logic.Quantification.Generators`. -/
theorem hamblinSet_decomposition (dom : List Entity) (w : World) :
    ∀ p ∈ hamblinSet dom, ∃ X ∈ nonemptySubsets dom,
      (p w = true ↔ conjGQ X (λ e => bought e w = true)) ∨
      (p w = true ↔ disjGQ X (λ e => bought e w = true)) := by
  intro p hp
  simp only [hamblinSet, List.mem_append, List.mem_map] at hp
  rcases hp with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · refine ⟨X, hX, Or.inl ?_⟩
    simp [List.all_eq_true, conjGQ_iff_forall]
  · refine ⟨X, hX, Or.inr ?_⟩
    simp [List.any_eq_true, disjGQ_iff_exists]

/-- B(t12) is extensionally equivalent to B(t1) ∧ B(t2): the mereological
    join's predicate equals the conjunction of its parts.
    This follows from distributivity (`bought_distributive`) and is how
    plural answers arise even from the BI individual Hamblin set:
    the -ro Hamblin set over biDomain includes B(t12), which is the
    conjunction proposition in disguise. -/
theorem plurality_via_gq :
    let bt12 := λ w => bought .t12 w
    let conjt1t2 := λ w => bought .t1 w && bought .t2 w
    allWorlds.all (λ w => bt12 w == conjt1t2 w) = true := by
  simp only [allWorlds, List.all, bought_distributive, beq_self_eq_true, Bool.and_self]

-- ============================================================================
-- § 9. Empirical Data
-- ============================================================================

/-- Farsi interrogative datum with acceptability judgment. -/
structure Datum where
  farsi : String
  gloss : String
  intType : IntType
  singularOk : Bool
  pluralOk : Bool
  exNum : String
  deriving Repr

def data : List Datum :=
  [ ⟨"Roya diruz chi xarid?",             "what.SG",                .sbi,   true,  true,  "20"⟩
  , ⟨"Roya diruz chi-a xarid?",           "what.PL",                .pbi,   false, true,  "21"⟩
  , ⟨"Roya diruz che ketab-i xarid?",     "what book.SG.INDEF",     .sci,   true,  true,  "23"⟩
  , ⟨"Roya diruz che ketab-a-i xarid?",   "what book.PL.INDEF",     .pci,   false, true,  "25"⟩
  , ⟨"Roya diruz chi ro xarid?",          "what.SG ACC",            .sbiRo, true,  true,  "26"⟩
  , ⟨"Roya diruz che ketab-i ro xarid?",  "what book.SG.INDEF ACC", .sciRo, true,  false, "27"⟩
  , ⟨"Roya diruz che ketab-a-i ro xarid?","what book.PL.INDEF ACC", .pciRo, false, true,  "28"⟩ ]

/-- Every datum's acceptability judgment matches the model's prediction.
    Each per-datum check is verified structurally in § 7; this aggregates
    them as a single data consistency check. -/
theorem data_consistent :
    data.all (λ d => d.singularOk == predictSg d.intType &&
                     d.pluralOk == predictPl d.intType) = true := by decide

end AlonsoOvalleMoghiseh2025b
