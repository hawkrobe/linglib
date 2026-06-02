import Linglib.Semantics.Exhaustification.Operators.Basic
import Linglib.Semantics.Exhaustification.Operators.InnocentInclusion
import Linglib.Semantics.Exhaustification.Operators.Decidable
import Linglib.Semantics.Conditionals.Counterfactual
import Linglib.Phenomena.FreeChoice.Basic
import Linglib.Studies.Santorio2018

/-!
# Bar-Lev & Fox (2020) — Free Choice via Innocent Inclusion
[bar-lev-fox-2020] [fox-2007] [spector-2016]

Worked example of [bar-lev-fox-2020] "Free choice, simplification, and
Innocent Inclusion" (Natural Language Semantics 28:175–223) over a five-world
toy modal model.

## What this file does

The abstract theory of Innocent Exclusion (`IE`), Innocent Inclusion (`II`),
the cell-of-the-induced-partition (`cell`), and the cell-identification theorem
`mem_II_of_cell_witness` lives in
`Semantics/Exhaustification/Operators/Basic.lean`. This file instantiates
that theory on a small `FCWorld` and verifies the paper's headline empirical
prediction:

  Exh^{IE+II}(◇(a ∨ b)) ⊨ ◇a ∧ ◇b

The contrast with simple disjunction (where the alternative set IS closed
under conjunction and free choice does *not* arise) is captured via a parallel
`DisjWorld` toy + `simpleALT` and `simple_has_conjunction`.

## Why the cell-identification API matters

In the paper, the move from "exhaustification of a disjunction" to "free
choice" is enabled by a structural property of the alternative set: the
pairwise conjunction of the disjunctive alternatives `◇a ∩ ◇b` is NOT a
member of `Alt(◇(a∨b))` (paper eqn 13b p. 182). The cell of the partition
induced by the alternatives is therefore consistent and identified by
`Exh^{IE+II}`. The free choice proof is a one-line corollary of
`mem_II_of_cell_witness` once a witness world for the cell is exhibited
(the `separatelyAB` world, where each disjunct is individually possible
but not jointly).

## On the `Exh^{IE+II}` definition (paper §3, eqn 24-25 pp. 187-188)

`Exh^{IE+II}` strengthens the prejacent with two operations:
1. **Innocent Exclusion (IE)** — the intersection of *maximal* subsets
   of alternatives that can consistently be assigned `false` together
   with the prejacent. Members are negated.
2. **Innocent Inclusion (II)** — the intersection of *maximal* subsets
   of alternatives that can consistently be assigned `true` together
   with the prejacent AND the IE negations from step 1. Members are
   asserted.

II is **not** "all non-IE alternatives" (a popular but incorrect gloss).
The non-IE = II coincidence in the basic FC case is a *derived* fact
(paper §3.3.3) once the cell is identified, not a definition. The
substrate `Semantics/Exhaustification/Operators/Basic.lean`
follows the paper's actual definitions.

-/

namespace BarLevFox2020

open Exhaustification

-- ============================================================================
-- §1. The five-world FC toy model
-- ============================================================================

/-- Possible worlds for free choice: each represents a configuration of which
disjuncts are individually or jointly permitted.

The `separatelyAB` world is the cell witness: each disjunct is individually
permitted but they are not jointly permitted. This world distinguishes
`◇a ∧ ◇b` from `◇(a ∧ b)` and is the cornerstone of [bar-lev-fox-2020]'s
free-choice derivation. -/
inductive FCWorld where
  | neither : FCWorld       -- Neither a nor b permitted
  | onlyA : FCWorld         -- Only a permitted
  | onlyB : FCWorld         -- Only b permitted
  | both : FCWorld          -- Both jointly permitted (◇(a ∧ b))
  | separatelyAB : FCWorld  -- Each individually permitted, not jointly
  deriving DecidableEq, Repr, Inhabited

/-- ◇a — `a` is permitted at the world. -/
def permA : Set FCWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => False
  | .both => True
  | .separatelyAB => True

/-- ◇b — `b` is permitted at the world. -/
def permB : Set FCWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => True
  | .both => True
  | .separatelyAB => True

/-- ◇(a ∨ b) — the prejacent. -/
def permAorB : Set FCWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => True
  | .both => True
  | .separatelyAB => True

/-- ◇(a ∧ b) — joint permission. -/
def permAandB : Set FCWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => False
  | .both => True
  | .separatelyAB => False

/-- The free-choice alternative set: `{◇(a ∨ b), ◇a, ◇b, ◇(a ∧ b)}`. -/
def fcALT : Set (Set FCWorld) :=
  {permAorB, permA, permB, permAandB}

/-- The prejacent: `◇(a ∨ b)`. -/
def fcPrejacent : Set FCWorld := permAorB

-- ============================================================================
-- §2. Non-closure under conjunction
-- ============================================================================

/-- [bar-lev-fox-2020] eqn (13b) p. 182: the pairwise conjunction
    of the disjunctive alternatives is NOT closed by `fcALT`. The
    `separatelyAB` world satisfies `permA ∩ permB` but no element of
    `fcALT` (specifically not `permAandB`); witnesses at `.onlyA`/
    `.onlyB` rule out the other three potential matches. This
    structural property — that `Alt(◇(a∨b))` is not closed under
    pairwise conjunction — is what lets cell identification yield
    free choice. -/
theorem fc_alt_not_closed_under_pairwise_conjunction :
    ¬(∀ (X : Set (Set FCWorld)), X ⊆ fcALT → (⋂₀ X) ∈ fcALT) := by
  intro h
  have hX : ({permA, permB} : Set (Set FCWorld)) ⊆ fcALT := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx with rfl | rfl <;> simp
  have hconj := h {permA, permB} hX
  simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hconj
  rcases hconj with heq | heq | heq | heq
  · have : ¬(⋂₀ ({permA, permB} : Set _)) .onlyA :=
      fun hc => hc permB (Set.mem_insert_of_mem _ rfl)
    rw [heq] at this; exact this trivial
  · have : ¬(⋂₀ ({permA, permB} : Set _)) .onlyA :=
      fun hc => hc permB (Set.mem_insert_of_mem _ rfl)
    rw [heq] at this; exact this trivial
  · have : ¬(⋂₀ ({permA, permB} : Set _)) .onlyB :=
      fun hc => hc permA (Set.mem_insert_iff.mpr (Or.inl rfl))
    rw [heq] at this; exact this trivial
  · have : (⋂₀ ({permA, permB} : Set _)) .separatelyAB := by
      intro φ hφ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
      rcases hφ with rfl | rfl <;> trivial
    rw [heq] at this; exact this

-- ============================================================================
-- §3. The cell witness: `separatelyAB`
-- ============================================================================

/-!
The cornerstone of the free-choice derivation is exhibiting a world that
witnesses the `cell` of the partition induced by `fcALT`. Once this is in
place, free choice follows as a one-line corollary of
`mem_II_of_cell_witness`.

The witness world is `separatelyAB`. Establishing the cell predicate at
`separatelyAB` requires four facts about the IE structure of `fcALT`:

* `permAorB` is *not* innocently excludable (since permAorBᶜ contradicts the
  prejacent in any MC-set);
* `permA` is *not* innocently excludable (witnessed by an MC-set that omits
  permAᶜ);
* `permB` is *not* innocently excludable (symmetric);
* `permAandB` *is* innocently excludable.
-/

private theorem fcALT_finite : Set.Finite fcALT :=
  Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _)))

private theorem fcPrejacent_sat : ∃ w, fcPrejacent w := ⟨.onlyA, trivial⟩

private theorem permAorB_not_ie :
    ¬IsInnocentlyExcludable fcALT fcPrejacent permAorB :=
  not_isInnocentlyExcludable_of_phi_subset fcALT_finite fcPrejacent_sat
    (Set.Subset.refl _)

/-- ¬`permA` and ¬`permB` together with the prejacent are inconsistent on
`FCWorld`: every world satisfying `permAorB` satisfies at least one disjunct. -/
private theorem perm_cover : ∀ u, fcPrejacent u → ¬permA u → ¬permB u → False :=
  fun u => by cases u <;> simp [fcPrejacent, permAorB, permA, permB]

private theorem mc_set_without_neg_permA :
    IsMCSet fcALT fcPrejacent {fcPrejacent, permBᶜ, permAandBᶜ} := by
  constructor
  · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · intro ψ hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl | rfl
      · left; rfl
      · right; exact ⟨permB, by simp [fcALT], rfl⟩
      · right; exact ⟨permAandB, by simp [fcALT], rfl⟩
    · exact ⟨.onlyA, fun ψ hψ => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
        rcases hψ with rfl | rfl | rfl
        · exact trivial
        · exact id
        · exact id⟩
  · intro E' hE' hsub ψ hψ'
    rcases hE'.2.1 ψ hψ' with rfl | ⟨a, ha, rfl⟩
    · exact Set.mem_insert _ _
    · simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hu (permAorBᶜ) hψ' (hu fcPrejacent (hsub (Set.mem_insert _ _)))
      · exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact perm_cover u
          (hu fcPrejacent (hsub (Set.mem_insert _ _)))
          (hu (permAᶜ) hψ')
          (hu (permBᶜ) (hsub (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

private theorem mc_set_without_neg_permB :
    IsMCSet fcALT fcPrejacent {fcPrejacent, permAᶜ, permAandBᶜ} := by
  constructor
  · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · intro ψ hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl | rfl
      · left; rfl
      · right; exact ⟨permA, by simp [fcALT], rfl⟩
      · right; exact ⟨permAandB, by simp [fcALT], rfl⟩
    · exact ⟨.onlyB, fun ψ hψ => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
        rcases hψ with rfl | rfl | rfl
        · exact trivial
        · exact id
        · exact id⟩
  · intro E' hE' hsub ψ hψ'
    rcases hE'.2.1 ψ hψ' with rfl | ⟨a, ha, rfl⟩
    · exact Set.mem_insert _ _
    · simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hu (permAorBᶜ) hψ' (hu fcPrejacent (hsub (Set.mem_insert _ _)))
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact perm_cover u
          (hu fcPrejacent (hsub (Set.mem_insert _ _)))
          (hu (permAᶜ) (hsub (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
          (hu (permBᶜ) hψ')
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

private theorem permA_not_ie :
    ¬IsInnocentlyExcludable fcALT fcPrejacent permA := by
  refine mc_set_without_neg_permA.not_isInnocentlyExcludable_of_compl_notMem ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨fun h => Eq.mp (congrFun h .neither) id,
         fun h => Eq.mpr (congrFun h .onlyA) id trivial,
         fun h => Eq.mpr (congrFun h .onlyA) id trivial⟩

private theorem permB_not_ie :
    ¬IsInnocentlyExcludable fcALT fcPrejacent permB := by
  refine mc_set_without_neg_permB.not_isInnocentlyExcludable_of_compl_notMem ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨fun h => Eq.mp (congrFun h .neither) id,
         fun h => Eq.mp (congrFun h .onlyA) id trivial,
         fun h => Eq.mpr (congrFun h .onlyB) id trivial⟩

/-- `permAandB` *is* innocently excludable: every MC-set contains `permAandBᶜ`,
because adjoining `permAandBᶜ` to any MC-set is consistent (witnessed at
`onlyA` whenever the MC-set itself is consistent), so maximality forces
inclusion. -/
private theorem permAandB_is_ie :
    IsInnocentlyExcludable fcALT fcPrejacent permAandB := by
  refine ⟨by simp [fcALT], ?_⟩
  intro E hE
  apply hE.2 (E ∪ {permAandBᶜ}) ?_ Set.subset_union_left
    (Set.mem_union_right E rfl)
  refine ⟨Set.mem_union_left _ hE.1.1, ?_, ?_⟩
  · rintro ψ (hψE | hψN)
    · exact hE.1.2.1 ψ hψE
    · refine Or.inr ⟨permAandB, by simp [fcALT], Set.mem_singleton_iff.mp hψN⟩
  · obtain ⟨u₀, hu₀⟩ := hE.1.2.2
    by_cases hpAB : permAandB u₀
    · -- u₀ satisfies permAandB, so u₀ = .both. Switch witness to .onlyA.
      have hu_both : u₀ = FCWorld.both := by
        cases u₀ <;> simp_all [permAandB]
      refine ⟨FCWorld.onlyA, fun ψ hψ => ?_⟩
      rcases hψ with hψE | hψN
      · -- ψ ∈ E and ψ holds at .both. Cases on ψ's structure.
        have hψBoth : ψ FCWorld.both := hu_both ▸ hu₀ ψ hψE
        rcases hE.1.2.1 ψ hψE with hψφ | ⟨a, ha, hψN⟩
        · rw [hψφ]; exact trivial
        · exfalso
          rw [hψN] at hψBoth
          simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          rcases ha with rfl | rfl | rfl | rfl
          · exact hψBoth trivial
          · exact hψBoth trivial
          · exact hψBoth trivial
          · exact hψBoth trivial
      · rw [Set.mem_singleton_iff.mp hψN]; intro h; exact h
    · refine ⟨u₀, fun ψ hψ => ?_⟩
      rcases hψ with hψE | hψN
      · exact hu₀ ψ hψE
      · rw [Set.mem_singleton_iff.mp hψN]; exact hpAB

/-- **Cell witness for the FC alternative set.** The `separatelyAB` world
verifies `cell fcALT fcPrejacent` — it satisfies the prejacent, falsifies
every IE-excludable alternative (only `permAandB`), and verifies every
non-excludable alternative (`permAorB`, `permA`, `permB`). -/
theorem separatelyAB_in_cell : cell fcALT fcPrejacent .separatelyAB := by
  refine ⟨trivial, ?_, ?_⟩
  · intro q hq
    have hqAlt : q ∈ fcALT := hq.1
    simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hqAlt
    rcases hqAlt with rfl | rfl | rfl | rfl
    · exact absurd hq permAorB_not_ie
    · exact absurd hq permA_not_ie
    · exact absurd hq permB_not_ie
    · intro h; exact h
  · rintro r ⟨hrAlt, hrNotIE⟩
    simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hrAlt
    rcases hrAlt with rfl | rfl | rfl | rfl
    · exact trivial
    · exact trivial
    · exact trivial
    · exact absurd permAandB_is_ie hrNotIE

-- ============================================================================
-- §4. Free choice as a corollary of cell identification
-- ============================================================================

/-- **Main free-choice theorem.** `Exh^{IE+II}(◇(a ∨ b)) ⊨ ◇a ∧ ◇b`.

Direct application of the substrate-level cell-witness factorization
`exhIEII_implies_cell_witnessed_alt` (`Operators/InnocentInclusion.lean`)
to each disjunct, using `separatelyAB_in_cell` as the cell witness.
The substrate theorem encapsulates the abstract content of
[bar-lev-fox-2020] §3.3: any alternative true at a cell witness
is entailed by `exhIEII`. -/
theorem free_choice :
    ∀ w, exhIEII fcALT fcPrejacent w → permA w ∧ permB w := fun w h_exh =>
  ⟨exhIEII_implies_cell_witnessed_alt fcALT fcPrejacent
      (by simp [fcALT]) .separatelyAB separatelyAB_in_cell trivial w h_exh,
   exhIEII_implies_cell_witnessed_alt fcALT fcPrejacent
      (by simp [fcALT]) .separatelyAB separatelyAB_in_cell trivial w h_exh⟩

-- ============================================================================
-- §5. Contrast: simple disjunction (closed under ∧)
-- ============================================================================

/-- Simple-disjunction worlds (no modal layer). -/
inductive DisjWorld where
  | neither : DisjWorld
  | onlyA : DisjWorld
  | onlyB : DisjWorld
  | both : DisjWorld
  deriving DecidableEq, Repr, Inhabited

/-- Atomic proposition `a`. -/
def propA : Set DisjWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => False
  | .both => True

/-- Atomic proposition `b`. -/
def propB : Set DisjWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => True
  | .both => True

/-- Disjunction `a ∨ b`. -/
def propAorB : Set DisjWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => True
  | .both => True

/-- Conjunction `a ∧ b`. -/
def propAandB : Set DisjWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => False
  | .both => True

/-- Simple disjunction's alternative set: `{a ∨ b, a, b, a ∧ b}`. -/
def simpleALT : Set (Set DisjWorld) :=
  {propAorB, propA, propB, propAandB}

/-- The structural contrast with FC: simple disjunction's alternative set
**is** closed under conjunction (`a ∧ b ∈ simpleALT`). This is what blocks
the cell from being consistent and prevents free choice from arising. -/
theorem simple_has_conjunction : propAandB ∈ simpleALT := by simp [simpleALT]

-- ============================================================================
-- §6. SDA via Innocent Inclusion (paper §7, pp. 204–206)
-- ============================================================================

/-!
## SDA — the second contribution highlighted in the paper title

[bar-lev-fox-2020] §7 derives **simplification of disjunctive
antecedents** by applying `Exh^{IE+II}` to a counterfactual prejacent
`(p∨q)□→r` over the 4-element alternative set obtained by
disjunct-replacement (eqn 65 p. 205):

  Alt((p∨q)□→r) = {(p∨q)□→r, p□→r, q□→r, (p∧q)□→r}

The maximal-false-assignment sets (eqn 66 p. 206) yield IE =
`{(p∧q)□→r}`. Innocent Inclusion then asserts the three non-IE
alternatives, giving Bar-Lev/Fox's verdict (eqn 67 p. 206):

  Exh^{IE+II}((p∨q)□→r) ⇔ (p□→r) ∧ (q□→r) ∧ ¬((p∧q)□→r)

This is the **central rival mechanism** to [santorio-2018]'s
homogeneity-based SDA derivation: both predict the SDA inference
`(p∨q)□→r ⊨ (p□→r) ∧ (q□→r)` via incompatible mechanisms (Bar-Lev/Fox:
exhaustification-via-Innocent-Inclusion; Santorio: per-alternative
DIST_π homogeneity over Katzir-generated truthmakers). The
`bar_lev_fox_sda_implies_santorio_sda_inference` theorem at the end
of this section makes this cross-mechanism agreement Lean-checkable.
-/

section SDA

open Semantics.Conditionals.Counterfactual (universalCounterfactual)

/-- Worlds for the SDA toy model. `actual` is the evaluation world
    (no atomic prop holds); `wp` / `wq` / `wpq` are the relevant
    counterfactual alternatives where p (and r), q (and r), or both
    p and q (but not r) hold respectively.

    Designed so that, centered at `actual`, `wp` and `wq` are closer
    than `wpq`, making the three conditional alternatives evaluate as
    follows at `actual`: prejacent TRUE, p□→r TRUE, q□→r TRUE,
    (p∧q)□→r FALSE. -/
inductive SDAWorld where
  | actual : SDAWorld    -- ¬p, ¬q, ¬r
  | wp : SDAWorld        -- p, ¬q, r
  | wq : SDAWorld        -- ¬p, q, r
  | wpq : SDAWorld       -- p, q, ¬r
  deriving DecidableEq, Repr, Inhabited

instance : Fintype SDAWorld where
  elems := {.actual, .wp, .wq, .wpq}
  complete x := by cases x <;> decide

/-- Atomic proposition `p`. -/
def sdaP : SDAWorld → Prop
  | .actual => False | .wp => True | .wq => False | .wpq => True
/-- Atomic proposition `q`. -/
def sdaQ : SDAWorld → Prop
  | .actual => False | .wp => False | .wq => True | .wpq => True
/-- Atomic proposition `r`. -/
def sdaR : SDAWorld → Prop
  | .actual => False | .wp => True | .wq => True | .wpq => False

instance : DecidablePred sdaP := fun w => by cases w <;> unfold sdaP <;> infer_instance
instance : DecidablePred sdaQ := fun w => by cases w <;> unfold sdaQ <;> infer_instance
instance : DecidablePred sdaR := fun w => by cases w <;> unfold sdaR <;> infer_instance

/-- Similarity ordering: from `actual`, `wp` and `wq` are closer than
    `wpq`. From `wp`, `wp` itself is closer than `wpq` (so closest
    p-worlds from wp are just {wp}). Symmetric for `wq`. The minimal
    structure needed for the cell-witness analysis at `actual`. -/
def sdaSim : Core.Order.SimilarityOrdering SDAWorld := .ofBool
  (fun w₀ w₁ w₂ => w₁ == w₂ ||
    (w₀ == .actual && (w₁ == .wp || w₁ == .wq) && w₂ == .wpq) ||
    (w₀ == .wp && w₁ == .wp && w₂ == .wpq) ||
    (w₀ == .wq && w₁ == .wq && w₂ == .wpq))
  (by decide) (by decide)

/-- The conditional `p □→ r` as a `Set SDAWorld`. -/
def sdaPbox : Set SDAWorld := fun w => universalCounterfactual sdaSim sdaP sdaR w
/-- The conditional `q □→ r` as a `Set SDAWorld`. -/
def sdaQbox : Set SDAWorld := fun w => universalCounterfactual sdaSim sdaQ sdaR w
/-- The conditional `(p∨q) □→ r` (the prejacent) as a `Set SDAWorld`. -/
def sdaPorQbox : Set SDAWorld :=
  fun w => universalCounterfactual sdaSim (fun v => sdaP v ∨ sdaQ v) sdaR w
/-- The conditional `(p∧q) □→ r` as a `Set SDAWorld`. -/
def sdaPandQbox : Set SDAWorld :=
  fun w => universalCounterfactual sdaSim (fun v => sdaP v ∧ sdaQ v) sdaR w

/-- The SDA alternative set per eqn (65) p. 205. -/
def sdaALT : Set (Set SDAWorld) :=
  {sdaPorQbox, sdaPbox, sdaQbox, sdaPandQbox}

/-- The SDA prejacent: `(p∨q) □→ r`. -/
def sdaPrejacent : Set SDAWorld := sdaPorQbox

/-! ### Per-alternative verdicts at `.actual` -/

theorem sdaPrejacent_at_actual : sdaPrejacent .actual := by
  unfold sdaPrejacent sdaPorQbox universalCounterfactual
  decide

theorem sdaPbox_at_actual : sdaPbox .actual := by
  unfold sdaPbox universalCounterfactual; decide

theorem sdaQbox_at_actual : sdaQbox .actual := by
  unfold sdaQbox universalCounterfactual; decide

theorem sdaPandQbox_false_at_actual : ¬ sdaPandQbox .actual := by
  unfold sdaPandQbox universalCounterfactual; decide

/-! Per-world verdicts at the MC-set witnesses `.wp` and `.wq`. -/

theorem sdaPrejacent_at_wp : sdaPrejacent SDAWorld.wp := by
  unfold sdaPrejacent sdaPorQbox universalCounterfactual; decide

theorem sdaPrejacent_at_wq : sdaPrejacent SDAWorld.wq := by
  unfold sdaPrejacent sdaPorQbox universalCounterfactual; decide

theorem sdaPbox_at_wp : sdaPbox SDAWorld.wp := by
  unfold sdaPbox universalCounterfactual; decide

theorem sdaPbox_false_at_wq : ¬ sdaPbox SDAWorld.wq := by
  unfold sdaPbox universalCounterfactual; decide

theorem sdaQbox_at_wq : sdaQbox SDAWorld.wq := by
  unfold sdaQbox universalCounterfactual; decide

theorem sdaQbox_false_at_wp : ¬ sdaQbox SDAWorld.wp := by
  unfold sdaQbox universalCounterfactual; decide

/-! ### IE structure (paper eqn 66 p. 206)

The maximal-false-assignment subsets of `sdaALT` (consistent with the
prejacent) are `{sdaPbox, sdaPandQbox}` and `{sdaQbox, sdaPandQbox}`,
yielding `IE(prejacent, sdaALT) = {sdaPandQbox}`. The proofs adapt §3's
FC pattern (`permA_not_ie` / `permB_not_ie` / `permAandB_is_ie`) to
conditional-typed alternatives. -/

/-- `sdaPandQbox` is identically false on `SDAWorld`: the unique
    `(p∧q)`-world is `.wpq`, where `r` does not hold, so
    `universalCounterfactual sim (p∧q) r u` fails for every `u`. -/
theorem sdaPandQbox_always_false (u : SDAWorld) : ¬ sdaPandQbox u := by
  unfold sdaPandQbox universalCounterfactual
  intro h
  have hfilter : (Finset.univ.filter (fun v : SDAWorld => sdaP v ∧ sdaQ v))
      = {SDAWorld.wpq} := by
    ext v; cases v <;> simp [sdaP, sdaQ]
  rw [hfilter] at h
  have hwpq_in : SDAWorld.wpq ∈ sdaSim.closestWorlds u {SDAWorld.wpq} := by
    rw [Core.Order.SimilarityOrdering.mem_closestWorlds]
    refine ⟨Finset.mem_singleton.mpr rfl, ?_⟩
    intro w'' hw''
    rw [Finset.mem_singleton] at hw''; subst hw''
    exact Or.inl (sdaSim.closer_refl u SDAWorld.wpq)
  exact h SDAWorld.wpq hwpq_in

/-- The prejacent + the two negated alternatives `sdaQboxᶜ` and
    `sdaPandQboxᶜ` form an MC-set witnessed at `.wp`. This is the
    paper's first maximal-false set (paper eqn 66a-i p. 206), with
    `sdaPbox` notably absent. -/
private theorem mc_set_without_neg_sdaPbox :
    IsMCSet sdaALT sdaPrejacent
      {sdaPrejacent, sdaQboxᶜ, sdaPandQboxᶜ} := by
  constructor
  · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · intro ψ hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl | rfl
      · left; rfl
      · right; exact ⟨sdaQbox, by simp [sdaALT], rfl⟩
      · right; exact ⟨sdaPandQbox, by simp [sdaALT], rfl⟩
    · refine ⟨SDAWorld.wp, fun ψ hψ => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl | rfl
      · exact sdaPrejacent_at_wp
      · exact sdaQbox_false_at_wp
      · exact sdaPandQbox_always_false SDAWorld.wp
  · -- Maximality: any compatible superset is contained in the MC-set
    intro E' hE' hsub ψ hψ'
    rcases hE'.2.1 ψ hψ' with rfl | ⟨a, ha, rfl⟩
    · exact Set.mem_insert _ _
    · simp only [sdaALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · -- ψ = sdaPorQboxᶜ: contradicts sdaPrejacent ∈ E'
        exfalso
        obtain ⟨u, hu⟩ := hE'.2.2
        exact hu sdaPorQboxᶜ hψ' (hu sdaPrejacent (hsub (Set.mem_insert _ _)))
      · -- ψ = sdaPboxᶜ: must show this is impossible. The witness u must
        -- satisfy sdaPrejacent (≡ sdaPorQbox) AND sdaQboxᶜ AND sdaPboxᶜ.
        -- But (p∨q)□→r ∧ ¬(p□→r) ∧ ¬(q□→r) is unsatisfiable (every
        -- closest (p∨q)-world is a closest p-world or closest q-world).
        exfalso
        obtain ⟨u, hu⟩ := hE'.2.2
        have hPrej : sdaPrejacent u :=
          hu sdaPrejacent (hsub (Set.mem_insert _ _))
        have hNotP : ¬ sdaPbox u := hu sdaPboxᶜ hψ'
        have hNotQ : ¬ sdaQbox u :=
          hu sdaQboxᶜ (hsub (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        revert hPrej hNotP hNotQ
        cases u <;>
          unfold sdaPrejacent sdaPorQbox sdaPbox sdaQbox universalCounterfactual <;>
          decide
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

/-- Symmetric MC-set: prejacent + `sdaPboxᶜ` + `sdaPandQboxᶜ`,
    witnessed at `.wq`. Paper eqn 66a-ii p. 206. -/
private theorem mc_set_without_neg_sdaQbox :
    IsMCSet sdaALT sdaPrejacent
      {sdaPrejacent, sdaPboxᶜ, sdaPandQboxᶜ} := by
  constructor
  · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · intro ψ hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl | rfl
      · left; rfl
      · right; exact ⟨sdaPbox, by simp [sdaALT], rfl⟩
      · right; exact ⟨sdaPandQbox, by simp [sdaALT], rfl⟩
    · refine ⟨SDAWorld.wq, fun ψ hψ => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl | rfl
      · exact sdaPrejacent_at_wq
      · exact sdaPbox_false_at_wq
      · exact sdaPandQbox_always_false SDAWorld.wq
  · intro E' hE' hsub ψ hψ'
    rcases hE'.2.1 ψ hψ' with rfl | ⟨a, ha, rfl⟩
    · exact Set.mem_insert _ _
    · simp only [sdaALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exfalso
        obtain ⟨u, hu⟩ := hE'.2.2
        exact hu sdaPorQboxᶜ hψ' (hu sdaPrejacent (hsub (Set.mem_insert _ _)))
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exfalso
        obtain ⟨u, hu⟩ := hE'.2.2
        have hPrej : sdaPrejacent u :=
          hu sdaPrejacent (hsub (Set.mem_insert _ _))
        have hNotP : ¬ sdaPbox u :=
          hu sdaPboxᶜ (hsub (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        have hNotQ : ¬ sdaQbox u := hu sdaQboxᶜ hψ'
        revert hPrej hNotP hNotQ
        cases u <;>
          unfold sdaPrejacent sdaPorQbox sdaPbox sdaQbox universalCounterfactual <;>
          decide
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

theorem sdaPrejacent_not_ie :
    ¬ IsInnocentlyExcludable sdaALT sdaPrejacent sdaPorQbox := by
  apply not_isInnocentlyExcludable_of_phi_subset
  · exact (Set.Finite.insert _ (Set.Finite.insert _
      (Set.Finite.insert _ (Set.finite_singleton _))))
  · exact ⟨.actual, sdaPrejacent_at_actual⟩
  · rfl

/-- `sdaPbox` is **not** innocently excludable: the MC-set
    `{prejacent, sdaQboxᶜ, sdaPandQboxᶜ}` does not contain
    `sdaPboxᶜ`. -/
theorem sdaPbox_not_ie :
    ¬ IsInnocentlyExcludable sdaALT sdaPrejacent sdaPbox := by
  refine mc_set_without_neg_sdaPbox.not_isInnocentlyExcludable_of_compl_notMem ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨?_, ?_, ?_⟩
  · -- sdaPboxᶜ ≠ sdaPrejacent: differ at .actual (prejacent T, sdaPboxᶜ F)
    intro h
    have heq := congrFun h SDAWorld.actual
    simp only [eq_iff_iff] at heq
    exact (heq.mpr sdaPrejacent_at_actual) sdaPbox_at_actual
  · -- sdaPboxᶜ ≠ sdaQboxᶜ: differ at .wp (sdaPboxᶜ F, sdaQboxᶜ T)
    intro h
    have heq := congrFun h SDAWorld.wp
    simp only [eq_iff_iff] at heq
    exact (heq.mpr sdaQbox_false_at_wp) sdaPbox_at_wp
  · -- sdaPboxᶜ ≠ sdaPandQboxᶜ: sdaPandQboxᶜ T everywhere; sdaPboxᶜ F at .wp
    intro h
    have heq := congrFun h SDAWorld.wp
    simp only [eq_iff_iff] at heq
    exact (heq.mpr (sdaPandQbox_always_false SDAWorld.wp)) sdaPbox_at_wp

/-- `sdaQbox` is **not** innocently excludable (symmetric to `sdaPbox`). -/
theorem sdaQbox_not_ie :
    ¬ IsInnocentlyExcludable sdaALT sdaPrejacent sdaQbox := by
  refine mc_set_without_neg_sdaQbox.not_isInnocentlyExcludable_of_compl_notMem ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have heq := congrFun h SDAWorld.actual
    simp only [eq_iff_iff] at heq
    exact (heq.mpr sdaPrejacent_at_actual) sdaQbox_at_actual
  · intro h
    have heq := congrFun h SDAWorld.wq
    simp only [eq_iff_iff] at heq
    exact (heq.mpr sdaPbox_false_at_wq) sdaQbox_at_wq
  · intro h
    have heq := congrFun h SDAWorld.wq
    simp only [eq_iff_iff] at heq
    exact (heq.mpr (sdaPandQbox_always_false SDAWorld.wq)) sdaQbox_at_wq

/-- `sdaPandQbox` IS innocently excludable: since `sdaPandQbox` is
    identically false on `SDAWorld`, `sdaPandQboxᶜ` holds at every
    world, so adjoining it to any MC-set keeps it consistent —
    maximality forces inclusion. -/
theorem sdaPandQbox_is_ie :
    IsInnocentlyExcludable sdaALT sdaPrejacent sdaPandQbox := by
  apply IsInnocentlyExcludable.of_extension_consistent
  · simp [sdaALT]
  · intro E hE
    obtain ⟨u₀, hu₀⟩ := hE.1.2.2
    refine ⟨u₀, ?_⟩
    intro ψ hψ
    rcases hψ with hψE | hψS
    · exact hu₀ ψ hψE
    · rw [Set.mem_singleton_iff] at hψS
      rw [hψS]
      exact sdaPandQbox_always_false u₀

/-- **Cell witness for the SDA alternative set.** The `.actual` world
    verifies `cell sdaALT sdaPrejacent`: it satisfies the prejacent
    plus the two non-IE conditional alternatives (`sdaPbox`, `sdaQbox`)
    and falsifies the unique IE alternative (`sdaPandQbox`). Once the
    IE-structure proofs above are complete, this follows from the
    per-alternative verdicts at `.actual`. -/
theorem actual_in_sda_cell : cell sdaALT sdaPrejacent .actual := by
  refine ⟨sdaPrejacent_at_actual, ?_, ?_⟩
  · intro q hq
    have hqAlt : q ∈ sdaALT := hq.1
    simp only [sdaALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hqAlt
    rcases hqAlt with rfl | rfl | rfl | rfl
    · exact absurd hq sdaPrejacent_not_ie
    · exact absurd hq sdaPbox_not_ie
    · exact absurd hq sdaQbox_not_ie
    · exact sdaPandQbox_false_at_actual
  · rintro r ⟨hrAlt, hrNotIE⟩
    simp only [sdaALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hrAlt
    rcases hrAlt with rfl | rfl | rfl | rfl
    · exact sdaPrejacent_at_actual
    · exact sdaPbox_at_actual
    · exact sdaQbox_at_actual
    · exact absurd sdaPandQbox_is_ie hrNotIE

/-- **Bar-Lev/Fox SDA derivation** (paper eqn 67 p. 206).
    `Exh^{IE+II}((p∨q)□→r)` entails `(p□→r) ∧ (q□→r) ∧ ¬((p∧q)□→r)`.
    Three one-shot applications of the substrate-level cell-witness
    factorization theorems (`Operators/InnocentInclusion.lean`):
    `exhIEII_implies_cell_witnessed_alt` for the two non-IE
    conditionals (witnessed at `.actual`), and
    `exhIEII_negates_excludable` for the unique IE alternative. -/
theorem bar_lev_fox_sda :
    ∀ w, exhIEII sdaALT sdaPrejacent w →
      sdaPbox w ∧ sdaQbox w ∧ ¬ sdaPandQbox w := fun w h_exh =>
  ⟨exhIEII_implies_cell_witnessed_alt sdaALT sdaPrejacent
      (by simp [sdaALT]) .actual actual_in_sda_cell sdaPbox_at_actual w h_exh,
   exhIEII_implies_cell_witnessed_alt sdaALT sdaPrejacent
      (by simp [sdaALT]) .actual actual_in_sda_cell sdaQbox_at_actual w h_exh,
   exhIEII_negates_excludable sdaALT sdaPrejacent sdaPandQbox_is_ie w h_exh⟩

end SDA

-- ============================================================================
-- §7. Cross-framework agreement: Bar-Lev/Fox SDA vs Santorio's `sdaEval`
-- ============================================================================

/-!
## The central debate Zani-Ciardelli-Sanfelici 2026 frames

[santorio-2018] derives SDA via per-alternative homogeneity
(`sdaEval` = universal over per-disjunct counterfactuals).
[bar-lev-fox-2020] derives SDA via Innocent Inclusion
(`exhIEII` over disjunct-replacement alternatives, asserting the
non-IE conditional alternatives). The two mechanisms are RIVAL but
they AGREE on the SDA inference proper:

   `(p∨q)□→r  ⊨  (p□→r) ∧ (q□→r)`

This agreement is the substrate for [zani-ciardelli-sanfelici-2026]'s
acquisition study, which contrasts the two frameworks' predicted
developmental trajectories (Bar-Lev/Fox: AR→SDA; Santorio: DCR→SDA).
The cross-mechanism agreement theorem below makes this Lean-checkable.

Bar-Lev/Fox's full verdict additionally entails `¬((p∧q)□→r)` (the
IE-driven negation of the conjunctive alternative); Santorio's
`sdaEval` does not entail this. So Bar-Lev/Fox is STRICTLY STRONGER
than Santorio on this scenario — they agree on SDA, diverge on the
extra negative conjunct.
-/

open Santorio2018

/-- The SDA alternatives as `DecAlt SDAWorld`s for use in
    [santorio-2018]'s `sdaEval` apparatus. -/
def sdaSantorioAlts : List (DecAlt SDAWorld) :=
  [⟨sdaP, inferInstance⟩, ⟨sdaQ, inferInstance⟩]

/-- **Cross-framework agreement on the SDA inference.**
    [bar-lev-fox-2020]'s `Exh^{IE+II}` verdict on the SDA prejacent
    entails [santorio-2018]'s `sdaEval` verdict on the same scenario.

    Direct application of the substrate-level multi-target cell-witness
    factorization `exhIEII_implies_cell_witnessed_alts` to the list of
    Santorio-style disjunct conditionals `[sdaPbox, sdaQbox]`. The
    factorization captures the abstract structural fact (any
    cell-witnessed alternatives are jointly entailed by `Exh^{IE+II}`);
    the bridge to `sdaEval` is mechanical via `sdaEval_iff_forall`.
    Santorio is silent on the negative conjunct
    `¬((p∧q)□→r)` that Bar-Lev/Fox additionally derives — they coincide
    on the SDA inference proper, diverge on the negative component. -/
theorem bar_lev_fox_sda_implies_santorio_sda_inference :
    ∀ w, exhIEII sdaALT sdaPrejacent w →
      sdaEval sdaSim sdaSantorioAlts sdaR w := by
  intro w h
  have h_targets := exhIEII_implies_cell_witnessed_alts sdaALT sdaPrejacent
    [sdaPbox, sdaQbox]
    (by intros t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> simp [sdaALT])
    .actual actual_in_sda_cell
    (by intros t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact sdaPbox_at_actual
        · exact sdaQbox_at_actual)
    w h
  rw [sdaEval_iff_forall]
  intro a ha
  simp only [sdaSantorioAlts, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h_targets sdaPbox (by simp)
  · exact h_targets sdaQbox (by simp)

-- ============================================================================
-- §8. Universal Free Choice (paper §6.1 pp. 201–203)
-- ============================================================================

/-!
## ◇∀x(Px ∨ Qx) ⊨ ◇∀xPx ∧ ◇∀xQx — second application of `Exh^{IE+II}`

[bar-lev-fox-2020] §6.1 derives **universal free choice** by
applying `Exh^{IE+II}` to a counterfactual prejacent `◇∀x(Px ∨ Qx)`
over the 8-element alternative set obtained by replacing both the
universal quantifier and the disjunction (eqn 55 p. 202):

  Alt(◇∀x(P∨Q)) = {◇∀x(P∨Q), ◇∀xP, ◇∀xQ, ◇∀x(P∧Q),
                   ◇∃x(P∨Q), ◇∃xP, ◇∃xQ, ◇∃x(P∧Q)}

The maximal-false-assignment subsets (eqn 56 p. 202) are three:
- (i)   {◇∀xP, ◇∀xQ, ◇∀x(P∧Q), ◇∃x(P∧Q)} — witnessed at `wMixed`
- (ii)  {◇∀xP, ◇∃xP, ◇∀x(P∧Q), ◇∃x(P∧Q)} — witnessed at `wAllQ`
- (iii) {◇∀xQ, ◇∃xQ, ◇∀x(P∧Q), ◇∃x(P∧Q)} — witnessed at `wAllP`

yielding `IE = {◇∀x(P∧Q), ◇∃x(P∧Q)}`. Innocent Inclusion then asserts
the six non-IE alternatives, giving Bar-Lev/Fox's verdict (eqn 57 p. 202):

  Exh^{IE+II}(◇∀x(P∨Q)) ⇔ ◇∀xP ∧ ◇∀xQ ∧ ¬◇∃x(P∧Q)

This is the **second consumer** of the substrate factorization
theorems `exhIEII_implies_cell_witnessed_alt` and
`exhIEII_negates_excludable` added in
`Semantics/Exhaustification/Operators/InnocentInclusion.lean`.
The cell witness `wAllP_AllQ` realizes simultaneous accessibility of
the all-P and all-Q scenarios with no overlap-scenario; the main
theorem follows in 3 substrate-application lines.
-/

section UniversalFC

/-- Worlds for the universal-FC toy model. Each world represents the
    set of accessible scenarios from the evaluation point — abstract
    enough to validate the 8-alternative IE structure of paper eqn 55
    p. 202. -/
inductive UnivFCWorld where
  | wAllP : UnivFCWorld         -- only the all-P scenario accessible
  | wAllQ : UnivFCWorld         -- only the all-Q scenario accessible
  | wMixed : UnivFCWorld        -- only the mixed (some-P, some-Q, no overlap) scenario accessible
  | wAllP_AllQ : UnivFCWorld    -- all-P AND all-Q scenarios accessible (cell witness)
  | wInaccessible : UnivFCWorld -- nothing accessible
  deriving DecidableEq, Repr, Inhabited

instance : Fintype UnivFCWorld where
  elems := {.wAllP, .wAllQ, .wMixed, .wAllP_AllQ, .wInaccessible}
  complete x := by cases x <;> decide

/-! ### The 8 alternative predicates per paper eqn (55) p. 202 -/

/-- ◇∀x(P∨Q) — the prejacent: some accessible scenario has every
    individual reading at least one of P, Q. -/
def univFcAllPorQ : Set UnivFCWorld
  | .wAllP => True | .wAllQ => True | .wMixed => True
  | .wAllP_AllQ => True | .wInaccessible => False

/-- ◇∀xP — some accessible scenario has every individual reading P. -/
def univFcAllP : Set UnivFCWorld
  | .wAllP => True | .wAllP_AllQ => True
  | .wAllQ => False | .wMixed => False | .wInaccessible => False

/-- ◇∀xQ — some accessible scenario has every individual reading Q. -/
def univFcAllQ : Set UnivFCWorld
  | .wAllQ => True | .wAllP_AllQ => True
  | .wAllP => False | .wMixed => False | .wInaccessible => False

/-- ◇∀x(P∧Q) — some accessible scenario has every individual reading
    both. None of our worlds witness an all-both scenario. -/
def univFcAllBoth : Set UnivFCWorld := fun _ => False

/-- ◇∃x(P∨Q) — some accessible scenario has some individual reading
    at least one. -/
def univFcSomePorQ : Set UnivFCWorld
  | .wInaccessible => False | _ => True

/-- ◇∃xP — some accessible scenario has some individual reading P. -/
def univFcSomeP : Set UnivFCWorld
  | .wAllP => True | .wMixed => True | .wAllP_AllQ => True
  | .wAllQ => False | .wInaccessible => False

/-- ◇∃xQ — some accessible scenario has some individual reading Q. -/
def univFcSomeQ : Set UnivFCWorld
  | .wAllQ => True | .wMixed => True | .wAllP_AllQ => True
  | .wAllP => False | .wInaccessible => False

/-- ◇∃x(P∧Q) — some accessible scenario has some individual reading
    both. None of our worlds witness an overlap scenario. -/
def univFcSomeBoth : Set UnivFCWorld := fun _ => False

/-- The 8-element alternative set per paper eqn (55) p. 202. -/
def universalFcALT : Set (Set UnivFCWorld) :=
  {univFcAllPorQ, univFcAllP, univFcAllQ, univFcAllBoth,
   univFcSomePorQ, univFcSomeP, univFcSomeQ, univFcSomeBoth}

/-- The universal-FC prejacent. -/
def universalFcPrejacent : Set UnivFCWorld := univFcAllPorQ

/-! ### Per-world verdicts at the cell witness `wAllP_AllQ`

Established by direct case analysis. The cell witness satisfies the
prejacent + every non-IE alternative; the two IE alternatives
(`univFcAllBoth`, `univFcSomeBoth`) are identically false on this
toy model. -/

theorem universalFcPrejacent_at_witness :
    universalFcPrejacent .wAllP_AllQ := trivial
theorem univFcAllP_at_witness : univFcAllP .wAllP_AllQ := trivial
theorem univFcAllQ_at_witness : univFcAllQ .wAllP_AllQ := trivial
theorem univFcSomePorQ_at_witness : univFcSomePorQ .wAllP_AllQ := trivial
theorem univFcSomeP_at_witness : univFcSomeP .wAllP_AllQ := trivial
theorem univFcSomeQ_at_witness : univFcSomeQ .wAllP_AllQ := trivial

theorem univFcAllBoth_always_false (u : UnivFCWorld) :
    ¬ univFcAllBoth u := id
theorem univFcSomeBoth_always_false (u : UnivFCWorld) :
    ¬ univFcSomeBoth u := id

/-! ### Finset-side alternative set + bridge to Set side

For decidability of cell membership and IE-ness, work with Finset
versions of the 8 alternatives. Bridge equations to the Set side let
the general substrate theorems
(`Operators/InnocentInclusion.lean::mem_II_of_cell_witness`,
`not_isInnocentlyExcludable_of_cell_witness`) consume Finset-derived
facts via `decide`. -/

/-- Finset version of `univFcAllPorQ`. -/
def univFcAllPorQ_f : Finset UnivFCWorld :=
  {.wAllP, .wAllQ, .wMixed, .wAllP_AllQ}
def univFcAllP_f : Finset UnivFCWorld := {.wAllP, .wAllP_AllQ}
def univFcAllQ_f : Finset UnivFCWorld := {.wAllQ, .wAllP_AllQ}
def univFcAllBoth_f : Finset UnivFCWorld := ∅
def univFcSomePorQ_f : Finset UnivFCWorld :=
  {.wAllP, .wAllQ, .wMixed, .wAllP_AllQ}
def univFcSomeP_f : Finset UnivFCWorld :=
  {.wAllP, .wMixed, .wAllP_AllQ}
def univFcSomeQ_f : Finset UnivFCWorld :=
  {.wAllQ, .wMixed, .wAllP_AllQ}
def univFcSomeBoth_f : Finset UnivFCWorld := ∅

/-- The 8-element alternative set (Finset-typed) per paper eqn (55) p. 202. -/
def universalFcALT_f : Finset (Finset UnivFCWorld) :=
  {univFcAllPorQ_f, univFcAllP_f, univFcAllQ_f, univFcAllBoth_f,
   univFcSomePorQ_f, univFcSomeP_f, univFcSomeQ_f, univFcSomeBoth_f}

/-- The Finset-side prejacent. -/
def universalFcPrejacent_f : Finset UnivFCWorld := univFcAllPorQ_f

/-! ### Per-alt Set/Finset bridge equations -/

theorem univFcAllPorQ_eq : univFcAllPorQ = ↑univFcAllPorQ_f := by
  ext w; show univFcAllPorQ w ↔ w ∈ univFcAllPorQ_f
  cases w <;> simp [univFcAllPorQ, univFcAllPorQ_f]
theorem univFcAllP_eq : univFcAllP = ↑univFcAllP_f := by
  ext w; show univFcAllP w ↔ w ∈ univFcAllP_f
  cases w <;> simp [univFcAllP, univFcAllP_f]
theorem univFcAllQ_eq : univFcAllQ = ↑univFcAllQ_f := by
  ext w; show univFcAllQ w ↔ w ∈ univFcAllQ_f
  cases w <;> simp [univFcAllQ, univFcAllQ_f]
theorem univFcAllBoth_eq : univFcAllBoth = ↑univFcAllBoth_f := by
  ext w; show univFcAllBoth w ↔ w ∈ univFcAllBoth_f
  cases w <;> simp [univFcAllBoth, univFcAllBoth_f]
theorem univFcSomePorQ_eq : univFcSomePorQ = ↑univFcSomePorQ_f := by
  ext w; show univFcSomePorQ w ↔ w ∈ univFcSomePorQ_f
  cases w <;> simp [univFcSomePorQ, univFcSomePorQ_f]
theorem univFcSomeP_eq : univFcSomeP = ↑univFcSomeP_f := by
  ext w; show univFcSomeP w ↔ w ∈ univFcSomeP_f
  cases w <;> simp [univFcSomeP, univFcSomeP_f]
theorem univFcSomeQ_eq : univFcSomeQ = ↑univFcSomeQ_f := by
  ext w; show univFcSomeQ w ↔ w ∈ univFcSomeQ_f
  cases w <;> simp [univFcSomeQ, univFcSomeQ_f]
theorem univFcSomeBoth_eq : univFcSomeBoth = ↑univFcSomeBoth_f := by
  ext w; show univFcSomeBoth w ↔ w ∈ univFcSomeBoth_f
  cases w <;> simp [univFcSomeBoth, univFcSomeBoth_f]

/-- ALT-level bridge: the Set-typed `universalFcALT` equals the
    `asSetOfSets` image of the Finset-typed `universalFcALT_f`. Lifts
    Finset-side membership facts to the Set-side substrate theorems. -/
theorem universalFcALT_eq :
    universalFcALT = Exhaustification.Innocent.asSetOfSets universalFcALT_f := by
  rw [universalFcALT, univFcAllPorQ_eq, univFcAllP_eq, univFcAllQ_eq,
      univFcAllBoth_eq, univFcSomePorQ_eq, univFcSomeP_eq,
      univFcSomeQ_eq, univFcSomeBoth_eq]
  ext s
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
    Exhaustification.Innocent.mem_asSetOfSets, universalFcALT_f,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals (
      first
        | exact ⟨univFcAllPorQ_f, Or.inl rfl, rfl⟩
        | exact ⟨univFcAllP_f, Or.inr (Or.inl rfl), rfl⟩
        | exact ⟨univFcAllQ_f, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
        | exact ⟨univFcAllBoth_f, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
        | exact ⟨univFcSomePorQ_f,
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
        | exact ⟨univFcSomeP_f,
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), rfl⟩
        | exact ⟨univFcSomeQ_f,
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), rfl⟩
        | exact ⟨univFcSomeBoth_f,
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), rfl⟩)
  · rintro ⟨a, ha, rfl⟩
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; left; rfl
    · right; right; right; right; left; rfl
    · right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; rfl

/-- Prejacent bridge. -/
theorem universalFcPrejacent_eq :
    universalFcPrejacent = (↑universalFcPrejacent_f : Set UnivFCWorld) :=
  univFcAllPorQ_eq

/-! ### Cell witness via Finset bridge -/

set_option maxRecDepth 2000 in
/-- **Cell witness for the universal-FC alternative set** (paper eqn
    56 p. 202 cell). `wAllP_AllQ` is in the cell. Proof: `decide`-
    checkable on the Finset side (`Operators/Decidable.lean::cellFinset`);
    lifted to Set via `mem_cellFinset_iff` + `universalFcALT_eq` /
    `universalFcPrejacent_eq`. Replaces ~250 LOC of manual MC-set +
    IE-structure proofs from earlier versions. -/
theorem wAllP_AllQ_in_universal_fc_cell :
    cell universalFcALT universalFcPrejacent UnivFCWorld.wAllP_AllQ := by
  rw [universalFcALT_eq, universalFcPrejacent_eq]
  exact (Exhaustification.Innocent.mem_cellFinset_iff
    universalFcALT_f universalFcPrejacent_f UnivFCWorld.wAllP_AllQ).mp (by decide)

/-! ### Innocent excludability theorems (cell-witness corollaries) -/

theorem universalFcPrejacent_not_ie :
    ¬ IsInnocentlyExcludable universalFcALT universalFcPrejacent univFcAllPorQ :=
  not_isInnocentlyExcludable_of_phi_subset
    (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
      (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
      (Set.Finite.insert _ (Set.finite_singleton _))))))))
    ⟨UnivFCWorld.wAllP_AllQ, universalFcPrejacent_at_witness⟩
    (Set.Subset.refl _)

theorem univFcAllP_not_ie :
    ¬ IsInnocentlyExcludable universalFcALT universalFcPrejacent univFcAllP :=
  not_isInnocentlyExcludable_of_cell_witness universalFcALT universalFcPrejacent
    UnivFCWorld.wAllP_AllQ wAllP_AllQ_in_universal_fc_cell univFcAllP_at_witness

theorem univFcAllQ_not_ie :
    ¬ IsInnocentlyExcludable universalFcALT universalFcPrejacent univFcAllQ :=
  not_isInnocentlyExcludable_of_cell_witness universalFcALT universalFcPrejacent
    UnivFCWorld.wAllP_AllQ wAllP_AllQ_in_universal_fc_cell univFcAllQ_at_witness

theorem univFcSomePorQ_not_ie :
    ¬ IsInnocentlyExcludable universalFcALT universalFcPrejacent univFcSomePorQ :=
  not_isInnocentlyExcludable_of_cell_witness universalFcALT universalFcPrejacent
    UnivFCWorld.wAllP_AllQ wAllP_AllQ_in_universal_fc_cell univFcSomePorQ_at_witness

theorem univFcSomeP_not_ie :
    ¬ IsInnocentlyExcludable universalFcALT universalFcPrejacent univFcSomeP :=
  not_isInnocentlyExcludable_of_cell_witness universalFcALT universalFcPrejacent
    UnivFCWorld.wAllP_AllQ wAllP_AllQ_in_universal_fc_cell univFcSomeP_at_witness

theorem univFcSomeQ_not_ie :
    ¬ IsInnocentlyExcludable universalFcALT universalFcPrejacent univFcSomeQ :=
  not_isInnocentlyExcludable_of_cell_witness universalFcALT universalFcPrejacent
    UnivFCWorld.wAllP_AllQ wAllP_AllQ_in_universal_fc_cell univFcSomeQ_at_witness

/-- `univFcAllBoth` IS innocently excludable: identically false on
    `UnivFCWorld`, so its negation is trivially consistent with any
    MC-set; maximality forces inclusion. -/
theorem univFcAllBoth_is_ie :
    IsInnocentlyExcludable universalFcALT universalFcPrejacent univFcAllBoth := by
  apply IsInnocentlyExcludable.of_extension_consistent
  · simp [universalFcALT]
  · intro E hE
    obtain ⟨u₀, hu₀⟩ := hE.1.2.2
    refine ⟨u₀, ?_⟩
    intro ψ hψ
    rcases hψ with hψE | hψS
    · exact hu₀ ψ hψE
    · rw [Set.mem_singleton_iff] at hψS
      rw [hψS]
      exact univFcAllBoth_always_false u₀

/-- `univFcSomeBoth` IS innocently excludable (parallel to AllBoth). -/
theorem univFcSomeBoth_is_ie :
    IsInnocentlyExcludable universalFcALT universalFcPrejacent univFcSomeBoth := by
  apply IsInnocentlyExcludable.of_extension_consistent
  · simp [universalFcALT]
  · intro E hE
    obtain ⟨u₀, hu₀⟩ := hE.1.2.2
    refine ⟨u₀, ?_⟩
    intro ψ hψ
    rcases hψ with hψE | hψS
    · exact hu₀ ψ hψE
    · rw [Set.mem_singleton_iff] at hψS
      rw [hψS]
      exact univFcSomeBoth_always_false u₀

/-- **Bar-Lev/Fox universal free choice** (paper eqn 57 p. 202).
    `Exh^{IE+II}(◇∀x(P∨Q)) ⊨ ◇∀xP ∧ ◇∀xQ ∧ ¬◇∃x(P∧Q)`.

    Three one-shot applications of the substrate-level cell-witness
    factorization theorems: `exhIEII_implies_cell_witnessed_alt` for
    the two universal-distributive non-IE alternatives, and
    `exhIEII_negates_excludable` for the existential-conjunctive IE
    alternative. The substrate factorization (`Semantics/
    Exhaustification/Operators/InnocentInclusion.lean`) is what makes
    this main theorem a 3-line consequence of the cell witness. -/
theorem universal_fc :
    ∀ w, exhIEII universalFcALT universalFcPrejacent w →
      univFcAllP w ∧ univFcAllQ w ∧ ¬ univFcSomeBoth w := fun w h_exh =>
  ⟨exhIEII_implies_cell_witnessed_alt universalFcALT universalFcPrejacent
      (by simp [universalFcALT]) .wAllP_AllQ wAllP_AllQ_in_universal_fc_cell
      univFcAllP_at_witness w h_exh,
   exhIEII_implies_cell_witnessed_alt universalFcALT universalFcPrejacent
      (by simp [universalFcALT]) .wAllP_AllQ wAllP_AllQ_in_universal_fc_cell
      univFcAllQ_at_witness w h_exh,
   exhIEII_negates_excludable universalFcALT universalFcPrejacent
      univFcSomeBoth_is_ie w h_exh⟩

end UniversalFC

end BarLevFox2020
