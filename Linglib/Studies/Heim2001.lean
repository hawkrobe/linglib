import Linglib.Studies.Kennedy1999
import Linglib.Semantics.Degree.Quantifier
import Linglib.Syntax.Minimalist.Movement.DegreeMovement
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Heim 2001: Degree Operators and Scope
[heim-2001] [heim-1999] [kennedy-1999] [percus-2000]
[von-stechow-1984] [fox-hackl-2006] [schwarzschild-wilkinson-2002]
[beck-2001] [kennedy-mcnally-2005] [szabolcsi-1986]

Irene Heim. Degree Operators and Scope. In C. Féry & W. Sternefeld (eds.),
*Audiatur Vox Sapientiae*, Akademie Verlag, pp. 214–239.

## Headline

Heim's central §2.1 observation — that the high-DegP and low-DegP LFs for
↑monotone operators are truth-conditionally equivalent — reduces to two
lattice identities:

* `sSup (⋃ᵢ Iic (μ i)) = ⨆ᵢ μ i`   (mathlib's `sSup_iUnion_Iic`)
* `sSup (⋂ᵢ Iic (μ i)) = ⨅ᵢ μ i`   (`sSup_iInter_Iic_eq_iInf` below)

Heim's max-set semantics for `-er` (paper exs. (5)–(6)) computes the high-DegP
truth condition as `sSup (matrixSet) > threshold`. The lattice identities
reduce this to the low-DegP threshold form (with an attainment caveat for
the ∀ direction; see `heim_collapse_forall_low_to_high`, paper fn. 6).

For the negation case (paper exs. 17–19), `no_isGreatest_Ioi_of_noMaxOrder`
shows the high-DegP LF is undefined: the negated degree set `Ioi (μ a)` has
no greatest element on any `NoMaxOrder` scale. This is the same mechanism
behind [fox-hackl-2006] negative islands.

Kennedy's generalization (paper ex. (27)) is formalized via the
Heim-Kennedy Constraint substrate
(`Syntax/Minimalist/DegreeMovement.lean`),
re-exported below.

## Section map

| Paper                                | This file                                    |
|--------------------------------------|----------------------------------------------|
| §2.1 monotone collapse (8–16)        | `heim_collapse_exists`, `heim_collapse_forall_*` |
| §2.1 negation (17–19)                | `no_isGreatest_Ioi_of_noMaxOrder`, `negation_high_DegP_undefined` |
| §2.2 Kennedy's generalization (20–27) | `nonMonotone_blocked_by_HKC`                |
| §2.3 intensional verbs (28–36)       | `intensionalVerbData` + `BhattPancheva2004` HKC bridge |
| §2.4 Russell ambiguity (37–42)       | docstring only — see `VonStechow1984.lean`   |
| §3.2 semantic ellipsis (58–64)       | reference to `Degree.absoluteSuperlative` |

## What this file does NOT formalize

- **Heim's free-world-variable implementation of de re/de dicto**
  (paper §2.4, ex. (40); Percus-style binding per [percus-2000] and
  Abusch 1994 — paper fn. 16). The substrate's
  `Semantics/Degree/Intensional.lean` formalizes the alternative
  ACTUALLY-operator implementation (von Stechow 1984), used in
  `VonStechow1984.lean`. The two implementations agree on the diagnosis
  (Russell ambiguity is de re/de dicto, not DegP-scope) but differ on the
  LF mechanism.
- **Typed ⟨dt,t⟩ DegP-as-generalized-quantifier denotations** over
  arbitrary degree predicates. For monotone adjectives the max-set
  computation reduces to the substrate's measure-function comparative
  `Degree.comparativeSem` (via `isGreatest_Iic`).

## Recent literature this file does not engage

- [schwarzschild-wilkinson-2002] interval semantics, which Heim's
  own fn. 21 flags as work that may force her to revise basic assumptions
- [beck-2001] intervention effects, parallel to Kennedy's generalization
- [kennedy-mcnally-2005] closed-scale adjective behavior under negation

-/

namespace Heim2001

open Set
open Degree (comparativeSem)
open Minimalist.DegreeMovement
  (IsHeimKennedy ScopeBinding not_isHeimKennedy_QP_above_bound_DegP)

/-! ### Degree-scope configurations

Heim's DegP-scope LFs for quantified subjects, and the §2.1 monotone
collapse arguments. -/

/-- Low-DegP for ∀ ("every girl is taller than 4ft"): each restrictor
entity exceeds the threshold. -/
def lowDegP_forall {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) : Prop :=
  ∀ x, restrictor x → μ x > threshold

/-- High-DegP for ∀: the maximal degree to which every restrictor entity
measures exceeds the threshold. -/
def highDegP_forall {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) : Prop :=
  ∃ d, (∀ x, restrictor x → μ x ≥ d) ∧ d > threshold

/-- Low-DegP for ∃: some restrictor entity exceeds the threshold. -/
def lowDegP_exists {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) : Prop :=
  ∃ x, restrictor x ∧ μ x > threshold

/-- High-DegP for ∃: some degree above the threshold is reached by some
restrictor entity. -/
def highDegP_exists {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) : Prop :=
  ∃ d, (∃ x, restrictor x ∧ μ x ≥ d) ∧ d > threshold

/-- Monotone collapse (§2.1), ∀ + more: high-DegP entails low-DegP. -/
theorem forall_more_high_to_low {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) :
    highDegP_forall restrictor μ threshold →
    lowDegP_forall restrictor μ threshold := by
  rintro ⟨d, hall, hgt⟩ x hR
  exact lt_of_lt_of_le hgt (hall x hR)

/-- Monotone collapse (§2.1), ∀ + more: low-DegP entails high-DegP given
a minimal witness. -/
theorem forall_more_low_to_high {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D)
    (w : Entity) (hw : restrictor w)
    (hmin : ∀ x, restrictor x → μ x ≥ μ w) :
    lowDegP_forall restrictor μ threshold →
    highDegP_forall restrictor μ threshold := by
  intro hlow
  exact ⟨μ w, hmin, hlow w hw⟩

/-- Monotone collapse, ∃ + more: the two scope readings coincide. -/
theorem exists_more_scope_collapse {Entity D : Type*} [LinearOrder D]
    (restrictor : Entity → Prop) (μ : Entity → D) (threshold : D) :
    lowDegP_exists restrictor μ threshold ↔
    highDegP_exists restrictor μ threshold := by
  constructor
  · rintro ⟨x, hR, hgt⟩
    exact ⟨μ x, ⟨x, hR, le_refl _⟩, hgt⟩
  · rintro ⟨d, ⟨x, hR, hge⟩, hgt⟩
    exact ⟨x, hR, lt_of_lt_of_le hgt hge⟩

/-- The negated degree predicate `{d : ¬(μ(a) ≥ d)}` — the degrees `a`
lacks (p. 220); extensionally `Set.Ioi (μ a)`. -/
def negatedDegreePredicate {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (a : Entity) (d : D) : Prop :=
  ¬ (μ a ≥ d)

/-- The negated degree set is `Set.Ioi (μ a)`. -/
theorem negatedDegreePredicate_eq {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a : Entity) (d : D) :
    negatedDegreePredicate μ a d ↔ d > μ a := by
  simp [negatedDegreePredicate, not_le]

/-! ### Lattice substrate (the Galois identity) -/

/-- The intersection of principal downsets is the principal downset of the
infimum. Pure order-theoretic fact, dual to mathlib's `iUnion_Iic`. -/
private theorem iInter_Iic_eq_Iic_iInf {α : Type*} [CompleteLattice α]
    {ι : Type*} (f : ι → α) :
    ⋂ i, Iic (f i) = Iic (⨅ i, f i) := by
  ext x; simp [le_iInf_iff]

/-- **`sSup ∘ ⋂ ∘ Iic = ⨅`** on a `CompleteLinearOrder`. The dual of
mathlib's `sSup_iUnion_Iic`. Heim's high-DegP-over-∀ truth condition
reduces to this two-step calculation (`⋂Iic = Iic ⨅`, then `csSup_Iic`). -/
theorem sSup_iInter_Iic_eq_iInf {α : Type*} [CompleteLinearOrder α]
    {ι : Type*} (f : ι → α) :
    sSup (⋂ i, Iic (f i)) = ⨅ i, f i := by
  rw [iInter_Iic_eq_Iic_iInf]; exact csSup_Iic

/-! ### Heim §2.1: monotone collapse (exs 8–16) -/

/-- **Heim §2.1, ∃-side**: high-DegP and low-DegP collapse for existentially
quantified subjects ("Some girl is taller than 4 feet"). Re-export of the
substrate identity; the underlying lattice content is `sSup_iUnion_Iic`:
`sSup (⋃ᵢ Iic (μ i)) > t ↔ ∃ i, μ i > t`. -/
theorem heim_collapse_exists {α D : Type*} [LinearOrder D]
    (R : α → Prop) (μ : α → D) (t : D) :
    lowDegP_exists R μ t ↔ highDegP_exists R μ t :=
  exists_more_scope_collapse R μ t

/-- **Heim §2.1, ∀-side, lattice form**: the high-DegP-over-∀ max-set
`{d | ∀ i, d ≤ μ i}` has truth condition `(⨅ᵢ μ i) > t`. -/
theorem highDegP_forall_lattice {α : Type*} [CompleteLinearOrder α]
    {ι : Type*} (μ : ι → α) (t : α) :
    sSup {d | ∀ i, d ≤ μ i} > t ↔ ⨅ i, μ i > t := by
  have h : {d : α | ∀ i, d ≤ μ i} = ⋂ i, Iic (μ i) := by ext; simp
  rw [h, sSup_iInter_Iic_eq_iInf]

/-- **Heim §2.1, ∀-side collapse, forward direction** (paper p. 218,
discussion of ex. (10)): high-DegP entails low-DegP. Always holds.
Substrate re-export. -/
theorem heim_collapse_forall_high_to_low {α D : Type*} [LinearOrder D]
    (R : α → Prop) (μ : α → D) (t : D) :
    highDegP_forall R μ t → lowDegP_forall R μ t :=
  forall_more_high_to_low R μ t

/-- **Heim §2.1, ∀-side collapse, reverse direction** (paper fn. 6: holds
"whenever these maxima are defined"): low-DegP entails high-DegP given an
attaining witness — the "shortest girl" of Heim's prose. Substrate
re-export. -/
theorem heim_collapse_forall_low_to_high {α D : Type*} [LinearOrder D]
    (R : α → Prop) (μ : α → D) (t : D) (w : α)
    (hw : R w) (hmin : ∀ x, R x → μ x ≥ μ w) :
    lowDegP_forall R μ t → highDegP_forall R μ t :=
  forall_more_low_to_high R μ t w hw hmin

/-! ### Heim §2.1: negation (exs 17–19) -/

/-- **The lattice fact behind Heim's negation argument**: on any
`NoMaxOrder` linear order, the strict upper interval `Ioi a` has no
greatest element. This is the same mechanism behind [fox-hackl-2006]
negative islands. -/
theorem no_isGreatest_Ioi_of_noMaxOrder {α : Type*} [LinearOrder α]
    [NoMaxOrder α] (a : α) :
    ¬ ∃ m, IsGreatest (Ioi a) m := by
  rintro ⟨m, hm, hub⟩
  obtain ⟨n, hn⟩ := exists_gt m
  exact absurd (hub (lt_trans hm hn)) (not_le.mpr hn)

/-- **Heim §2.1, ex. (17c)**: the high-DegP LF for "Mary isn't taller than
4 feet" computes `max{d | ¬ tall(m,d)} > 4` = `max(Ioi (μ m)) > 4`, which
is undefined on any `NoMaxOrder` scale. The high-DegP LF is therefore
ruled out by presupposition failure.

Heim p. 220 generalizes this to `at most n` (ex. 18) and to implicitly
negative verbs like `refuse` (ex. 19) — both classified as
"implicitly negative or monotone decreasing operators", not as
neg-raising verbs (which are §2.3, exs (34)–(36)). -/
theorem negation_high_DegP_undefined {Entity D : Type*} [LinearOrder D]
    [NoMaxOrder D] (μ : Entity → D) (a : Entity) :
    ¬ ∃ m, IsGreatest {d | negatedDegreePredicate μ a d} m := by
  have h : {d | negatedDegreePredicate μ a d} = Ioi (μ a) := by
    ext d
    rw [mem_setOf_eq, negatedDegreePredicate_eq]
    rfl
  rw [h]; exact no_isGreatest_Ioi_of_noMaxOrder (μ a)

/-! ### Heim §2.2: Kennedy's generalization (exs 20–27) -/

/-- **Kennedy's generalization** (paper ex. (27)): "If the scope of a
quantificational DP contains the trace of a DegP, it also contains that
DegP itself." Equivalently: a high-DegP LF in which the QP binds into
the DegP's restrictor is illicit.

Re-export of `not_isHeimKennedy_QP_above_bound_DegP` from the
Minimalism–degree-semantics interface substrate. The exemplar binding
`⟨degHeight := 0, qpHeight := 1, qpBindsDeg := true⟩` covers Heim's
§2.2 examples uniformly: `exactly`-differentials (exs 20, 22),
`less`-comparatives (24), and object-position quantifiers (25).
[bhatt-pancheva-2004] §4 is the dedicated formalization; see
`BhattPancheva2004.bp_hkc_matches_heim_intensional_data`. -/
theorem nonMonotone_blocked_by_HKC (degH qpH : Nat) (h : degH < qpH) :
    ¬ IsHeimKennedy ⟨degH, qpH, qpH, true⟩ :=
  not_isHeimKennedy_QP_above_bound_DegP degH qpH h

/-- The §2.2 examples instantiate `nonMonotone_blocked_by_HKC` at the
exemplar binding `⟨0, 1, 1, true⟩` (high-DegP attempted; QP binds DegP). -/
example : ¬ IsHeimKennedy ⟨0, 1, 1, true⟩ :=
  nonMonotone_blocked_by_HKC 0 1 (by omega)

/-! ### Heim §2.3: intensional verb data (exs 28–36) -/

/-- Heim's classification of intensional verbs by whether they admit the
high-DegP reading with `exactly`-differentials or `less`. Heim presents
this 4-vs-4 split as descriptive, **not** explanatory: paper p. 226
("I am unable to spell out any concrete explanations for the unambiguity
of (33–36), and it is only a hope that it will follow without specific
stipulations about DegP-movement").

[bhatt-pancheva-2004] §5.2 derives the split from the Heim-Kennedy
Constraint plus the assumption that intensional subjects bind into the
degree predicate; see `BhattPancheva2004.bp_hkc_matches_heim_intensional_data`. -/
inductive IntensionalVerbClass where
  /-- Necessity / requirement modals. Heim §2.3 (28), (32b). -/
  | deontic
  /-- Possibility / ability modals. Heim §2.3 (29), (32a). -/
  | possibility
  /-- Epistemic modals: high-DegP unavailable. Heim §2.3 (33). -/
  | epistemic
  /-- Neg-raising verbs (`should`, `supposed-to`, `want`): high-DegP
      unavailable. Heim §2.3 (34)–(36), citing von Fintel & Iatridou
      2001 in fn. 14. (Note: `refuse` from Heim §2.1 ex. (19) is
      *implicitly negative*, **not** neg-raising.) -/
  | negRaising
  deriving DecidableEq, Repr

/-- Per `IntensionalVerbClass`, predict whether high-DegP is admitted. -/
def IntensionalVerbClass.admitsHighDegP : IntensionalVerbClass → Bool
  | .deontic | .possibility => true
  | .epistemic | .negRaising => false

/-- A row of Heim's §2.3 intensional-verb table. -/
structure IntensionalVerbDatum where
  sentence : String
  verb : String
  verbClass : IntensionalVerbClass
  /-- Does the high-DegP reading exist for this verb (with `exactly` or
      `less`)? Determined by `verbClass` (see `verbClass_predicts_highDegPAvailable`). -/
  highDegPAvailable : Bool
  deriving Repr

/-- Heim §2.3, exs. (28)–(36). The 4-vs-4 split is by `verbClass`;
`deontic` and `possibility` admit high-DegP, `epistemic` and `negRaising`
block it. -/
def intensionalVerbData : List IntensionalVerbDatum :=
  [ ⟨"The paper is required to be exactly 5 pages longer than that",
     "require", .deontic, true⟩
  , ⟨"The paper is allowed to be exactly 5 pages longer than that",
     "allow", .possibility, true⟩
  , ⟨"John is able to run less fast than that",
     "be able", .possibility, true⟩
  , ⟨"The paper needs to be exactly 5 pp longer than that",
     "need", .deontic, true⟩
  , ⟨"The paper might be less long than that",
     "might", .epistemic, false⟩
  , ⟨"The paper should be less long than that",
     "should", .negRaising, false⟩
  , ⟨"The paper is supposed to be less long than that",
     "supposed to", .negRaising, false⟩
  , ⟨"I want the paper to be less long than that",
     "want", .negRaising, false⟩
  ]

/-- Per-row drift sentry: each datum's `highDegPAvailable` flag matches
its `verbClass`. Adding/removing a row keeps the witness localized.
Replaces the previous aggregate-count theorem (`length = 4 ∧ length = 4`),
which would silently go stale on any data edit. -/
theorem verbClass_predicts_highDegPAvailable :
    ∀ d ∈ intensionalVerbData,
      d.highDegPAvailable = d.verbClass.admitsHighDegP := by
  intro d hd
  simp only [intensionalVerbData, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ### Heim §2.4: Russell ambiguity ≠ DegP-scope (exs 37–42) -/

-- Heim follows von Stechow 1984's diagnosis: the Russell ambiguity in
-- "John thinks the yacht is longer than it is" arises from de re vs de
-- dicto interpretation of the than-clause, NOT from DegP-movement over
-- `think`.
--
-- Heim's *implementation* of the de re / de dicto distinction (paper
-- exs. (40a/b), p. 228) uses **free world-variables** on than-clause
-- predicates (`long_w'` vs `long_w`), citing [percus-2000] and
-- Abusch 1994 (paper fn. 16). This is distinct from von Stechow 1984's
-- own ACTUALLY-operator implementation, which the substrate
-- (`Semantics/Degree/Intensional.lean`) formalizes — see
-- `VonStechow1984.lean` for the substrate use.
--
-- The two implementations agree on the diagnosis but differ on the LF
-- mechanism. Heim's free-world-variable implementation is not currently
-- in the linglib substrate.

/-! ### Heim §3.2: superlative semantic ellipsis (exs 58–64) -/

-- Heim §3.2 argues that `-est` in "John screamed (the) loudest" uses its
-- complement `R` twice in the semantic calculation (paper ex. (59)),
-- giving evidence for DegP-movement independent of VP-ellipsis. The
-- semantic decomposition `λR. λx. max{d : R(x,d)} > max{d : ∃y ≠ x. R(y,d)}`
-- is formalized as `Degree.absoluteSuperlative`;
-- consumers should reference the substrate definition directly.
--
-- The contrast "Kim climbed the highest mountain" / "KIM climbed the
-- highest mountain" (focus-sensitive relative reading) is from
-- [szabolcsi-1986] / [heim-1999] — *not* from Heim 2001 — and
-- belongs in a future `Heim1999.lean` study file.

end Heim2001
