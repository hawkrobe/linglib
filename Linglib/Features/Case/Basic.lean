import Mathlib.Data.Finset.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.DeriveFintype
import Linglib.Data.UD.Basic

/-!
# Case — the canonical inventory
[blake-1994] [de-marneffe-zeman-2021] [stassen-1985]

The root-namespace `Case` type is the canonical, analytical case
inventory: the values languages' case systems distinguish. All
theoretical machinery — Blake's hierarchy (here), Caha containment
(`Syntax/Case/Order.lean`), syncretism and *ABA
(`Morphology/Case/Allomorphy.lean`), grammaticalization clines
(`Features/Case/Grammaticalization.lean`) — operates over this type.

`UD.Case` (`Data/UD/Basic.lean`) is the *realization* vocabulary — what
corpora annotate — reachable by `toUD`/`fromUD`. The two inventories
currently coincide cell-for-cell, so both round-trips hold; the
analytical inventory is where refinements that UD conflates would land
(e.g. the Latin-type syncretic general ablative and the Finnish
exterior-source ablative both realize as `Abl`), breaking only
`fromUD_toUD` — exactly as `Person.fromUD_toUD` degrades to `coarsen`
under UD's clusivity conflation.

This mirrors the `Person`/`Number`/`Gender` API
(`Features/{Person,Number,Gender}/Basic.lean`): canonical analytical
inventory at root namespace, UD demoted to realization.

## Main declarations

* `Case` — the 28-cell analytical inventory
* `Case.toUD`/`Case.fromUD` — UD realization round-trip
* `Case.hierarchyRank` — Blake's implicational hierarchy
  ([blake-1994], `Fin 7`-codomain rank)
* `Case.IsValidInventory` — inventory contiguity on the hierarchy,
  decidable, with the order-theoretic characterization
  `isValidInventory_iff_ordConnected`
* `Features.AlignmentFamily`, `Features.CaseAssignment`,
  `Features.FixedCaseEncoding` — small per-entry companion enums
-/

set_option autoImplicit false

/-- Grammatical case — the canonical analytical inventory. -/
inductive Case where
  /-- Nominative: citation/subject case. -/
  | nom
  /-- Accusative: direct object. -/
  | acc
  /-- Genitive: possessor, nominal dependent. -/
  | gen
  /-- Dative: indirect object, recipient. -/
  | dat
  /-- Instrumental: means, instrument. -/
  | inst
  /-- Locative: static location (general). -/
  | loc
  /-- Vocative: address form. -/
  | voc
  /-- Ablative: source, motion from (general). -/
  | abl
  /-- Ergative: transitive subject in ergative alignment. -/
  | erg
  /-- Absolutive: intransitive subject / transitive object in ergative
      alignment. -/
  | abs
  /-- Partitive: partial affectedness, indeterminate quantity
      (Finnic). -/
  | part
  /-- Essive: temporary state, capacity ("as an X"). -/
  | ess
  /-- Translative: change of state ("into an X"). -/
  | transl
  /-- Comitative: accompaniment ("with X"). -/
  | com
  /-- Adessive: at/near (exterior static). -/
  | ade
  /-- Inessive: in (interior static). -/
  | ine
  /-- Illative: into (interior goal). -/
  | ill
  /-- Elative: out of (interior source). -/
  | ela
  /-- Allative: onto/towards (exterior goal). -/
  | all
  /-- Sublative: onto (surface goal; Hungarian). -/
  | sub
  /-- Superessive: on (surface static; Hungarian). -/
  | sup
  /-- Delative: off of (surface source; Hungarian). -/
  | del
  /-- Terminative: up to a limit ("as far as X"). -/
  | ter
  /-- Temporal: at a time. -/
  | tem
  /-- Causative/causal: because of X. -/
  | caus
  /-- Benefactive: for the benefit of X. -/
  | ben
  /-- Perlative: path, motion through. -/
  | perl
  /-- Abessive/privative: without X. -/
  | abess
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Case

/-! ### UD realization vocabulary -/

/-- Realize as UD annotation. Currently cell-for-cell; analytical
    refinements that UD conflates collapse here. -/
def toUD : Case → UD.Case
  | .nom => .Nom
  | .acc => .Acc
  | .gen => .Gen
  | .dat => .Dat
  | .inst => .Ins
  | .loc => .Loc
  | .voc => .Voc
  | .abl => .Abl
  | .erg => .Erg
  | .abs => .Abs
  | .part => .Par
  | .ess => .Ess
  | .transl => .Tra
  | .com => .Com
  | .ade => .Ade
  | .ine => .Ine
  | .ill => .Ill
  | .ela => .Ela
  | .all => .All
  | .sub => .Sub
  | .sup => .Sup
  | .del => .Del
  | .ter => .Ter
  | .tem => .Tem
  | .caus => .Cau
  | .ben => .Ben
  | .perl => .Per
  | .abess => .Abe

/-- Analytical value of a UD annotation. -/
def fromUD : UD.Case → Case
  | .Nom => .nom
  | .Acc => .acc
  | .Gen => .gen
  | .Dat => .dat
  | .Ins => .inst
  | .Loc => .loc
  | .Voc => .voc
  | .Abl => .abl
  | .Erg => .erg
  | .Abs => .abs
  | .Par => .part
  | .Ess => .ess
  | .Tra => .transl
  | .Com => .com
  | .Ade => .ade
  | .Ine => .ine
  | .Ill => .ill
  | .Ela => .ela
  | .All => .all
  | .Sub => .sub
  | .Sup => .sup
  | .Del => .del
  | .Ter => .ter
  | .Tem => .tem
  | .Cau => .caus
  | .Ben => .ben
  | .Per => .perl
  | .Abe => .abess

/-- UD round-trips on its own image. -/
@[simp] theorem toUD_fromUD (u : UD.Case) : (fromUD u).toUD = u := by
  cases u <;> rfl

/-- The analytical inventory round-trips through UD — for now. This is
    the theorem that *degrades* (to a `coarsen` identity, as in
    `Person.fromUD_toUD`) when an analytical refinement splits a UD
    cell. -/
@[simp] theorem fromUD_toUD (c : Case) : fromUD c.toUD = c := by
  cases c <;> rfl

/-! ### Blake's case hierarchy [blake-1994]

Implicational hierarchy over case inventories with contiguity checking.
The fine-grained spatial cases all sit at the peripheral spatial tier
(rank 1) since Blake's hierarchy collapses them into a single locative/
spatial group. -/

/-- Position on Blake's case hierarchy ([blake-1994]).

    Higher rank = more likely to exist in a language's case inventory.
    Blake's hierarchy orders NOM/ACC/ERG/ABS > GEN > DAT > LOC >
    ABL/INST and lumps everything below into a single undifferentiated
    "others" tier; the further split of that tier into rank 1
    (COM/ALL/PERL/BEN + fine-grained spatial cases — Finnish/Hungarian
    ADE/INE/ILL/ELA/SUB/SUP/DEL) vs rank 0 (peripheral non-spatial:
    VOC/PART/CAUS/ESS/TRANSL/ABESS/TER/TEM) is this formalization's
    extrapolation, not Blake's.

    Codomain is `Fin 7` — the boundedness is encoded in the type, not as
    a separate `*_bounded` theorem. -/
def hierarchyRank : Case → Fin 7
  | .nom | .acc | .erg | .abs => 6
  | .gen                      => 5
  | .dat                      => 4
  | .loc                      => 3
  | .abl | .inst              => 2
  | .com | .all | .perl | .ben
  | .ade | .ine | .ill | .ela | .sub | .sup | .del => 1
  | .voc | .part | .caus | .ess | .transl | .abess
  | .ter | .tem => 0

/-- An inventory is **contiguous** on Blake's hierarchy: every rank
    between two realized ranks is itself realized. Formalizes Blake's
    implicational tendency ([blake-1994]), in a form `decide` can
    mechanically check; `isValidInventory_iff_ordConnected` is the
    order-theoretic content. -/
def IsValidInventory (inv : Finset Case) : Prop :=
  ∀ r : Fin 7,
    (∃ c ∈ inv, c.hierarchyRank < r) →
    (∃ c ∈ inv, r < c.hierarchyRank) →
    (∃ c ∈ inv, c.hierarchyRank = r)

instance (inv : Finset Case) : Decidable (IsValidInventory inv) := by
  unfold IsValidInventory; infer_instance

/-- **The transfer equation**: inventory validity is order-connectedness
    of the rank image — Blake's implicational tendency is `Icc`-closure
    in `Fin 7`. -/
theorem isValidInventory_iff_ordConnected (inv : Finset Case) :
    IsValidInventory inv ↔
      (↑(inv.image hierarchyRank) : Set (Fin 7)).OrdConnected := by
  simp only [Set.ordConnected_iff, Set.subset_def, Set.mem_Icc,
    Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro hval x ⟨cx, hcx, rfl⟩ y ⟨cy, hcy, rfl⟩ _ r ⟨hr1, hr2⟩
    rcases eq_or_lt_of_le hr1 with rfl | h1
    · exact ⟨cx, hcx, rfl⟩
    rcases eq_or_lt_of_le hr2 with rfl | h2
    · exact ⟨cy, hcy, rfl⟩
    · exact hval r ⟨cx, hcx, h1⟩ ⟨cy, hcy, h2⟩
  · rintro hconn r ⟨clo, hclo, hlo⟩ ⟨chi, hchi, hhi⟩
    exact hconn _ ⟨clo, hclo, rfl⟩ _ ⟨chi, hchi, rfl⟩
      (le_of_lt (lt_trans hlo hhi)) r ⟨le_of_lt hlo, le_of_lt hhi⟩

/-! Contiguity verdicts on representative inventories (positive: Latin-
    through Finnish-sized systems; negative: hierarchy skips). Kept as
    `example`s — no codebase consumer references them by name. -/

example : IsValidInventory {.nom, .acc} := by decide
example : IsValidInventory {.nom, .acc, .gen} := by decide
example : IsValidInventory {.nom, .acc, .gen, .dat} := by decide
example : IsValidInventory {.nom, .acc, .gen, .dat, .loc} := by decide
example : IsValidInventory {.nom, .acc, .gen, .dat, .loc, .abl, .inst} := by
  decide
example : IsValidInventory {.erg, .abs, .gen, .dat} := by decide
example : IsValidInventory {.nom, .erg, .abs, .gen} := by decide
example : ¬ IsValidInventory {.nom, .acc, .dat} := by decide
example : ¬ IsValidInventory {.nom, .acc, .loc} := by decide
example : ¬ IsValidInventory {.nom, .acc, .abl} := by decide
example : ¬ IsValidInventory {.nom, .acc, .gen, .loc} := by decide

end Case

namespace Features

/-! ### Companion per-entry enums -/

/-- The two major morphosyntactic alignment families. -/
inductive AlignmentFamily where
  | accusative
  | ergative
  deriving DecidableEq, Repr

/-- How case is assigned to an NP in a given construction
    ([stassen-1985], §2.2.1). -/
inductive CaseAssignment where
  | derived
  | fixed
  deriving DecidableEq, Repr

/-- For fixed-case NPs, what syntactic role the NP occupies. -/
inductive FixedCaseEncoding where
  | directObject
  | adverbial
  deriving DecidableEq, Repr

end Features
