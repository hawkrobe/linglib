import Linglib.Semantics.Mereology
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# Borer 2005: dividing and counting in the nominal spine

[borer-2005] (*In Name Only*) locates the mass/count distinction in functional
structure: roots denote cumulative stuff, mass interpretation is the default in
the absence of dividing structure, the classifier head (⟨e⟩div, the `Q` head of
the nominal spine) divides the stuff, and the quantity head (⟨e⟩#, the `Num`
head) counts the divisions — or measures undivided mass, *much salt*. Division
creates no individuals: bare plurals stay cumulative, and plural marking
presupposes no singulars (*zero apples*, *0.5 apples*). Individuals emerge only
when a counter assigns range to ⟨e⟩#, selecting from the divisions — the
book's reticules — one with the requisite number of complete cells. Singular
*a*, *one* and *every*, *each* are portmanteau divider-counters assigning
range to both heads, cardinals are pure counters, and the features count and
divide generate the book's determiner typology.

## Main definitions

* `Division` — a reticule over cumulative stuff: finitely many cells, none
  required to be a canonical unit.
* `Division.merge`, `Division.counts` — the sum of two divisions; the number
  of complete cells a counter selects for.
* `DeterminerClass`, with `much`, `every`, `indefArticle`, `cardinal`,
  `allDet`, `hungarianCardinal` — the typology's two features and its rows.
* `status`, `Countable` — the spine's bottom-up typing and count structure.

## Main results

* `sumFrom_mem` — divided stuff is still stuff: apples plus apples gives
  apples, the cumulativity bare plurals share with mass nouns.
* `exists_division_without_units`, `exists_unit_of_counts_pos` — plural
  marking presupposes no singulars, while a positively counted division
  yields individuals: individuals emerge at ⟨e⟩#, not at ⟨e⟩div.
* `counters_reject_bare_stems`, `dividers_take_bare_stems`, `all_pattern`,
  `hungarian_no_plural` — the determiner distribution derived from the two
  features.
* `q_below_num`, `quantified_mass` — dividing feeds counting and nothing
  divides a quantity, while the quantity head alone over undivided stuff is
  quantified mass.

## References

* [borer-2005] — the book.
* [krifka-1998] — the cumulative and quantized notions the book measures its
  proposal against.
* [chierchia-1998] — the lexical rival.
-/

namespace Borer2005

open Mereology Minimalist

variable {α : Type*} {P : α → Prop}

/-! ### Dividing without individuating

Assigning range to ⟨e⟩div superimposes divisions on a mass denotation. A
division carves cells; it does not choose among reticules, and its cells need
not be canonical units — the book's apple portions, and the reticules with no
complete cells that ground *zero apples* and *0.5 apples*. -/

/-- A division of cumulative stuff — the book's reticule: finitely many cells
carved from the `P`-stuff, possibly none of them a canonical unit. -/
structure Division (P : α → Prop) where
  /-- The cells the reticule carves. -/
  cells : List α
  /-- Every cell is carved from the stuff. -/
  stuff : ∀ x ∈ cells, P x

/-- Merging two divisions divides the same stuff. -/
def Division.merge (d₁ d₂ : Division P) : Division P :=
  ⟨d₁.cells ++ d₂.cells, fun x hx =>
    (List.mem_append.mp hx).elim (d₁.stuff x) (d₂.stuff x)⟩

section Sums

variable [SemilatticeSup α]

/-- The sum of a list of cells, accumulated from a first cell. -/
def sumFrom (a : α) (l : List α) : α := l.foldl (· ⊔ ·) a

/-- Divided stuff is still stuff: the sum of cells of the cumulative root
satisfies the root — apples plus apples gives apples, the cumulativity bare
plurals share with mass nouns against singulars. -/
theorem sumFrom_mem (hCum : CUM P) {a : α} (ha : P a) {l : List α}
    (hl : ∀ x ∈ l, P x) : P (sumFrom a l) := by
  induction l generalizing a with
  | nil => exact ha
  | cons b l ih =>
    exact ih (hCum ha (hl b (by simp))) fun x hx => hl x (by simp [hx])

end Sums

section Units

variable (unit : α → Prop)

/-- Plural marking presupposes no singulars: whenever the stuff has a
noncanonical portion, some cell-nonempty division contains no unit at all —
the divisions behind *zero apples*, *0.5 apples*, and the apple-portion
readings of bare plurals. -/
theorem exists_division_without_units (h : ∃ x, P x ∧ ¬ unit x) :
    ∃ d : Division P, d.cells ≠ [] ∧ ∀ x ∈ d.cells, ¬ unit x :=
  let ⟨x, hP, hu⟩ := h
  ⟨⟨[x], by simpa using hP⟩, by simp, by simpa using hu⟩

variable [DecidablePred unit]

/-- The counting function: a counter assigning range to ⟨e⟩# selects a
division by its number of complete cells — cells that are canonical units. -/
def Division.counts (d : Division P) : ℕ :=
  (d.cells.filter fun x => decide (unit x)).length

/-- Individuals emerge at ⟨e⟩#: a division counted positively contains a
canonical unit of the stuff — *more than three circles* cannot be true
without individual circles, though bare *circles* can. -/
theorem exists_unit_of_counts_pos {d : Division P} (h : 0 < d.counts unit) :
    ∃ x, unit x ∧ P x := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos h
  exact ⟨x, by simpa using List.of_mem_filter hx, d.stuff x (List.mem_of_mem_filter hx)⟩

end Units

/-! ### The determiner typology

The typology sorts determiners by two features — counting, the assignment of
range to ⟨e⟩#, and dividing, the assignment of range to ⟨e⟩div — and the
distribution over bare stems, plurals, and mass follows from the features. -/

/-- A determiner class: whether it counts (`none` for the unspecified
determiners) and whether it divides. -/
structure DeterminerClass where
  /-- Assigns range to ⟨e⟩#; `none` when unspecified. -/
  counts : Option Bool
  /-- Assigns range to ⟨e⟩div. -/
  divides : Bool
  deriving DecidableEq, Repr

/-- *much*, *little*: quantity over undivided mass; no classifier phrase. -/
def much : DeterminerClass := ⟨some false, false⟩

/-- *every*, *each*: portmanteau divider-counters over bare stems. -/
def every : DeterminerClass := ⟨some true, true⟩

/-- *a*, *one*: the singular as simultaneous division and counting — the
dividing and counting functions can never be separated for singulars. -/
def indefArticle : DeterminerClass := ⟨some true, true⟩

/-- Cardinals and the plural-selecting quantifiers (*three*, *several*,
*many*): pure counters over previously introduced divisions. -/
def cardinal : DeterminerClass := ⟨some true, false⟩

/-- *all*, *a lot of*, *most*: unspecified for counting, never dividing. -/
def allDet : DeterminerClass := ⟨none, false⟩

/-- Hungarian, Turkish, and Armenian cardinals: dividing counters, on a par
with *every* and *each*. -/
def hungarianCardinal : DeterminerClass := ⟨some true, true⟩

/-- Combination with a bare stem: the stem is undivided stuff, so the
determiner must either divide it or tolerate mass — pure counters cannot. -/
abbrev takesBareStem (c : DeterminerClass) : Prop :=
  c.divides = true ∨ c.counts ≠ some true

/-- Combination with plural marking: the plural assigns range to ⟨e⟩div, so a
divider clashes with it, and a pure mass quantity has nothing to count. -/
abbrev takesPlural (c : DeterminerClass) : Prop :=
  c.divides = false ∧ c.counts ≠ some false

/-- Pure counters reject bare stems — mass cannot be counted: *two boy*,
*two meat* — while taking plurals: *two boys*. -/
theorem counters_reject_bare_stems :
    ¬ takesBareStem cardinal ∧ takesPlural cardinal := by decide

/-- The divider-counters take bare stems of either sort — *a boy*, *one
meat*, *every boy*, *each meat* — and reject plurals: *every boys*. -/
theorem dividers_take_bare_stems :
    (takesBareStem indefArticle ∧ ¬ takesPlural indefArticle) ∧
      takesBareStem every ∧ ¬ takesPlural every := by decide

/-- *all* takes mass and plurals but, not dividing, yields no count reading
on a bare stem: *all meat*, *all boys*, not *all boy*. -/
theorem all_pattern :
    takesBareStem allDet ∧ takesPlural allDet ∧ allDet.divides = false := by decide

/-- Dividing cardinals take bare stems and never co-occur with plural
marking — the Hungarian, Turkish, and Armenian pattern. -/
theorem hungarian_no_plural :
    takesBareStem hungarianCardinal ∧ ¬ takesPlural hungarianCardinal := by decide

/-! ### The nominal spine -/

/-- A nominal spine is count when it projects the dividing head. -/
abbrev Countable (spine : List Cat) : Prop := Cat.Q ∈ spine

example : Countable [.N, .n, .Q, .Num, .D] := by decide
example : ¬ Countable [.N, .n, .D] := by decide

/-- The mereological type of a nominal denotation along the spine: cumulative
stuff, divided stuff, or quantity. -/
inductive Status where
  | stuff
  | divided
  | quantity
  deriving DecidableEq, Repr

/-- The semantically active heads: ⟨e⟩div divides stuff, and ⟨e⟩# counts
divisions or measures undivided stuff — *three cats* against *much salt*;
the other heads are transparent. Nothing divides a quantity. -/
def steps : Cat → Status → Option Status
  | .Q, .stuff => some .divided
  | .Q, _ => none
  | .Num, .quantity => none
  | .Num, _ => some .quantity
  | _, s => some s

/-- The type of a spine's denotation, composed bottom-up from cumulative
stuff; `none` when a head has no well-typed input. -/
def status (spine : List Cat) : Option Status :=
  spine.foldl (fun s c => s.bind (steps c)) (some .stuff)

/-- Dividing feeds counting and nothing divides a quantity: the only
well-typed order puts the dividing head below the quantity head — the order
the extended projection's F-values encode. -/
theorem q_below_num :
    status [.N, .n, .Q, .Num] = some .quantity ∧
      status [.N, .n, .Num, .Q] = none := by decide

/-- The quantity head alone, over undivided stuff, is quantified mass —
*much salt* projects no classifier phrase. -/
theorem quantified_mass : status [.N, .n, .Num] = some .quantity := by decide

/-- The truncations: the bare stem is mass, the divided stem a bare plural. -/
theorem status_truncations :
    status [.N, .n] = some .stuff ∧ status [.N, .n, .Q] = some .divided := by decide

/-- The extended projection's F-values place the dividing head below the
quantity head. -/
theorem fValue_Q_lt_Num : fValue .Q < fValue .Num := by decide

end Borer2005
