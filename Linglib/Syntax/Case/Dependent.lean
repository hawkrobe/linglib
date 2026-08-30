import Linglib.Features.Case.Basic
import Linglib.Features.Case.Source
import Linglib.Syntax.Case.Alignment

/-!
# Dependent case

Structural case read off the arrangement of NPs in a domain, under a disjunctive hierarchy:
case a lexical head has valued is kept; otherwise an NP that c-commands a distinct caseless NP
in the domain takes the domain's high case and one c-commanded by such an NP its low case, the
two rules reading the same configuration, so a domain with both marks the higher NP and the
lower NP at once; whatever remains takes the domain's elsewhere case. Which of the two
dependent rules a clause has is its alignment: accusative, ergative, tripartite or neutral.
The passes are generic in what an NP is, so a phase-cyclic grammar can run them domain by
domain.

## Main definitions

* `Mechanism`: what valued a case — a lexical head, a dependent rule, Agree, or the elsewhere
  case — projecting onto the account-neutral `Case.Source`.
* `Rules`: the high, low and elsewhere cases of one domain; `Rules.alignment` and
  `Rules.ofAlignment` relate them to the alignment they show.
* `NP`, `Valuation`: an NP before assignment, and its case with what valued it.
* `Rules.dependentPass`, `Rules.unmarkedPass`: the passes, over the NPs a predicate selects.
* `Rules.assign`, `assignCases`: the one-domain algorithm, and its form for an alignment.

## Main results

* `Rules.dependentPass_high`, `Rules.dependentPass_low`, `Rules.dependentPass_alone`: what the
  dependent rules do to an NP with a caseless NP below it, above it, or neither.
* `Rules.assign_length`: the algorithm is total.
* `Rules.assign_getElem?_of_some`: lexical case is kept, so it bleeds the dependent rules.
* `Rules.case_mem_cases`: a caseless NP is valued only with a case the rules mention.
* `alignment_ofAlignment`: the rules of an alignment show that alignment.

## Implementation notes

List position encodes structural height: earlier is higher, and c-commands everything later.
Labels are inert; `getCaseOf` and `getMechanismOf` look them up.

## References

* [marantz-1991]
* [baker-2015]
-/

namespace Case

variable {α : Type*}

/-! ### Mechanisms -/

/-- What valued a case: a lexical head, a dependent rule, Agree with a functional head, or
    the elsewhere case of its domain. -/
inductive Mechanism
  | lexical
  | dependent
  | agree
  | unmarked
  deriving DecidableEq, Repr

/-- The account-neutral provenance: lexical case is inherent, dependent and Agree-valued case
    structural, the elsewhere case default. -/
def Mechanism.toSource : Mechanism → Source
  | .lexical => .inherent
  | .dependent => .structural
  | .agree => .structural
  | .unmarked => .default

/-! ### Rules -/

/-- The rules of one domain: the case of an NP c-commanding a distinct caseless NP in it, the
    case of one c-commanded by such an NP, and the elsewhere case. -/
structure Rules where
  high : Option Case := none
  low : Option Case := none
  unmarked : Option Case := none
  deriving DecidableEq, Repr

/-- The cases the rules can value a caseless NP with. -/
def Rules.cases (r : Rules) : List Case := [r.high, r.low, r.unmarked].filterMap id

theorem high_mem_cases {r : Rules} {c : Case} (h : r.high = some c) : c ∈ r.cases := by
  simp [Rules.cases, h]

theorem low_mem_cases {r : Rules} {c : Case} (h : r.low = some c) : c ∈ r.cases := by
  simp [Rules.cases, h]

theorem unmarked_mem_cases {r : Rules} {c : Case} (h : r.unmarked = some c) : c ∈ r.cases := by
  simp [Rules.cases, h]

/-- The alignment a domain's rules show: which of the two dependent rules it has. -/
def Rules.alignment (r : Rules) : Alignment.AlignmentType :=
  match r.high, r.low with
  | none, none => .neutral
  | none, some _ => .accusative
  | some _, none => .ergative
  | some _, some _ => .tripartite

/-- The clausal rules of an alignment: accusative on the lower NP, ergative on the higher,
    both, or neither, with the elsewhere case nominative where the lower NP is marked and
    absolutive otherwise. A split-S system is not a dependent-case setting and gets the
    neutral rules. -/
def Rules.ofAlignment : Alignment.AlignmentType → Rules
  | .accusative => { low := some .acc, unmarked := some .nom }
  | .ergative => { high := some .erg, unmarked := some .abs }
  | .tripartite => { high := some .erg, low := some .acc, unmarked := some .abs }
  | .neutral | .active => { unmarked := some .nom }

/-- The rules of an alignment show that alignment. -/
theorem alignment_ofAlignment (a : Alignment.AlignmentType) (ha : a ≠ .active) :
    (Rules.ofAlignment a).alignment = a := by
  cases a <;> first | rfl | exact absurd rfl ha

/-! ### NPs and valuations -/

/-- An NP as the rules see it: its label and any case a lexical head has valued. -/
structure NP where
  label : String
  lexicalCase : Option Case := none
  deriving DecidableEq, Repr

/-- A case together with what valued it, or nothing if no rule has reached the NP. -/
abbrev Valuation := Option (Case × Mechanism)

/-- Every NP with its lexical case valued and nothing else. -/
def initial (lexicalCase : α → Option Case) (xs : List α) : List (α × Valuation) :=
  xs.map λ x => (x, (lexicalCase x).map (·, .lexical))

/-- The case of the NP labelled `label`, if any. -/
def getCaseOf (label : String) (out : List (NP × Valuation)) : Option Case :=
  (out.find? (·.1.label == label)).bind (·.2.map (·.1))

/-- What valued the NP labelled `label`, if anything. -/
def getMechanismOf (label : String) (out : List (NP × Valuation)) : Option Mechanism :=
  (out.find? (·.1.label == label)).bind (·.2.map (·.2))

/-! ### The passes -/

/-- `markBy`, with indices counted from `i`. -/
def markByFrom (f : ℕ → α × Valuation → Valuation) :
    ℕ → List (α × Valuation) → List (α × Valuation)
  | _, [] => []
  | i, s :: rest => (if s.2.isNone then (s.1, f i s) else s) :: markByFrom f (i + 1) rest

/-- Value every unvalued NP for which `f` proposes a value. -/
def markBy (f : ℕ → α × Valuation → Valuation) (states : List (α × Valuation)) :
    List (α × Valuation) :=
  markByFrom f 0 states

theorem markByFrom_getElem? (f : ℕ → α × Valuation → Valuation) (i j : ℕ)
    (states : List (α × Valuation)) :
    (markByFrom f i states)[j]? =
      states[j]?.map λ s => if s.2.isNone then (s.1, f (i + j) s) else s := by
  induction states generalizing i j with
  | nil => simp [markByFrom]
  | cons s rest ih =>
    cases j with
    | zero => simp [markByFrom]
    | succ j => simp [markByFrom, ih, Nat.add_assoc, Nat.add_comm 1 j]

theorem markBy_getElem? (f : ℕ → α × Valuation → Valuation) (states : List (α × Valuation))
    (j : ℕ) :
    (markBy f states)[j]? = states[j]?.map λ s => if s.2.isNone then (s.1, f j s) else s := by
  simp [markBy, markByFrom_getElem?]

/-- The indices of the unvalued NPs `P` selects, highest first. -/
def eligible (P : α → Bool) (states : List (α × Valuation)) : List ℕ :=
  (states.zipIdx.filter λ s => s.1.2.isNone && P s.1.1).map (·.2)

theorem mem_eligible_iff {P : α → Bool} {states : List (α × Valuation)} {i : ℕ} :
    i ∈ eligible P states ↔ ∃ x, states[i]? = some (x, none) ∧ P x := by
  simp only [eligible, List.mem_map, List.mem_filter, List.mem_zipIdx_iff_getElem?,
    Bool.and_eq_true, Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨⟨⟨x, v⟩, j⟩, ⟨hj, rfl, hx⟩, rfl⟩
    exact ⟨x, hj, hx⟩
  · rintro ⟨x, hx, hP⟩
    exact ⟨((x, none), i), ⟨hx, rfl, hP⟩, rfl⟩

/-- The dependent rules over the NPs `P` selects: the high case goes to those c-commanding
    another and the low case to those c-commanded by another, both read off the same
    configuration; an NP in both positions takes the high case. -/
def Rules.dependentPass (r : Rules) (P : α → Bool) (states : List (α × Valuation)) :
    List (α × Valuation) :=
  let e := eligible P states
  markBy (λ i _ =>
    if i ∈ e then
      if r.high.isSome && e.any (i < ·) then r.high.map (·, .dependent)
      else if e.any (· < i) then r.low.map (·, .dependent)
      else none
    else none) states

/-- The elsewhere case to the unvalued NPs `P` selects. -/
def Rules.unmarkedPass (r : Rules) (P : α → Bool) (states : List (α × Valuation)) :
    List (α × Valuation) :=
  markBy (λ _ s => if P s.1 then r.unmarked.map (·, .unmarked) else none) states

/-- Case for every NP of one domain: the dependent rules, then the elsewhere case. -/
def Rules.assign (r : Rules) (nps : List NP) : List (NP × Valuation) :=
  r.unmarkedPass (λ _ => true) (r.dependentPass (λ _ => true) (initial NP.lexicalCase nps))

/-- The one-domain algorithm of an alignment. -/
def assignCases (a : Alignment.AlignmentType) (nps : List NP) : List (NP × Valuation) :=
  (Rules.ofAlignment a).assign nps

/-! ### Totality -/

theorem markByFrom_length (f : ℕ → α × Valuation → Valuation) (i : ℕ)
    (states : List (α × Valuation)) : (markByFrom f i states).length = states.length := by
  induction states generalizing i with
  | nil => rfl
  | cons _ _ ih => simp [markByFrom, ih]

@[simp] theorem markBy_length (f : ℕ → α × Valuation → Valuation) (states : List (α × Valuation)) :
    (markBy f states).length = states.length := markByFrom_length ..

@[simp] theorem Rules.dependentPass_length (r : Rules) (P : α → Bool)
    (states : List (α × Valuation)) : (r.dependentPass P states).length = states.length :=
  markBy_length ..

@[simp] theorem Rules.unmarkedPass_length (r : Rules) (P : α → Bool)
    (states : List (α × Valuation)) : (r.unmarkedPass P states).length = states.length :=
  markBy_length ..

@[simp] theorem initial_length (lexicalCase : α → Option Case) (xs : List α) :
    (initial lexicalCase xs).length = xs.length := List.length_map ..

/-- The algorithm is total: one valuation per NP. -/
@[simp] theorem Rules.assign_length (r : Rules) (nps : List NP) :
    (r.assign nps).length = nps.length := by
  simp [Rules.assign]

/-! ### What each pass does -/

theorem markBy_getElem?_of_some (f : ℕ → α × Valuation → Valuation)
    {states : List (α × Valuation)} {i : ℕ} {x : α} {v : Case × Mechanism}
    (h : states[i]? = some (x, some v)) : (markBy f states)[i]? = some (x, some v) := by
  simp [markBy_getElem?, h]

theorem markBy_getElem?_of_none (f : ℕ → α × Valuation → Valuation)
    {states : List (α × Valuation)} {i : ℕ} {x : α} (h : states[i]? = some (x, none)) :
    (markBy f states)[i]? = some (x, f i (x, none)) := by
  simp [markBy_getElem?, h]

theorem Rules.dependentPass_getElem?_of_some (r : Rules) (P : α → Bool)
    {states : List (α × Valuation)} {i : ℕ} {x : α} {v : Case × Mechanism}
    (h : states[i]? = some (x, some v)) : (r.dependentPass P states)[i]? = some (x, some v) :=
  markBy_getElem?_of_some _ h

theorem Rules.unmarkedPass_getElem?_of_some (r : Rules) (P : α → Bool)
    {states : List (α × Valuation)} {i : ℕ} {x : α} {v : Case × Mechanism}
    (h : states[i]? = some (x, some v)) : (r.unmarkedPass P states)[i]? = some (x, some v) :=
  markBy_getElem?_of_some _ h

theorem initial_getElem?_of_some (lexicalCase : α → Option Case) {xs : List α} {i : ℕ} {x : α}
    {c : Case} (hx : xs[i]? = some x) (hc : lexicalCase x = some c) :
    (initial lexicalCase xs)[i]? = some (x, some (c, .lexical)) := by
  simp [initial, hx, hc]

/-- A caseless NP with a caseless NP below it in the domain takes the high case. -/
theorem Rules.dependentPass_high (r : Rules) (P : α → Bool) {states : List (α × Valuation)}
    {i j : ℕ} {x : α} {c : Case} (hx : states[i]? = some (x, none)) (hP : P x)
    (hj : j ∈ eligible P states) (hij : i < j) (hc : r.high = some c) :
    (r.dependentPass P states)[i]? = some (x, some (c, .dependent)) := by
  have hi : i ∈ eligible P states := mem_eligible_iff.2 ⟨x, hx, hP⟩
  have hany : ∃ k ∈ eligible P states, i < k := ⟨j, hj, hij⟩
  simp [Rules.dependentPass, markBy_getElem?_of_none _ hx, hi, hany, hc]

/-- A caseless NP with a caseless NP above it in the domain, and none below it that the high
    rule could mark it for, takes the low case. -/
theorem Rules.dependentPass_low (r : Rules) (P : α → Bool) {states : List (α × Valuation)}
    {i j : ℕ} {x : α} {c : Case} (hx : states[i]? = some (x, none)) (hP : P x)
    (hj : j ∈ eligible P states) (hji : j < i)
    (hhigh : r.high = none ∨ ∀ k ∈ eligible P states, ¬ i < k) (hc : r.low = some c) :
    (r.dependentPass P states)[i]? = some (x, some (c, .dependent)) := by
  have hi : i ∈ eligible P states := mem_eligible_iff.2 ⟨x, hx, hP⟩
  have hany : ∃ k ∈ eligible P states, k < i := ⟨j, hj, hji⟩
  rcases hhigh with h | h
  · simp [Rules.dependentPass, markBy_getElem?_of_none _ hx, hi, hany, h, hc]
  · have hno : ¬ ∃ k ∈ eligible P states, i < k := λ ⟨k, hk, hik⟩ => h k hk hik
    simp [Rules.dependentPass, markBy_getElem?_of_none _ hx, hi, hany, hno, hc]

/-- A caseless NP alone in its domain is untouched by the dependent rules. -/
theorem Rules.dependentPass_alone (r : Rules) (P : α → Bool) {states : List (α × Valuation)}
    {i : ℕ} {x : α} (hx : states[i]? = some (x, none))
    (halone : ∀ j ∈ eligible P states, j = i) :
    (r.dependentPass P states)[i]? = some (x, none) := by
  have h1 : ¬ ∃ k ∈ eligible P states, i < k :=
    λ ⟨k, hk, hik⟩ => lt_irrefl i (halone k hk ▸ hik)
  have h2 : ¬ ∃ k ∈ eligible P states, k < i :=
    λ ⟨k, hk, hki⟩ => lt_irrefl i (halone k hk ▸ hki)
  simp [Rules.dependentPass, markBy_getElem?_of_none _ hx, h1, h2]

/-- Lexical case is kept, so it bleeds the dependent rules. -/
theorem Rules.assign_getElem?_of_some (r : Rules) {nps : List NP} {i : ℕ} {np : NP} {c : Case}
    (hnp : nps[i]? = some np) (hc : np.lexicalCase = some c) :
    (r.assign nps)[i]? = some (np, some (c, .lexical)) :=
  r.unmarkedPass_getElem?_of_some _
    (r.dependentPass_getElem?_of_some _ (initial_getElem?_of_some _ hnp hc))

/-! ### The cases the rules value -/

theorem markBy_value {f : ℕ → α × Valuation → Valuation} {states : List (α × Valuation)} {i : ℕ}
    {x : α} {v : Case × Mechanism} (h : (markBy f states)[i]? = some (x, some v)) :
    states[i]? = some (x, some v) ∨ ∃ s, states[i]? = some s ∧ s.1 = x ∧ f i s = some v := by
  simp only [markBy_getElem?] at h
  obtain ⟨s, hs, hfs⟩ := Option.map_eq_some_iff.1 h
  by_cases hnone : s.2.isNone
  · simp only [hnone, ↓reduceIte, Prod.mk.injEq] at hfs
    exact .inr ⟨s, hs, hfs.1, hfs.2⟩
  · simp only [hnone, Bool.false_eq_true, ↓reduceIte] at hfs
    exact .inl (hfs ▸ hs)

theorem Rules.dependentPass_case (r : Rules) (P : α → Bool) {states : List (α × Valuation)}
    {i : ℕ} {x : α} {v : Case × Mechanism}
    (h : (r.dependentPass P states)[i]? = some (x, some v)) :
    states[i]? = some (x, some v) ∨ v.1 ∈ r.cases := by
  refine (markBy_value h).imp_right λ ⟨s, _, _, hf⟩ => ?_
  split_ifs at hf
  all_goals first
    | cases hf
    | (obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hf
       first | exact high_mem_cases hc | exact low_mem_cases hc)

theorem Rules.unmarkedPass_case (r : Rules) (P : α → Bool) {states : List (α × Valuation)}
    {i : ℕ} {x : α} {v : Case × Mechanism}
    (h : (r.unmarkedPass P states)[i]? = some (x, some v)) :
    states[i]? = some (x, some v) ∨ v.1 ∈ r.cases := by
  refine (markBy_value h).imp_right λ ⟨s, _, _, hf⟩ => ?_
  split_ifs at hf
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hf
  exact unmarked_mem_cases hc

theorem initial_value {lexicalCase : α → Option Case} {xs : List α} {i : ℕ} {x : α}
    {v : Case × Mechanism} (h : (initial lexicalCase xs)[i]? = some (x, some v)) :
    lexicalCase x = some v.1 := by
  simp only [initial, List.getElem?_map] at h
  obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨rfl, hv⟩ := Prod.mk.injEq .. ▸ hy
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hv
  exact hc

/-- A caseless NP is valued only with a case the rules mention. -/
theorem Rules.case_mem_cases (r : Rules) {nps : List NP} {i : ℕ} {np : NP} {c : Case}
    {m : Mechanism} (hlex : np.lexicalCase = none)
    (h : (r.assign nps)[i]? = some (np, some (c, m))) : c ∈ r.cases := by
  rcases r.unmarkedPass_case _ h with h | h
  · rcases r.dependentPass_case _ h with h | h
    · exact absurd (initial_value h) (by simp [hlex])
    · exact h
  · exact h

/-! ### What each pass values as -/

theorem markBy_none (states : List (α × Valuation)) : markBy (λ _ _ => none) states = states := by
  apply List.ext_getElem?
  intro i
  simp only [markBy_getElem?]
  rcases states[i]? with _ | ⟨x, _ | v⟩ <;> simp

/-- With no elsewhere case the pass does nothing. -/
theorem Rules.unmarkedPass_of_none (r : Rules) (P : α → Bool) (h : r.unmarked = none)
    (states : List (α × Valuation)) : r.unmarkedPass P states = states := by
  simp [Rules.unmarkedPass, h, markBy_none]

/-- The dependent rules value as such. -/
theorem Rules.dependentPass_mechanism (r : Rules) (P : α → Bool) {states : List (α × Valuation)}
    {i : ℕ} {x : α} {v : Case × Mechanism}
    (h : (r.dependentPass P states)[i]? = some (x, some v)) :
    states[i]? = some (x, some v) ∨ v.2 = .dependent := by
  refine (markBy_value h).imp_right λ ⟨s, _, _, hf⟩ => ?_
  split_ifs at hf
  all_goals first
    | cases hf
    | (obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hf; rfl)

/-- The initial valuation is lexical. -/
theorem initial_mechanism {lexicalCase : α → Option Case} {xs : List α} {i : ℕ} {x : α}
    {v : Case × Mechanism} (h : (initial lexicalCase xs)[i]? = some (x, some v)) :
    v.2 = .lexical := by
  simp only [initial, List.getElem?_map] at h
  obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨rfl, hv⟩ := Prod.mk.injEq .. ▸ hy
  obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 hv
  rfl

/-! ### Alignments on a transitive and an intransitive clause -/

/-- Two caseless NPs: the accusative rules value the lower accusative and leave the higher
    nominative, the ergative rules mirror this, and the tripartite rules do both. -/
theorem assignCases_transitive :
    let nps : List NP := [{ label := "higher" }, { label := "lower" }]
    (assignCases .accusative nps).map (·.2.map (·.1)) = [some .nom, some .acc] ∧
    (assignCases .ergative nps).map (·.2.map (·.1)) = [some .erg, some .abs] ∧
    (assignCases .tripartite nps).map (·.2.map (·.1)) = [some .erg, some .acc] := by
  decide

/-- A sole caseless NP takes the elsewhere case under every alignment. -/
theorem assignCases_intransitive (a : Alignment.AlignmentType) :
    getMechanismOf "sole" (assignCases a [{ label := "sole" }]) = some .unmarked := by
  cases a <;> decide

end Case
