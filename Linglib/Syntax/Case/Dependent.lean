module

public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Case.Alignment
public import Linglib.Syntax.Case.Valuation

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

* `Mechanism`: what valued a case, a lexical head, a dependent rule, Agree, or the elsewhere
  case.
* `Rules`: the high, low and elsewhere cases of one domain, and `Rules.ofAlignment`, the rules
  of an alignment.
* `NP`, `lexicalValuation`: an NP before assignment, and the valuation of NPs by lexical case.
* `Rules.dependentPass`, `Rules.unmarkedPass`: the passes, over the NPs a predicate selects.
* `Rules.valuations`: the valuations the rules can assign.
* `Rules.assign`, `assignCases`: the one-domain algorithm, and its form for an alignment.

## Main results

* `Rules.dependentPass_high`, `Rules.dependentPass_low`, `Rules.dependentPass_alone`: what the
  dependent rules do to an NP with a caseless NP below it, above it, or neither.
* `Rules.extends_dependentPass`, `Rules.extends_unmarkedPass`, `Rules.extends_assign`: each pass
  extends the valuation by what the rules assign.
* `Rules.assign_length`: the algorithm is total.
* `Rules.assign_getElem?_of_some`: lexical case is kept, so it bleeds the dependent rules.
* `Rules.case_mem_cases`: a caseless NP is valued only with a case the rules mention.
* `Rules.assign_singleton`, `Rules.assign_pair`: the algorithm in closed form on domains of one
  and two NPs.

## Implementation notes

List position encodes structural height: earlier is higher, and c-commands everything later.
Labels are inert; `getCaseOf` and `getMechanismOf` look them up. The passes are `Valuation.fill`,
so what they share (totality, persistence of values) comes from `Case.Valuation.Extends`.

## References

* [marantz-1991]
* [baker-2015]
-/

@[expose] public section

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

/-- The clausal rules of an alignment: accusative on the lower NP, ergative on the higher,
    both, or neither, with the elsewhere case nominative where the lower NP is marked and
    absolutive otherwise. A split-S system is not a dependent-case setting and gets the
    neutral rules. -/
def Rules.ofAlignment : Alignment.AlignmentType → Rules
  | .accusative => { low := some .acc, unmarked := some .nom }
  | .ergative => { high := some .erg, unmarked := some .abs }
  | .tripartite => { high := some .erg, low := some .acc, unmarked := some .abs }
  | .neutral | .active => { unmarked := some .nom }

/-! ### NPs and valuations -/

/-- An NP as the rules see it: its label and any case a lexical head has valued. -/
structure NP where
  label : String
  lexicalCase : Option Case := none
  deriving DecidableEq, Repr

/-- Every NP with its lexical case valued and nothing else. -/
def lexicalValuation (lexicalCase : α → Option Case) (xs : List α) :
    Valuation α (Case × Mechanism) :=
  Valuation.initial (fun x ↦ (lexicalCase x).map (·, .lexical)) xs

/-- The case of the NP labelled `label`, if any. -/
def getCaseOf (label : String) (out : Valuation NP (Case × Mechanism)) : Option Case :=
  (out.find? (·.1.label == label)).bind (·.2.map (·.1))

/-- What valued the NP labelled `label`, if anything. -/
def getMechanismOf (label : String) (out : Valuation NP (Case × Mechanism)) :
    Option Mechanism :=
  (out.find? (·.1.label == label)).bind (·.2.map (·.2))

/-! ### The passes -/

/-- The dependent rules over the NPs `P` selects: the high case goes to those c-commanding
    another and the low case to those c-commanded by another, both read off the same
    configuration; an NP in both positions takes the high case. -/
def Rules.dependentPass (r : Rules) (P : α → Bool) (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  let e := s.unvalued P
  s.fill fun i _ ↦
    if i ∈ e then
      if r.high.isSome && e.any (i < ·) then r.high.map (·, .dependent)
      else if e.any (· < i) then r.low.map (·, .dependent)
      else none
    else none

/-- The elsewhere case to the unvalued NPs `P` selects. -/
def Rules.unmarkedPass (r : Rules) (P : α → Bool) (s : Valuation α (Case × Mechanism)) :
    Valuation α (Case × Mechanism) :=
  s.fill fun _ x ↦ if P x then r.unmarked.map (·, .unmarked) else none

/-- Case for every NP of one domain: the dependent rules, then the elsewhere case. -/
def Rules.assign (r : Rules) (nps : List NP) : Valuation NP (Case × Mechanism) :=
  r.unmarkedPass (fun _ ↦ true) <|
    r.dependentPass (fun _ ↦ true) (lexicalValuation (·.lexicalCase) nps)

/-- The one-domain algorithm of an alignment. -/
def assignCases (a : Alignment.AlignmentType) (nps : List NP) : Valuation NP (Case × Mechanism) :=
  (Rules.ofAlignment a).assign nps

/-! ### What the passes assign -/

/-- The valuations the rules can assign: a dependent case, or the elsewhere case. -/
def Rules.valuations (r : Rules) : Set (Case × Mechanism) :=
  {v | v.2 = .dependent ∧ (r.high = some v.1 ∨ r.low = some v.1) ∨
    v.2 = .unmarked ∧ r.unmarked = some v.1}

theorem Rules.fst_mem_cases {r : Rules} {v : Case × Mechanism} (h : v ∈ r.valuations) :
    v.1 ∈ r.cases := by
  rcases h with ⟨-, h | h⟩ | ⟨-, h⟩
  · exact high_mem_cases h
  · exact low_mem_cases h
  · exact unmarked_mem_cases h

theorem Rules.extends_dependentPass (r : Rules) (P : α → Bool)
    (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ r.valuations) (r.dependentPass P s) :=
  Valuation.extends_fill (fun _ _ v hv ↦ by
    split_ifs at hv <;>
      first
      | cases hv
      | (obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hv
         first | exact .inl ⟨rfl, .inl hc⟩ | exact .inl ⟨rfl, .inr hc⟩)) s

theorem Rules.extends_unmarkedPass (r : Rules) (P : α → Bool)
    (s : Valuation α (Case × Mechanism)) :
    s.Extends (· ∈ r.valuations) (r.unmarkedPass P s) :=
  Valuation.extends_fill (fun _ _ v hv ↦ by
    split_ifs at hv
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hv
    exact .inr ⟨rfl, hc⟩) s

/-- Assignment extends the lexical valuation by what the rules assign. -/
theorem Rules.extends_assign (r : Rules) (nps : List NP) :
    (lexicalValuation (·.lexicalCase) nps).Extends (· ∈ r.valuations) (r.assign nps) :=
  (r.extends_dependentPass _ _).trans (r.extends_unmarkedPass _ _)

/-- The algorithm is total: one valuation per NP. -/
@[simp] theorem Rules.assign_length (r : Rules) (nps : List NP) :
    (r.assign nps).length = nps.length := by
  rw [← (r.extends_assign nps).length_eq, lexicalValuation, Valuation.length_initial]

theorem lexicalValuation_getElem?_of_some (lexicalCase : α → Option Case) {xs : List α} {i : ℕ}
    {x : α} {c : Case} (hx : xs[i]? = some x) (hc : lexicalCase x = some c) :
    (lexicalValuation lexicalCase xs)[i]? = some (x, some (c, .lexical)) := by
  simp [lexicalValuation, Valuation.initial_getElem?, hx, hc]

theorem lexicalValuation_getElem? {lexicalCase : α → Option Case} {xs : List α} {i : ℕ} {x : α}
    {v : Case × Mechanism} (h : (lexicalValuation lexicalCase xs)[i]? = some (x, some v)) :
    lexicalCase x = some v.1 ∧ v.2 = .lexical := by
  simp only [lexicalValuation, Valuation.initial_getElem?] at h
  obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨rfl, hv⟩ := Prod.mk.injEq .. ▸ hy
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hv
  exact ⟨hc, rfl⟩

/-- Lexical case is kept, so it bleeds the dependent rules. -/
theorem Rules.assign_getElem?_of_some (r : Rules) {nps : List NP} {i : ℕ} {np : NP} {c : Case}
    (hnp : nps[i]? = some np) (hc : np.lexicalCase = some c) :
    (r.assign nps)[i]? = some (np, some (c, .lexical)) :=
  (r.extends_assign nps).getElem?_of_some (lexicalValuation_getElem?_of_some _ hnp hc)

/-- A caseless NP is valued only with a case the rules mention. -/
theorem Rules.case_mem_cases (r : Rules) {nps : List NP} {i : ℕ} {np : NP} {c : Case}
    {m : Mechanism} (hlex : np.lexicalCase = none)
    (h : (r.assign nps)[i]? = some (np, some (c, m))) : c ∈ r.cases := by
  rcases (r.extends_assign nps).of_getElem? h with h | h
  · exact absurd (lexicalValuation_getElem? h).1 (by simp [hlex])
  · exact Rules.fst_mem_cases h

/-! ### What the dependent rules do -/

/-- A caseless NP with a caseless NP below it in the domain takes the high case. -/
theorem Rules.dependentPass_high (r : Rules) (P : α → Bool) {s : Valuation α (Case × Mechanism)}
    {i j : ℕ} {x : α} {c : Case} (hx : s[i]? = some (x, none)) (hP : P x)
    (hj : j ∈ s.unvalued P) (hij : i < j) (hc : r.high = some c) :
    (r.dependentPass P s)[i]? = some (x, some (c, .dependent)) := by
  have hi : i ∈ s.unvalued P := Valuation.mem_unvalued_iff.2 ⟨x, hx, hP⟩
  have hany : ∃ k ∈ s.unvalued P, i < k := ⟨j, hj, hij⟩
  simp [Rules.dependentPass, Valuation.fill_getElem?_of_none hx, hi, hany, hc]

/-- A caseless NP with a caseless NP above it in the domain, and none below it that the high
    rule could mark it for, takes the low case. -/
theorem Rules.dependentPass_low (r : Rules) (P : α → Bool) {s : Valuation α (Case × Mechanism)}
    {i j : ℕ} {x : α} {c : Case} (hx : s[i]? = some (x, none)) (hP : P x)
    (hj : j ∈ s.unvalued P) (hji : j < i)
    (hhigh : r.high = none ∨ ∀ k ∈ s.unvalued P, ¬ i < k) (hc : r.low = some c) :
    (r.dependentPass P s)[i]? = some (x, some (c, .dependent)) := by
  have hi : i ∈ s.unvalued P := Valuation.mem_unvalued_iff.2 ⟨x, hx, hP⟩
  have hany : ∃ k ∈ s.unvalued P, k < i := ⟨j, hj, hji⟩
  rcases hhigh with h | h
  · simp [Rules.dependentPass, Valuation.fill_getElem?_of_none hx, hi, hany, h, hc]
  · have hno : ¬ ∃ k ∈ s.unvalued P, i < k := fun ⟨k, hk, hik⟩ ↦ h k hk hik
    simp [Rules.dependentPass, Valuation.fill_getElem?_of_none hx, hi, hany, hno, hc]

/-- A caseless NP alone in its domain is untouched by the dependent rules. -/
theorem Rules.dependentPass_alone (r : Rules) (P : α → Bool) {s : Valuation α (Case × Mechanism)}
    {i : ℕ} {x : α} (hx : s[i]? = some (x, none)) (halone : ∀ j ∈ s.unvalued P, j = i) :
    (r.dependentPass P s)[i]? = some (x, none) := by
  have h1 : ¬ ∃ k ∈ s.unvalued P, i < k :=
    fun ⟨k, hk, hik⟩ ↦ lt_irrefl i (halone k hk ▸ hik)
  have h2 : ¬ ∃ k ∈ s.unvalued P, k < i :=
    fun ⟨k, hk, hki⟩ ↦ lt_irrefl i (halone k hk ▸ hki)
  simp [Rules.dependentPass, Valuation.fill_getElem?_of_none hx, h1, h2]

/-- With no elsewhere case the pass does nothing. -/
theorem Rules.unmarkedPass_of_none (r : Rules) (P : α → Bool) (h : r.unmarked = none)
    (s : Valuation α (Case × Mechanism)) : r.unmarkedPass P s = s := by
  simp [Rules.unmarkedPass, h]

/-- With neither dependent case the pass does nothing. -/
theorem Rules.dependentPass_of_none (r : Rules) (P : α → Bool) (hh : r.high = none)
    (hl : r.low = none) (s : Valuation α (Case × Mechanism)) : r.dependentPass P s = s := by
  simp [Rules.dependentPass, hh, hl]

/-! ### Domains of one and two NPs -/

/-- The valuation of an NP no dependent rule reaches: its lexical case, or the elsewhere case. -/
def Rules.elsewhere (r : Rules) (np : NP) : Option (Case × Mechanism) :=
  (np.lexicalCase.map (·, Mechanism.lexical)).or (r.unmarked.map (·, .unmarked))

/-- A sole NP is never reached by a dependent rule. -/
theorem Rules.assign_singleton (r : Rules) (np : NP) : r.assign [np] = [(np, r.elsewhere np)] := by
  obtain ⟨hi, lo, un⟩ := r
  obtain ⟨lbl, _ | l⟩ := np <;> cases hi <;> cases lo <;> cases un <;> rfl

/-- Of two NPs the dependent rules reach both or neither: when neither has lexical case, the
    higher takes the high case and the lower the low case, where the rules have one. -/
theorem Rules.assign_pair (r : Rules) (x y : NP) :
    r.assign [x, y] =
      [(x, if x.lexicalCase = none ∧ y.lexicalCase = none ∧ r.high.isSome
            then r.high.map (·, .dependent) else r.elsewhere x),
       (y, if x.lexicalCase = none ∧ y.lexicalCase = none ∧ r.low.isSome
            then r.low.map (·, .dependent) else r.elsewhere y)] := by
  obtain ⟨hi, lo, un⟩ := r
  obtain ⟨lx, _ | cx⟩ := x <;> obtain ⟨ly, _ | cy⟩ := y <;>
    cases hi <;> cases lo <;> cases un <;> rfl

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
