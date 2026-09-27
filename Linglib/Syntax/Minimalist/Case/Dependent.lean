module

public import Linglib.Syntax.Case.Dependent
public import Linglib.Syntax.Minimalist.Defs
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Lookmap

/-!
# Dependent case by phase

The configurational rules of `Syntax/Case/Dependent.lean` run domain by domain: each phase
head's spell-out domain has its own high, low and elsewhere cases, the domains spell out
innermost first, and a case valued in an inner domain — or by a lexical head — is never
overwritten, so a dative valued in the verb phrase survives the clause. Functional heads may
also value case under Agree, each probing the highest caseless NP of the domain it agrees
into. A language's case assigners are the table of domain rules together with the Agree cases,
so a purely configurational system, a purely Agree-based one, and the hybrids are points in one
space.
Which functional heads a derivation contains is a fact about it, so assignment takes the
probes present with the domain each agrees into.

## Main definitions

* `agreeValue`: Agree into a domain, valuing the highest NP there whose case is unvalued.
* `PhasedNP`: an NP with the phase head whose domain merges it, and whether it has shifted
  to the clause edge.
* `CaseAssigners`: the phase heads in spell-out order with their rules, and the Agree cases.
* `CaseAssigners.assign`: case for every NP of a derivation.

## Main results

* `agreeValue_getElem?`: Agree values at most one NP, an unvalued one in its domain.
* `agreeValue_eq_self_iff`: Agree values nothing iff the probe seeking an unvalued NP in its
  domain finds no goal.
* `ValuedLE.agreeValue`, `valuedLE_agreeValue`: Agree only adds values, and preserves which of
  two derivations has valued more.
* `CaseAssigners.assign_length`: assignment is total.
* `CaseAssigners.assign_getElem?_of_some`: lexical case is kept.
* `CaseAssigners.case_mem_cases`: a caseless NP is valued only with a case the assigners
  mention.

## References

* [baker-vinokurova-2010]
* [baker-2015]
* [chomsky-2000], [chomsky-2001]
* [preminger-2014]
-/

@[expose] public section

namespace Minimalist

open Case (Rules Mechanism Valuation initial markBy eligible)

/-! ### Agree -/

section Agree

variable {α β : Type*} {P : α → Bool} {v : β} {s t : List (α × Option β)}

/-- Agree into the domain `P`, valuing `v`: the highest NP that `P` selects whose case is still
    unvalued is valued `v`, the activity condition of [chomsky-2000]. -/
def agreeValue (P : α → Bool) (v : β) : List (α × Option β) → List (α × Option β)
  | [] => []
  | p :: s => if p.2.isNone && P p.1 then (p.1, some v) :: s else p :: agreeValue P v s

@[simp] theorem agreeValue_nil : agreeValue P v [] = [] := rfl

@[simp] theorem agreeValue_cons (p : α × Option β) (s : List (α × Option β)) :
    agreeValue P v (p :: s) =
      if p.2.isNone && P p.1 then (p.1, some v) :: s else p :: agreeValue P v s := rfl

/-- Agree is `List.lookmap` of the update that values an unvalued NP in the domain. -/
theorem agreeValue_eq_lookmap (s : List (α × Option β)) :
    agreeValue P v s =
      s.lookmap fun p ↦ if p.2.isNone && P p.1 then some (p.1, some v) else none := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    by_cases h : p.2.isNone && P p.1
    · rw [List.lookmap_cons_some (b := (p.1, some v)) _ _ (by simp [h])]; simp [h]
    · rw [List.lookmap_cons_none _ _ (by simp [h])]; simp [h, ih]

@[simp] theorem length_agreeValue : (agreeValue P v s).length = s.length := by
  rw [agreeValue_eq_lookmap, List.length_lookmap]

/-- Agree values nothing iff the probe seeking an unvalued NP in its domain finds no goal, the
    failed Agree of [preminger-2014]. -/
theorem agreeValue_eq_self_iff : agreeValue P v s = s ↔
    (Probe.relativized fun p : α × Option β ↦ p.2.isNone && P p.1).search s = none := by
  induction s with
  | nil => simp [Probe.search]
  | cons p s ih =>
    obtain ⟨x, _ | a⟩ := p <;> cases hx : P x <;> simp_all [Probe.search]

/-- Agree leaves every NP as it was except at most one, an unvalued NP in its domain, which it
    values. -/
theorem agreeValue_getElem? (s : List (α × Option β)) (i : ℕ) :
    (agreeValue P v s)[i]? = s[i]? ∨
      ∃ x, s[i]? = some (x, none) ∧ P x ∧ (agreeValue P v s)[i]? = some (x, some v) := by
  induction s generalizing i with
  | nil => simp
  | cons p s ih =>
    obtain ⟨x, a⟩ := p
    by_cases h : a.isNone && P x
    · rcases i with _ | i
      · simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
        obtain ⟨rfl, hx⟩ := h
        simp [hx]
      · simp [h]
    · rcases i with _ | i
      · simp [h]
      · simpa [h] using ih i

/-- An NP already valued stays valued as it was. -/
theorem agreeValue_getElem?_of_some {i : ℕ} {x : α} {w : β} (h : s[i]? = some (x, some w)) :
    (agreeValue P v s)[i]? = some (x, some w) := by
  rcases agreeValue_getElem? (P := P) (v := v) s i with e | ⟨_, e, -⟩
  · rw [e, h]
  · simp [h] at e

/-- A value Agree leaves is one the NP already had, or `v`. -/
theorem agreeValue_value {i : ℕ} {x : α} {w : β} (h : (agreeValue P v s)[i]? = some (x, some w)) :
    s[i]? = some (x, some w) ∨ w = v := by
  rcases agreeValue_getElem? (P := P) (v := v) s i with e | ⟨_, -, -, e⟩
  · exact .inl (e ▸ h)
  · simp_all

theorem mem_agreeValue {p : α × Option β} (h : p ∈ agreeValue P v s) :
    p ∈ s ∨ p.2 = some v := by
  induction s with
  | nil => simp at h
  | cons q s ih =>
    rw [agreeValue_cons] at h
    split_ifs at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inr rfl
      · exact .inl (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl (List.mem_cons_self ..)
      · exact (ih h).imp_left (List.mem_cons_of_mem _)

/-- `t` has the NPs of `s`, and values every NP `s` values. -/
abbrev ValuedLE (s t : List (α × Option β)) : Prop :=
  List.Forall₂ (fun p q ↦ p.1 = q.1 ∧ (p.2.isSome → q.2.isSome)) s t

@[refl] theorem ValuedLE.refl (s : List (α × Option β)) : ValuedLE s s :=
  List.forall₂_same.2 fun _ _ ↦ ⟨rfl, id⟩

theorem ValuedLE.trans {u : List (α × Option β)} :
    ValuedLE s t → ValuedLE t u → ValuedLE s u := by
  intro h₁ h₂
  induction h₁ generalizing u with
  | nil => cases h₂; exact .nil
  | cons h _ ih =>
    cases h₂ with
    | cons h' h₂ => exact .cons ⟨h.1.trans h'.1, h'.2 ∘ h.2⟩ (ih h₂)

/-- Agree only adds values. -/
theorem valuedLE_agreeValue (s : List (α × Option β)) : ValuedLE s (agreeValue P v s) := by
  induction s with
  | nil => exact .nil
  | cons p s ih =>
    rw [agreeValue_cons]
    split_ifs
    · exact .cons ⟨rfl, fun _ ↦ rfl⟩ (ValuedLE.refl s)
    · exact .cons ⟨rfl, id⟩ ih

/-- Agree preserves which of two derivations has valued more. -/
theorem ValuedLE.agreeValue (h : ValuedLE s t) :
    ValuedLE (agreeValue P v s) (agreeValue P v t) := by
  induction h with
  | nil => exact .nil
  | @cons p q s t hpq hst ih =>
    obtain ⟨x, a⟩ := p
    obtain ⟨y, b⟩ := q
    obtain ⟨rfl, hab⟩ := hpq
    rcases a with _ | a <;> rcases b with _ | b <;> cases hx : P x <;>
      simp only [agreeValue_cons, Option.isNone_none, Option.isNone_some, hx, Bool.and_true,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    · exact .cons ⟨rfl, by simp⟩ ih
    · exact .cons ⟨rfl, by simp⟩ hst
    · exact .cons ⟨rfl, by simp⟩ ih
    · exact .cons ⟨rfl, by simp⟩ (ValuedLE.trans hst (valuedLE_agreeValue t))
    · simp at hab
    · simp at hab
    · exact .cons ⟨rfl, by simp⟩ ih
    · exact .cons ⟨rfl, by simp⟩ ih

/-- Agree commutes with relabelling the NPs and the values, provided the relabelling keeps what
    is in the domain and what is valued. -/
theorem agreeValue_map {α' β' : Type*} {P' : α' → Bool} {v' : β'} (f : α → α') (g : β → β')
    (hP : ∀ x, P' (f x) = P x) (hv : g v = v') (s : List (α × Option β)) :
    agreeValue P' v' (s.map (Prod.map f (Option.map g))) =
      (agreeValue P v s).map (Prod.map f (Option.map g)) := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    obtain ⟨x, a⟩ := p
    rcases a with _ | a
    · by_cases hx : P x <;> simp [hx, hP, hv, ih]
    · simp [ih]

end Agree

/-- An NP with its position: the phase head whose spell-out domain merges it, and whether it
    has shifted to the clause edge, where C's domain spells it out. -/
structure PhasedNP extends Case.NP where
  phase : Cat := .C
  shifted : Bool := false
  deriving DecidableEq, Repr

/-- Whether the NP is in the domain of `c` when it spells out. -/
def PhasedNP.visible (np : PhasedNP) (c : Cat) : Bool := np.phase == c || (np.shifted && c == .C)

/-- The phase head whose elsewhere case the NP falls back on. -/
def PhasedNP.spellOut (np : PhasedNP) : Cat := if np.shifted then .C else np.phase

/-- The case assigners of a language, in both modalities of [baker-vinokurova-2010]: the phase
    heads in spell-out order with the dependent-case rules of their domains, and the case each
    functional head values under Agree. -/
structure CaseAssigners where
  domains : List (Cat × Rules)
  agree : List (Cat × Case) := []
  deriving DecidableEq, Repr

/-- The rules of the domain of `c`. -/
def CaseAssigners.rules (g : CaseAssigners) (c : Cat) : Rules :=
  ((g.domains.find? (·.1 == c)).map (·.2)).getD {}

/-- The case `h` values under Agree, if any. -/
def CaseAssigners.agreeCase (g : CaseAssigners) (h : Cat) : Option Case :=
  (g.agree.find? (·.1 == h)).map (·.2)

/-- The cases the assigners can value a caseless NP with. -/
def CaseAssigners.cases (g : CaseAssigners) : List Case :=
  g.domains.flatMap (·.2.cases) ++ g.agree.map (·.2)

/-- The head `h` probing the domain of `c`: it values what the assigners let it. -/
def probePass (g : CaseAssigners) (c h : Cat) (states : List (PhasedNP × Valuation)) :
    List (PhasedNP × Valuation) :=
  match g.agreeCase h with
  | some k => agreeValue (·.visible c) (k, .agree) states
  | none => states

/-- One spell-out domain: its dependent rules, then its probes in order, then its elsewhere
    case. -/
def domainPass (g : CaseAssigners) (probes : List (Cat × Cat)) (c : Cat)
    (states : List (PhasedNP × Valuation)) : List (PhasedNP × Valuation) :=
  (g.rules c).unmarkedPass (·.spellOut == c) <|
    (probes.filter (·.2 == c)).foldl (fun st hp ↦ probePass g c hp.1 st)
      ((g.rules c).dependentPass (·.visible c) states)

/-- Case for every NP, the domains spelling out in the assigners' order. `probes` lists the
    functional heads present with the phase head whose domain each agrees into. -/
def CaseAssigners.assign (g : CaseAssigners) (probes : List (Cat × Cat)) (nps : List PhasedNP) :
    List (Case.NP × Valuation) :=
  ((g.domains.map (·.1)).foldl (fun st c ↦ domainPass g probes c st)
    (initial (·.lexicalCase) nps)).map fun s ↦ (s.1.toNP, s.2)

/-! ### Totality -/

@[simp] theorem probePass_length (g : CaseAssigners) (c h : Cat)
    (states : List (PhasedNP × Valuation)) : (probePass g c h states).length = states.length := by
  unfold probePass; split <;> simp

private theorem foldlAgree_length (g : CaseAssigners) (c : Cat) (l : List (Cat × Cat))
    (st : List (PhasedNP × Valuation)) :
    (l.foldl (fun st hp ↦ probePass g c hp.1 st) st).length = st.length := by
  induction l generalizing st with
  | nil => rfl
  | cons _ _ ih => exact (ih _).trans (probePass_length ..)

@[simp] theorem domainPass_length (g : CaseAssigners) (probes : List (Cat × Cat)) (c : Cat)
    (states : List (PhasedNP × Valuation)) :
    (domainPass g probes c states).length = states.length := by
  rw [domainPass, Rules.unmarkedPass_length, foldlAgree_length, Rules.dependentPass_length]

private theorem foldlDomain_length (g : CaseAssigners) (probes : List (Cat × Cat)) (cs : List Cat)
    (st : List (PhasedNP × Valuation)) :
    (cs.foldl (fun st c ↦ domainPass g probes c st) st).length = st.length := by
  induction cs generalizing st with
  | nil => rfl
  | cons _ _ ih => exact (ih _).trans (domainPass_length ..)

/-- Assignment is total: one valuation per NP. -/
@[simp] theorem CaseAssigners.assign_length (g : CaseAssigners) (probes : List (Cat × Cat))
    (nps : List PhasedNP) : (g.assign probes nps).length = nps.length := by
  rw [CaseAssigners.assign, List.length_map, foldlDomain_length, Case.initial_length]

/-! ### Valued NPs persist -/

theorem probePass_getElem?_of_some (g : CaseAssigners) (c hd : Cat)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : states[i]? = some (np, some v)) : (probePass g c hd states)[i]? = some (np, some v) := by
  unfold probePass; split
  · exact agreeValue_getElem?_of_some h
  · exact h

private theorem foldlAgree_getElem?_of_some (g : CaseAssigners) (c : Cat) (l : List (Cat × Cat))
    {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : st[i]? = some (np, some v)) :
    (l.foldl (fun st hp ↦ probePass g c hp.1 st) st)[i]? = some (np, some v) := by
  induction l generalizing st with
  | nil => exact h
  | cons hp _ ih => exact ih (probePass_getElem?_of_some g c hp.1 h)

theorem domainPass_getElem?_of_some (g : CaseAssigners) (probes : List (Cat × Cat)) (c : Cat)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : states[i]? = some (np, some v)) :
    (domainPass g probes c states)[i]? = some (np, some v) :=
  Rules.unmarkedPass_getElem?_of_some _ _
    (foldlAgree_getElem?_of_some g c _ (Rules.dependentPass_getElem?_of_some _ _ h))

private theorem foldlDomain_getElem?_of_some (g : CaseAssigners) (probes : List (Cat × Cat))
    (cs : List Cat) {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP}
    {v : Case × Mechanism} (h : st[i]? = some (np, some v)) :
    (cs.foldl (fun st c ↦ domainPass g probes c st) st)[i]? = some (np, some v) := by
  induction cs generalizing st with
  | nil => exact h
  | cons _ _ ih => exact ih (domainPass_getElem?_of_some g probes _ h)

/-- Lexical case is kept through every domain. -/
theorem CaseAssigners.assign_getElem?_of_some (g : CaseAssigners) (probes : List (Cat × Cat))
    {nps : List PhasedNP} {i : ℕ} {np : PhasedNP} {c : Case} (hnp : nps[i]? = some np)
    (hc : np.lexicalCase = some c) :
    (g.assign probes nps)[i]? = some (np.toNP, some (c, .lexical)) := by
  rw [CaseAssigners.assign, List.getElem?_map,
    foldlDomain_getElem?_of_some g probes _ (Case.initial_getElem?_of_some _ hnp hc)]
  rfl

/-! ### The cases the assigners value -/

theorem CaseAssigners.rules_cases_subset (g : CaseAssigners) (c : Cat) :
    (g.rules c).cases ⊆ g.cases := by
  intro x hx
  unfold CaseAssigners.rules at hx
  rcases hf : g.domains.find? (·.1 == c) with _ | ⟨d, r⟩
  · simp [hf, Rules.cases] at hx
  · simp only [hf, Option.map_some, Option.getD_some] at hx
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨(d, r), List.mem_of_find?_eq_some hf, hx⟩)

theorem CaseAssigners.agreeCase_mem_cases {g : CaseAssigners} {h : Cat} {c : Case}
    (hc : g.agreeCase h = some c) : c ∈ g.cases := by
  unfold CaseAssigners.agreeCase at hc
  obtain ⟨⟨d, k⟩, hf, hk⟩ := Option.map_eq_some_iff.1 hc
  subst hk
  exact List.mem_append_right _ (List.mem_map.2 ⟨(d, k), List.mem_of_find?_eq_some hf, rfl⟩)

private theorem probePass_case (g : CaseAssigners) (c hd : Cat)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (probePass g c hd states)[i]? = some (np, some v)) :
    states[i]? = some (np, some v) ∨ v.1 ∈ g.cases := by
  unfold probePass at h
  split at h
  · rename_i k hk
    exact (agreeValue_value h).imp_right fun e ↦ by rw [e]; exact g.agreeCase_mem_cases hk
  · exact .inl h

private theorem foldlAgree_case (g : CaseAssigners) (c : Cat) (l : List (Cat × Cat))
    {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (l.foldl (fun st hp ↦ probePass g c hp.1 st) st)[i]? = some (np, some v)) :
    st[i]? = some (np, some v) ∨ v.1 ∈ g.cases := by
  induction l generalizing st with
  | nil => exact .inl h
  | cons hp _ ih => exact (ih h).elim (probePass_case g c hp.1) .inr

private theorem domainPass_case (g : CaseAssigners) (probes : List (Cat × Cat)) (c : Cat)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (domainPass g probes c states)[i]? = some (np, some v)) :
    states[i]? = some (np, some v) ∨ v.1 ∈ g.cases :=
  ((g.rules c).unmarkedPass_case _ h).elim
    (fun h ↦ (foldlAgree_case g c _ h).elim
      (fun h ↦ ((g.rules c).dependentPass_case _ h).imp_right fun h ↦ g.rules_cases_subset c h)
      .inr)
    (fun h ↦ .inr (g.rules_cases_subset c h))

private theorem foldlDomain_case (g : CaseAssigners) (probes : List (Cat × Cat)) (cs : List Cat)
    {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (cs.foldl (fun st c ↦ domainPass g probes c st) st)[i]? = some (np, some v)) :
    st[i]? = some (np, some v) ∨ v.1 ∈ g.cases := by
  induction cs generalizing st with
  | nil => exact .inl h
  | cons _ _ ih => exact (ih h).elim (domainPass_case g probes _) .inr

/-- A caseless NP is valued only with a case the assigners mention. -/
theorem CaseAssigners.case_mem_cases (g : CaseAssigners) (probes : List (Cat × Cat))
    {nps : List PhasedNP} {i : ℕ} {np : Case.NP} {c : Case} {m : Mechanism}
    (hlex : np.lexicalCase = none) (h : (g.assign probes nps)[i]? = some (np, some (c, m))) :
    c ∈ g.cases := by
  rw [CaseAssigners.assign, List.getElem?_map] at h
  obtain ⟨⟨np', v⟩, hs, hsv⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at hsv
  obtain ⟨hnp, rfl⟩ := hsv
  rcases foldlDomain_case g probes _ hs with h | h
  · have := Case.initial_value h
    rw [← hnp] at hlex
    simp [hlex] at this
  · exact h

/-! ### Assigners without an elsewhere case -/

theorem CaseAssigners.rules_unmarked_of (g : CaseAssigners)
    (hg : ∀ d ∈ g.domains, d.2.unmarked = none) (c : Cat) : (g.rules c).unmarked = none := by
  unfold CaseAssigners.rules
  rcases hf : g.domains.find? (·.1 == c) with _ | d
  · rw [hf]; rfl
  · rw [hf]; exact hg d (List.mem_of_find?_eq_some hf)

private theorem probePass_mechanism (g : CaseAssigners) (c hd : Cat)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (probePass g c hd states)[i]? = some (np, some v)) :
    states[i]? = some (np, some v) ∨ v.2 = .agree := by
  unfold probePass at h
  split at h
  · exact (agreeValue_value h).imp_right (congrArg Prod.snd)
  · exact .inl h

private theorem foldlAgree_mechanism (g : CaseAssigners) (c : Cat) (l : List (Cat × Cat))
    {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (l.foldl (fun st hp ↦ probePass g c hp.1 st) st)[i]? = some (np, some v)) :
    st[i]? = some (np, some v) ∨ v.2 = .agree := by
  induction l generalizing st with
  | nil => exact .inl h
  | cons hp _ ih => exact (ih h).elim (probePass_mechanism g c hp.1) .inr

private theorem domainPass_mechanism (g : CaseAssigners) (probes : List (Cat × Cat)) (c : Cat)
    (hu : (g.rules c).unmarked = none) {states : List (PhasedNP × Valuation)} {i : ℕ}
    {np : PhasedNP} {v : Case × Mechanism}
    (h : (domainPass g probes c states)[i]? = some (np, some v)) :
    states[i]? = some (np, some v) ∨ v.2 = .dependent ∨ v.2 = .agree := by
  unfold domainPass at h
  rw [Rules.unmarkedPass_of_none _ _ hu] at h
  rcases foldlAgree_mechanism g c _ h with h | h
  · exact ((g.rules c).dependentPass_mechanism _ h).imp_right .inl
  · exact .inr (.inr h)

private theorem foldlDomain_mechanism (g : CaseAssigners) (probes : List (Cat × Cat))
    (hg : ∀ d ∈ g.domains, d.2.unmarked = none) (cs : List Cat)
    {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (cs.foldl (fun st c ↦ domainPass g probes c st) st)[i]? = some (np, some v)) :
    st[i]? = some (np, some v) ∨ v.2 = .dependent ∨ v.2 = .agree := by
  induction cs generalizing st with
  | nil => exact .inl h
  | cons c _ ih =>
    exact (ih h).elim (domainPass_mechanism g probes c (g.rules_unmarked_of hg c)) .inr

/-- Assigners with no elsewhere case in any domain never value an NP as unmarked: an NP that
    no rule and no head reaches stays caseless. -/
theorem CaseAssigners.mechanism_ne_unmarked (g : CaseAssigners) (probes : List (Cat × Cat))
    (hg : ∀ d ∈ g.domains, d.2.unmarked = none) {nps : List PhasedNP} {i : ℕ} {np : Case.NP}
    {c : Case} {m : Mechanism} (h : (g.assign probes nps)[i]? = some (np, some (c, m))) :
    m ≠ .unmarked := by
  rw [CaseAssigners.assign, List.getElem?_map] at h
  obtain ⟨⟨np', v⟩, hs, hsv⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at hsv
  obtain ⟨-, rfl⟩ := hsv
  rcases foldlDomain_mechanism g probes hg _ hs with h | h | h
  · have := Case.initial_mechanism h
    intro hm; simp [hm] at this
  · intro hm; simp [hm] at h
  · intro hm; simp [hm] at h

end Minimalist
