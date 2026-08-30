import Linglib.Syntax.Case.Dependent
import Linglib.Syntax.Minimalist.Defs

/-!
# Dependent case by phase

The configurational rules of `Syntax/Case/Dependent.lean` run domain by domain: each phase
head's spell-out domain has its own high, low and elsewhere cases, the domains spell out
innermost first, and a case valued in an inner domain — or by a lexical head — is never
overwritten, so a dative valued in the verb phrase survives the clause. Functional heads may
also value case under Agree, each probing the highest caseless NP of the domain it agrees
into. A grammar is the table of domain rules together with the Agree cases, so a purely
configurational grammar, a purely Agree-based one, and the hybrids are points in one space.
Which functional heads a derivation contains is a fact about it, so assignment takes the
probes present with the domain each agrees into.

## Main definitions

* `PhasedNP`: an NP with the phase head whose domain merges it, and whether it has shifted
  to the clause edge.
* `CaseGrammar`: the phase heads in spell-out order with their rules, and the Agree cases.
* `CaseGrammar.assign`: case for every NP of a derivation.

## Main results

* `CaseGrammar.assign_length`: assignment is total.
* `CaseGrammar.assign_getElem?_of_some`: lexical case is kept.
* `CaseGrammar.case_mem_cases`: a caseless NP is valued only with a case the grammar
  mentions.

## References

* [baker-vinokurova-2010]
* [baker-2015]
* [chomsky-2000], [chomsky-2001]
-/

namespace Minimalist

open Case (Rules Mechanism Valuation initial markBy eligible)

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

/-- A grammar of structural case: the phase heads in spell-out order with the rules of their
    domains, and the case each functional head values under Agree. -/
structure CaseGrammar where
  domains : List (Cat × Rules)
  agree : List (Cat × Case) := []
  deriving DecidableEq, Repr

/-- The rules of the domain of `c`. -/
def CaseGrammar.rules (g : CaseGrammar) (c : Cat) : Rules :=
  ((g.domains.find? (·.1 == c)).map (·.2)).getD {}

/-- The case `h` values under Agree, if any. -/
def CaseGrammar.agreeCase (g : CaseGrammar) (h : Cat) : Option Case :=
  (g.agree.find? (·.1 == h)).map (·.2)

/-- The cases the grammar can value a caseless NP with. -/
def CaseGrammar.cases (g : CaseGrammar) : List Case :=
  g.domains.flatMap (·.2.cases) ++ g.agree.map (·.2)

/-- The alignment the clausal rules show. -/
def CaseGrammar.alignment (g : CaseGrammar) : Alignment.AlignmentType := (g.rules .C).alignment

/-- A head valuing `c` under Agree in the domain `P` selects values its highest unvalued NP. -/
def agreePass (c : Case) (P : PhasedNP → Bool) (states : List (PhasedNP × Valuation)) :
    List (PhasedNP × Valuation) :=
  match eligible P states with
  | i :: _ => markBy (λ j _ => if j = i then some (c, .agree) else none) states
  | [] => states

/-- The head `h` probing the domain of `c`: it values what the grammar lets it. -/
def probePass (g : CaseGrammar) (c h : Cat) (states : List (PhasedNP × Valuation)) :
    List (PhasedNP × Valuation) :=
  match g.agreeCase h with
  | some k => agreePass k (·.visible c) states
  | none => states

/-- One spell-out domain: its dependent rules, then its probes in order, then its elsewhere
    case. -/
def domainPass (g : CaseGrammar) (probes : List (Cat × Cat)) (c : Cat)
    (states : List (PhasedNP × Valuation)) : List (PhasedNP × Valuation) :=
  (g.rules c).unmarkedPass (·.spellOut == c) <|
    (probes.filter (·.2 == c)).foldl (λ st hp => probePass g c hp.1 st)
      ((g.rules c).dependentPass (·.visible c) states)

/-- Case for every NP, the domains spelling out in the grammar's order. `probes` lists the
    functional heads present with the phase head whose domain each agrees into. -/
def CaseGrammar.assign (g : CaseGrammar) (probes : List (Cat × Cat)) (nps : List PhasedNP) :
    List (Case.NP × Valuation) :=
  ((g.domains.map (·.1)).foldl (λ st c => domainPass g probes c st)
    (initial (·.lexicalCase) nps)).map λ s => (s.1.toNP, s.2)

/-! ### Totality -/

@[simp] theorem agreePass_length (c : Case) (P : PhasedNP → Bool)
    (states : List (PhasedNP × Valuation)) : (agreePass c P states).length = states.length := by
  unfold agreePass; split <;> simp

@[simp] theorem probePass_length (g : CaseGrammar) (c h : Cat)
    (states : List (PhasedNP × Valuation)) : (probePass g c h states).length = states.length := by
  unfold probePass; split <;> simp

private theorem foldlAgree_length (g : CaseGrammar) (c : Cat) (l : List (Cat × Cat))
    (st : List (PhasedNP × Valuation)) :
    (l.foldl (λ st hp => probePass g c hp.1 st) st).length = st.length := by
  induction l generalizing st with
  | nil => rfl
  | cons _ _ ih => exact (ih _).trans (probePass_length ..)

@[simp] theorem domainPass_length (g : CaseGrammar) (probes : List (Cat × Cat)) (c : Cat)
    (states : List (PhasedNP × Valuation)) :
    (domainPass g probes c states).length = states.length := by
  rw [domainPass, Rules.unmarkedPass_length, foldlAgree_length, Rules.dependentPass_length]

private theorem foldlDomain_length (g : CaseGrammar) (probes : List (Cat × Cat)) (cs : List Cat)
    (st : List (PhasedNP × Valuation)) :
    (cs.foldl (λ st c => domainPass g probes c st) st).length = st.length := by
  induction cs generalizing st with
  | nil => rfl
  | cons _ _ ih => exact (ih _).trans (domainPass_length ..)

/-- Assignment is total: one valuation per NP. -/
@[simp] theorem CaseGrammar.assign_length (g : CaseGrammar) (probes : List (Cat × Cat))
    (nps : List PhasedNP) : (g.assign probes nps).length = nps.length := by
  rw [CaseGrammar.assign, List.length_map, foldlDomain_length, Case.initial_length]

/-! ### Valued NPs persist -/

theorem agreePass_getElem?_of_some (c : Case) (P : PhasedNP → Bool)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : states[i]? = some (np, some v)) : (agreePass c P states)[i]? = some (np, some v) := by
  unfold agreePass; split
  · exact Case.markBy_getElem?_of_some _ h
  · exact h

theorem probePass_getElem?_of_some (g : CaseGrammar) (c hd : Cat)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : states[i]? = some (np, some v)) : (probePass g c hd states)[i]? = some (np, some v) := by
  unfold probePass; split
  · exact agreePass_getElem?_of_some _ _ h
  · exact h

private theorem foldlAgree_getElem?_of_some (g : CaseGrammar) (c : Cat) (l : List (Cat × Cat))
    {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : st[i]? = some (np, some v)) :
    (l.foldl (λ st hp => probePass g c hp.1 st) st)[i]? = some (np, some v) := by
  induction l generalizing st with
  | nil => exact h
  | cons hp _ ih => exact ih (probePass_getElem?_of_some g c hp.1 h)

theorem domainPass_getElem?_of_some (g : CaseGrammar) (probes : List (Cat × Cat)) (c : Cat)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : states[i]? = some (np, some v)) :
    (domainPass g probes c states)[i]? = some (np, some v) :=
  Rules.unmarkedPass_getElem?_of_some _ _
    (foldlAgree_getElem?_of_some g c _ (Rules.dependentPass_getElem?_of_some _ _ h))

private theorem foldlDomain_getElem?_of_some (g : CaseGrammar) (probes : List (Cat × Cat))
    (cs : List Cat) {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP}
    {v : Case × Mechanism} (h : st[i]? = some (np, some v)) :
    (cs.foldl (λ st c => domainPass g probes c st) st)[i]? = some (np, some v) := by
  induction cs generalizing st with
  | nil => exact h
  | cons _ _ ih => exact ih (domainPass_getElem?_of_some g probes _ h)

/-- Lexical case is kept through every domain. -/
theorem CaseGrammar.assign_getElem?_of_some (g : CaseGrammar) (probes : List (Cat × Cat))
    {nps : List PhasedNP} {i : ℕ} {np : PhasedNP} {c : Case} (hnp : nps[i]? = some np)
    (hc : np.lexicalCase = some c) :
    (g.assign probes nps)[i]? = some (np.toNP, some (c, .lexical)) := by
  rw [CaseGrammar.assign, List.getElem?_map,
    foldlDomain_getElem?_of_some g probes _ (Case.initial_getElem?_of_some _ hnp hc)]
  rfl

/-! ### The cases a grammar values -/

theorem CaseGrammar.rules_cases_subset (g : CaseGrammar) (c : Cat) :
    (g.rules c).cases ⊆ g.cases := by
  intro x hx
  unfold CaseGrammar.rules at hx
  rcases hf : g.domains.find? (·.1 == c) with _ | ⟨d, r⟩
  · simp [hf, Rules.cases] at hx
  · simp only [hf, Option.map_some, Option.getD_some] at hx
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨(d, r), List.mem_of_find?_eq_some hf, hx⟩)

theorem CaseGrammar.agreeCase_mem_cases {g : CaseGrammar} {h : Cat} {c : Case}
    (hc : g.agreeCase h = some c) : c ∈ g.cases := by
  unfold CaseGrammar.agreeCase at hc
  obtain ⟨⟨d, k⟩, hf, hk⟩ := Option.map_eq_some_iff.1 hc
  subst hk
  exact List.mem_append_right _ (List.mem_map.2 ⟨(d, k), List.mem_of_find?_eq_some hf, rfl⟩)

private theorem agreePass_case (c : Case) (P : PhasedNP → Bool)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (agreePass c P states)[i]? = some (np, some v)) :
    states[i]? = some (np, some v) ∨ v.1 = c := by
  unfold agreePass at h
  split at h
  · refine (Case.markBy_value h).imp_right λ ⟨s, _, _, hf⟩ => ?_
    split_ifs at hf
    obtain rfl := Option.some.inj hf
    rfl
  · exact .inl h

private theorem probePass_case (g : CaseGrammar) (c hd : Cat)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (probePass g c hd states)[i]? = some (np, some v)) :
    states[i]? = some (np, some v) ∨ v.1 ∈ g.cases := by
  unfold probePass at h
  split at h
  · rename_i k hk
    exact (agreePass_case k _ h).imp_right λ e => by rw [e]; exact g.agreeCase_mem_cases hk
  · exact .inl h

private theorem foldlAgree_case (g : CaseGrammar) (c : Cat) (l : List (Cat × Cat))
    {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (l.foldl (λ st hp => probePass g c hp.1 st) st)[i]? = some (np, some v)) :
    st[i]? = some (np, some v) ∨ v.1 ∈ g.cases := by
  induction l generalizing st with
  | nil => exact .inl h
  | cons hp _ ih => exact (ih h).elim (probePass_case g c hp.1) .inr

private theorem domainPass_case (g : CaseGrammar) (probes : List (Cat × Cat)) (c : Cat)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (domainPass g probes c states)[i]? = some (np, some v)) :
    states[i]? = some (np, some v) ∨ v.1 ∈ g.cases :=
  ((g.rules c).unmarkedPass_case _ h).elim
    (λ h => (foldlAgree_case g c _ h).elim
      (λ h => ((g.rules c).dependentPass_case _ h).imp_right λ h => g.rules_cases_subset c h)
      .inr)
    (λ h => .inr (g.rules_cases_subset c h))

private theorem foldlDomain_case (g : CaseGrammar) (probes : List (Cat × Cat)) (cs : List Cat)
    {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (cs.foldl (λ st c => domainPass g probes c st) st)[i]? = some (np, some v)) :
    st[i]? = some (np, some v) ∨ v.1 ∈ g.cases := by
  induction cs generalizing st with
  | nil => exact .inl h
  | cons _ _ ih => exact (ih h).elim (domainPass_case g probes _) .inr

/-- A caseless NP is valued only with a case the grammar mentions. -/
theorem CaseGrammar.case_mem_cases (g : CaseGrammar) (probes : List (Cat × Cat))
    {nps : List PhasedNP} {i : ℕ} {np : Case.NP} {c : Case} {m : Mechanism}
    (hlex : np.lexicalCase = none) (h : (g.assign probes nps)[i]? = some (np, some (c, m))) :
    c ∈ g.cases := by
  rw [CaseGrammar.assign, List.getElem?_map] at h
  obtain ⟨⟨np', v⟩, hs, hsv⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at hsv
  obtain ⟨hnp, rfl⟩ := hsv
  rcases foldlDomain_case g probes _ hs with h | h
  · have := Case.initial_value h
    rw [← hnp] at hlex
    simp [hlex] at this
  · exact h

/-! ### A grammar without an elsewhere case -/

theorem CaseGrammar.rules_unmarked_of (g : CaseGrammar)
    (hg : ∀ d ∈ g.domains, d.2.unmarked = none) (c : Cat) : (g.rules c).unmarked = none := by
  unfold CaseGrammar.rules
  rcases hf : g.domains.find? (·.1 == c) with _ | d
  · rw [hf]; rfl
  · rw [hf]; exact hg d (List.mem_of_find?_eq_some hf)

private theorem agreePass_mechanism (c : Case) (P : PhasedNP → Bool)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (agreePass c P states)[i]? = some (np, some v)) :
    states[i]? = some (np, some v) ∨ v.2 = .agree := by
  unfold agreePass at h
  split at h
  · refine (Case.markBy_value h).imp_right λ ⟨s, _, _, hf⟩ => ?_
    split_ifs at hf
    obtain rfl := Option.some.inj hf
    rfl
  · exact .inl h

private theorem probePass_mechanism (g : CaseGrammar) (c hd : Cat)
    {states : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (probePass g c hd states)[i]? = some (np, some v)) :
    states[i]? = some (np, some v) ∨ v.2 = .agree := by
  unfold probePass at h
  split at h
  · exact agreePass_mechanism _ _ h
  · exact .inl h

private theorem foldlAgree_mechanism (g : CaseGrammar) (c : Cat) (l : List (Cat × Cat))
    {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (l.foldl (λ st hp => probePass g c hp.1 st) st)[i]? = some (np, some v)) :
    st[i]? = some (np, some v) ∨ v.2 = .agree := by
  induction l generalizing st with
  | nil => exact .inl h
  | cons hp _ ih => exact (ih h).elim (probePass_mechanism g c hp.1) .inr

private theorem domainPass_mechanism (g : CaseGrammar) (probes : List (Cat × Cat)) (c : Cat)
    (hu : (g.rules c).unmarked = none) {states : List (PhasedNP × Valuation)} {i : ℕ}
    {np : PhasedNP} {v : Case × Mechanism}
    (h : (domainPass g probes c states)[i]? = some (np, some v)) :
    states[i]? = some (np, some v) ∨ v.2 = .dependent ∨ v.2 = .agree := by
  unfold domainPass at h
  rw [Rules.unmarkedPass_of_none _ _ hu] at h
  rcases foldlAgree_mechanism g c _ h with h | h
  · exact ((g.rules c).dependentPass_mechanism _ h).imp_right .inl
  · exact .inr (.inr h)

private theorem foldlDomain_mechanism (g : CaseGrammar) (probes : List (Cat × Cat))
    (hg : ∀ d ∈ g.domains, d.2.unmarked = none) (cs : List Cat)
    {st : List (PhasedNP × Valuation)} {i : ℕ} {np : PhasedNP} {v : Case × Mechanism}
    (h : (cs.foldl (λ st c => domainPass g probes c st) st)[i]? = some (np, some v)) :
    st[i]? = some (np, some v) ∨ v.2 = .dependent ∨ v.2 = .agree := by
  induction cs generalizing st with
  | nil => exact .inl h
  | cons c _ ih =>
    exact (ih h).elim (domainPass_mechanism g probes c (g.rules_unmarked_of hg c)) .inr

/-- A grammar with no elsewhere case in any domain never values an NP as unmarked: an NP that
    no rule and no head reaches stays caseless. -/
theorem CaseGrammar.mechanism_ne_unmarked (g : CaseGrammar) (probes : List (Cat × Cat))
    (hg : ∀ d ∈ g.domains, d.2.unmarked = none) {nps : List PhasedNP} {i : ℕ} {np : Case.NP}
    {c : Case} {m : Mechanism} (h : (g.assign probes nps)[i]? = some (np, some (c, m))) :
    m ≠ .unmarked := by
  rw [CaseGrammar.assign, List.getElem?_map] at h
  obtain ⟨⟨np', v⟩, hs, hsv⟩ := Option.map_eq_some_iff.1 h
  simp only [Prod.mk.injEq] at hsv
  obtain ⟨-, rfl⟩ := hsv
  rcases foldlDomain_mechanism g probes hg _ hs with h | h | h
  · have := Case.initial_mechanism h
    intro hm; simp [hm] at this
  · intro hm; simp [hm] at h
  · intro hm; simp [hm] at h

end Minimalist
