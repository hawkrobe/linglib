module

public import Linglib.Syntax.Minimalist.Case.Dependent
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Order.Minimal

/-!
# Obligatory and secondary licensing

This file formalizes the theory of nominal licensing of [kalin-2018]. Every nominal bears a Case
feature, unvalued unless a lexical head has valued it, and so every nominal is visible to a
licenser; only some nominals bear *uninterpretable* Case ([pesetsky-torrego-2007]), and those
alone crash the derivation when their Case goes unvalued. A licenser is a head with a φ-probe
that Agrees with the highest nominal in the phase domain it probes whose Case is still unvalued,
and values that Case (`agreeValue`). Some licensers merge in every derivation; a secondary
licenser merges only as a last resort ([rezac-2011]), by the Licensing Economy Principle: it is
activated iff the derivation would otherwise not converge. Differential object marking is the
visible signature of a secondary licenser.

The derivation never sees which nominals need licensing, since it runs on `PhasedNP`s: an
obligatory licenser values the highest nominal in its domain whatever its needs, and needs are
read only by convergence. Licensing is monotone in the licensers, activating one more never
leaving a nominal unvalued, so the Licensing Economy Principle, stated for each secondary
licenser, coincides with the preference for a derivation with fewer licensers. Licensing is the
Agree modality of case assignment: case assigners with no dependent or elsewhere case assign
exactly what the licensing derivation does, each licenser read as the case its head values.

## Main definitions

* `Licenser`: a head with a φ-probe, the phase domain it probes, and whether it is obligatory.
* `LicensedNP`: a nominal together with whether it needs licensing.
* `CaseValue`: what valued a nominal's Case, a lexical head or a licenser.
* `license`: the licensers of each phase domain merged in order as the domains spell out.
* `Converges`: every nominal that needs licensing has its Case valued.
* `activate`, `Economical`: the licensers under an activation of secondaries, and the
  activations the Licensing Economy Principle selects.
* `IsDOMMarked`: a nominal's Case was valued by a secondary licenser.

## Main results

* `agree_cons_none`: a licenser values the highest unvalued nominal in its domain, whether or
  not that nominal needs licensing.
* `license_mono`, `monotone_converges_activate`: activating more licensers values more
  nominals.
* `economical_iff`: the Licensing Economy Principle as stated for each secondary licenser.
* `exists_economical_iff`: some activation is economical iff the clause converges with all of
  its licensers.
* `Economical.eq_empty`, `Economical.not_isDOMMarked`: when the obligatory licensers suffice,
  no secondary is activated and nothing is marked.
* `CaseAssigners.assign_eq_map_license`: licensing is the Agree modality of case assignment.

## Implementation notes

Nominals are listed from the highest down; the licensers probing one phase domain are listed in
merge order, the lowest first, and the domains spell out in the order given. Only structural
licensing under c-command is modelled: an inherent licenser that values only its specifier is
not.

## References

* [kalin-2018]
* [pesetsky-torrego-2007]
* [rezac-2011]
* [baker-vinokurova-2010]
-/

@[expose] public section

namespace Minimalist.Licensing

open List
open Case (Valuation)

/-! ### Licensers and nominals -/

/-- Whether a licenser merges in every derivation or only as a last resort. -/
inductive LicenserKind where
  | obligatory
  | secondary
  deriving DecidableEq, Repr

/-- A licenser: a head with a φ-probe, the phase whose domain it probes, and whether it merges in
every derivation. -/
structure Licenser where
  head : Cat
  domain : Cat := .C
  kind : LicenserKind
  deriving DecidableEq, Repr

/-- A nominal together with whether it bears uninterpretable Case and so needs licensing. -/
structure LicensedNP extends PhasedNP where
  needsLicensing : Bool
  deriving DecidableEq, Repr

/-- A nominal is active, visible to a probe, iff its Case is unvalued. Every nominal bears
unvalued Case unless a lexical head has valued it, whether or not it needs licensing. -/
def LicensedNP.isActive (np : LicensedNP) : Bool := np.lexicalCase.isNone

/-- What valued a nominal's Case: a lexical head, with the case it assigned, or a licenser. -/
inductive CaseValue where
  | lexical (c : _root_.Case)
  | licenser (l : Licenser)
  deriving DecidableEq, Repr

/-! ### The derivation -/

/-- The Case of each nominal before any licenser probes: valued only by a lexical head. -/
def initial (nps : List PhasedNP) : Valuation PhasedNP CaseValue :=
  Valuation.initial (·.lexicalCase.map .lexical) nps

/-- The Agree of licenser `l`. -/
def Licenser.agree (l : Licenser) : Valuation PhasedNP CaseValue → Valuation PhasedNP CaseValue :=
  agreeValue (·.visible l.domain) (.licenser l)

/-- The licensers probing the domain of `c` merge, the lowest first. -/
def cycle (ls : List Licenser) (c : Cat) (st : Valuation PhasedNP CaseValue) :
    Valuation PhasedNP CaseValue :=
  (ls.filter (·.domain == c)).foldl (fun st l ↦ l.agree st) st

/-- The derivation: the phase domains `ds` spell out in order, each with its licensers. -/
def license (ds : List Cat) (ls : List Licenser) (nps : List PhasedNP) :
    Valuation PhasedNP CaseValue :=
  ds.foldl (fun st c ↦ cycle ls c st) (initial nps)

/-- A derivation converges iff every nominal that needs licensing has its Case valued. -/
def Converges (ds : List Cat) (ls : List Licenser) (nps : List LicensedNP) : Prop :=
  Forall₂ (fun np p ↦ np.needsLicensing → p.2.isSome) nps (license ds ls (nps.map (·.toPhasedNP)))

instance (ds : List Cat) (ls : List Licenser) (nps : List LicensedNP) :
    Decidable (Converges ds ls nps) :=
  inferInstanceAs (Decidable (Forall₂ _ _ _))

/-- A nominal is DOM-marked iff a secondary licenser valued its Case. -/
def IsDOMMarked : Option CaseValue → Prop
  | some (.licenser l) => l.kind = .secondary
  | _ => False

instance : DecidablePred IsDOMMarked
  | some (.licenser l) => inferInstanceAs (Decidable (l.kind = .secondary))
  | some (.lexical _) | none => inferInstanceAs (Decidable False)

section Derivation

variable {l : Licenser} {ds : List Cat} {ls ls' : List Licenser} {nps : List LicensedNP}

/-- A licenser values the highest nominal of its domain if that nominal's Case is unvalued. -/
theorem agree_cons_none {np : PhasedNP} (hnp : np.visible l.domain)
    (s : Valuation PhasedNP CaseValue) :
    l.agree ((np, none) :: s) = (np, some (.licenser l)) :: s := by
  simp [Licenser.agree, hnp]

/-- A licenser passes over a nominal whose Case is already valued. -/
theorem agree_cons_some (np : PhasedNP) (v : CaseValue) (s : Valuation PhasedNP CaseValue) :
    l.agree ((np, some v) :: s) = (np, some v) :: l.agree s := by
  simp [Licenser.agree]

/-- The derivation extends the lexical valuation, each value it adds naming a licenser of the
clause. -/
theorem extends_license (ds : List Cat) (ls : List Licenser) (nps : List PhasedNP) :
    (initial nps).Extends (fun v ↦ ∀ l, v = .licenser l → l ∈ ls) (license ds ls nps) :=
  Valuation.Extends.foldl _ (fun c _ st ↦ Valuation.Extends.foldl _
    (fun l hl st ↦ extends_agreeValue (fun _ h ↦ by cases h; exact mem_of_mem_filter hl) st) st) _

@[simp]
theorem length_license (ds : List Cat) (ls : List Licenser) (nps : List PhasedNP) :
    (license ds ls nps).length = nps.length := by
  simp [← (extends_license ds ls nps).length_eq, initial]

/-- Every licenser that values a nominal's Case is a licenser of the clause. -/
theorem mem_of_mem_license {nps : List PhasedNP} {np : PhasedNP}
    (h : (np, some (.licenser l)) ∈ license ds ls nps) : l ∈ ls := by
  rcases (extends_license ds ls nps).of_mem h with h | h
  · simp [initial, Valuation.initial] at h
  · exact h l rfl

/-! ### Monotonicity -/

private theorem forall₂_trans {α β γ : Type*} {R : α → β → Prop} {S : β → γ → Prop}
    {T : α → γ → Prop} (hRST : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l₁ l₂ l₃}, Forall₂ R l₁ l₂ → Forall₂ S l₂ l₃ → Forall₂ T l₁ l₃
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h₁ h₂, .cons h₃ h₄ =>
    .cons (hRST _ _ _ h₁ h₃) (forall₂_trans hRST h₂ h₄)

private theorem valuedLE_foldl_agree :
    ∀ {L L' : List Licenser}, L <+ L' → ∀ {s t : Valuation PhasedNP CaseValue}, s.ValuedLE t →
      (L.foldl (fun st l ↦ l.agree st) s).ValuedLE (L'.foldl (fun st l ↦ l.agree st) t)
  | _, _, .slnil, _, _, h => h
  | _, _, .cons l hL, _, _, h =>
    valuedLE_foldl_agree hL (h.trans (valuedLE_agreeValue _))
  | _, _, .cons_cons l hL, _, _, h => valuedLE_foldl_agree hL h.agreeValue

/-- Adding licensers to a clause never leaves a nominal unvalued. -/
theorem license_mono (h : ls <+ ls') (ds : List Cat) (nps : List PhasedNP) :
    (license ds ls nps).ValuedLE (license ds ls' nps) := by
  suffices ∀ {s t : Valuation PhasedNP CaseValue}, s.ValuedLE t →
      (ds.foldl (fun st c ↦ cycle ls c st) s).ValuedLE (ds.foldl (fun st c ↦ cycle ls' c st) t)
    from this (.refl _)
  induction ds with
  | nil => exact id
  | cons c ds ih => exact fun hst ↦ ih (valuedLE_foldl_agree (h.filter _) hst)

theorem Converges.mono (hc : Converges ds ls nps) (h : ls <+ ls') : Converges ds ls' nps :=
  forall₂_trans (fun _ _ _ h₁ h₂ hn ↦ h₂.2 (h₁ hn)) hc (license_mono h ds _)

/-- A clause with no nominal that needs licensing converges. -/
theorem converges_of_forall_needsLicensing_eq_false
    (h : ∀ np ∈ nps, np.needsLicensing = false) : Converges ds ls nps :=
  forall₂_iff_zip.2 ⟨by simp, fun hx hn ↦ by simp [h _ (of_mem_zip hx).1] at hn⟩

end Derivation

/-! ### The Licensing Economy Principle -/

section Economy

variable {ds : List Cat} {ls : List Licenser} {nps : List LicensedNP} {S : Finset Licenser}

/-- The licensers of a clause when the secondaries in `S` are activated: the obligatory ones
and the activated ones, in place. -/
def activate (ls : List Licenser) (S : Finset Licenser) : List Licenser :=
  ls.filter fun l ↦ decide (l.kind = .obligatory ∨ l ∈ S)

/-- An activation is economical iff it converges and no activation of fewer licensers does: the
derivation with fewer licensers is preferred. -/
def Economical (ds : List Cat) (ls : List Licenser) (nps : List LicensedNP)
    (S : Finset Licenser) : Prop :=
  Minimal (fun S ↦ Converges ds (activate ls S) nps) S

theorem activate_sublist (ls : List Licenser) (S : Finset Licenser) : activate ls S <+ ls :=
  filter_sublist

theorem monotone_converges_activate (ds : List Cat) (ls : List Licenser)
    (nps : List LicensedNP) : Monotone fun S ↦ Converges ds (activate ls S) nps :=
  fun _ _ hS hc ↦ hc.mono <| monotone_filter_right _ fun _ ↦ by simpa using Or.imp_right (@hS _)

/-- The Licensing Economy Principle, (36) of [kalin-2018]: an activation is economical iff it
converges and each activated secondary licenser is activated because the derivation would
otherwise not converge. -/
theorem economical_iff : Economical ds ls nps S ↔
    Converges ds (activate ls S) nps ∧ ∀ l ∈ S, ¬ Converges ds (activate ls (S.erase l)) nps :=
  Finset.minimal_iff_forall_erase fun _ _ h hts ↦ monotone_converges_activate ds ls nps hts h

instance : Decidable (Economical ds ls nps S) := decidable_of_iff' _ economical_iff

/-- Every activated licenser is a secondary licenser of the clause. -/
theorem Economical.mem (h : Economical ds ls nps S) {l : Licenser} (hl : l ∈ S) :
    l ∈ ls ∧ l.kind = .secondary := by
  rw [economical_iff] at h
  by_contra hs
  have he : activate ls (S.erase l) = activate ls S := filter_congr fun x hx ↦ by
    by_cases hxl : x = l
    · subst hxl
      cases hk : x.kind <;> simp_all
    · simp [hxl]
  exact h.2 l hl (he ▸ h.1)

theorem Economical.subset_toFinset (h : Economical ds ls nps S) : S ⊆ ls.toFinset :=
  fun _ hl ↦ mem_toFinset.2 (h.mem hl).1

/-- An economical activation exists iff the clause converges with all its licensers. -/
theorem exists_economical_iff : (∃ S, Economical ds ls nps S) ↔ Converges ds ls nps := by
  refine ⟨fun ⟨S, h⟩ ↦ (Minimal.prop h).mono (activate_sublist _ _), fun h ↦ ?_⟩
  refine exists_minimal_of_wellFoundedLT _ ⟨ls.toFinset, ?_⟩
  rwa [activate, filter_eq_self.2 fun l hl ↦ by simp [mem_toFinset.2 hl]]

/-- If the obligatory licensers suffice, no secondary licenser is activated. -/
theorem Economical.eq_empty (h : Economical ds ls nps S)
    (h₀ : Converges ds (activate ls ∅) nps) : S = ∅ :=
  (Minimal.eq_of_le h h₀ (Finset.empty_subset S)).symm

/-- If the obligatory licensers suffice, the economical derivation marks no nominal. -/
theorem Economical.not_isDOMMarked (h : Economical ds ls nps S)
    (h₀ : Converges ds (activate ls ∅) nps) :
    ∀ p ∈ license ds (activate ls S) (nps.map (·.toPhasedNP)), ¬ IsDOMMarked p.2 := by
  rintro ⟨np, _ | _ | l⟩ hp hdom <;> simp only [IsDOMMarked] at hdom
  have hl := mem_of_mem_license hp
  simp [h.eq_empty h₀, activate, hdom] at hl

end Economy

/-! ### Licensing as the Agree modality of case assignment -/

/-- The case and mechanism a Case value amounts to: the lexical case, or under Agree the case
`κ` gives the licensing head. -/
def CaseValue.assigned (κ : Cat → _root_.Case) :
    CaseValue → _root_.Case × _root_.Case.Mechanism
  | .lexical c => (c, .lexical)
  | .licenser l => (κ l.head, .agree)

private theorem rules_eq_of (g : CaseAssigners) (hg : ∀ d ∈ g.domains, d.2 = {}) (c : Cat) :
    g.rules c = {} := by
  unfold CaseAssigners.rules
  rcases hf : g.domains.find? (·.1 == c) with _ | d
  · rw [hf]; rfl
  · rw [hf]; exact hg d (mem_of_find?_eq_some hf)

/-- Licensing is the Agree modality of case assignment: case assigners with no dependent or
elsewhere case in any domain, under which each licenser's head values the case `κ` gives it,
assign what the licensing derivation does, each licenser read as that case. -/
theorem _root_.Minimalist.CaseAssigners.assign_eq_map_license (g : CaseAssigners)
    (hg : ∀ d ∈ g.domains, d.2 = {}) (κ : Cat → _root_.Case) {ls : List Licenser}
    (hκ : ∀ l ∈ ls, g.agreeCase l.head = some (κ l.head)) (nps : List PhasedNP) :
    g.assign (ls.map fun l ↦ (l.head, l.domain)) nps =
      (license (g.domains.map (·.1)) ls nps).map
        fun p ↦ (p.1.toNP, p.2.map (CaseValue.assigned κ)) := by
  set φ : PhasedNP × Option CaseValue → PhasedNP × Option (_root_.Case × _root_.Case.Mechanism) :=
    Prod.map id (Option.map (CaseValue.assigned κ))
  have key (c : Cat) (L : List Licenser)
      (hL : ∀ l ∈ L, l.domain = c ∧ g.agreeCase l.head = some (κ l.head))
      (st : Valuation PhasedNP CaseValue) :
      L.foldl (fun st l ↦ probePass g c l.head st) (st.map φ) =
        (L.foldl (fun st l ↦ l.agree st) st).map φ := by
    induction L generalizing st with
    | nil => rfl
    | cons l L ih =>
      obtain ⟨hdom, hcase⟩ := hL l (mem_cons_self ..)
      have hstep : probePass g c l.head (st.map φ) = (l.agree st).map φ := by
        simp only [probePass, hcase, Licenser.agree, hdom]
        exact agreeValue_map (P := (·.visible c)) (P' := (·.visible c)) (v := .licenser l)
          id (CaseValue.assigned κ) (fun _ ↦ rfl) rfl st
      rw [foldl_cons, foldl_cons, hstep, ih (fun l hl ↦ hL l (mem_cons_of_mem _ hl))]
  have hcycle (c : Cat) (st : Valuation PhasedNP CaseValue) :
      domainPass g (ls.map fun l ↦ (l.head, l.domain)) c (st.map φ) = (cycle ls c st).map φ := by
    rw [domainPass, rules_eq_of g hg, _root_.Case.Rules.unmarkedPass_of_none _ _ rfl,
      _root_.Case.Rules.dependentPass_of_none _ _ rfl rfl, filter_map, foldl_map, cycle]
    exact key c _ (fun l hl ↦ by
      obtain ⟨hl, hc⟩ := mem_filter.1 hl
      exact ⟨by simpa using hc, hκ l hl⟩) st
  have hinit : _root_.Case.lexicalValuation (·.lexicalCase) nps = (initial nps).map φ := by
    simp [_root_.Case.lexicalValuation, initial, Valuation.initial, φ, Option.map_map,
      Function.comp_def, CaseValue.assigned]
  rw [CaseAssigners.assign, CaseAssigners.derive, license, hinit]
  suffices ∀ st : Valuation PhasedNP CaseValue, (g.domains.map (·.1)).foldl
      (fun st c ↦ domainPass g (ls.map fun l ↦ (l.head, l.domain)) c st) (st.map φ) =
      ((g.domains.map (·.1)).foldl (fun st c ↦ cycle ls c st) st).map φ by
    rw [this, map_map]; rfl
  intro st
  induction g.domains.map (·.1) generalizing st with
  | nil => rfl
  | cons c ds ih => rw [foldl_cons, foldl_cons, hcycle, ih]

end Minimalist.Licensing
