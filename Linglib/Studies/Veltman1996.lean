import Linglib.Semantics.Dynamic.UpdateSemantics.Default
import Mathlib.Data.Fintype.Powerset

/-!
# Veltman (1996): defaults in update semantics

[veltman-1996] treats *normally φ* as an update of an agent's expectations rather than a
sentence about them: a state is a pair of an expectation pattern (a preorder on worlds) and
the agent's knowledge of the facts, *normally φ* refines the pattern in favour of `φ`-worlds,
and *presumably φ* tests whether `φ` holds in the optimal worlds of the state. That §3
system is `Semantics/Dynamic/UpdateSemantics/Default.lean`; the first section checks its
Examples 3.10 on the paper's four worlds, the rain-or-snow contrast that shows *normally
(p ∨ q)* to be stronger than *normally p*, and `normally_not_normally_or`.

The heart of the paper (§4) adds *restricted* rules *if φ, then normally ψ* (`φ ⇝ ψ`): an
**expectation frame** assigns a pattern to every domain `d` of worlds (Definition 4.2), a
world is **normal** in `d` when it is top-ranked in every subdomain containing it
(Definition 4.3), a frame is **coherent** when every nonempty domain has a normal world,
accepting `φ ⇝ ψ` refines the pattern at `⟦φ⟧` and crashes when the result is incoherent
(Definitions 4.5–4.6), and a set of defaults **applies within** `s` when every domain
extending `s` has a normal world complying with them (Definition 4.9). The optimal worlds
of a state comply with a maximal applicable set of defaults (Definition 4.13), which
Proposition 4.14 lets one compute over the explicitly accepted rules. Since every frame an
agent reaches from the minimal state is the refinement of the total frame by the rules it
has accepted, a frame is presented here by its list of rules (`Frame.ofRules`): that makes
coherence, normality, applicability and the optimal worlds decidable, so each verdict of
the paper is checked by `decide` on Veltman's eight worlds over the atoms `p`, `q`, `r`.
Validity is his validity₁ (§1.2): the minimal state updated with the premises in order
accepts the conclusion (`Valid`).

Proved in general: Definition 4.5's refinement clause as theorems about the presentation
(`ofRules_cons_self`, `ofRules_cons_of_ne`), Proposition 4.7 as the equivalence of
coherent acceptance with the new rule's applicability within its own domain
(`coherent_cons_iff`), Conditional Identity and Conjunction of Consequents (`rule_self`,
`conjConsequents`), and the §5 observation that Weakening the Consequent never crashes a
state (`weakenConsequent_coherent`). Checked on the model: Examples 4.8 and 4.11, the §5
benchmarks (the Nixon diamond, the student–adult–employment argument, Independence), the
validity of defeasible Modus Tollens and of Modus Ponens over Modus Tollens on a cyclic
net, the failure of Hypothetical Syllogism, Contraposition and Strengthening the Antecedent
together with their defeasible versions, and the near-validity of Strengthening with a
Consequent and Disjunction of Antecedents.
-/

namespace Veltman1996

open Core.Order UpdateSemantics.Default

/-! ### Rules with exceptions (§3) -/

/-- Veltman's four worlds over the atoms `p`, `q`: `w₀ = ∅`, `w₁ = {p}`, `w₂ = {q}`,
`w₃ = {p, q}`. -/
inductive PQWorld where
  | w₀ | w₁ | w₂ | w₃
  deriving DecidableEq

open PQWorld

def atomP : PQWorld → Prop
  | .w₁ | .w₃ => True
  | _ => False

def atomQ : PQWorld → Prop
  | .w₂ | .w₃ => True
  | _ => False

private theorem atomP_w₀ : ¬atomP w₀ := id
private theorem atomP_w₁ : atomP w₁ := trivial
private theorem atomP_w₂ : ¬atomP w₂ := id
private theorem atomP_w₃ : atomP w₃ := trivial
private theorem atomQ_w₀ : ¬atomQ w₀ := id
private theorem atomQ_w₁ : ¬atomQ w₁ := id
private theorem atomQ_w₂ : atomQ w₂ := trivial
private theorem atomQ_w₃ : atomQ w₃ := trivial

/-- The minimal state `0`. -/
private def σ₀ : ExpState PQWorld := ExpState.init

/-- Rules can have exceptions: after *normally p*, learning `¬p` does not crash (3.10(i)). -/
theorem ex310_exception : ((σ₀.promote atomP).assert (¬atomP ·)).info.Nonempty :=
  ⟨w₀, Set.mem_univ _, atomP_w₀⟩

/-- But the opposite rule is then unacceptable: no optimal world of `0[normally p]` is a
`¬p`-world (3.10(i)). -/
theorem ex310_conflict :
    ¬∃ w ∈ Normality.optimal (σ₀.promote atomP).order Set.univ, ¬atomP w := by
  rintro ⟨w, hw, hnp⟩
  have hw' : w ∈ Normality.optimal (Normality.refine Normality.total atomP) Set.univ := hw
  rw [Normality.refine_total_optimal atomP Set.univ ⟨w₁, Set.mem_univ _, atomP_w₁⟩] at hw'
  exact hnp hw'.2

private theorem w₀_optimal : w₀ ∈ ((σ₀.promote atomP).assert (¬atomP ·)).optimal :=
  ⟨⟨Set.mem_univ _, atomP_w₀⟩, fun _ ⟨_, hnpv⟩ _ => ⟨trivial, fun hpv => absurd hpv hnpv⟩⟩

/-- Exceptions defeat presumptions: *normally p, ¬p ⊮ presumably p* (3.10(ii)). -/
theorem ex310_defeat :
    ¬∀ w ∈ ((σ₀.promote atomP).assert (¬atomP ·)).optimal, atomP w :=
  fun h => atomP_w₀ (h w₀ w₀_optimal)

/-- But not the rule: *normally p, ¬p ⊩ normally p* (3.10(ii)). -/
theorem ex310_rule_persists :
    Normality.respects ((σ₀.promote atomP).assert (¬atomP ·)).order atomP :=
  persistence_assert (σ₀.promote atomP) atomP _ (normally_creates_respect σ₀ atomP)

/-- Irrelevant information does not block a presumption: *normally p, q ⊩ presumably p*
(3.10(iii)). -/
theorem ex310_irrelevant : ∀ w ∈ ((σ₀.promote atomP).assert atomQ).optimal, atomP w := by
  rintro w ⟨_, hopt⟩
  by_contra hnpw
  exact hnpw ((hopt ⟨Set.mem_univ _, atomQ_w₃⟩ ⟨trivial, fun _ => atomP_w₃⟩).2 atomP_w₃)

/-- Independence: *normally p, normally q, ¬p ⊩ presumably q* (3.10(iv)). -/
theorem ex310_independence :
    ∀ w ∈ (((σ₀.promote atomP).promote atomQ).assert (¬atomP ·)).optimal, atomQ w := by
  rintro w ⟨⟨_, hnpw⟩, hopt⟩
  by_contra hnqw
  exact hnqw ((hopt ⟨Set.mem_univ _, atomP_w₂⟩
    ⟨⟨trivial, fun hpw => absurd hpw hnpw⟩, fun hqw => absurd hqw hnqw⟩).2 atomQ_w₂)

/-- Ambiguity: *normally p, normally q, ¬(p ∧ q)* presumes neither `p` nor `q`
(3.10(v)). -/
theorem ex310_ambiguity :
    let σ := ((σ₀.promote atomP).promote atomQ).assert fun w => ¬(atomP w ∧ atomQ w)
    ¬(∀ w ∈ σ.optimal, atomP w) ∧ ¬(∀ w ∈ σ.optimal, atomQ w) := by
  refine ⟨fun h => atomP_w₂ (h w₂ ⟨⟨Set.mem_univ _, fun ⟨hp, _⟩ => atomP_w₂ hp⟩, ?_⟩),
    fun h => atomQ_w₁ (h w₁ ⟨⟨Set.mem_univ _, fun ⟨_, hq⟩ => atomQ_w₁ hq⟩, ?_⟩)⟩
  · rintro v ⟨_, hnpq⟩ ⟨⟨_, _⟩, hqv⟩
    exact ⟨⟨trivial, fun hpv => absurd ⟨hpv, hqv atomQ_w₂⟩ hnpq⟩, fun _ => atomQ_w₂⟩
  · rintro v ⟨_, hnpq⟩ ⟨⟨_, hpv⟩, _⟩
    exact ⟨⟨trivial, fun _ => atomP_w₁⟩, fun hqv => absurd ⟨hpv atomP_w₁, hqv⟩ hnpq⟩

/-- *Normally it rains; it is not raining; so presumably it snows* is invalid, but
*normally it rains or snows; it is not raining; so presumably it snows* is valid (§3): a
rule *normally (p ∨ q)* says what to expect when `p` fails. -/
theorem rain_or_snow :
    ¬(∀ w ∈ ((σ₀.promote atomP).assert (¬atomP ·)).optimal, atomQ w) ∧
      ∀ w ∈ ((σ₀.promote fun w => atomP w ∨ atomQ w).assert (¬atomP ·)).optimal, atomQ w := by
  refine ⟨fun h => atomQ_w₀ (h w₀ w₀_optimal), ?_⟩
  rintro w ⟨⟨_, hnpw⟩, hopt⟩
  by_contra hnqw
  exact ((hopt ⟨Set.mem_univ _, atomP_w₂⟩ ⟨trivial, fun _ => Or.inr atomQ_w₂⟩).2
    (Or.inr atomQ_w₂)).elim hnpw hnqw

/-- Hence *normally p ⊮ normally (p ∨ q)*: the second rule further refines the pattern. -/
theorem normally_not_normally_or :
    (σ₀.promote atomP).promote (fun w => atomP w ∨ atomQ w) ≠ σ₀.promote atomP := by
  intro h
  have h' : Normality.refine (Normality.refine Normality.total atomP)
      (fun w => atomP w ∨ atomQ w) = Normality.refine Normality.total atomP :=
    congrArg ExpState.order h
  have hle : (Normality.refine (Normality.refine Normality.total atomP)
      fun w => atomP w ∨ atomQ w).le w₀ w₂ := by
    rw [h']; exact ⟨trivial, fun hp => absurd hp atomP_w₂⟩
  exact (hle.2 (Or.inr atomQ_w₂)).elim atomP_w₀ atomQ_w₀

/-! ### Rules for exceptions (§4) -/

variable {W : Type*}

/-- A restricted rule `φ ⇝ ψ`: `default` is a default in the domain `domain`. -/
structure Rule (W : Type*) where
  domain : Finset W
  default : Finset W
  deriving DecidableEq

/-- An expectation frame assigns to every domain `d` a pattern on `d` (Definition 4.2). -/
abbrev Frame (W : Type*) := (d : Finset W) → Preorder d

/-- The frame presented by a list of rules: the pattern at `d` is the total pattern refined
by the defaults of the rules with domain `d` (Proposition 4.14). -/
@[reducible] def Frame.ofRules (R : List (Rule W)) : Frame W := fun d =>
  Preorder.ofCriteria (fun (w : d) (r : Rule W) => w.1 ∈ r.default) {r | r ∈ R ∧ r.domain = d}

/-- Refinement at the rule's own domain (Definition 4.5(ii)(b)): the pattern at
`r.domain` is the old one refined with `r.default`. -/
theorem Frame.ofRules_cons_self (r : Rule W) (R : List (Rule W)) :
    Frame.ofRules (r :: R) r.domain =
      Normality.refine (Frame.ofRules R r.domain) (fun w => w.1 ∈ r.default) :=
  Preorder.ext fun w v =>
    ⟨fun h => ⟨fun c hc => h c ⟨List.mem_cons_of_mem _ hc.1, hc.2⟩, h r ⟨List.mem_cons_self, rfl⟩⟩,
     fun h c hc => by
      rcases List.mem_cons.1 hc.1 with rfl | hc' <;> [exact h.2; exact h.1 c ⟨hc', hc.2⟩]⟩

/-- Other domains are untouched (Definition 4.5(ii)(a)). -/
theorem Frame.ofRules_cons_of_ne (r : Rule W) (R : List (Rule W)) {d : Finset W}
    (h : d ≠ r.domain) : Frame.ofRules (r :: R) d = Frame.ofRules R d :=
  Preorder.ext fun _ _ =>
    ⟨fun h' c hc => h' c ⟨List.mem_cons_of_mem _ hc.1, hc.2⟩, fun h' c hc => by
      rcases List.mem_cons.1 hc.1 with rfl | hc'
      · exact absurd hc.2 h.symm
      · exact h' c ⟨hc', hc.2⟩⟩

/-- `w` is normal in `πd` (Definition 4.3(i)): `w ∈ d` and `w` is at least as normal as every
world of every subdomain of `d` containing it, under that subdomain's pattern. -/
def Normal (π : Frame W) (d : Finset W) (w : W) : Prop :=
  w ∈ d ∧ ∀ d' ⊆ d, ∀ hw : w ∈ d', ∀ v, ∀ hv : v ∈ d', (π d').le ⟨w, hw⟩ ⟨v, hv⟩

/-- In a presented frame, only the rules' own domains can disqualify a world. -/
theorem normal_ofRules_iff (R : List (Rule W)) (d : Finset W) (w : W) :
    Normal (Frame.ofRules R) d w ↔ w ∈ d ∧ ∀ r ∈ R, r.domain ⊆ d → w ∈ r.domain →
      ∀ v ∈ r.domain, v ∈ r.default → w ∈ r.default :=
  and_congr_right fun _ =>
    ⟨fun h r hr hsub hw v hv => h r.domain hsub hw v hv r ⟨hr, rfl⟩,
     fun h d' hsub hw v hv r ⟨hr, hd⟩ => by subst hd; exact h r hr hsub hw v hv⟩

/-- A world normal in a domain is normal in every subdomain containing it. -/
theorem Normal.mono {π : Frame W} {d d' : Finset W} {w : W} (h : Normal π d w) (hw : w ∈ d')
    (hd : d' ⊆ d) : Normal π d' w :=
  ⟨hw, fun _ hsub => h.2 _ (hsub.trans hd)⟩

/-- Accepting a rule can only remove normal worlds. -/
theorem Normal.of_cons {r : Rule W} {R : List (Rule W)} {d : Finset W} {w : W}
    (h : Normal (Frame.ofRules (r :: R)) d w) : Normal (Frame.ofRules R) d w :=
  (normal_ofRules_iff ..).2 ⟨h.1, fun r' hr' =>
    ((normal_ofRules_iff ..).1 h).2 r' (List.mem_cons_of_mem _ hr')⟩

variable [DecidableEq W]

instance (R : List (Rule W)) (d : Finset W) : DecidableRel (Frame.ofRules R d).le := fun w v =>
  decidable_of_iff (∀ r ∈ R, r.domain = d → v.1 ∈ r.default → w.1 ∈ r.default)
    ⟨fun h c ⟨hc, hd⟩ => h c hc hd, fun h c hc hd => h c ⟨hc, hd⟩⟩

instance (R : List (Rule W)) (d : Finset W) : DecidablePred (Normal (Frame.ofRules R) d) :=
  fun w => decidable_of_iff _ (normal_ofRules_iff R d w).symm

/-- The normal worlds `nπd` (Definition 4.3(ii)). -/
def normal (π : Frame W) (d : Finset W) [DecidablePred (Normal π d)] : Finset W :=
  d.filter (Normal π d)

/-- `w` complies with the defaults `D` (Definition 4.9(i)). -/
def Complies (w : W) (D : List (Rule W)) : Prop := ∀ r ∈ D, w ∈ r.domain → w ∈ r.default

instance (w : W) (D : List (Rule W)) : Decidable (Complies w D) :=
  inferInstanceAs (Decidable (∀ r ∈ D, w ∈ r.domain → w ∈ r.default))

/-- `e` is a default in `πd` (Definition 4.2(ii)): `d ∩ e ≠ ∅` and `πd ∘ e = πd`, i.e. `πd`
already respects `e` (`Normality.refine_of_respects`). -/
def IsDefault (π : Frame W) (d e : Finset W) : Prop :=
  (d ∩ e).Nonempty ∧ Normality.respects (π d) (fun w => w.1 ∈ e)

/-- Every accepted rule with a nonempty domain-default intersection is a default of the
presented frame. -/
theorem isDefault_of_mem {R : List (Rule W)} {r : Rule W} (hr : r ∈ R)
    (hne : (r.domain ∩ r.default).Nonempty) : IsDefault (Frame.ofRules R) r.domain r.default :=
  ⟨hne, fun _ _ h hv => h r ⟨hr, rfl⟩ hv⟩

/-- Conjunction of Consequents: once `φ ⇝ ψ` and `φ ⇝ χ` have been accepted, the pattern
at `⟦φ⟧` respects `ψ ∧ χ`, so `φ ⇝ (ψ ∧ χ)` refines nothing. -/
theorem conjConsequents {R : List (Rule W)} {φ ψ χ : Finset W}
    (hψ : ⟨φ, ψ⟩ ∈ R) (hχ : ⟨φ, χ⟩ ∈ R) :
    Frame.ofRules (⟨φ, ψ ∩ χ⟩ :: R) = Frame.ofRules R := by
  refine funext fun d => Preorder.ext fun w v =>
    ⟨fun h c hc => h c ⟨List.mem_cons_of_mem _ hc.1, hc.2⟩, fun h c hc => ?_⟩
  rcases List.mem_cons.1 hc.1 with rfl | hc'
  · exact fun hv => Finset.mem_inter.2
      ⟨h _ ⟨hψ, hc.2⟩ (Finset.mem_inter.1 hv).1, h _ ⟨hχ, hc.2⟩ (Finset.mem_inter.1 hv).2⟩
  · exact h c ⟨hc', hc.2⟩

/-- A frame is coherent when every nonempty domain has a normal world (Definition 4.3(iii)). -/
def Coherent (π : Frame W) [∀ d, DecidablePred (Normal π d)] : Prop :=
  ∀ d : Finset W, d.Nonempty → (normal π d).Nonempty

/-- The defaults `D` jointly apply within `s` (Definition 4.9(ii)): every domain extending
`s` has a normal world complying with them. -/
def Applies (π : Frame W) [∀ d, DecidablePred (Normal π d)] (D : List (Rule W))
    (s : Finset W) : Prop :=
  ∀ d : Finset W, s ⊆ d → ∃ w ∈ normal π d, Complies w D

/-- Proposition 4.7: a coherent frame stays coherent under a new rule `r` with
`r.domain ∩ r.default ≠ ∅` iff `r` applies within its own domain — no domain extending
`r.domain` has all its normal worlds in `r.domain \ r.default`. -/
theorem coherent_cons_iff {R : List (Rule W)} (hR : Coherent (Frame.ofRules R)) {r : Rule W}
    (hne : (r.domain ∩ r.default).Nonempty) :
    Coherent (Frame.ofRules (r :: R)) ↔ Applies (Frame.ofRules R) [r] r.domain := by
  obtain ⟨v₀, hv₀⟩ := hne
  rw [Finset.mem_inter] at hv₀
  constructor
  · intro h d hd
    obtain ⟨w, hw⟩ := h d ⟨v₀, hd hv₀.1⟩
    rw [normal, Finset.mem_filter] at hw
    refine ⟨w, Finset.mem_filter.2 ⟨hw.1, hw.2.of_cons⟩, fun _ hr' => ?_⟩
    rcases List.mem_singleton.1 hr' with rfl
    exact fun hwd => ((normal_ofRules_iff ..).1 hw.2).2 _ List.mem_cons_self hd hwd v₀ hv₀.1 hv₀.2
  · intro h d hd
    by_cases hsub : r.domain ⊆ d
    · obtain ⟨w, hw, hc⟩ := h d hsub
      rw [normal, Finset.mem_filter] at hw
      refine ⟨w, Finset.mem_filter.2 ⟨hw.1, (normal_ofRules_iff ..).2 ⟨hw.1, fun r' hr' => ?_⟩⟩⟩
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact fun _ hwd _ _ _ => hc r' (List.mem_singleton_self _) hwd
      · exact ((normal_ofRules_iff ..).1 hw.2).2 r' hr'
    · obtain ⟨w, hw⟩ := hR d hd
      rw [normal, Finset.mem_filter] at hw
      refine ⟨w, Finset.mem_filter.2 ⟨hw.1, (normal_ofRules_iff ..).2 ⟨hw.1, fun r' hr' => ?_⟩⟩⟩
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact fun h => absurd h hsub
      · exact ((normal_ofRules_iff ..).1 hw.2).2 r' hr'

/-- Weakening the Consequent is "almost valid" (§5): a state that has accepted `φ ⇝ ψ` never
crashes on `φ ⇝ (ψ ∨ χ)`, since any normal world of a domain extending `⟦φ⟧` that lies in
`⟦φ⟧` already satisfies `ψ`. -/
theorem weakenConsequent_applies {R : List (Rule W)} (hR : Coherent (Frame.ofRules R))
    {φ ψ χ : Finset W} (hψ : ⟨φ, ψ⟩ ∈ R) (hne : (φ ∩ ψ).Nonempty) :
    Applies (Frame.ofRules R) [⟨φ, ψ ∪ χ⟩] φ := by
  obtain ⟨v₀, hv₀⟩ := hne
  rw [Finset.mem_inter] at hv₀
  intro d hd
  obtain ⟨w, hw⟩ := hR d ⟨v₀, hd hv₀.1⟩
  refine ⟨w, hw, fun _ hr' => ?_⟩
  rcases List.mem_singleton.1 hr' with rfl
  rw [normal, Finset.mem_filter] at hw
  exact fun hwφ => Finset.mem_union_left _
    (((normal_ofRules_iff ..).1 hw.2).2 _ hψ hd hwφ v₀ hv₀.1 hv₀.2)

theorem weakenConsequent_coherent {R : List (Rule W)} (hR : Coherent (Frame.ofRules R))
    {φ ψ χ : Finset W} (hψ : ⟨φ, ψ⟩ ∈ R) (hne : (φ ∩ ψ).Nonempty) :
    Coherent (Frame.ofRules (⟨φ, ψ ∪ χ⟩ :: R)) :=
  (coherent_cons_iff hR (hne.mono (Finset.inter_subset_inter_left Finset.subset_union_left))).2
    (weakenConsequent_applies hR hψ hne)

variable [Fintype W]

instance (R R' : List (Rule W)) : Decidable (Frame.ofRules R = Frame.ofRules R') :=
  decidable_of_iff (∀ d : Finset W, ∀ w v : d, (Frame.ofRules R d).le w v ↔
      (Frame.ofRules R' d).le w v)
    ⟨fun h => funext fun d => Preorder.ext (h d), fun h _ _ _ => h ▸ Iff.rfl⟩

instance (π : Frame W) [∀ d, DecidablePred (Normal π d)] : Decidable (Coherent π) :=
  inferInstanceAs (Decidable (∀ d : Finset W, d.Nonempty → (normal π d).Nonempty))

instance (π : Frame W) [∀ d, DecidablePred (Normal π d)] (D : List (Rule W)) (s : Finset W) :
    Decidable (Applies π D s) :=
  inferInstanceAs (Decidable (∀ d : Finset W, s ⊆ d → ∃ w ∈ normal π d, Complies w D))

/-- A state `(π, s)`: the frame, presented by the accepted rules, and the agent's knowledge
of the facts (Definition 4.4). -/
structure State (W : Type*) where
  rules : List (Rule W)
  info : Finset W
  deriving DecidableEq

namespace State

/-- The minimal state `0`: the total frame, every world possible. -/
def init : State W := ⟨[], Finset.univ⟩

/-- The absurd state `1`. -/
def absurd : State W := ⟨[], ∅⟩

variable (σ : State W)

/-- The frame of a state. -/
abbrev frame : Frame W := Frame.ofRules σ.rules

/-- `D` is a maximal applicable set of defaults in `σ` (Definition 4.13(i)), over the
accepted rules (Proposition 4.14). -/
def MaximalApplicable (D : List (Rule W)) : Prop :=
  Applies σ.frame D σ.info ∧ ∀ r ∈ σ.rules, Applies σ.frame (r :: D) σ.info → r ∈ D

instance (D : List (Rule W)) : Decidable (σ.MaximalApplicable D) :=
  inferInstanceAs (Decidable (_ ∧ ∀ r ∈ σ.rules, Applies σ.frame (r :: D) σ.info → r ∈ D))

/-- The optimal worlds `mσ` (Definition 4.13(ii)): the worlds of `s` complying with a maximal
applicable set of defaults. -/
def optimal : Finset W :=
  σ.info.filter fun w => ∃ D ∈ σ.rules.sublists, σ.MaximalApplicable D ∧ Complies w D

/-- `σ ⊩ φ`: `σ[φ]` is `σ` — the same facts and the same frame. -/
def Accepts (φ : State W → State W) : Prop := (φ σ).info = σ.info ∧ (φ σ).frame = σ.frame

instance (φ : State W → State W) : Decidable (σ.Accepts φ) :=
  inferInstanceAs (Decidable (_ ∧ Frame.ofRules _ = Frame.ofRules _))

end State

/-- `σ[φ ⇝ ψ]` (Definition 4.6): refine the frame at `⟦φ⟧` with `⟦ψ⟧`, crashing if
`⟦φ⟧ ∩ ⟦ψ⟧ = ∅` or the refined frame is incoherent. -/
def rule (φ ψ : Finset W) (σ : State W) : State W :=
  if (φ ∩ ψ).Nonempty ∧ Coherent (Frame.ofRules (⟨φ, ψ⟩ :: σ.rules)) ∧ σ.info.Nonempty
  then ⟨⟨φ, ψ⟩ :: σ.rules, σ.info⟩ else .absurd

/-- *Normally ψ* is `(ψ ∨ ¬ψ) ⇝ ψ` (Definition 4.1). -/
def normally (ψ : Finset W) : State W → State W := rule (ψ ∪ ψᶜ) ψ

/-- `σ[φ]` for a factual `φ`: eliminate the `¬φ`-worlds, crashing if none remain. -/
def fact (φ : Finset W) (σ : State W) : State W :=
  if (σ.info ∩ φ).Nonempty then ⟨σ.rules, σ.info ∩ φ⟩ else .absurd

/-- `σ[presumably φ]` (Definition 4.13(iii)): a test passing iff `φ` holds in every optimal
world. -/
def presumably (φ : Finset W) (σ : State W) : State W :=
  if σ.optimal ⊆ φ then σ else .absurd

/-- Validity₁ (§1.2): the minimal state updated with the premises in order accepts the
conclusion. -/
def Valid (prems : List (State W → State W)) (concl : State W → State W) : Prop :=
  (prems.foldl (fun σ φ => φ σ) State.init).Accepts concl

instance (prems : List (State W → State W)) (concl : State W → State W) :
    Decidable (Valid prems concl) :=
  inferInstanceAs (Decidable (State.Accepts _ _))

/-- Conditional Identity: `φ ⇝ φ` is accepted in the minimal state for nonempty `φ` — the
rule refines nothing. -/
theorem rule_self {φ : Finset W} (hφ : φ.Nonempty) : Valid [] (rule φ φ) := by
  have hco : Coherent (Frame.ofRules [(⟨φ, φ⟩ : Rule W)]) := fun d ⟨w, hw⟩ =>
    ⟨w, Finset.mem_filter.2 ⟨hw, (normal_ofRules_iff ..).2 ⟨hw, fun r hr => by
      rcases List.mem_singleton.1 hr with rfl; exact fun _ hw _ _ _ => hw⟩⟩⟩
  have h : rule φ φ ⟨[], Finset.univ⟩ = ⟨[⟨φ, φ⟩], Finset.univ⟩ := by
    rw [rule, if_pos ⟨by rwa [Finset.inter_self], hco, hφ.elim fun w _ => ⟨w, Finset.mem_univ w⟩⟩]
  show State.Accepts ⟨[], Finset.univ⟩ (rule φ φ)
  rw [State.Accepts, h]
  refine ⟨rfl, funext fun d => Preorder.ext fun w v => ⟨fun _ c hc => by simp at hc, ?_⟩⟩
  rintro _ c ⟨hc, rfl⟩
  rcases List.mem_singleton.1 hc with rfl
  exact fun _ => w.2

/-! ### Veltman's eight worlds -/

/-- `wᵢ` is the set of atoms whose bits are set in `i`: `w₀ = ∅`, `w₁ = {p}`, `w₂ = {q}`,
`w₃ = {p, q}`, `w₄ = {r}`, …, `w₇ = {p, q, r}`. -/
abbrev World := Fin 8

def p : Finset World := Finset.univ.filter (·.val % 2 = 1)
def q : Finset World := Finset.univ.filter (·.val / 2 % 2 = 1)
def r : Finset World := Finset.univ.filter (·.val / 4 % 2 = 1)

/-- Examples 4.8(i)–(iii): an exception to *normally p* for `q` is acceptable, but not a
further exception for `¬q` (too many exceptions), nor *normally q* on top of it. -/
theorem ex48 :
    (State.init |> normally p |> rule q pᶜ) ≠ State.absurd ∧
      (State.init |> normally p |> rule q pᶜ |> rule qᶜ pᶜ) = State.absurd ∧
      (State.init |> normally p |> rule q pᶜ |> normally q) = State.absurd := by
  decide +kernel

/-- Examples 4.11(i)–(iii), the verdicts of §4: the more specific rule takes precedence, and
an exception to an exception restores the general verdict. -/
theorem ex411_specificity :
    Valid [normally p, rule q pᶜ, fact q] (presumably pᶜ) ∧
      Valid [normally p, rule q pᶜ, fact (q ∩ r)] (presumably pᶜ) ∧
      Valid [normally p, rule q pᶜ, rule (q ∩ r) p, fact (q ∩ r)] (presumably p) := by
  decide +kernel

/-- Example 4.11(iv): neither rule is more specific, yet in the context `p ∧ q` only
`q ⇝ (p ∧ ¬r)` applies. -/
theorem ex411_iv : Valid [rule p r, rule q (p ∩ rᶜ), fact (p ∩ q)] (presumably rᶜ) := by
  decide +kernel

/-- Example 4.11(v), the Nixon diamond (§5): `p ⇝ r`, `q ⇝ ¬r`, `p ∧ q` presume neither `r`
nor `¬r` — the two defaults apply separately but not jointly. -/
theorem nixon :
    ¬Valid [rule p r, rule q rᶜ, fact (p ∩ q)] (presumably r) ∧
      ¬Valid [rule p r, rule q rᶜ, fact (p ∩ q)] (presumably rᶜ) := by
  decide +kernel

/-- Example 4.11(vi): `q ⇝ p`, `p ⇝ r`, `q ⊩ presumably r` — the defeasible Hypothetical
Syllogism (§5's `(*)`). -/
theorem ex411_vi : Valid [rule q p, rule p r, fact q] (presumably r) := by
  decide +kernel

/-! ### Comparisons (§5) -/

/-- Students are normally adults (`q ⇝ p`), students are normally not employed
(`q ⇝ ¬r`), adults are normally employed (`p ⇝ r`): John, a student, is presumably an
unemployed adult — `q ⇝ ¬r` overrides `p ⇝ r` in the presence of `q ⇝ p`. -/
theorem students : Valid [rule p r, rule q rᶜ, rule q p, fact q] (presumably (p ∩ rᶜ)) := by
  decide +kernel

/-- Independence: an exception in one respect is not an exception in others — a student
who is employed is still presumably an adult. -/
theorem independence : Valid [rule q p, rule q rᶜ, fact q, fact r] (presumably p) := by
  decide +kernel

/-- Defeasible Modus Tollens is valid: `p ⇝ q`, `¬q ⊩ presumably ¬p`. -/
theorem defeasibleModusTollens : Valid [rule p q, fact qᶜ] (presumably pᶜ) := by
  decide +kernel

/-- On the cyclic net `p ⇝ q`, `q ⇝ ¬p`, Modus Ponens takes precedence over Modus Tollens:
`p ⊩ presumably q`. -/
theorem modusPonens_over_modusTollens :
    Valid [rule p q, rule q pᶜ, fact p] (presumably q) := by
  decide +kernel

/-- Validity₁ is not closed under substitution: `(*)` holds for independent predicates,
but substituting `¬q` for `r` defeats it. -/
theorem substitution_fails : ¬Valid [rule q p, rule p qᶜ, fact q] (presumably qᶜ) := by
  decide +kernel

/-- Hypothetical Syllogism fails although its defeasible version `(*)` holds: the rule
`q ⇝ r` is not accepted. -/
theorem hypotheticalSyllogism_fails : ¬Valid [rule q p, rule p r] (rule q r) := by
  decide +kernel

/-- Defeasible Modus Tollens holds but Contraposition fails. -/
theorem contraposition_fails : ¬Valid [rule p q] (rule qᶜ pᶜ) := by
  decide +kernel

/-- `p ⇝ q`, `p ∧ r ⊩ presumably q`, but Strengthening the Antecedent fails. -/
theorem strengthening :
    Valid [rule p q, fact (p ∩ r)] (presumably q) ∧ ¬Valid [rule p q] (rule (p ∩ r) q) := by
  decide +kernel

/-- Strengthening with a Consequent and Disjunction of Antecedents are almost valid: the
derived rule never crashes the state, though it is not accepted. -/
theorem nearValid :
    (State.init |> rule p q |> rule p r |> rule (p ∩ q) r) ≠ State.absurd ∧
      ¬Valid [rule p q, rule p r] (rule (p ∩ q) r) ∧
      (State.init |> rule p r |> rule q r |> rule (p ∪ q) r) ≠ State.absurd ∧
      ¬Valid [rule p r, rule q r] (rule (p ∪ q) r) := by
  decide +kernel

end Veltman1996
