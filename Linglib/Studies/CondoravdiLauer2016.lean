import Linglib.Semantics.Attitudes.Desire.Preferential
import Linglib.Semantics.Conditionals.Restrictor
import Linglib.Data.Examples.CondoravdiLauer2016
import Mathlib.Tactic.FinCases

/-!
# Condoravdi and Lauer 2016: anankastic conditionals are just conditionals

[condoravdi-lauer-2016] argue that *If you want to go to Harlem, you have to take the A train* is
a regular hypothetical indicative conditional: the problem [saebo-2001] found, that the antecedent
goal must enter the ordering of the modal, and the one [vonfintel-iatridou-2005] and
[vonstechow-krasikova-penka-2006] added, that conflicting actual goals must not, are both resolved
by the lexical meanings involved once *want* reports an action-relevant preference. On that
reading *want* says its complement is a maximal element of the agent's effective preference
structure, a strict partial order on propositions that is consistent with the agent's beliefs, so
hypothesizing a preference for Harlem hypothesizes the absence of every preference the agent knows
to be incompatible with it. The conditional has the double-modal structure of [frank-1996], a
covert necessity over the speaker's beliefs, ordered by stereotypicality and restricted by the
antecedent, with the priority modal over the historical alternatives in its scope, whose ordering
source at each world is the agent's maximal effective preferences there. The same setting covers
the near-anankastics of strengthened goals, teleological consequences and specializations, which
differ from anankastics only in the pragmatic implication that the temporal relation of goal and
prejacent invites; reading *want* or the modal differently gives the non-anankastic and deontic
cases.

## Implementation notes

The priority modal is evaluated with `PreferenceStructure.best`, the optimal worlds under the
preorder the maximal preferences induce, [kratzer-1981]'s ordering-source construction over a
set of propositions rather than a list; the covert modal is
`Conditionals.Restrictor.conditionalNecessity`. The sufficient condition for (88) quantifies
over every antecedent world of the speaker's beliefs rather than the typical ones and assumes
the effective preferences jointly realizable among the historical alternatives, which the paper
leaves to a separate mechanism that ignores atypical continuations. The Hoboken scenario is a
model in which the speaker is uncertain about the addressee's goal, with an empty
stereotypical ordering and one effective preference per world, so the Harlem sentence is true
through its antecedent worlds rather than vacuously; Sæbø's rival is evaluated with the
list-valued Kratzer operators, the paper's with `PreferenceStructure.best`. Of the double-modal
argument, the entailment a single restricted modal validates is proved; the consistency of the
double-modal readings of (81) to (83) is not modelled.

## TODO

* Informal in the paper and not formalized: the temporal interpretation of the internal
  antecedent and the prejacent, the pragmatic derivation of the means-of implication, the
  strong/weak modal contrast of (96) and (97), purpose constructions, informational asymmetry,
  and the closure condition that would validate conjunction introduction for effective
  preferences.

## References

* [C. Condoravdi and S. Lauer, *Anankastic conditionals are just conditionals*
  (2016)][condoravdi-lauer-2016]
* [C. Condoravdi and S. Lauer, *Performative verbs and performative acts*
  (2011)][condoravdi-lauer-2011]
* [K. J. Sæbø, *Necessary conditions in a natural language* (2001)][saebo-2001]
* [K. von Fintel and S. Iatridou, *What to do if you want to go to Harlem: Anankastic
  conditionals and related matters* (2005)][vonfintel-iatridou-2005]
* [A. von Stechow, S. Krasikova and D. Penka, *Anankastic conditionals again*
  (2006)][vonstechow-krasikova-penka-2006]
* [J. Huitink, *Modals, conditionals and compositionality* (2008)][huitink-2008]
* [A. Frank, *Context dependence in modal constructions* (1996)][frank-1996]
* [S. Kaufmann and M. Schwager, *A unified analysis of conditional imperatives*
  (2009)][kaufmann-schwager-2009]
* [R. M. Hare, *Wanting: Some pitfalls* (1971)][hare-1971]
* [D. Levinson, *Probabilistic model-theoretic semantics for want* (2003)][levinson-2003]
* [T. E. Zimmermann, *Monotonicity in opaque verbs* (2006)][zimmermann-2006]
* [A. Kratzer, *The notional category of modality* (1981)][kratzer-1981]
-/

namespace CondoravdiLauer2016

open Desire.Preferential Modality.Kratzer Conditionals.Restrictor Data.Examples

section General

variable {A W : Type*} {P : A → W → PreferenceStructure W} {a : A} {p q : Set W} {w : W}
  {B : W → Set W}

/-! ### The semantics of *want*

`Want P a p w` is (69): `p` is a maximal element of the structure `P a w` that a preferential
background assigns to `a` at `w`, (68); the effective preference structure is the consistent
and realistic one that guides action, (66) and (67), realism derivable from consistency,
`PreferenceStructure.Consistent.realistic`, footnote 30. `WantSufficient` and `WantNecessary`
are the success-oriented and Quine–Hintikka alternatives of (71), after [zimmermann-2006],
downward and upward entailing, `WantSufficient.anti` and `WantNecessary.mono`. The
mere-desire and effective readings that [hare-1971] and [levinson-2003] observe are two
backgrounds for one predicate. -/

/-- Exact-match *want*, (71c), is not upward entailing in its complement, §5.5: the single
preference `{x}` is not a preference for `Set.univ`. -/
theorem want_not_mono [Nontrivial W] :
    ¬ ∀ (P : Unit → W → PreferenceStructure W) (p q : Set W) (w : W),
      p ⊆ q → Want P () p w → Want P () q w := by
  obtain ⟨x, -, -⟩ := exists_pair_ne W
  intro h
  have : Set.univ = {x} := by
    simpa [Want] using h (λ _ _ => PreferenceStructure.single {x}) {x} Set.univ x
      (Set.subset_univ _) ⟨rfl, λ _ _ h => h⟩
  exact Set.singleton_ne_univ x this.symm

/-- Nor downward entailing: the single preference `Set.univ` is not a preference for `{x}`. -/
theorem want_not_anti [Nontrivial W] :
    ¬ ∀ (P : Unit → W → PreferenceStructure W) (p q : Set W) (w : W),
      p ⊆ q → Want P () q w → Want P () p w := by
  obtain ⟨x, -, -⟩ := exists_pair_ne W
  intro h
  have : ({x} : Set W) = Set.univ := by
    simpa [Want] using h (λ _ _ => PreferenceStructure.single Set.univ) {x} Set.univ x
      (Set.subset_univ _) ⟨rfl, λ _ _ h => h⟩
  exact Set.singleton_ne_univ x this

/-- On a background that need not be consistent, wanting `p` and wanting `q` are compatible even
when `p` and `q` are not, §2.3 and §5.4: the mere-desire reading of (52) and (53). -/
theorem want_both (p q : Set W) :
    Want (λ _ _ => PreferenceStructure.discrete {p, q}) () p w ∧
      Want (λ _ _ => PreferenceStructure.discrete {p, q}) () q w := by
  unfold Want
  rw [PreferenceStructure.maxElts_discrete]
  exact ⟨Or.inl rfl, Or.inr rfl⟩

/-- Levinson's Paris and Rome, (56) and (58), on the effective reading, §5.2: two effective
preferences leave no room for a third that is incompatible with their conjunction, since the
maximal elements of a consistent structure are jointly compatible with the agent's beliefs. -/
theorem no_third_effective {r : Set W} (hC : (P a w).Consistent (B w)) (hp : Want P a p w)
    (hq : Want P a q w) (hr : Want P a r w) : (B w ∩ (p ∩ q ∩ r)).Nonempty :=
  hC.inter_sInter_maxElts_nonempty.mono <| Set.inter_subset_inter_right _ <|
    Set.subset_inter (Set.subset_inter (Set.sInter_subset_of_mem hp) (Set.sInter_subset_of_mem hq))
      (Set.sInter_subset_of_mem hr)

/-- Three unranked preferences over three worlds, pairwise compatible but jointly
inconsistent. -/
private def threeWay : PreferenceStructure (Fin 3) :=
  PreferenceStructure.discrete {{w | w ≠ 2}, {w | w ≠ 0}, {w | w ≠ 1}}

/-- Footnote 29: consistency (66) is stronger than pairwise compatibility, which is what the
weaker version of [condoravdi-lauer-2011] leaves. -/
theorem threeWay_pairwise_not_consistent :
    (∀ p ∈ threeWay.prefs, ∀ q ∈ threeWay.prefs, (p ∩ q).Nonempty) ∧
      ¬ threeWay.Consistent Set.univ := by
  refine ⟨?_, λ h => ?_⟩
  · rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) <;> exact Set.nonempty_def.2 (by decide)
  · let ⟨_, _, _, _, h⟩ := h threeWay.prefs subset_rfl (by
      ext w
      fin_cases w <;> simp [threeWay, PreferenceStructure.discrete])
    exact h

/-! ### Previous approaches -/

/-- [vonfintel-iatridou-2005]'s designated goal, §3.2.2: a primary ordering source with the
single proposition `p` has the effect of adding `p` to the modal base, as long as the two are
compatible, so the analysis amounts to adding the internal antecedent to the modal base; the
effective-preference source of (88) instead varies from world to world, footnote 46. -/
theorem designatedGoal_eq {f : ModalBase W} {p : W → Prop}
    (h : ∃ v ∈ accessibleWorlds f w, p v) :
    bestWorlds f (λ _ => [p]) w = accessibleWorlds (restrictedBase f p) w := by
  rw [restricted_accessible_eq, bestWorlds, kratzerNormality, Core.Order.Normality.fromProps,
    Core.Order.Normality.optimal_ofCriteria_eq]
  · ext u
    simp
  · obtain ⟨v, hv, hp⟩ := h
    exact ⟨v, hv, λ c hc => by rw [List.mem_singleton.1 hc]; exact hp⟩

/-! ### Double-modal structure -/

/-- A single necessity modal restricted by the antecedent validates strengthening of the
antecedent in the form [kaufmann-schwager-2009] reject, §6.2: *if A, must C* and *if A and B,
must not C* together entail that no best *A*-world is a *B*-world, a preference against *B*
that (81) to (83) do not carry. The double-modal structure (76b) escapes, since each
conditional's inner modal is evaluated in its own typical antecedent worlds. -/
theorem single_modal_strengthening {f : ModalBase W} {g : OrderingSource W} {α β γ : W → Prop}
    (h₁ : conditionalNecessity f g α γ w)
    (h₂ : conditionalNecessity f g (λ v => α v ∧ β v) (λ v => ¬ γ v) w) :
    ∀ u ∈ bestWorlds (restrictedBase f α) g w, ¬ β u := by
  intro u hu hβ
  have hu' := mem_accessibleWorlds_restrictedBase.1 hu.1
  exact h₂ u (mem_bestWorlds_of_subset (λ v hv => restrictor_monotone f α _ w (λ _ h => h.1) v hv)
    hu (mem_accessibleWorlds_restrictedBase.2 ⟨hu'.1, hu'.2, hβ⟩)) (h₁ u hu)

/-! ### The analysis -/

/-- The teleological construal of the priority modal, §7.1: the prejacent holds throughout the
worlds of the modal base that best realize the agent's effective preferences at the world of
evaluation, the ordering source `g_epA(v) = max[EP(a, v)]`. -/
def Teleological (f : ModalBase W) (P : A → W → PreferenceStructure W) (a : A) (q : Set W)
    (v : W) : Prop :=
  (P a v).best (accessibleWorlds f v) ⊆ q

/-- (88): the covert necessity over the speaker's beliefs, ordered by stereotypicality and
restricted by the effective preference for `p`, with the teleological modal over the historical
alternatives in its scope. -/
def Anankastic (f₁ : ModalBase W) (g₁ : OrderingSource W) (f₂ : ModalBase W)
    (P : A → W → PreferenceStructure W) (a : A) (p q : Set W) (w : W) : Prop :=
  conditionalNecessity f₁ g₁ (Want P a p) (Teleological f₂ P a q) w

/-- (90): under consistency, an effective preference for `p` excludes one for any `q` the agent
believes incompatible with `p`. -/
theorem want_disjoint (hC : ∀ w, (P a w).Consistent (B w)) (h : ∀ w, B w ∩ (p ∩ q) = ∅) :
    Disjoint {w | Want P a p w} {w | Want P a q w} :=
  Set.disjoint_left.2 λ w hp hq =>
    ((hC w).inter_inter_nonempty_of_mem_maxElts hp hq).ne_empty (h w)

/-- The antecedent's restriction removes every world with a conflicting effective preference,
§7.1.1, so an actual preference for Hoboken never reaches the priority modal. -/
theorem not_want_of_mem_restricted {f : ModalBase W} (hC : ∀ w, (P a w).Consistent (B w))
    (h : ∀ w, B w ∩ (p ∩ q) = ∅) {v : W}
    (hv : v ∈ accessibleWorlds (restrictedBase f (Want P a p)) w) : ¬ Want P a q v :=
  Set.disjoint_left.1 (want_disjoint hC h) (mem_accessibleWorlds_restrictedBase.1 hv).2

/-- An anankastic conditional whose antecedent the speaker's beliefs exclude is vacuously
true, §7.1.1; the indicative is then infelicitous and the subjunctive required, (91). -/
theorem anankastic_of_not_want {f₁ f₂ : ModalBase W} {g₁ : OrderingSource W}
    (h : ∀ v ∈ accessibleWorlds f₁ w, ¬ Want P a p v) : Anankastic f₁ g₁ f₂ P a p q w :=
  vacuous_conditional f₁ g₁ _ _ w h

/-- A sufficient condition for (88), stronger than the paraphrase (89) in bypassing the
typicality restriction: when in every belief world where the agent effectively prefers `p` the
effective preferences are jointly realizable among the historical alternatives and realizing
`p` there requires `q`, the conditional holds. Compatible goals such as comfort in (92) stay in
the ordering; conflicting ones are gone by `not_want_of_mem_restricted`. -/
theorem anankastic_of_subset {f₁ f₂ : ModalBase W} {g₁ : OrderingSource W}
    (hreal : ∀ v ∈ accessibleWorlds (restrictedBase f₁ (Want P a p)) w,
      (accessibleWorlds f₂ v ∩ ⋂₀ (P a v).maxElts).Nonempty)
    (hfacts : ∀ v ∈ accessibleWorlds (restrictedBase f₁ (Want P a p)) w,
      accessibleWorlds f₂ v ∩ p ⊆ q) :
    Anankastic f₁ g₁ f₂ P a p q w := by
  intro v hv
  rw [Teleological, (P a v).best_eq_of_nonempty (hreal v hv.1)]
  exact λ u ⟨hu, hmax⟩ => hfacts v hv.1
    ⟨hu, Set.mem_sInter.1 hmax p (mem_accessibleWorlds_restrictedBase.1 hv.1).2⟩

end General

/-! ### The Hoboken scenario

Von Fintel and Iatridou's stranger on the platform, §2.3 and §7.1.1: the speaker knows the
facts about the trains but not the addressee's goal, which is Hoboken. -/

namespace HobokenScenario

/-- Where the addressee wants to go. -/
inductive Goal
  | harlem | hoboken
  deriving DecidableEq

/-- Which train the addressee takes. -/
inductive Train
  | aTrain | path
  deriving DecidableEq

/-- A world: the addressee's goal, the train taken, and whether the facts hold, the A train going
to Harlem and the PATH train to Hoboken. -/
structure World where
  /-- The addressee's effective goal. -/
  goal : Goal
  /-- The train the addressee takes. -/
  train : Train
  /-- Whether the A train goes to Harlem and the PATH train to Hoboken. -/
  facts : Bool
  deriving DecidableEq

variable {w : World}

/-- The addressee goes to Harlem. -/
def harlem : Set World := {w | w.train = if w.facts then .aTrain else .path}

/-- The addressee goes to Hoboken. -/
def hoboken : Set World := {w | w.train = if w.facts then .path else .aTrain}

/-- The addressee takes the A train. -/
def aTrain : Set World := {w | w.train = .aTrain}

/-- The addressee takes the PATH train. -/
def path : Set World := {w | w.train = .path}

/-- The proposition a goal is a preference for. -/
def Goal.dest : Goal → Set World
  | .harlem => HobokenScenario.harlem
  | .hoboken => HobokenScenario.hoboken

/-- The addressee's effective preference structure: the single preference for the goal. -/
def ep : Unit → World → PreferenceStructure World :=
  λ _ w => PreferenceStructure.single w.goal.dest

/-- The addressee's beliefs: the facts hold. -/
def belief : World → Set World := λ _ => {v | v.facts = true}

/-- The speaker's beliefs: the facts hold. -/
def fBelS : ModalBase World := λ _ => [λ v => v.facts = true]

/-- The historical alternatives before boarding: the goal and the facts are settled, the train
is not. -/
def fHist : ModalBase World := λ v => [λ u => u.goal = v.goal, λ u => u.facts = v.facts]

/-- The world where the facts hold and the addressee is heading for Hoboken. -/
def w₀ : World := ⟨.hoboken, .path, true⟩

private theorem mem_fBelS {v : World} : v ∈ accessibleWorlds fBelS w ↔ v.facts = true := by
  simp [accessibleWorlds, propIntersection, fBelS]

private theorem mem_fHist {u v : World} :
    u ∈ accessibleWorlds fHist v ↔ u.goal = v.goal ∧ u.facts = v.facts := by
  simp [accessibleWorlds, propIntersection, fHist]

theorem consistent_ep (v : World) : (ep () v).Consistent (belief v) :=
  PreferenceStructure.consistent_single (by
    cases v.goal
    · exact ⟨⟨.harlem, .aTrain, true⟩, by simp [Goal.dest, harlem, belief]⟩
    · exact ⟨⟨.hoboken, .path, true⟩, by simp [Goal.dest, hoboken, belief]⟩)

/-- Nobody reaches both Harlem and Hoboken once the facts hold. -/
theorem belief_inter_harlem_hoboken (v : World) : belief v ∩ (harlem ∩ hoboken) = ∅ := by
  ext ⟨_, t, f⟩
  cases t <;> cases f <;> simp [belief, harlem, hoboken]

/-- At the Hoboken world the addressee wants Hoboken, so by (90) not Harlem: the world is in
the speaker's belief state and out of the antecedent's restriction of it, §7.1.1, so the
actual preference never reaches the priority modal. -/
theorem w₀_excluded :
    w₀ ∈ accessibleWorlds fBelS w₀ ∧
      w₀ ∉ accessibleWorlds (restrictedBase fBelS (Want ep () harlem)) w₀ :=
  ⟨mem_fBelS.2 rfl, λ h => not_want_of_mem_restricted consistent_ep belief_inter_harlem_hoboken h
    (show hoboken ∈ (PreferenceStructure.single hoboken).maxElts from
      ⟨Set.mem_singleton _, λ _ _ h => h⟩)⟩

/-- An anankastic whose destination is reached exactly by one train once the facts hold is true
at every world, the Hoboken world included. -/
private theorem anankastic_dest {d t : Set World}
    (hd : ∀ u : World, u.facts = true → (u ∈ d ↔ u ∈ t))
    (hne : ∀ g, ∃ u : World, u.goal = g ∧ u.facts = true ∧ u ∈ d) :
    Anankastic fBelS emptyBackground fHist ep () d t w := by
  refine anankastic_of_subset (λ v hv => ?_) (λ v hv u ⟨hu, hd'⟩ => ?_)
  · have hv' := mem_accessibleWorlds_restrictedBase.1 hv
    have hw : d = v.goal.dest := by simpa [Want, ep] using hv'.2
    obtain ⟨u, hg, hf, hu⟩ := hne v.goal
    refine ⟨u, mem_fHist.2 ⟨hg, hf.trans (mem_fBelS.1 hv'.1).symm⟩, ?_⟩
    simp only [ep, PreferenceStructure.maxElts_single, Set.sInter_singleton]
    exact hw ▸ hu
  · have hv' := mem_accessibleWorlds_restrictedBase.1 hv
    exact (hd u ((mem_fHist.1 hu).2.trans (mem_fBelS.1 hv'.1))).1 hd'

/-- The Harlem sentence (1) is true at every world, the Hoboken world included, §7.1.1. -/
theorem anankastic_harlem : Anankastic fBelS emptyBackground fHist ep () harlem aTrain w :=
  anankastic_dest (λ u hu => by simp [harlem, aTrain, hu])
    (λ g => ⟨⟨g, .aTrain, true⟩, rfl, rfl, by simp [harlem]⟩)

/-- The Hoboken sentence (15) is true alongside it. -/
theorem anankastic_hoboken : Anankastic fBelS emptyBackground fHist ep () hoboken path w :=
  anankastic_dest (λ u hu => by simp [hoboken, path, hu])
    (λ g => ⟨⟨g, .path, true⟩, rfl, rfl, by simp [hoboken]⟩)

/-- The Hoboken world is a best world under the addressee's actual goal alone. -/
private theorem w₀_mem_bestWorlds :
    w₀ ∈ bestWorlds fBelS (λ _ => [(· ∈ hoboken)]) w₀ :=
  ⟨mem_fBelS.2 rfl, λ _ _ _ c hc _ => by rw [List.mem_singleton.1 hc]; exact rfl⟩

private theorem not_harlem_of_hoboken : ∀ v : World, v ∈ hoboken → v ∉ harlem := by
  rintro ⟨_, t, f⟩ hv hh
  cases t <;> cases f <;> simp [hoboken, harlem] at hv hh

/-- Sæbø's analysis, §2.3, on the circumstantial base that here coincides with the speaker's
beliefs: adding Harlem to the ordering source that holds the addressee's actual goal partitions
the best worlds, so the Harlem sentence comes out false at the Hoboken world. -/
theorem saebo_harlem :
    ¬ necessity fBelS (λ _ => [(· ∈ harlem), (· ∈ hoboken)]) (· ∈ aTrain) w₀ :=
  not_necessity_cons (List.mem_singleton_self _) not_harlem_of_hoboken w₀_mem_bestWorlds rfl nofun

/-- On the same analysis (14) comes out true: some best world takes the PATH train. -/
theorem saebo_path :
    possibility fBelS (λ _ => [(· ∈ harlem), (· ∈ hoboken)]) (· ∈ path) w₀ :=
  ⟨w₀, mem_bestWorlds_cons (List.mem_singleton_self _) not_harlem_of_hoboken w₀_mem_bestWorlds
    rfl, rfl⟩

end HobokenScenario

/-! ### The rows

The construal rows classify the paper's conditionals by the reading of *want* and the construal
of the modal; the other rows instantiate the theorems above. -/

/-- The reading of the desire predicate. -/
inductive WantReading
  | effective | mere | weak
  deriving DecidableEq

/-- The construal of the modal in the consequent. -/
inductive ModalConstrual
  | teleological | deontic | speakerTeleological
  deriving DecidableEq

/-- The interpretation the paper assigns. -/
inductive Interpretation
  | anankastic | nearAnankastic | nonAnankastic
  deriving DecidableEq

/-- The relation the prejacent bears to the goal, §7.1.2: a means to it, a precondition for it,
a means to a strengthened goal, a consequence of it, a specialization of it, or none. -/
inductive Implication
  | means | precondition | strengthenedGoal | consequence | specialization | none
  deriving DecidableEq

/-- The implications a purpose or conditional row may record. -/
private def implications : List (String × Implication) :=
  [("means", .means), ("precondition", .precondition), ("strengthenedGoal", .strengthenedGoal),
    ("consequence", .consequence), ("specialization", .specialization), ("none", .none)]

/-- A construal row. -/
structure Construal where
  /-- The reading of *want*. -/
  want : WantReading
  /-- The construal of the modal. -/
  modal : ModalConstrual
  /-- The interpretation. -/
  interpretation : Interpretation
  /-- The implication. -/
  implication : Implication

/-- The configuration a construal row records. -/
def Construal.ofRow (row : LinguisticExample) : Option Construal := do
  guard (row.feature? "construction" = some "construal")
  return ⟨← row.parse? "want"
      [("effective", WantReading.effective), ("mere", .mere), ("weak", .weak)],
    ← row.parse? "modal" [("teleological", ModalConstrual.teleological), ("deontic", .deontic),
      ("speakerTeleological", .speakerTeleological)],
    ← row.parse? "interpretation" [("anankastic", Interpretation.anankastic),
      ("nearAnankastic", .nearAnankastic), ("nonAnankastic", .nonAnankastic)],
    ← row.parse? "implication" implications⟩

/-- §7.2.1: an anankastic interpretation arises only when *want* targets effective preferences
and the modal is construed teleologically over the same agent's effective preferences, (88). -/
theorem anankastic_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "construal" →
    ∃ c ∈ Construal.ofRow row,
      (c.interpretation = .anankastic → c.want = .effective ∧ c.modal = .teleological) := by
  decide

/-- §7.1.2: with that setting fixed, anankastics and the near-anankastics of §4 differ only in
the implication the temporal relation of goal and prejacent invites, a means or a precondition
for the former, a strengthened goal, a consequence or a specialization for the latter. -/
theorem implication_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "construal" →
    ∃ c ∈ Construal.ofRow row, c.want = .effective → c.modal = .teleological →
      (c.interpretation = .anankastic ↔
        c.implication = .means ∨ c.implication = .precondition) := by
  decide

/-- The reading of *want* an incompatible-wants row records. -/
def WantReading.ofRow (row : LinguisticExample) : Option WantReading := do
  guard (row.feature? "construction" = some "incompatibleWants")
  row.parse? "construal" [("mere", WantReading.mere), ("effective", .effective)]

/-- (52) to (55): two wants the agent knows to be incompatible are coherent on the mere-desire
reading, `want_both`, and not on the effective one, since maximal elements of a consistent
structure are jointly compatible with the agent's beliefs,
`PreferenceStructure.Consistent.inter_inter_nonempty_of_mem_maxElts`. -/
theorem incompatible_rows : ∀ row ∈ Examples.all,
    row.feature? "construction" = some "incompatibleWants" →
    ∃ r ∈ WantReading.ofRow row, (row.judgment = .acceptable ↔ r = .mere) := by
  decide

/-- The mood of a conditional whose antecedent the speaker has just excluded. -/
inductive Mood
  | indicative | subjunctive
  deriving DecidableEq

/-- The mood a row records. -/
def Mood.ofRow (row : LinguisticExample) : Option Mood := do
  guard (row.feature? "construction" = some "mood")
  row.parse? "mood" [("indicative", Mood.indicative), ("subjunctive", .subjunctive)]

/-- (91) and (98): when the speaker knows the agent lacks the hypothesized preference, the
antecedent is epistemically impossible, the conditional vacuously true, `anankastic_of_not_want`,
and the constraint on indicatives applies, for conditionals and purpose constructions alike. -/
theorem mood_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "mood" →
    ∃ m ∈ Mood.ofRow row, (row.judgment = .acceptable ↔ m = .subjunctive) := by
  decide

/-- The implication a purpose row records. -/
def Implication.ofRow (row : LinguisticExample) : Option Implication := do
  guard (row.feature? "construction" = some "purpose")
  row.parse? "implication" implications

/-- §7.1.3: purpose constructions admit means and preconditions; teleological consequences are
excluded because the prejacent cannot be subsequent to the goal, and the infelicity with
specializations is data the paper leaves open. -/
theorem purpose_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "purpose" →
    ∃ i ∈ Implication.ofRow row,
      (row.judgment = .acceptable ↔ i = .means ∨ i = .precondition) := by
  decide

end CondoravdiLauer2016
