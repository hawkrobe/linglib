module

public import Linglib.Semantics.Attitudes.Preference.Structure
public import Linglib.Semantics.Conditionals.Restrictor
public import Linglib.Data.Examples.CondoravdiLauer2016
public import Studies.VonFintelIatridou2005
public import Mathlib.Tactic.FinCases

/-!
# Condoravdi and Lauer 2016: anankastic conditionals are just conditionals

Condoravdi and Lauer argue that *If you want to go to Harlem, you have to take the A train* is
a regular hypothetical indicative conditional: the problem Sæbø found, that the antecedent
goal must enter the ordering of the modal, and the one von Fintel and Iatridou and
von Stechow, Krasikova and Penka added, that conflicting actual goals must not, are both resolved
by the lexical meanings involved once *want* reports an action-relevant preference. On that
reading *want* says its complement is a maximal element of the agent's effective preference
structure, a strict partial order on propositions that is consistent with the agent's beliefs, so
hypothesizing a preference for Harlem hypothesizes the absence of every preference the agent knows
to be incompatible with it. The conditional has the double-modal structure of Frank, a
covert necessity over the speaker's beliefs, ordered by stereotypicality and restricted by the
antecedent, with the priority modal over the historical alternatives in its scope, whose ordering
source at each world is the agent's maximal effective preferences there. The same setting covers
the near-anankastics of strengthened goals, teleological consequences and specializations, which
differ from anankastics only in the pragmatic implication that the temporal relation of goal and
prejacent invites; reading *want* or the modal differently gives the non-anankastic and deontic
cases.

## Main statements

* `anankastic_of_subset`: (88) holds when the effective preferences are consistent and realizing
  the goal among the historical alternatives requires the prejacent.
* `HobokenScenario.anankastic_harlem`, `HobokenScenario.not_possibility_path`: in the Hoboken
  scenario the Harlem sentence (1) is true and (14) false, where Sæbø's analysis makes (1) false
  and (14) true, `HobokenScenario.saebo_harlem`, `HobokenScenario.saebo_path`.
* `HobokenScenario.not_anankastic_desire`: on the mere-desire construal of *want* the Harlem
  sentence is false at the Hoboken world.

## Implementation notes

* Both modals are Kratzer's `necessity`, as (88) says. The priority modal's ordering source is
  `orderingSource P a`, the maximal preferences of `P a v` at each world `v`, so an anankastic is
  `conditionalNecessity` with no operator of its own, and Sæbø's rival restricts the same
  ordering source where the paper restricts the outer modal base.
* The sufficient condition for (88) quantifies over every antecedent world of the speaker's
  beliefs rather than the typical ones, and takes the effective preferences consistent relative to
  the historical alternatives, which keeps out the atypical continuations the paper leaves to a
  separate mechanism.
* The Hoboken scenario is a model in which the speaker is uncertain about the addressee's goal,
  with an empty stereotypical ordering, so the Harlem sentence is true through its antecedent
  worlds rather than vacuously.

## TODO

* Informal in the paper and not formalized: the temporal interpretation of the internal
  antecedent and the prejacent, the pragmatic derivation of the means-of implication, the
  strong/weak modal contrast of (96) and (97), purpose constructions, informational asymmetry,
  the consistency of the double-modal readings of (81) to (83), and the closure condition that
  would validate conjunction introduction for effective preferences.

## References

* [C. Condoravdi and S. Lauer, *Anankastic conditionals are just conditionals*
  (2016)][condoravdi-lauer-2016]
* [C. Condoravdi and S. Lauer, *Performative verbs and performative acts*
  (2011)][condoravdi-lauer-2011]
* [K. J. Sæbø, *Necessary conditions in a natural language* (2001)][saebo-2001]
* [K. von Fintel and S. Iatridou, *What to do if you want to go to Harlem: Anankastic
  conditionals and related matters* (2005)][von-fintel-iatridou-2005]
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

@[expose] public section

namespace CondoravdiLauer2016

open Desire.Preferential Modality Conditional.Restrictor

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
preference `{w}` is not a preference for `Set.univ`. -/
theorem not_monotone_want [Nontrivial W] :
    ¬ Monotone (Want (fun (_ : Unit) _ ↦ .single {w}) () · w) := fun h ↦
  Set.singleton_ne_univ w (h (Set.subset_univ {w}) ⟨rfl, fun _ _ h ↦ h⟩).1.symm

/-- Nor is it downward entailing, since the single preference `Set.univ` is not a preference for
`{w}`. -/
theorem not_antitone_want [Nontrivial W] :
    ¬ Antitone (Want (fun (_ : Unit) _ ↦ .single Set.univ) () · w) := fun h ↦
  Set.singleton_ne_univ w (h (Set.subset_univ {w}) ⟨rfl, fun _ _ h ↦ h⟩).1

/-- On a background that need not be consistent, wanting `p` and wanting `q` are compatible even
when `p` and `q` are not, as on the mere-desire reading of (52) and (53), §2.3 and §5.4. -/
theorem want_both (p q : Set W) :
    Want (fun (_ : Unit) _ ↦ .discrete {p, q}) () p w ∧
      Want (fun (_ : Unit) _ ↦ .discrete {p, q}) () q w := by
  simp [Want]

/-- In Levinson's Paris and Rome, (56) and (58), on the effective reading, §5.2, two effective
preferences leave no room for a third that is incompatible with their conjunction, since the
maximal elements of a consistent structure are jointly compatible with the agent's beliefs. -/
theorem no_third_effective {r : Set W} (hC : (P a w).Consistent (B w)) (hp : Want P a p w)
    (hq : Want P a q w) (hr : Want P a r w) : (B w ∩ (p ∩ q ∩ r)).Nonempty :=
  hC.inter_sInter_maxElts_nonempty.mono <| Set.inter_subset_inter_right _ <|
    Set.subset_inter (Set.subset_inter (Set.sInter_subset_of_mem hp) (Set.sInter_subset_of_mem hq))
      (Set.sInter_subset_of_mem hr)

/-- Three unranked preferences over three worlds, pairwise compatible but jointly
inconsistent. -/
def threeWay : PreferenceStructure (Fin 3) :=
  .discrete {{w | w ≠ 2}, {w | w ≠ 0}, {w | w ≠ 1}}

/-- By footnote 29, consistency (66) is stronger than pairwise compatibility, which is what the
weaker version of [condoravdi-lauer-2011] leaves. -/
theorem threeWay_pairwise_not_consistent :
    (∀ p ∈ threeWay.prefs, ∀ q ∈ threeWay.prefs, (p ∩ q).Nonempty) ∧
      ¬ threeWay.Consistent Set.univ := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) <;> exact Set.nonempty_def.2 (by decide)
  · obtain ⟨_, _, _, _, h⟩ := h threeWay.prefs subset_rfl (by
      ext w
      fin_cases w <;> simp [threeWay, PreferenceStructure.discrete])
    exact h

/-! ### Previous approaches -/

/-- [von-fintel-iatridou-2005]'s *have to* on the reading (26), §3.2.2, is necessity under the
primary ordering source `g_desG(w) = {p}` of the designated goal. A single proposition has the
effect of adding it to the modal base, as long as the two are compatible, so this is the
designated-goal *have to* of that study and the analysis amounts to adding the internal
antecedent to the modal base; the effective-preference source of (88) instead varies from world
to world, footnote 46. -/
theorem necessity_designatedGoal_iff_haveTo {f : Background W} {p r : W → Prop}
    (h : ((f.restrict p).accessibleWorlds w).Nonempty) :
    necessity f (fun _ ↦ {p}) r w ↔ VonFintelIatridou2005.haveTo f p r w := by
  have hf : f ⊔ (fun _ ↦ {p}) = f.restrict p := funext fun _ ↦ Set.union_singleton
  rw [VonFintelIatridou2005.haveTo, conditionalNecessity, necessity_iff, necessity_iff,
    bestWorlds_bot, bestWorlds_eq_accessibleWorlds_sup (hf ▸ h), hf]

/-! ### Double-modal structure -/

/-- A single necessity modal restricted by the antecedent validates strengthening of the
antecedent in the form [kaufmann-schwager-2009] reject, §6.2: *if A, must C* and *if A and B,
must not C* together entail that no best *A*-world is a *B*-world, a preference against *B*
that (81) to (83) do not carry. The double-modal structure (76b) escapes, since each
conditional's inner modal is evaluated in its own typical antecedent worlds. -/
theorem single_modal_strengthening {f g : Background W} {α β γ : W → Prop}
    (h₁ : conditionalNecessity f g α γ w)
    (h₂ : conditionalNecessity f g (fun v ↦ α v ∧ β v) (fun v ↦ ¬ γ v) w) :
    ∀ u ∈ bestWorlds (f.restrict α) g w, ¬ β u := by
  intro u hu hβ
  have hu' := Background.mem_accessibleWorlds_restrict.1 hu.1
  exact h₂ u (mem_bestWorlds_of_subset
    (fun v hv ↦ Background.accessibleWorlds_restrict_mono (fun _ h ↦ h.1) hv)
    hu (Background.mem_accessibleWorlds_restrict.2 ⟨hu'.1, hu'.2, hβ⟩)) (h₁ u hu)

/-! ### The analysis -/

/-- On its teleological construal, §7.1, the priority modal is ordered at each world `v` by the
maximal preferences of `P a v`, so that `orderingSource EP a` is the paper's `g_epA`. -/
def orderingSource (P : A → W → PreferenceStructure W) (a : A) : Background W :=
  fun v ↦ (P a v).maxElts

/-- Preferences consistent relative to the modal base do not split the best worlds as the
ordering source of §2.3 does: the best worlds are the accessible ones realizing every maximal
preference. -/
theorem bestWorlds_orderingSource {f : Background W} {v : W}
    (hC : (P a v).Consistent (f.accessibleWorlds v)) :
    bestWorlds f (orderingSource P a) v = f.accessibleWorlds v ∩ ⋂₀ (P a v).maxElts := by
  have h : (f ⊔ orderingSource P a).accessibleWorlds v =
      f.accessibleWorlds v ∩ ⋂₀ (P a v).maxElts := by
    rw [Background.accessibleWorlds_sup]
    rfl
  rw [bestWorlds_eq_accessibleWorlds_sup (h ▸ hC.inter_sInter_maxElts_nonempty), h]

/-- By (90), under consistency, an effective preference for `p` excludes one for any `q` the agent
believes incompatible with `p`. -/
theorem want_disjoint (hC : ∀ w, (P a w).Consistent (B w)) (h : ∀ w, B w ∩ (p ∩ q) = ∅) :
    Disjoint {w | Want P a p w} {w | Want P a q w} :=
  Set.disjoint_left.2 fun w hp hq ↦
    ((hC w).inter_inter_nonempty_of_mem_maxElts hp hq).ne_empty (h w)

/-- The antecedent's restriction removes every world with a conflicting effective preference,
§7.1.1, so an actual preference for Hoboken never reaches the priority modal. -/
theorem not_want_of_mem_restricted {f : Background W} (hC : ∀ w, (P a w).Consistent (B w))
    (h : ∀ w, B w ∩ (p ∩ q) = ∅) {v : W}
    (hv : v ∈ (f.restrict (Want P a p)).accessibleWorlds w) : ¬ Want P a q v :=
  Set.disjoint_left.1 (want_disjoint hC h) (Background.mem_accessibleWorlds_restrict.1 hv).2

/-- The conditional (88) holds when at every belief world where the agent effectively prefers `p`
the effective preferences are consistent relative to the historical alternatives and realizing `p`
there requires `q`, a condition stronger than the paraphrase (89) in bypassing the typicality
restriction. The antecedent's preference enters the ordering source
because *want* and the modal read the same background; compatible goals such as comfort in (92)
stay in the ordering, and conflicting ones are gone by `not_want_of_mem_restricted`. -/
theorem anankastic_of_subset {f₁ g₁ f₂ : Background W}
    (hC : ∀ v ∈ (f₁.restrict (Want P a p)).accessibleWorlds w,
      (P a v).Consistent (f₂.accessibleWorlds v))
    (hq : ∀ v ∈ (f₁.restrict (Want P a p)).accessibleWorlds w, f₂.accessibleWorlds v ∩ p ⊆ q) :
    conditionalNecessity f₁ g₁ (Want P a p) (necessity f₂ (orderingSource P a) (· ∈ q)) w := by
  intro v hv u hu
  rw [mem_bestAccessible, bestWorlds_orderingSource (hC v hv.1)] at hu
  exact hq v hv.1 ⟨hu.1, hu.2 p (Background.mem_accessibleWorlds_restrict.1 hv.1).2⟩

end General

/-! ### The Hoboken scenario

Von Fintel and Iatridou's stranger on the platform, §2.3 and §7.1.1: the speaker knows the
facts about the trains but not the addressee's goal, which is Hoboken. -/

namespace HobokenScenario

/-- Where the addressee wants to go. -/
inductive Goal
  | harlem | hoboken
  deriving DecidableEq

/-- The two trains. -/
inductive Train
  | aTrain | path
  deriving DecidableEq

/-- A world records the addressee's goal, the train taken, and which train goes to Harlem, the
other going to Hoboken. -/
structure World where
  /-- The addressee's effective goal. -/
  goal : Goal
  /-- The train the addressee takes. -/
  train : Train
  /-- The train that goes to Harlem. -/
  harlemTrain : Train
  deriving DecidableEq

variable {w : World}

/-- The addressee goes to Harlem. -/
def harlem : Set World := {w | w.train = w.harlemTrain}

/-- The addressee goes to Hoboken. -/
def hoboken : Set World := {w | w.train ≠ w.harlemTrain}

/-- The addressee takes the A train. -/
def aTrain : Set World := {w | w.train = .aTrain}

/-- The addressee takes the PATH train. -/
def path : Set World := {w | w.train = .path}

/-- The proposition a goal is a preference for. -/
def Goal.dest : Goal → Set World
  | .harlem => HobokenScenario.harlem
  | .hoboken => HobokenScenario.hoboken

/-- The addressee's effective preference structure is the single preference for the goal. -/
def ep (_ : Unit) (w : World) : PreferenceStructure World := .single w.goal.dest

/-- The addressee's mere desires are both destinations, unranked, at every world. -/
def desire (_ : Unit) (_ : World) : PreferenceStructure World := .discrete {harlem, hoboken}

/-- The speaker believes that the A train goes to Harlem. -/
def fBelS : Background World := fun _ ↦ {fun v ↦ v.harlemTrain = .aTrain}

/-- In the historical alternatives before boarding the goal and the routes are settled and the
train is not. -/
def fHist : Background World :=
  fun v ↦ {fun u ↦ u.goal = v.goal, fun u ↦ u.harlemTrain = v.harlemTrain}

/-- The world where the A train goes to Harlem and the addressee, heading for Hoboken, takes the
PATH train. -/
def w₀ : World := ⟨.hoboken, .path, .aTrain⟩

private theorem mem_fBelS {v : World} :
    v ∈ fBelS.accessibleWorlds w ↔ v.harlemTrain = .aTrain := by
  simp [fBelS]

private theorem mem_fHist {u v : World} :
    u ∈ fHist.accessibleWorlds v ↔ u.goal = v.goal ∧ u.harlemTrain = v.harlemTrain := by
  simp [fHist]

/-- Every goal is reachable among the historical alternatives. -/
theorem consistent_ep (v : World) : (ep () v).Consistent (fHist.accessibleWorlds v) := by
  refine PreferenceStructure.consistent_single ?_
  obtain ⟨g, t, h⟩ := v
  cases g <;> cases h
  exacts [⟨⟨.harlem, .aTrain, .aTrain⟩, rfl, mem_fHist.2 ⟨rfl, rfl⟩⟩,
    ⟨⟨.harlem, .path, .path⟩, rfl, mem_fHist.2 ⟨rfl, rfl⟩⟩,
    ⟨⟨.hoboken, .path, .aTrain⟩, nofun, mem_fHist.2 ⟨rfl, rfl⟩⟩,
    ⟨⟨.hoboken, .aTrain, .path⟩, nofun, mem_fHist.2 ⟨rfl, rfl⟩⟩]

/-- The best continuations of a world are its historical alternatives that reach the goal. -/
theorem bestWorlds_fHist (v : World) :
    bestWorlds fHist (orderingSource ep ()) v = fHist.accessibleWorlds v ∩ v.goal.dest := by
  rw [bestWorlds_orderingSource (consistent_ep v)]
  simp [ep]

/-- Nobody reaches both Harlem and Hoboken. -/
theorem harlem_inter_hoboken : harlem ∩ hoboken = ∅ := by
  ext
  simp [harlem, hoboken]

/-- At the Hoboken world the addressee wants Hoboken, so by (90) not Harlem; the world is in
the speaker's belief state and out of the antecedent's restriction of it, §7.1.1, so the
actual preference never reaches the priority modal. -/
theorem w₀_excluded :
    w₀ ∈ fBelS.accessibleWorlds w₀ ∧
      w₀ ∉ (fBelS.restrict (Want ep () harlem)).accessibleWorlds w₀ :=
  ⟨mem_fBelS.2 rfl, fun h ↦ not_want_of_mem_restricted (q := hoboken) consistent_ep
    (fun _ ↦ by rw [harlem_inter_hoboken, Set.inter_empty]) h ⟨rfl, fun _ _ h ↦ h⟩⟩

/-- A world where the A train goes to Harlem is a best world of the outer modal base the
antecedent restricts, as long as it verifies the antecedent. -/
private theorem mem_bestWorlds_fBelS {α : World → Prop} {v : World}
    (hv : v.harlemTrain = .aTrain) (hα : α v) : v ∈ bestWorlds (fBelS.restrict α) ⊥ w := by
  rw [bestWorlds_bot, Background.mem_accessibleWorlds_restrict]
  exact ⟨mem_fBelS.2 hv, hα⟩

/-- An anankastic whose destination is reached exactly by one train, when the A train goes to
Harlem, is true at every world, the Hoboken world included. -/
private theorem anankastic_dest {d t : Set World}
    (hd : ∀ u : World, u.harlemTrain = .aTrain → (u ∈ d ↔ u ∈ t)) :
    conditionalNecessity fBelS ⊥ (Want ep () d) (necessity fHist (orderingSource ep ()) (· ∈ t))
      w :=
  anankastic_of_subset (fun v _ ↦ consistent_ep v) fun _ hv u ⟨hu, hdu⟩ ↦
    (hd u ((mem_fHist.1 hu).2.trans
      (mem_fBelS.1 (Background.mem_accessibleWorlds_restrict.1 hv).1))).1 hdu

/-- The Harlem sentence (1) is true at every world, the Hoboken world included, §7.1.1. -/
theorem anankastic_harlem :
    conditionalNecessity fBelS ⊥ (Want ep () harlem)
      (necessity fHist (orderingSource ep ()) (· ∈ aTrain)) w :=
  anankastic_dest fun u hu ↦ by simp [harlem, aTrain, hu]

/-- The Hoboken sentence (15) is true alongside it. -/
theorem anankastic_hoboken :
    conditionalNecessity fBelS ⊥ (Want ep () hoboken)
      (necessity fHist (orderingSource ep ()) (· ∈ path)) w :=
  anankastic_dest fun ⟨_, t, _⟩ hu ↦ by cases t <;> simp_all [hoboken, path]

/-- (14), *if you want to go to Harlem, you can take the PATH train*, is false at every world,
§2.3, since the best continuations of every antecedent world reach Harlem, which only the A train
does. -/
theorem not_possibility_path :
    ¬ conditionalNecessity fBelS ⊥ (Want ep () harlem)
      (possibility fHist (orderingSource ep ()) (· ∈ path)) w := fun h ↦ by
  obtain ⟨u, hu, hpath⟩ := h ⟨.harlem, .aTrain, .aTrain⟩
    (mem_bestWorlds_fBelS rfl ⟨rfl, fun _ _ h ↦ h⟩)
  rw [mem_bestAccessible, bestWorlds_fHist] at hu
  have := (mem_fHist.1 hu.1).2
  simp_all [Goal.dest, harlem, path]

/-- On the mere-desire construal of (105), with `desire` for *want* and the modal still ordered by
the effective preferences, the Harlem sentence is false at the Hoboken world, §7.2.1: the
addressee merely desires Harlem there too, so the antecedent does not exclude the world, and its
best continuations take the PATH train. The anankastic reading needs the effective construal of
both. -/
theorem not_anankastic_desire :
    ¬ conditionalNecessity fBelS ⊥ (Want desire () harlem)
      (necessity fHist (orderingSource ep ()) (· ∈ aTrain)) w₀ := fun h ↦
  nomatch h w₀ (mem_bestWorlds_fBelS rfl ⟨.inl rfl, fun _ _ h ↦ h⟩) w₀
    (by rw [mem_bestAccessible, bestWorlds_fHist]; exact ⟨mem_fHist.2 ⟨rfl, rfl⟩, nofun⟩)

/-- The Hoboken world is a best world under the addressee's actual goal alone. -/
private theorem w₀_mem_bestWorlds : w₀ ∈ bestWorlds fBelS (orderingSource ep ()) w₀ := by
  have hC : (ep () w₀).Consistent (fBelS.accessibleWorlds w₀) :=
    PreferenceStructure.consistent_single ⟨w₀, nofun, mem_fBelS.2 rfl⟩
  rw [bestWorlds_orderingSource hC]
  exact ⟨mem_fBelS.2 rfl, by simp [ep, w₀]; exact nofun⟩

/-- Sæbø's analysis, §2.3, adds the internal antecedent to the bouletic ordering source, the
addressee's actual goals, on the circumstantial base that here coincides with the speaker's
beliefs. At the Hoboken world the ordering then holds Harlem and Hoboken, which no world realizes
together, so the best worlds split and the Harlem sentence comes out false. -/
theorem saebo_harlem :
    ¬ necessity fBelS ((orderingSource ep ()).restrict (· ∈ harlem)) (· ∈ aTrain) w₀ :=
  not_necessity_insert (q := (· ∈ hoboken)) ⟨rfl, fun _ _ h ↦ h⟩
    (fun _ h h' ↦ h h') w₀_mem_bestWorlds nofun nofun

/-- On the same analysis (14) comes out true, since some best world takes the PATH train. -/
theorem saebo_path :
    possibility fBelS ((orderingSource ep ()).restrict (· ∈ harlem)) (· ∈ path) w₀ :=
  ⟨w₀, mem_bestWorlds_insert (q := (· ∈ hoboken)) ⟨rfl, fun _ _ h ↦ h⟩
    (fun _ h h' ↦ h h') w₀_mem_bestWorlds nofun, rfl⟩

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

/-- The relation the prejacent bears to the goal, §7.1.2, is a means to it, a precondition for it,
a means to a strengthened goal, a consequence of it, a specialization of it, or none. -/
inductive Implication
  | means | precondition | strengthenedGoal | consequence | specialization | none
  deriving DecidableEq

/-- The implications a purpose or conditional row may record. -/
def implications : List (String × Implication) :=
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
def Construal.ofRow (row : Datum) : Option Construal := do
  guard (row.feature? "construction" = some "construal")
  return ⟨← row.parse? "want"
      [("effective", WantReading.effective), ("mere", .mere), ("weak", .weak)],
    ← row.parse? "modal" [("teleological", ModalConstrual.teleological), ("deontic", .deontic),
      ("speakerTeleological", .speakerTeleological)],
    ← row.parse? "interpretation" [("anankastic", Interpretation.anankastic),
      ("nearAnankastic", .nearAnankastic), ("nonAnankastic", .nonAnankastic)],
    ← row.parse? "implication" implications⟩

/-- By §7.2.1, an anankastic interpretation arises only when *want* targets effective preferences
and the modal is construed teleologically over the same agent's effective preferences, (88); on
the mere-desire construal the Harlem sentence fails, `HobokenScenario.not_anankastic_desire`. -/
theorem anankastic_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "construal" →
    ∃ c ∈ Construal.ofRow row,
      (c.interpretation = .anankastic → c.want = .effective ∧ c.modal = .teleological) := by
  decide

/-- By §7.1.2, with that setting fixed, anankastics and the near-anankastics of §4 differ only in
the implication the temporal relation of goal and prejacent invites, a means or a precondition
for the former, a strengthened goal, a consequence or a specialization for the latter. -/
theorem implication_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "construal" →
    ∃ c ∈ Construal.ofRow row, c.want = .effective → c.modal = .teleological →
      (c.interpretation = .anankastic ↔
        c.implication = .means ∨ c.implication = .precondition) := by
  decide

/-- The reading of *want* an incompatible-wants row records. -/
def WantReading.ofRow (row : Datum) : Option WantReading := do
  guard (row.feature? "construction" = some "incompatibleWants")
  row.parse? "construal" [("mere", WantReading.mere), ("effective", .effective)]

/-- In (52) to (55), two wants the agent knows to be incompatible are coherent on the mere-desire
reading, `want_both`, and not on the effective one, since maximal elements of a consistent
structure are jointly compatible with the agent's beliefs,
`PreferenceStructure.Consistent.inter_inter_nonempty_of_mem_maxElts`. -/
theorem incompatible_rows : ∀ row ∈ Examples.all,
    row.feature? "construction" = some "incompatibleWants" →
    ∃ r ∈ WantReading.ofRow row, (row.JudgedFelicitous ↔ r = .mere) := by
  decide

/-- The mood of a conditional whose antecedent the speaker has just excluded. -/
inductive Mood
  | indicative | subjunctive
  deriving DecidableEq

/-- The mood a row records. -/
def Mood.ofRow (row : Datum) : Option Mood := do
  guard (row.feature? "construction" = some "mood")
  row.parse? "mood" [("indicative", Mood.indicative), ("subjunctive", .subjunctive)]

/-- In (91) and (98), when the speaker knows the agent lacks the hypothesized preference, the
antecedent is epistemically impossible, the conditional vacuously true, `vacuous_conditional`,
and the constraint on indicatives applies, for conditionals and purpose constructions alike. -/
theorem mood_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "mood" →
    ∃ m ∈ Mood.ofRow row, (row.judgment = .acceptable ↔ m = .subjunctive) := by
  decide

/-- The implication a purpose row records. -/
def Implication.ofRow (row : Datum) : Option Implication := do
  guard (row.feature? "construction" = some "purpose")
  row.parse? "implication" implications

/-- By §7.1.3, purpose constructions admit means and preconditions; teleological consequences are
excluded because the prejacent cannot be subsequent to the goal, and the infelicity with
specializations is data the paper leaves open. -/
theorem purpose_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "purpose" →
    ∃ i ∈ Implication.ofRow row,
      (row.judgment = .acceptable ↔ i = .means ∨ i = .precondition) := by
  decide

end CondoravdiLauer2016
