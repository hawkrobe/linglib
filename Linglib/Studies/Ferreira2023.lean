import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Modality.Directive
import Linglib.Fragments.Portuguese.Modals
import Linglib.Data.Examples.Ferreira2023

/-!
# Ferreira (2023): A square of necessities

This file formalizes [ferreira-2023]'s square of necessities. Portuguese has a weak necessity
modal *dever* between *poder* and *ter que* ((28)–(29), the test of [rubinstein-2021] in (27)),
and both necessity modals take past imperfect morphology (*devia*, *tinha que*) without a
change of force. That morphology is [von-fintel-iatridou-2023]'s X-marking, read as
[stalnaker-1975]'s suspension of a presupposition: the modal base is replaced by its
∗-revision for the prejacent, which adds the prejacent-worlds most similar to the accessible
ones (79), so the marked modals reason from a domain that no longer excludes the prejacent
((78), (84)). The weak/strong contrast is X-marking of the other parameter: the
∗∗-revision of an ordering source for a proposition makes every best world satisfying it
better than every best world failing it (131), and strong necessity under the revised
ordering is [von-fintel-iatridou-2008]'s weak necessity, the best of the best worlds ((129),
(133): `snXg_iff_weakNecessity`, with no side condition). The two shifters `revise` and
`starstar` generate the square (134), which Portuguese fills with *tem que*, *tinha que*,
*deve*, *devia* (135): the fragment's forces are weak necessity exactly at the Xg-marked
vertices (`force_of_vertex`). The consistency paradigm of §2 ((16)–(25), (30), (32)) is
derived: each contradictory conjunction is contradictory in every model and each acceptable
one has a model (`rows_predicted`); the dialogues (80)–(81) are a four-world model in which
suspending the knowledge that Peter is not in his office reinstates the marked necessity on a
workday and not on a holiday.

## Implementation notes

* `bestOf R D` is the set of members of `D` no member betters under a relation; with the
  betterness of an ordering source (130) it is the substrate's `bestAmong`
  (`bestOf_better`), and with the ∗∗-revised betterness the `p`-best of the best
  (`bestOf_starstar`). The ∗∗-revision is defined on the betterness relation, as in (131),
  not by adding a premise to the ordering source.
* The ∗-revision (79) is a modal base whose single premise is the widened domain, so it is a
  definition rather than a property (`accessibleWorlds_revise`). Its similarity orderings are
  premise sets per world; (41a) is `Similarity.IsCentered`.
* The ordering revision targets a proposition `p` independent of the prejacent, the asymmetry
  the paper leaves open (§4): with `p` the prejacent, weak necessity would collapse into
  possibility.
* Contradictoriness of a conjunction quantifies over models with nonempty best worlds, the
  deliberative reading of (27ii); consistency is a two-world model.
* The model of (80)–(81) reads B's initial guess as taking the day for a workday, which the
  holiday news of (80) replaces; the marked necessity there is strong, the weak one differing
  only by the ordering revision.

## TODO

* (82) states that no entailment holds between an X-marked necessity and its unmarked
  counterpart. The reverse direction fails (`snXf_not_entails_sn`), but under (79) and (129a)
  the unmarked necessity entails the marked one (`sn_entails_snXf`): a ∗-revision adds only
  prejacent-worlds, which cannot unseat a best world, so the forward non-entailment does not
  follow from the paper's definitions.

## References

* [ferreira-2023]
* [von-fintel-iatridou-2008]
* [von-fintel-iatridou-2023]
* [rubinstein-2021]
* [stalnaker-1975]
* [kratzer-1981]
* [kratzer-2012]
-/

namespace Ferreira2023

open Modality Modality.Kratzer Modality.Directive Data.Examples

variable {W : Type*}

/-! ### ∗-revision of a modal base (79) -/

/-- A similarity ordering: for each world, the premise set ranking worlds by their similarity
to it. -/
abbrev Similarity (W : Type*) := W → List (W → Prop)

/-- (41a): each world's similarity ordering singles it out. -/
def Similarity.IsCentered (sim : Similarity W) : Prop := ∀ w, propIntersection (sim w) = {w}

/-- (79): the ∗-revision of `f` for `p`, the modal base whose domain at `w` is the domain of
`f` together with the `p`-worlds most similar to some world of it. -/
def revise (sim : Similarity W) (f : ModalBase W) (p : W → Prop) : ModalBase W :=
  λ w => [λ w' => w' ∈ accessibleWorlds f w ∨
    ∃ w'' ∈ accessibleWorlds f w, w' ∈ bestAmong {v | p v} (sim w'')]

theorem accessibleWorlds_revise (sim : Similarity W) (f : ModalBase W) (p : W → Prop) (w : W) :
    accessibleWorlds (revise sim f p) w =
      accessibleWorlds f w ∪
        {w' | ∃ w'' ∈ accessibleWorlds f w, w' ∈ bestAmong {v | p v} (sim w'')} := by
  ext w'
  simp [accessibleWorlds, propIntersection, revise]

/-- The revision widens the domain. -/
theorem subset_accessibleWorlds_revise (sim : Similarity W) (f : ModalBase W) (p : W → Prop)
    (w : W) : accessibleWorlds f w ⊆ accessibleWorlds (revise sim f p) w := by
  rw [accessibleWorlds_revise]; exact Set.subset_union_left

/-- Every world the revision adds is a `p`-world. -/
theorem revise_new (sim : Similarity W) (f : ModalBase W) (p : W → Prop) (w w' : W)
    (h : w' ∈ accessibleWorlds (revise sim f p) w) (hn : w' ∉ accessibleWorlds f w) : p w' := by
  rw [accessibleWorlds_revise] at h
  rcases h with h | ⟨_, _, h⟩
  · exact absurd h hn
  · exact bestAmong_sub _ _ h

/-! ### ∗∗-revision of an ordering source (130)–(131) -/

/-- (130): `u` is better than `v` according to `g w`. -/
def Better (g : OrderingSource W) (w u v : W) : Prop :=
  atLeastAsGoodAs (g w) u v ∧ ¬ atLeastAsGoodAs (g w) v u

/-- The members of `D` no member betters under `R`. -/
def bestOf (R : W → W → Prop) (D : Set W) : Set W := {u | u ∈ D ∧ ∀ v ∈ D, ¬ R v u}

/-- Under the betterness of an ordering source, the best worlds are the substrate's. -/
theorem bestOf_better (g : OrderingSource W) (w : W) (D : Set W) :
    bestOf (Better g w) D = bestAmong D (g w) := by
  ext u
  simp only [bestOf, bestAmong, Better, Set.mem_ofPred_eq, not_and, not_not]

theorem bestWorlds_eq_bestAmong (f : ModalBase W) (g : OrderingSource W) (w : W) :
    bestWorlds f g w = bestAmong (accessibleWorlds f w) (g w) := rfl

/-- (131): the ∗∗-revision of the betterness of `g w` on `D` for `p`: in addition, every best
`p`-world betters every best non-`p`-world. -/
def starstar (g : OrderingSource W) (p : W → Prop) (w : W) (D : Set W) (u v : W) : Prop :=
  Better g w u v ∨ (p u ∧ ¬ p v ∧ u ∈ bestAmong D (g w) ∧ v ∈ bestAmong D (g w))

/-- The best worlds under the ∗∗-revision are the `p`-best of the best: the lexicographic
refinement of (129b). -/
theorem bestOf_starstar (g : OrderingSource W) (p : W → Prop) (w : W) (D : Set W) :
    bestOf (starstar g p w D) D = bestAmong (bestAmong D (g w)) [p] := by
  ext u
  constructor
  · rintro ⟨hu, h⟩
    have hbest : u ∈ bestAmong D (g w) :=
      ⟨hu, λ v hv hvu => by_contra λ huv => h v hv (Or.inl ⟨hvu, huv⟩)⟩
    refine ⟨hbest, λ v hv _ q hq hqv => ?_⟩
    rcases List.mem_singleton.mp hq with rfl
    by_contra hqu
    exact h v hv.1 (Or.inr ⟨hqv, hqu, hv, hbest⟩)
  · rintro ⟨⟨hu, hbest⟩, hp⟩
    refine ⟨hu, λ v hv h => ?_⟩
    rcases h with ⟨hvu, huv⟩ | ⟨hpv, hpu, hv', hu'⟩
    · exact huv (hbest v hv hvu)
    · refine hpu (hp v hv' (λ q hq hqu => ?_) p (List.mem_singleton.mpr rfl) hpv)
      rcases List.mem_singleton.mp hq with rfl
      exact absurd hqu hpu

/-- The `p`-best of a nonempty set are nonempty: a `p`-member if there is one, else all. -/
theorem exists_mem_bestAmong_singleton (S : Set W) (hS : S.Nonempty) (p : W → Prop) :
    ∃ u, u ∈ bestAmong S [p] := by
  by_cases hp : ∃ v ∈ S, p v
  · obtain ⟨v, hv, hpv⟩ := hp
    exact ⟨v, hv, λ _ _ _ q hq _ => by rcases List.mem_singleton.mp hq with rfl; exact hpv⟩
  · push Not at hp
    obtain ⟨u, hu⟩ := hS
    exact ⟨u, hu, λ u' hu' _ q hq hqu' => by
      rcases List.mem_singleton.mp hq with rfl; exact absurd hqu' (hp u' hu')⟩

/-! ### The square of necessities (134) -/

/-- (132b): strong necessity with the ordering source ∗∗-revised for `p`. -/
def snXg (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop) (w : W) : Prop :=
  ∀ w' ∈ bestOf (starstar g p w (accessibleWorlds f w)) (accessibleWorlds f w), q w'

/-- (133): weak necessity is strong necessity with an X-marked ordering source. -/
theorem snXg_iff_weakNecessity (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop)
    (w : W) : snXg f g p q w ↔ weakNecessity f g (λ _ => [p]) q w := by
  simp only [snXg, weakNecessity, bestOf_starstar, bestWorlds_eq_bestAmong]

/-- (78b), (84b): strong necessity with the modal base ∗-revised for the prejacent. -/
def snXf (sim : Similarity W) (f : ModalBase W) (g : OrderingSource W) (q : W → Prop) (w : W) :
    Prop :=
  necessity (revise sim f q) g q w

/-- A vertex of the square (134): whether the modal base and the ordering source are
X-marked. -/
structure Vertex where
  xf : Bool
  xg : Bool
  deriving DecidableEq, Repr

/-- (134): the necessity at a vertex, `p` the proposition the ordering revision targets and
`q` the prejacent. -/
def Vertex.necessity (v : Vertex) (sim : Similarity W) (f : ModalBase W) (g : OrderingSource W)
    (p q : W → Prop) (w : W) : Prop :=
  let f' := if v.xf then revise sim f q else f
  ∀ w' ∈ bestOf (if v.xg then starstar g p w (accessibleWorlds f' w) else Better g w)
    (accessibleWorlds f' w), q w'

theorem vertex_sn (sim : Similarity W) (f : ModalBase W) (g : OrderingSource W)
    (p q : W → Prop) (w : W) :
    Vertex.necessity ⟨false, false⟩ sim f g p q w ↔ strongNecessity f g q w := by
  simp only [Vertex.necessity, Bool.false_eq_true, ite_false, bestOf_better, strongNecessity,
    necessity_iff_all, bestWorlds_eq_bestAmong]

theorem vertex_snXg (sim : Similarity W) (f : ModalBase W) (g : OrderingSource W)
    (p q : W → Prop) (w : W) :
    Vertex.necessity ⟨false, true⟩ sim f g p q w ↔ snXg f g p q w := Iff.rfl

theorem vertex_snXf (sim : Similarity W) (f : ModalBase W) (g : OrderingSource W)
    (p q : W → Prop) (w : W) :
    Vertex.necessity ⟨true, false⟩ sim f g p q w ↔ snXf sim f g q w := by
  simp only [Vertex.necessity, Bool.false_eq_true, ite_false, ite_true, bestOf_better, snXf,
    necessity_iff_all, bestWorlds_eq_bestAmong]

theorem vertex_snXfg (sim : Similarity W) (f : ModalBase W) (g : OrderingSource W)
    (p q : W → Prop) (w : W) :
    Vertex.necessity ⟨true, true⟩ sim f g p q w ↔ snXg (revise sim f q) g p q w := Iff.rfl

/-! ### Entailments ((29), (82)) and Rubinstein's test (27) -/

/-- (27i), (29): strong necessity entails weak necessity, the `p`-best of the best being
best. -/
theorem sn_entails_snXg (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop) (w : W)
    (h : strongNecessity f g q w) : snXg f g p q w :=
  (snXg_iff_weakNecessity f g p q w).mpr (strong_entails_weak f g _ q w h)

/-- The best worlds when nothing is excluded and nothing ordered: every world. -/
theorem bestWorlds_empty_empty (w : W) :
    bestWorlds (emptyBackground (W := W)) (emptyBackground (W := W)) w = Set.univ := by
  rw [empty_ordering_emptyBackground, empty_base_universal_access]

/-- The `b`-best of both truth values. -/
theorem bestAmong_univ_eq (b : Bool) :
    bestAmong (Set.univ : Set Bool) [λ v => v = b] = {b} := by
  ext u
  simp only [bestAmong, atLeastAsGoodAs_iff, Set.mem_univ, true_and, List.forall_mem_cons,
    List.mem_nil_iff, false_implies, implies_true, and_true, Set.mem_singleton_iff,
    Set.mem_ofPred_eq]
  cases u <;> cases b <;> decide

/-- (27i), (20), (29): weak necessity does not entail strong necessity. -/
theorem snXg_not_entails_sn :
    ¬ ∀ (W : Type) (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop) (w : W),
      snXg f g p q w → strongNecessity f g q w := by
  intro h
  have hw : snXg (W := Bool) emptyBackground emptyBackground (· = true) (· = true) true := by
    rw [snXg_iff_weakNecessity]
    intro w' hw'
    rw [bestWorlds_empty_empty, bestAmong_univ_eq] at hw'
    exact hw'
  have hsn := h Bool emptyBackground emptyBackground (· = true) (· = true) true hw
  rw [strongNecessity, necessity_iff_all, bestWorlds_empty_empty] at hsn
  exact Bool.false_ne_true (hsn false (Set.mem_univ _))

/-- (27ii), (24): a weak necessity and the weak necessity of the negation are contradictory
as the conclusion of a deliberation. -/
theorem not_snXg_and_snXg_neg (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop) (w : W)
    (hne : (bestWorlds f g w).Nonempty) :
    ¬ (snXg f g p q w ∧ snXg f g p (λ v => ¬ q v) w) := by
  rintro ⟨h₁, h₂⟩
  rw [snXg_iff_weakNecessity] at h₁ h₂
  obtain ⟨u, hu⟩ := exists_mem_bestAmong_singleton _ hne p
  exact h₂ u hu (h₁ u hu)

/-- (29): weak necessity entails possibility when the best worlds are nonempty. -/
theorem snXg_entails_possibility (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop)
    (w : W) (hne : (bestWorlds f g w).Nonempty) (h : snXg f g p q w) : possibility f g q w := by
  rw [snXg_iff_weakNecessity] at h
  obtain ⟨u, hu⟩ := exists_mem_bestAmong_singleton _ hne p
  exact ⟨u, hu.1, h u hu⟩

/-- ∗-revising the base for the prejacent preserves strong necessity: a best world of the
widened domain is best in the original one or an added prejacent-world. -/
theorem sn_entails_snXf (sim : Similarity W) (f : ModalBase W) (g : OrderingSource W)
    (q : W → Prop) (w : W) (h : strongNecessity f g q w) : snXf sim f g q w := by
  intro w' hw'
  by_cases hmem : w' ∈ accessibleWorlds f w
  · exact h w' (bestAmong_superset (subset_accessibleWorlds_revise sim f q w) hw' hmem)
  · exact revise_new sim f q w w' hw'.1 hmem

/-- (82): the X-marked necessity does not entail the unmarked one. The revision adds the only
prejacent-world, which the ordering prefers. -/
theorem snXf_not_entails_sn :
    ¬ ∀ (W : Type) (sim : Similarity W) (f : ModalBase W) (g : OrderingSource W)
      (q : W → Prop) (w : W), snXf sim f g q w → strongNecessity f g q w := by
  intro h
  let f : ModalBase Bool := λ _ => [λ v => v = false]
  let g : OrderingSource Bool := λ _ => [λ v => v = true]
  have hacc : accessibleWorlds f true = {false} := by
    ext v; simp [accessibleWorlds, propIntersection, f]
  have hrev : accessibleWorlds (revise (λ _ => []) f (· = true)) true = Set.univ := by
    rw [accessibleWorlds_revise, hacc]
    ext v
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_univ, iff_true,
      bestAmong_empty, exists_eq_left]
    cases v <;> simp
  have hX : snXf (λ _ => []) f g (· = true) true := by
    rw [snXf, necessity_iff_all, bestWorlds_eq_bestAmong, hrev]
    intro w' hw'
    by_contra hq
    have hle : atLeastAsGoodAs (g true) true w' := (atLeastAsGoodAs_iff _ _ _).mpr λ r hr hrw => by
      rcases List.mem_singleton.mp hr with rfl; exact absurd hrw hq
    exact hq ((atLeastAsGoodAs_iff _ _ _).mp (hw'.2 true (Set.mem_univ _) hle) _
      (List.mem_singleton.mpr rfl) rfl)
  have hsn := h Bool (λ _ => []) f g (· = true) true hX
  rw [strongNecessity, necessity_iff_all, bestWorlds_eq_bestAmong, hacc] at hsn
  exact Bool.false_ne_true (hsn false ⟨rfl, λ v hv _ => by
    rw [Set.mem_singleton_iff.mp hv]; exact ordering_reflexive _ _⟩)

/-! ### Portuguese (135) -/

/-- The four necessity forms of Portuguese: Xg is lexical, from *ter que* to *dever*, and Xf
the past imperfect. -/
inductive Form where
  | temQue
  | deve
  | tinhaQue
  | devia
  deriving DecidableEq, Repr, Fintype

/-- (135): the vertex a form occupies. -/
def Form.vertex : Form → Vertex
  | .temQue => ⟨false, false⟩
  | .deve => ⟨false, true⟩
  | .tinhaQue => ⟨true, false⟩
  | .devia => ⟨true, true⟩

/-- The fragment entry of a form. -/
def Form.item : Form → ModalItem
  | .temQue => Portuguese.Modals.terQue
  | .deve => Portuguese.Modals.dever
  | .tinhaQue => Portuguese.Modals.tinhaQue
  | .devia => Portuguese.Modals.devia

/-- (83), (135): a form's force in the fragment is weak necessity exactly when its ordering
source is X-marked; X-marking the modal base leaves the force. -/
theorem force_of_vertex : ∀ φ : Form, ∀ ff ∈ φ.item.meaning,
    ff.force = if φ.vertex.xg then .weakNecessity else .necessity := by
  decide

/-! ### The consistency paradigm of §2 -/

/-- The three forces. -/
inductive Force where
  | pos
  | wn
  | sn
  deriving DecidableEq, Repr

/-- A conjunct: a modal of some force over the prejacent or its negation, possibly negated. -/
structure Conjunct where
  force : Force
  negModal : Bool
  negPrejacent : Bool
  deriving DecidableEq, Repr

/-- The conjunct's truth at `w`, `p` the proposition weak necessity's ordering revision
targets and `q` the prejacent. -/
def Conjunct.holds (c : Conjunct) (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop)
    (w : W) : Prop :=
  let q' : W → Prop := if c.negPrejacent then (λ v => ¬ q v) else q
  let m : Prop := match c.force with
    | .pos => possibility f g q' w
    | .wn => snXg f g p q' w
    | .sn => strongNecessity f g q' w
  if c.negModal then ¬ m else m

/-- A conjunction of two modal claims about one prejacent. -/
structure Pattern where
  first : Conjunct
  second : Conjunct
  deriving DecidableEq, Repr

/-- The conjunction is contradictory as the conclusion of a deliberation: false in every model
with nonempty best worlds. -/
def Pattern.Contradictory (pat : Pattern) : Prop :=
  ∀ (W : Type) (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop) (w : W),
    (bestWorlds f g w).Nonempty →
      ¬ (pat.first.holds f g p q w ∧ pat.second.holds f g p q w)

/-- The conjunction has a model. -/
def Pattern.Consistent (pat : Pattern) : Prop :=
  ∃ (W : Type) (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop) (w : W),
    (bestWorlds f g w).Nonempty ∧ pat.first.holds f g p q w ∧ pat.second.holds f g p q w

/-- (16), (19), (21), (24), (25), (32a): the contradictory conjunctions. -/
theorem contradictory_sn_posNeg :
    Pattern.Contradictory ⟨⟨.sn, false, false⟩, ⟨.pos, false, true⟩⟩ := by
  rintro _ f g p q w - ⟨h₁, ⟨u, hu, hnq⟩⟩
  exact hnq (h₁ u hu)

theorem contradictory_sn_notWn :
    Pattern.Contradictory ⟨⟨.sn, false, false⟩, ⟨.wn, true, false⟩⟩ := by
  rintro _ f g p q w - ⟨h₁, h₂⟩
  exact h₂ (sn_entails_snXg f g p q w h₁)

theorem contradictory_wn_notPos :
    Pattern.Contradictory ⟨⟨.wn, false, false⟩, ⟨.pos, true, false⟩⟩ := by
  rintro _ f g p q w hne ⟨h₁, h₂⟩
  exact h₂ (snXg_entails_possibility f g p q w hne h₁)

theorem contradictory_wn_wnNeg :
    Pattern.Contradictory ⟨⟨.wn, false, false⟩, ⟨.wn, false, true⟩⟩ :=
  λ _ f g p q w hne h => not_snXg_and_snXg_neg f g p q w hne h

theorem contradictory_sn_snNeg :
    Pattern.Contradictory ⟨⟨.sn, false, false⟩, ⟨.sn, false, true⟩⟩ := by
  rintro _ f g p q w ⟨u, hu⟩ ⟨h₁, h₂⟩
  exact h₂ u hu (h₁ u hu)

theorem contradictory_sn_notSn :
    Pattern.Contradictory ⟨⟨.sn, false, false⟩, ⟨.sn, true, false⟩⟩ :=
  λ _ _ _ _ _ _ _ h => h.2 h.1

/-- The two-world model of the acceptable conjunctions: every world accessible and best, the
weak necessity's ordering revision favoring `p`. -/
theorem consistent_of_bool (pat : Pattern) (p q : Bool → Prop)
    (h₁ : pat.first.holds (W := Bool) emptyBackground emptyBackground p q true)
    (h₂ : pat.second.holds (W := Bool) emptyBackground emptyBackground p q true) :
    pat.Consistent :=
  ⟨Bool, emptyBackground, emptyBackground, p, q, true,
    by rw [bestWorlds_empty_empty]; exact Set.univ_nonempty, h₁, h₂⟩

theorem snXg_bool (b : Bool) (q : Bool → Prop) (hq : q b) :
    snXg (W := Bool) emptyBackground emptyBackground (· = b) q true := by
  rw [snXg_iff_weakNecessity]
  intro w' hw'
  rw [bestWorlds_empty_empty, bestAmong_univ_eq] at hw'
  rw [hw']; exact hq

theorem not_snXg_bool (b : Bool) (q : Bool → Prop) (hq : ¬ q b) :
    ¬ snXg (W := Bool) emptyBackground emptyBackground (· = b) q true := by
  rw [snXg_iff_weakNecessity]
  intro h
  refine hq (h b ?_)
  rw [bestWorlds_empty_empty, bestAmong_univ_eq]; rfl

theorem possibility_bool (b : Bool) (q : Bool → Prop) (hq : q b) :
    possibility (W := Bool) emptyBackground emptyBackground q true :=
  (possibility_iff_any _ _ _ _).mpr ⟨b, by rw [bestWorlds_empty_empty]; exact Set.mem_univ _, hq⟩

theorem not_sn_bool (b : Bool) (q : Bool → Prop) (hq : ¬ q b) :
    ¬ strongNecessity (W := Bool) emptyBackground emptyBackground q true := λ h =>
  hq ((necessity_iff_all _ _ _ _).mp h b (by rw [bestWorlds_empty_empty]; exact Set.mem_univ _))

/-- (17), (18), (20), (22), (30a), (32b): the acceptable conjunctions. -/
theorem consistent_wn_posNeg : Pattern.Consistent ⟨⟨.wn, false, false⟩, ⟨.pos, false, true⟩⟩ :=
  consistent_of_bool _ (· = true) (· = true) (snXg_bool true _ rfl)
    (possibility_bool false _ Bool.false_ne_true)

theorem consistent_pos_posNeg : Pattern.Consistent ⟨⟨.pos, false, false⟩, ⟨.pos, false, true⟩⟩ :=
  consistent_of_bool _ (· = true) (· = true) (possibility_bool true _ rfl)
    (possibility_bool false _ Bool.false_ne_true)

theorem consistent_wn_notSn : Pattern.Consistent ⟨⟨.wn, false, false⟩, ⟨.sn, true, false⟩⟩ :=
  consistent_of_bool _ (· = true) (· = true) (snXg_bool true _ rfl)
    (not_sn_bool false _ Bool.false_ne_true)

theorem consistent_pos_notWn : Pattern.Consistent ⟨⟨.pos, false, false⟩, ⟨.wn, true, false⟩⟩ :=
  consistent_of_bool _ (· = false) (· = true) (possibility_bool true _ rfl)
    (not_snXg_bool false _ Bool.false_ne_true)

/-- (30b): a weak necessity reinforced by the strong one, in a model where every best world
is a prejacent-world. -/
theorem consistent_wn_sn : Pattern.Consistent ⟨⟨.wn, false, false⟩, ⟨.sn, false, false⟩⟩ := by
  have hbest : bestWorlds (W := Bool) (λ _ => [(· = true)]) emptyBackground true = {true} := by
    rw [empty_ordering_emptyBackground]
    ext v
    simp [accessibleWorlds, propIntersection]
  have hsn : strongNecessity (W := Bool) (λ _ => [(· = true)]) emptyBackground (· = true) true := by
    rw [strongNecessity, necessity_iff_all, hbest]
    intro w' hw'
    exact hw'
  exact ⟨Bool, _, _, (· = true), (· = true), true, by rw [hbest]; exact ⟨true, rfl⟩,
    sn_entails_snXg _ _ _ _ _ hsn, hsn⟩

/-- A row: the conjunction and the paper's judgment. -/
structure Row where
  pattern : Pattern
  judgment : Features.Judgment
  deriving DecidableEq, Repr

def conjunctTable : List (String × Conjunct) :=
  [("pos_p", ⟨.pos, false, false⟩), ("wn_p", ⟨.wn, false, false⟩), ("sn_p", ⟨.sn, false, false⟩),
   ("pos_notp", ⟨.pos, false, true⟩), ("wn_notp", ⟨.wn, false, true⟩),
   ("sn_notp", ⟨.sn, false, true⟩), ("not_pos_p", ⟨.pos, true, false⟩),
   ("not_wn_p", ⟨.wn, true, false⟩), ("not_sn_p", ⟨.sn, true, false⟩)]

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let first ← ex.parse? "first" conjunctTable
  let second ← ex.parse? "second" conjunctTable
  pure ⟨⟨first, second⟩, ex.judgment⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The paper's judgment is what the semantics predicts: a `#` conjunction is contradictory
and an acceptable one consistent. -/
def Row.Predicted (r : Row) : Prop :=
  (r.judgment = .unacceptable → r.pattern.Contradictory) ∧
    (r.judgment ≠ .unacceptable → r.pattern.Consistent)

theorem rows_eq : rows =
    [⟨⟨⟨.sn, false, false⟩, ⟨.pos, false, true⟩⟩, .unacceptable⟩,
     ⟨⟨⟨.wn, false, false⟩, ⟨.pos, false, true⟩⟩, .acceptable⟩,
     ⟨⟨⟨.pos, false, false⟩, ⟨.pos, false, true⟩⟩, .acceptable⟩,
     ⟨⟨⟨.sn, false, false⟩, ⟨.wn, true, false⟩⟩, .unacceptable⟩,
     ⟨⟨⟨.wn, false, false⟩, ⟨.sn, true, false⟩⟩, .acceptable⟩,
     ⟨⟨⟨.wn, false, false⟩, ⟨.pos, true, false⟩⟩, .unacceptable⟩,
     ⟨⟨⟨.pos, false, false⟩, ⟨.wn, true, false⟩⟩, .acceptable⟩,
     ⟨⟨⟨.wn, false, false⟩, ⟨.wn, false, true⟩⟩, .unacceptable⟩,
     ⟨⟨⟨.sn, false, false⟩, ⟨.sn, false, true⟩⟩, .unacceptable⟩,
     ⟨⟨⟨.wn, false, false⟩, ⟨.sn, true, false⟩⟩, .acceptable⟩,
     ⟨⟨⟨.wn, false, false⟩, ⟨.sn, false, false⟩⟩, .acceptable⟩,
     ⟨⟨⟨.sn, false, false⟩, ⟨.sn, true, false⟩⟩, .unacceptable⟩,
     ⟨⟨⟨.wn, false, false⟩, ⟨.sn, true, false⟩⟩, .acceptable⟩] := by
  decide

/-- Every judgment of (16)–(25), (30), (32) is predicted. -/
theorem rows_predicted : ∀ r ∈ rows, r.Predicted := by
  rw [rows_eq]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨λ h => ?_, λ h => ?_⟩ <;> first
    | exact absurd h (by decide)
    | exact absurd rfl h
    | exact contradictory_sn_posNeg
    | exact consistent_wn_posNeg
    | exact consistent_pos_posNeg
    | exact contradictory_sn_notWn
    | exact consistent_wn_notSn
    | exact contradictory_wn_notPos
    | exact consistent_pos_notWn
    | exact contradictory_wn_wnNeg
    | exact contradictory_sn_snNeg
    | exact consistent_wn_sn
    | exact contradictory_sn_notSn

/-! ### (80)–(81): suspending the knowledge that Peter is not in his office -/

/-- A world of the dialogues: whether Peter is in his office and whether the day is a
holiday. -/
@[ext]
structure Day where
  office : Bool
  holiday : Bool
  deriving DecidableEq, Repr

instance : Fintype Day :=
  ⟨{⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩},
    λ ⟨o, h⟩ => by cases o <;> cases h <;> simp⟩

/-- Similarity by agreement on each coordinate. -/
def sim : Similarity Day := λ w => [λ v => v.office = w.office, λ v => v.holiday = w.holiday]

theorem sim_isCentered : sim.IsCentered := by
  intro w
  ext v
  simp only [propIntersection, sim, Set.mem_ofPred_eq, Set.mem_singleton_iff, List.forall_mem_cons,
    List.mem_nil_iff, false_implies, implies_true, and_true, Day.ext_iff]

/-- Normality: people are in the office on workdays and not on holidays. -/
def normal : OrderingSource Day :=
  λ _ => [λ v => v.holiday = true → v.office = false, λ v => v.holiday = false → v.office = true]

/-- The prejacent: Peter is in his office. -/
def office (v : Day) : Prop := v.office = true

/-- (81): A has checked that Peter is not in his office; the day is taken for a workday. -/
def f81 : ModalBase Day := λ _ => [λ v => v.office = false, λ v => v.holiday = false]

/-- (80): A has said it is a holiday, and Peter is not in his office. -/
def f80 : ModalBase Day := λ _ => [λ v => v.office = false, λ v => v.holiday = true]

/-- (81): only the world where Peter is not in his office on a workday is accessible. -/
theorem accessible_f81 : accessibleWorlds f81 ⟨false, false⟩ = {⟨false, false⟩} := by
  ext v
  simp only [accessibleWorlds, propIntersection, f81, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true, Day.ext_iff]

/-- Suspending the knowledge that he is not there adds the most similar office-world: the
workday one. -/
theorem revise_f81 :
    accessibleWorlds (revise sim f81 office) ⟨false, false⟩ = {⟨false, false⟩, ⟨true, false⟩} := by
  rw [accessibleWorlds_revise, accessible_f81]
  ext v
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff, Set.mem_ofPred_eq,
    exists_eq_left, bestAmong, atLeastAsGoodAs_iff, sim, office, List.forall_mem_cons,
    List.mem_nil_iff, false_implies, implies_true, and_true]
  obtain ⟨o, h⟩ := v
  cases o <;> cases h <;> decide

/-- Normality then prefers the office-world. -/
theorem best_revise_f81 :
    bestAmong ({⟨false, false⟩, ⟨true, false⟩} : Set Day) (normal ⟨false, false⟩) =
      {⟨true, false⟩} := by
  ext v
  simp only [bestAmong, atLeastAsGoodAs_iff, normal, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true]
  obtain ⟨o, h⟩ := v
  cases o <;> cases h <;> decide

/-- (81): suspending the knowledge that Peter is not in his office reinstates the bias: the
marked necessity is true although the unmarked one is false. -/
theorem xMarked_81 :
    snXf sim f81 normal office ⟨false, false⟩ ∧
      ¬ strongNecessity f81 normal office ⟨false, false⟩ := by
  constructor
  · rw [snXf, necessity_iff_all, bestWorlds_eq_bestAmong, revise_f81, best_revise_f81]
    intro w' hw'
    rw [Set.mem_singleton_iff.mp hw']; rfl
  · rw [strongNecessity, necessity_iff_all, bestWorlds_eq_bestAmong, accessible_f81]
    intro h
    exact Bool.false_ne_true (h ⟨false, false⟩ ⟨rfl, λ v hv _ => by
      rw [Set.mem_singleton_iff.mp hv]; exact ordering_reflexive _ _⟩)

/-- (80): on the holiday the revision adds the holiday office-world. -/
theorem revise_f80 :
    accessibleWorlds (revise sim f80 office) ⟨false, true⟩ = {⟨false, true⟩, ⟨true, true⟩} := by
  have hacc : accessibleWorlds f80 ⟨false, true⟩ = {⟨false, true⟩} := by
    ext v
    simp only [accessibleWorlds, propIntersection, f80, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true, Day.ext_iff]
  rw [accessibleWorlds_revise, hacc]
  ext v
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff, Set.mem_ofPred_eq,
    exists_eq_left, bestAmong, atLeastAsGoodAs_iff, sim, office, List.forall_mem_cons,
    List.mem_nil_iff, false_implies, implies_true, and_true]
  obtain ⟨o, h⟩ := v
  cases o <;> cases h <;> decide

/-- Normality on a holiday prefers the world where he is not in his office. -/
theorem best_revise_f80 :
    bestAmong ({⟨false, true⟩, ⟨true, true⟩} : Set Day) (normal ⟨false, true⟩) =
      {⟨false, true⟩} := by
  ext v
  simp only [bestAmong, atLeastAsGoodAs_iff, normal, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true]
  obtain ⟨o, h⟩ := v
  cases o <;> cases h <;> decide

/-- (80): the holiday blocks the inference even after suspending that knowledge. -/
theorem not_xMarked_80 : ¬ snXf sim f80 normal office ⟨false, true⟩ := by
  rw [snXf, necessity_iff_all, bestWorlds_eq_bestAmong, revise_f80, best_revise_f80]
  intro h
  exact Bool.false_ne_true (h ⟨false, true⟩ rfl)

end Ferreira2023
