module

public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Semantics.Questions.Partition.Inquisitive
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Data.Examples.TheilerRoelofsenAloni2018

/-!
# Theiler, Roelofsen and Aloni (2018): A Uniform Semantics for Declarative and Interrogative Complements

This file formalizes [theiler-etal-2018]'s uniform semantics for the complements of responsive
verbs such as *know*, verbs that embed declaratives and interrogatives alike. Both kinds of
nucleus denote an inquisitive sentence meaning, a `Question`, and the embedding operator turns a
nucleus into the function from worlds to its truthful resolutions there: the consistent
resolutions that entail no answer or partial answer false at the world, Definitions 3 and 4,
with the complete variant also entailing every true alternative, Definitions 5 and 6. A verb
then relates the subject's information state to the truthful resolutions: *know* requires the
state to be one of them at the world of evaluation, (33); its internal interpretation adds
resolution introspection, that the state is a truthful resolution at every world it contains,
(35); *be certain* keeps only the introspective conjunct, (50), and *be right*, *be wrong*,
*be surprised* and *care* are built from the same parts, (59), (64), (68) and (72).

The false-answer sensitivity of *know* is the no-false-alternatives condition,
`not_know_of_subset`, and its absence for *be certain* is that in the subject's own worlds
her state entails no false partial answer, `certain_E_iff`. For declarative nuclei the truthful
resolutions are the nonempty subsets of the proposition at the worlds where it is true,
`isTruthful_ofSet_iff`, so *know* is factive and veridical, `know_ofSet_iff`, and *be certain*
is not, `certain_ofSet_iff`. Fact 1 holds in general: the mention-some reading and, on
partition nuclei, the strongly exhaustive reading do not distinguish the internal from the
external verb, `knowInt_E_iff`, `Ecmp_eq_E_of_isPartition`. Fact 2 is that the internal verb
does not distinguish the intermediate exhaustive reading of a wh-nucleus from its strongly
exhaustive one, `knowInt_Ecmp_nonExh_iff`. Section 6's constraints are Facts 5 and 6: a
c-distributive verb veridical for declaratives is veridical for interrogatives,
`IntVeridical.of_cDistributive`, and one with the choice property veridical for interrogatives
is veridical for declaratives, `DeclVeridical.of_choice`; *know* is c-distributive,
`cDistributive_know`.

## Implementation notes

Verb meanings are predicates on worlds; the paper's sentence meanings are their principal
ideals, the non-inquisitive contents `Question.ofSet`. Presuppositional entries are
`Presupposition.PartialProp`s. Worlds are finite where the paper assumes so, footnote 7, which
gives every resolution an alternative above it. The wh-nucleus of Fact 2 is a family of
answers, one per individual, with the non-exhaustive reading resolved by an answer or by there
being none and the exhaustive reading the partition by the set of true answers; the answers are
assumed nonempty and mutually non-entailing, the independence of the paper's diagrams.
C-distributivity is stated for partition nuclei, whose decomposition is the family of their
cells, which is all Facts 5 and 6 use. The examples are the rows of
`Data.Examples.TheilerRoelofsenAloni2018`.

## References

* [theiler-etal-2018]
* [groenendijk-stokhof-1984]
* [george-2011]
* [spector-egre-2015]
* [uegaki-2015]
* [cremers-chemla-2016]
* [klinedinst-rothschild-2011]
* [elliott-etal-2017]
* [ciardelli-roelofsen-2015]
-/

@[expose] public section

namespace TheilerRoelofsenAloni2018

open Question Presupposition

variable {W X : Type*}

/-! ### Truthful resolutions (section 3.3) -/

section Resolutions

/-- Definition 3: the unions of alternatives of a nucleus meaning, its answers and partial
answers. -/
def altUnion (P : Question W) : Set (Set W) := Set.sUnion '' 𝒫 alt P

variable {P : Question W} {w v : W} {p q : Set W}

theorem mem_altUnion : q ∈ altUnion P ↔ ∃ S ⊆ alt P, ⋃₀ S = q := by
  simp [altUnion]

theorem mem_altUnion_of_mem_alt (h : q ∈ alt P) : q ∈ altUnion P :=
  ⟨{q}, Set.singleton_subset_iff.2 h, Set.sUnion_singleton q⟩

/-- A resolution provides false information at a world if it entails an answer or partial
answer false there. -/
def ProvidesFalse (P : Question W) (w : W) (p : Set W) : Prop :=
  ∃ q ∈ altUnion P, w ∉ q ∧ p ⊆ q

/-- Definition 4: a truthful resolution is a consistent resolution providing no false
information, the no-false-alternatives condition. -/
structure IsTruthful (P : Question W) (w : W) (p : Set W) : Prop where
  mem : p ∈ P
  nonempty : p.Nonempty
  nfa : ¬ ProvidesFalse P w p

/-- Definition 5: a complete truthful resolution also entails every true alternative. -/
structure IsCompleteTruthful (P : Question W) (w : W) (p : Set W) : Prop
    extends IsTruthful P w p where
  complete : ∀ q ∈ alt P, w ∈ q → p ⊆ q

/-- Definition 6: the non-complete embedding operator. -/
def E (P : Question W) (w : W) : Set (Set W) := {p | IsTruthful P w p}

/-- Definition 6: the complete embedding operator. -/
def Ecmp (P : Question W) (w : W) : Set (Set W) := {p | IsCompleteTruthful P w p}

theorem mem_E : p ∈ E P w ↔ IsTruthful P w p := Iff.rfl

theorem mem_Ecmp : p ∈ Ecmp P w ↔ IsCompleteTruthful P w p := Iff.rfl

theorem Ecmp_subset_E : Ecmp P w ⊆ E P w := λ _ h => h.toIsTruthful

/-- A truthful resolution is truthful at every world it contains: there it entails nothing
false. -/
theorem IsTruthful.of_mem (h : IsTruthful P w p) (hv : v ∈ p) : IsTruthful P v p :=
  ⟨h.mem, h.nonempty, λ ⟨_, _, hvq, hpq⟩ => hvq (hpq hv)⟩

/-- An alternative entailed by a truthful resolution is true. -/
theorem IsTruthful.mem_of_subset (h : IsTruthful P w p) (hq : q ∈ alt P) (hpq : p ⊆ q) :
    w ∈ q :=
  by_contra λ hw => h.nfa ⟨q, mem_altUnion_of_mem_alt hq, hw, hpq⟩

/-! ### Declarative complements (section 3.6) -/

theorem altUnion_ofSet (q : Set W) : altUnion (ofSet q) = {∅, q} := by
  simp [altUnion, alt_ofSet, Set.powerset_singleton, Set.image_insert_eq, Set.image_singleton]

/-- At a world where a declarative nucleus is true its truthful resolutions are the nonempty
propositions entailing it; where it is false there are none. -/
theorem isTruthful_ofSet_iff : IsTruthful (ofSet q) w p ↔ w ∈ q ∧ p ⊆ q ∧ p.Nonempty := by
  refine ⟨λ h => ⟨h.mem_of_subset (by simp [alt_ofSet]) h.mem, h.mem, h.nonempty⟩, ?_⟩
  rintro ⟨hw, hpq, hne⟩
  refine ⟨hpq, hne, ?_⟩
  rintro ⟨r, hr, hwr, hpr⟩
  rw [altUnion_ofSet] at hr
  rcases hr with rfl | rfl
  · exact hne.ne_empty (Set.subset_empty_iff.1 hpr)
  · exact hwr hw

/-- Every truthful resolution of a declarative complement is complete. -/
theorem isCompleteTruthful_ofSet_iff :
    IsCompleteTruthful (ofSet q) w p ↔ IsTruthful (ofSet q) w p :=
  ⟨λ h => h.toIsTruthful, λ h => ⟨h, λ r hr _ => by
    rw [alt_ofSet, Set.mem_singleton_iff] at hr
    exact hr ▸ h.mem⟩⟩

/-- The truthful resolutions of a declarative complement are downward closed among nonempty
propositions. -/
theorem isTruthful_ofSet_of_subset (h : IsTruthful (ofSet q) w p) {r : Set W} (hr : r ⊆ p)
    (hne : r.Nonempty) : IsTruthful (ofSet q) w r :=
  isTruthful_ofSet_iff.2 ⟨(isTruthful_ofSet_iff.1 h).1, hr.trans h.mem, hne⟩

/-! ### Partition nuclei -/

variable [Finite W]

/-- Over finitely many worlds a truthful resolution entails a true alternative. -/
theorem IsTruthful.exists_alt (h : IsTruthful P w p) : ∃ c ∈ alt P, w ∈ c ∧ p ⊆ c :=
  let ⟨c, hc, hpc⟩ := exists_alt_above P (Set.toFinite _) h.mem
  ⟨c, hc, h.mem_of_subset hc hpc, hpc⟩

/-- A nucleus has a truthful resolution at a world exactly when it is true there. -/
theorem E_nonempty_iff : (E P w).Nonempty ↔ w ∈ info P := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨c, hc, hwc, -⟩ := hp.exists_alt
    exact ⟨c, mem_of_mem_alt hc, hwc⟩
  · rintro ⟨p, hp, hwp⟩
    refine ⟨{w}, P.downward_closed p hp _ (Set.singleton_subset_iff.2 hwp),
      Set.singleton_nonempty w, ?_⟩
    rintro ⟨_, _, hwq, hq⟩
    exact hwq (hq rfl)

/-- On a partition nucleus, whose alternatives are the cells of the strongly exhaustive
reading, every truthful resolution is complete. -/
theorem Ecmp_eq_E_of_isPartition (h : P.IsPartition) : Ecmp P = E P := by
  funext w
  refine Set.Subset.antisymm Ecmp_subset_E λ p hp => ⟨hp, λ c hc hwc => ?_⟩
  obtain ⟨c', hc', hwc', hpc'⟩ := hp.exists_alt
  obtain ⟨b, -, hb⟩ := h.2 w
  exact ((hb c ⟨hc, hwc⟩).trans (hb c' ⟨hc', hwc'⟩).symm) ▸ hpc'

end Resolutions

/-! ### Responsive verbs (sections 3.4, 4.2 and 5) -/

section Verbs

variable (dox : X → W → Set W) (f : W → Set (Set W)) (x : X)

/-- *know* on its external interpretation, (33): the subject's information state is a truthful
resolution at the world of evaluation. -/
def know (w : W) : Prop := dox x w ∈ f w

/-- *know* on its internal interpretation, (35): the subject's state is a truthful resolution
at the world of evaluation and, by resolution introspection, at every world she considers
possible. -/
def knowInt (w : W) : Prop := dox x w ∈ f w ∧ ∀ v ∈ dox x w, dox x w ∈ f v

/-- *be certain*, (50): the subject's state is a truthful resolution at every world she
considers possible. -/
def certain (w : W) : Prop := ∀ v ∈ dox x w, dox x w ∈ f v

/-- *know* with its factivity presupposition, (43): the nucleus is true. -/
def knowFactive : PartialProp W where
  presup w := (f w).Nonempty
  assertion := know dox f x

/-- *be right*, (59): presupposes *be certain* and asserts *know*. -/
def right : PartialProp W where
  presup := certain dox f x
  assertion := know dox f x

/-- *be wrong*, (64): presupposes that the state is a truthful resolution at some world the
subject considers possible and asserts that it is none at the world of evaluation. -/
def wrong : PartialProp W where
  presup w := ∃ v ∈ dox x w, dox x w ∈ f v
  assertion w := dox x w ∉ f w

/-- *be surprised*, (68): some maximal truthful resolution at the world of evaluation is
believed but was not expected. -/
def surprised (exp : X → W → Set W) (w : W) : Prop :=
  ∃ q, Maximal (· ∈ f w) q ∧ dox x w ⊆ q ∧ ¬ exp x w ⊆ q

/-- *care*, (72): presupposes truthful resolutions at the world of evaluation and at every
world the subject considers possible, and asserts that some maximal truthful resolution at
some world is desired or undesired. -/
def care (bou : X → W → Set W) : PartialProp W where
  presup w := (f w).Nonempty ∧ ∀ v ∈ dox x w, (f v).Nonempty
  assertion w := ∃ v q, Maximal (· ∈ f v) q ∧ (bou x w ⊆ q ∨ Disjoint (bou x w) q)

variable {dox f x} {P : Question W} {q : Set W} {w : W}

/-- The internal *know* is *be certain* together with the assertion of *be right*
(section 5.3). -/
theorem knowInt_iff : knowInt dox f x w ↔ certain dox f x w ∧ know dox f x w := and_comm

/-- *know* is veridical and factive for declaratives, (39) and (41): the nucleus is true and
the subject believes it. -/
theorem know_ofSet_iff :
    know dox (E (ofSet q)) x w ↔ w ∈ q ∧ dox x w ⊆ q ∧ (dox x w).Nonempty :=
  isTruthful_ofSet_iff

/-- *be certain* is not veridical, (40): a consistent subject is certain of a declarative
exactly when she believes it. -/
theorem certain_ofSet_iff (hne : (dox x w).Nonempty) :
    certain dox (E (ofSet q)) x w ↔ dox x w ⊆ q :=
  ⟨λ h => (isTruthful_ofSet_iff.1 (h _ hne.some_mem)).2.1,
    λ hs _ hv => isTruthful_ofSet_iff.2 ⟨hs hv, hs, hne⟩⟩

/-- False-answer sensitivity, (13b) and (25): a subject believing an answer or partial answer
false at the world of evaluation does not know the question. -/
theorem not_know_of_subset (hq : q ∈ altUnion P) (hw : w ∉ q) (h : dox x w ⊆ q) :
    ¬ know dox (E P) x w :=
  λ hk => hk.nfa ⟨q, hq, hw, h⟩

/-- *be certain* shows no false-answer sensitivity effects, (15) and (53): a consistent
subject is certain of a question exactly when her state resolves it. -/
theorem certain_E_iff (hne : (dox x w).Nonempty) : certain dox (E P) x w ↔ dox x w ∈ P :=
  ⟨λ h => (h _ hne.some_mem).mem, λ hm _ hv => ⟨hm, hne, λ ⟨_, _, hvq, hpq⟩ => hvq (hpq hv)⟩⟩

/-- Fact 1 for mention-some readings: resolution introspection is automatic, so the internal
and external interpretations coincide. -/
theorem knowInt_E_iff : knowInt dox (E P) x w ↔ know dox (E P) x w :=
  ⟨And.left, λ h => ⟨h, λ _ hv => h.of_mem hv⟩⟩

/-- Fact 1 for strongly exhaustive readings: on a partition nucleus the complete operator is
the non-complete one. -/
theorem knowInt_Ecmp_iff_of_isPartition [Finite W] (h : P.IsPartition) :
    knowInt dox (Ecmp P) x w ↔ know dox (Ecmp P) x w := by
  rw [Ecmp_eq_E_of_isPartition h, knowInt_E_iff]

/-- The factivity presupposition of *know* with a declarative complement, (41). -/
theorem knowFactive_presup_ofSet_iff [Finite W] :
    (knowFactive dox (E (ofSet q)) x).presup w ↔ w ∈ q := by
  show (E (ofSet q) w).Nonempty ↔ w ∈ q
  rw [E_nonempty_iff, info_ofSet]

/-- With an interrogative complement, a partition nucleus, the presupposition of *know* is
trivial. -/
theorem knowFactive_presup_of_isPartition [Finite W] (h : P.IsPartition) :
    (knowFactive dox (E P) x).presup w := by
  show (E P w).Nonempty
  rw [E_nonempty_iff, h.info_eq_univ]
  trivial

/-- The presupposition of *care* with a declarative complement, (69a): the subject knows the
nucleus. -/
theorem care_presup_ofSet_iff [Finite W] (bou : X → W → Set W) :
    (care dox (E (ofSet q)) x bou).presup w ↔ w ∈ q ∧ dox x w ⊆ q := by
  simp only [care, E_nonempty_iff, info_ofSet, Set.subset_def]

/-- *be surprised* is veridical, (65): its maximal truthful resolution witnesses the truth of
the nucleus. -/
theorem mem_info_of_surprised [Finite W] {exp : X → W → Set W}
    (h : surprised dox (E P) x exp w) : w ∈ info P :=
  let ⟨_, hq, _, _⟩ := h
  E_nonempty_iff.1 ⟨_, hq.prop⟩

end Verbs

/-! ### Intermediate and strongly exhaustive readings (section 4, Fact 2) -/

section Exhaustivity

variable {ι : Type*} (a : ι → Set W)

/-- The individuals with the property at a world. -/
def ext (w : W) : Set ι := {d | w ∈ a d}

/-- The answer that no individual has the property. -/
def nobody : Set W := ⋂ d, (a d)ᶜ

/-- The non-exhaustive reading of a wh-nucleus, Figure 5(b): resolved by establishing of some
individual that it has the property, or that none has. -/
def nonExh : Question W := which Set.univ (Option.elim · (nobody a) a)

/-- The exhaustive reading, Figure 5(a): resolved by establishing exactly which individuals
have the property. -/
def exh : Question W := fromSetoid (Setoid.ker (ext a))

/-- The cell of the exhaustive reading containing a world. -/
def cell (w : W) : Set W := {v | ext a v = ext a w}

variable {a} {w v : W} {D : Set W}

theorem mem_cell_iff : v ∈ cell a w ↔ ∀ d, v ∈ a d ↔ w ∈ a d := by
  simp [cell, ext, Set.ext_iff]

theorem mem_cell_self : w ∈ cell a w := rfl

theorem cell_eq_of_mem (hv : v ∈ cell a w) : cell a v = cell a w := by
  ext u
  simp only [cell, Set.mem_ofPred_eq] at hv ⊢
  rw [hv]

theorem cell_mem_classes : cell a w ∈ (Setoid.ker (ext a)).classes :=
  Setoid.mem_classes _ w

theorem mem_nonExh : D ∈ nonExh a ↔ D = ∅ ∨ D ⊆ nobody a ∨ ∃ d, D ⊆ a d := by
  rw [nonExh, mem_which]
  simp [Option.exists]

/-- Under independence the alternatives of the non-exhaustive reading are the answers and
the answer that none holds. -/
theorem alt_nonExh (hne : ∀ d, (a d).Nonempty) (hN : (nobody a).Nonempty)
    (hind : ∀ d d', a d ⊆ a d' → d = d') :
    alt (nonExh a) = Set.range (Option.elim · (nobody a) a) := by
  rw [nonExh, alt_which_of_forall_subset_eq Set.univ_nonempty, Set.image_univ]
  · rintro (_ | d) -
    · exact hN
    · exact hne d
  · rintro (_ | d) - (_ | d') - h
    · rfl
    · obtain ⟨u, hu⟩ := hN
      have := h hu
      simp only [nobody, Set.mem_iInter, Set.mem_compl_iff] at hu
      exact absurd this (hu d')
    · obtain ⟨u, hu⟩ := hne d
      have := h hu
      simp only [Option.elim, nobody, Set.mem_iInter, Set.mem_compl_iff] at this
      exact absurd hu (this d)
    · exact congrArg _ (hind d d' h)

theorem subset_cell_of_Ecmp_nonExh (hne : ∀ d, (a d).Nonempty) (hN : (nobody a).Nonempty)
    (hind : ∀ d d', a d ⊆ a d' → d = d') (hw : D ∈ Ecmp (nonExh a) w)
    (h : ∀ v ∈ D, D ∈ Ecmp (nonExh a) v) : D ⊆ cell a w := by
  intro v hv
  rw [mem_cell_iff]
  intro d
  have hd : a d ∈ alt (nonExh a) := by
    rw [alt_nonExh hne hN hind]; exact ⟨some d, rfl⟩
  exact ⟨λ hvd => hw.mem_of_subset hd ((h v hv).complete _ hd hvd),
    λ hwd => hw.complete _ hd hwd hv⟩

theorem mem_Ecmp_nonExh_of_subset_cell (hne : ∀ d, (a d).Nonempty) (hN : (nobody a).Nonempty)
    (hind : ∀ d d', a d ⊆ a d' → d = d') (hsub : D ⊆ cell a w) (hne' : D.Nonempty) :
    D ∈ Ecmp (nonExh a) w := by
  have hcell : ∀ d, w ∈ a d → D ⊆ a d := λ d hwd u hu => (mem_cell_iff.1 (hsub hu) d).2 hwd
  have hnob : w ∈ nobody a → D ⊆ nobody a := λ hw u hu => by
    simp only [nobody, Set.mem_iInter, Set.mem_compl_iff] at hw ⊢
    exact λ d hud => hw d ((mem_cell_iff.1 (hsub hu) d).1 hud)
  refine ⟨⟨mem_nonExh.2 ?_, hne', ?_⟩, ?_⟩
  · by_cases hw : ∃ d, w ∈ a d
    · obtain ⟨d, hwd⟩ := hw
      exact Or.inr (Or.inr ⟨d, hcell d hwd⟩)
    · exact Or.inr (Or.inl (hnob (by simpa [nobody] using hw)))
  · rintro ⟨U, hU, hwU, hDU⟩
    obtain ⟨S, hS, rfl⟩ := mem_altUnion.1 hU
    obtain ⟨u, hu⟩ := hne'
    obtain ⟨m, hmS, hum⟩ := hDU hu
    rw [alt_nonExh hne hN hind] at hS
    obtain ⟨o, rfl⟩ := hS hmS
    refine hwU ⟨_, hmS, ?_⟩
    rcases o with _ | d
    · simp only [Option.elim, nobody, Set.mem_iInter, Set.mem_compl_iff] at hum ⊢
      exact λ d hwd => hum d ((mem_cell_iff.1 (hsub hu) d).2 hwd)
    · exact (mem_cell_iff.1 (hsub hu) d).1 hum
  · intro c hc hwc
    rw [alt_nonExh hne hN hind] at hc
    obtain ⟨o, rfl⟩ := hc
    rcases o with _ | d
    · exact hnob hwc
    · exact hcell d hwc

variable [Nonempty W]

theorem mem_E_exh_of_subset_cell (hsub : D ⊆ cell a w) (hne' : D.Nonempty) :
    D ∈ E (exh a) w := by
  refine ⟨Or.inr ⟨_, cell_mem_classes, hsub⟩, hne', ?_⟩
  rintro ⟨U, hU, hwU, hDU⟩
  obtain ⟨S, hS, rfl⟩ := mem_altUnion.1 hU
  obtain ⟨u, hu⟩ := hne'
  obtain ⟨c, hcS, huc⟩ := hDU hu
  rw [exh, alt_fromSetoid] at hS
  exact hwU ⟨c, hcS, Setoid.eq_of_mem_classes (hS hcS) huc cell_mem_classes (hsub hu) ▸
    mem_cell_self⟩

theorem subset_cell_of_E_exh [Finite W] (h : D ∈ E (exh a) w) : D ⊆ cell a w := by
  obtain ⟨c, hc, hwc, hDc⟩ := h.exists_alt
  rw [exh, alt_fromSetoid] at hc
  exact (Setoid.eq_of_mem_classes hc hwc cell_mem_classes mem_cell_self) ▸ hDc

/-- Fact 2: under the internal interpretation of *know*, the intermediate exhaustive reading
of a wh-complement, the complete operator on the non-exhaustive nucleus, and its strongly
exhaustive reading, the operator on the exhaustive nucleus, yield the same truth conditions:
the subject's state lies within one cell of the partition. -/
theorem knowInt_Ecmp_nonExh_iff [Finite W] {dox : X → W → Set W} {x : X}
    (hne : ∀ d, (a d).Nonempty) (hN : (nobody a).Nonempty)
    (hind : ∀ d d', a d ⊆ a d' → d = d') :
    knowInt dox (Ecmp (nonExh a)) x w ↔ knowInt dox (E (exh a)) x w := by
  constructor
  · rintro ⟨hw, h⟩
    have hsub := subset_cell_of_Ecmp_nonExh hne hN hind hw h
    exact ⟨mem_E_exh_of_subset_cell hsub hw.nonempty,
      λ _ hv => (mem_E_exh_of_subset_cell hsub hw.nonempty).of_mem hv⟩
  · rintro ⟨hw, -⟩
    have hsub := subset_cell_of_E_exh hw
    exact ⟨mem_Ecmp_nonExh_of_subset_cell hne hN hind hsub hw.nonempty, λ v hv =>
      mem_Ecmp_nonExh_of_subset_cell hne hN hind (cell_eq_of_mem (hsub hv) ▸ hsub) hw.nonempty⟩

end Exhaustivity

/-! ### Constraints on responsive verb meanings (section 6) -/

section Constraints

/-- A responsive verb meaning: a world predicate from a complement meaning and a subject. -/
abbrev Verb (W X : Type*) := (W → Set (Set W)) → X → W → Prop

variable (V : Verb W X)

/-- Definition 8 on partition nuclei, whose decomposition is the family of their cells: the
verb holds of the complement exactly when it holds of one of its cells. -/
def CDistributive : Prop :=
  ∀ Q : Question W, Q.IsPartition → ∀ x w, V (E Q) x w ↔ ∃ c ∈ alt Q, V (E (ofSet c)) x w

/-- Definition 10: veridicality with respect to declarative complements. -/
def DeclVeridical : Prop := ∀ (q : Set W) x w, V (E (ofSet q)) x w → w ∈ q

/-- Definition 11: veridicality with respect to interrogative complements, on
exhaustivity-neutral nuclei, the partitions, and the declaratives expressing their cells. -/
def IntVeridical : Prop :=
  ∀ Q : Question W, Q.IsPartition → ∀ c ∈ alt Q, ∀ x w, V (E Q) x w → w ∈ c → V (E (ofSet c)) x w

/-- Definition 9: the choice property, that the verb does not hold of two inconsistent
declaratives at once. -/
def Choice : Prop :=
  ∀ q q' : Set W, Disjoint q q' → ∀ x w, ¬ (V (E (ofSet q)) x w ∧ V (E (ofSet q')) x w)

variable {V}

/-- Fact 5: a c-distributive verb veridical for declaratives is veridical for
interrogatives. -/
theorem IntVeridical.of_cDistributive (hd : CDistributive V) (hv : DeclVeridical V) :
    IntVeridical V := by
  intro Q hQ c hc x w h hwc
  obtain ⟨c', hc', h'⟩ := (hd Q hQ x w).1 h
  obtain ⟨b, -, hb⟩ := hQ.2 w
  exact ((hb c ⟨hc, hwc⟩).trans (hb c' ⟨hc', hv c' x w h'⟩).symm) ▸ h'

/-- Fact 6: a c-distributive verb with the choice property veridical for interrogatives is
veridical for declaratives, by the polar question of the declarative. -/
theorem DeclVeridical.of_choice [Nonempty W] (hd : CDistributive V) (hch : Choice V)
    (hv : IntVeridical V) : DeclVeridical V := by
  intro q x w h
  by_contra hw
  rcases eq_or_ne q ∅ with rfl | hne
  · exact hch ∅ ∅ disjoint_bot_left x w ⟨h, h⟩
  have hnu : q ≠ Set.univ := λ hq => hw (hq ▸ Set.mem_univ w)
  have hP := isPartition_polar hne hnu
  have hpol : V (E (polar q)) x w :=
    (hd _ hP x w).2 ⟨q, (mem_alt_polar_of_nontrivial hne hnu q).2 (Or.inl rfl), h⟩
  exact hch q qᶜ disjoint_compl_right x w
    ⟨h, hv _ hP qᶜ ((mem_alt_polar_of_nontrivial hne hnu qᶜ).2 (Or.inr rfl)) x w hpol hw⟩

variable (dox : X → W → Set W)

theorem declVeridical_know : DeclVeridical (know dox) :=
  λ _ _ _ h => (know_ofSet_iff.1 h).1

variable [Finite W]

/-- *know* is c-distributive: on a partition nucleus a state is a truthful resolution exactly
when it is a truthful resolution of the true cell. -/
theorem cDistributive_know : CDistributive (know dox) := by
  intro Q hQ x w
  constructor
  · intro h
    obtain ⟨c, hc, hwc, hDc⟩ := h.exists_alt
    exact ⟨c, hc, isTruthful_ofSet_iff.2 ⟨hwc, hDc, h.nonempty⟩⟩
  · rintro ⟨c, hc, hk⟩
    obtain ⟨hwc, hDc, hne⟩ := isTruthful_ofSet_iff.1 hk
    refine ⟨Q.downward_closed c (mem_of_mem_alt hc) _ hDc, hne, ?_⟩
    rintro ⟨U, hU, hwU, hDU⟩
    obtain ⟨S, hS, rfl⟩ := mem_altUnion.1 hU
    obtain ⟨u, hu⟩ := hne
    obtain ⟨m, hmS, hum⟩ := hDU hu
    obtain ⟨b, -, hb⟩ := hQ.2 u
    exact hwU ⟨m, hmS, ((hb m ⟨hS hmS, hum⟩).trans (hb c ⟨hc, hDc hu⟩).symm) ▸ hwc⟩

/-- *know* is veridical for interrogatives, (45), by Fact 5. -/
theorem intVeridical_know : IntVeridical (know dox) :=
  IntVeridical.of_cDistributive (cDistributive_know dox) (declVeridical_know dox)

end Constraints

end TheilerRoelofsenAloni2018
