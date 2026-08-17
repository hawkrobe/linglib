import Linglib.Studies.DegenTonhauser2021
import Mathlib.Data.Finset.Lattice.Fold

/-!
# [degen-tonhauser-2022]: Are There Factive Predicates?

Six experiments testing whether the twenty clause-embedding predicates of
[degen-tonhauser-2021] contain a coherent class of factive predicates under either
standard definition: the clausal complement's content (CC) is presupposed (3a,
[kiparsky-kiparsky-1970]), or presupposed and entailed (3b). The paper's traditional
four-way classification (13) is `traditionalClass`. Definition 3a expects the
certainty ratings of canonically factive predicates to be categorically higher than
those of all other predicates — `Separates`, which over a finite domain holds iff
some threshold puts exactly the factive class on top (`separates_iff_exists_threshold`).

The data refute that expectation in both response tasks: the optionally factive
*inform* rates as projective as the canonically factive *reveal* or *discover*
(0.81 vs 0.70 and 0.78 in experiment 1a; 0.90 vs 0.69 and 0.84 in 1b), so the
ratings do not separate the class (`certainty1a_not_separated`) and no nonarbitrary
line can be drawn (`certainty1a_no_threshold`; likewise `certainty1b_*`). The
entailment experiments undermine definition 3b in turn: in experiment 2a only
*be right* and *prove* rated with the entailed controls, yet both project below
every canonically factive predicate (`entailment_projection_dissociation`);
experiment 2b adds *know*, *see*, *discover*, and *confirm* — a heterogeneous
class — and the contradictoriness experiments 3a/3b identify no entailed CCs at
all. Degen & Tonhauser conclude that the experiments support no coherent class of
factive predicates, while cautioning (their objection 3) that gradient ratings
alone cannot rule out a binary factivity category combined with lexical ambiguity
and interpreter uncertainty. The results bear on projection analyses ([heim-1983],
[van-der-sandt-1992]) whose explanandum is delimited by exactly this class.

Per-predicate mean ratings (`certainty1a`, `certainty1b`, `inference2a`) are
computed from the authors' data at github.com/judith-tonhauser/projective-probability
(results 5-projectivity-no-fact, 8-projectivity-no-fact-binary, 4-veridicality3),
rounded to two decimal places, and stored as `ℚ` so comparisons close by `norm_num`.
The predicates are bridged to their Fragment lexical entries via
`DegenTonhauser2021.toVerbEntry`; the traditional classification agrees with the
Fragment's factivity flags (`traditionalClass_consistent_with_fragment`).
-/

namespace DegenTonhauser2022

open DegenTonhauser2021

/-! ### The traditional classification -/

/-- The traditional four-way classification of the twenty clause-embedding
    predicates ((13) of [degen-tonhauser-2022]), by whether the complement content
    is taken to be presupposed and entailed. -/
inductive TraditionalClass where
  /-- CC presupposed (and, on definition 3b, entailed): *know*, *discover*, ... -/
  | factive
  /-- CC neither presupposed nor entailed: *think*, *say*, ... -/
  | nonveridicalNonfactive
  /-- CC entailed but not presupposed: *be right*, *demonstrate*. -/
  | veridicalNonfactive
  /-- CC only sometimes presupposed: *acknowledge*, *admit*, ... -/
  | optionallyFactive
  deriving DecidableEq, Repr

/-- The classification in (13). -/
def traditionalClass : Predicate → TraditionalClass
  | .beAnnoyed | .discover | .know | .reveal | .see => .factive
  | .pretend | .say | .suggest | .think => .nonveridicalNonfactive
  | .beRight | .demonstrate => .veridicalNonfactive
  | .acknowledge | .admit | .announce | .confess | .confirm
  | .establish | .hear | .inform | .prove => .optionallyFactive

/-! ### Categorical distinction as separation

Definition 3a expects factive certainty ratings "categorically higher" than the
rest. For a class and a rating over a finite domain this is the same demand as a
separating threshold, so a single interleaved pair refutes both readings. -/

section Separation

variable {α β : Type*} [LinearOrder β] {cls : α → Prop} {rating : α → β} {p q : α}

/-- Every in-class element outrates every out-of-class element. -/
def Separates (cls : α → Prop) (rating : α → β) : Prop :=
  ∀ ⦃p q⦄, cls p → ¬cls q → rating q < rating p

/-- An out-of-class element rating at least as high as an in-class one defeats
    separation. -/
theorem not_separates (hp : cls p) (hq : ¬cls q) (hpq : rating p ≤ rating q) :
    ¬ Separates cls rating :=
  fun h => absurd (h hp hq) (not_lt.mpr hpq)

/-- A class is separated by a rating iff some threshold puts exactly the class
    above it; the separating threshold is the top out-of-class rating. -/
theorem separates_iff_exists_threshold [Fintype α] [DecidablePred cls]
    (h : ∃ q, ¬cls q) :
    Separates cls rating ↔ ∃ t, ∀ p, cls p ↔ t < rating p := by
  obtain ⟨q₀, hq₀⟩ := h
  have hs : (Finset.univ.filter fun q => ¬cls q).Nonempty := ⟨q₀, by simp [hq₀]⟩
  constructor
  · intro hsep
    refine ⟨(Finset.univ.filter fun q => ¬cls q).sup' hs rating,
      fun p => ⟨fun hp => ?_, fun hlt => ?_⟩⟩
    · exact (Finset.sup'_lt_iff hs).mpr fun b hb => hsep hp (by simpa using hb)
    · by_contra hp
      exact absurd hlt (not_lt.mpr (Finset.le_sup' rating (by simpa using hp)))
  · rintro ⟨t, ht⟩ p q hp hq
    exact (not_lt.mp fun hlt => hq ((ht q).mpr hlt)).trans_lt ((ht p).mp hp)

end Separation

/-! ### Data: certainty and inference ratings

Computed from the authors' data at github.com/judith-tonhauser/projective-probability,
rounded to two decimals and listed in descending order as in the paper's figures. -/

/-- Mean certainty rating by predicate, experiment 1a ('certain that' diagnostic,
    gradient slider; Figure 2). From results/5-projectivity-no-fact (n = 266 per
    predicate; nonprojective main-clause control mean 0.11). -/
def certainty1a : Predicate → ℚ
  | .beAnnoyed => 0.88
  | .know => 0.86
  | .see => 0.81
  | .inform => 0.81
  | .discover => 0.78
  | .hear => 0.75
  | .acknowledge => 0.72
  | .reveal => 0.70
  | .admit => 0.66
  | .confess => 0.64
  | .announce => 0.58
  | .demonstrate => 0.49
  | .establish => 0.36
  | .confirm => 0.34
  | .prove => 0.30
  | .say => 0.24
  | .suggest => 0.22
  | .think => 0.20
  | .beRight => 0.18
  | .pretend => 0.15

/-- Proportion of 'yes' responses by predicate, experiment 1b ('certain that'
    diagnostic, forced choice; Figure 4). From results/8-projectivity-no-fact-binary
    (n = 436 per predicate; main-clause control mean 0.00). -/
def certainty1b : Predicate → ℚ
  | .know => 0.93
  | .beAnnoyed => 0.92
  | .inform => 0.90
  | .see => 0.86
  | .discover => 0.84
  | .hear => 0.81
  | .acknowledge => 0.78
  | .reveal => 0.69
  | .admit => 0.67
  | .confess => 0.58
  | .announce => 0.57
  | .demonstrate => 0.31
  | .establish => 0.19
  | .confirm => 0.16
  | .prove => 0.13
  | .suggest => 0.07
  | .pretend => 0.07
  | .say => 0.07
  | .think => 0.04
  | .beRight => 0.03

/-- Mean inference rating by predicate, experiment 2a ('does it follow' diagnostic,
    gradient slider; Figure 9). From results/4-veridicality3 (n = 259 per predicate;
    entailing control mean 0.96, non-entailing control mean 0.03). -/
def inference2a : Predicate → ℚ
  | .prove => 0.96
  | .beRight => 0.96
  | .see => 0.95
  | .discover => 0.94
  | .confirm => 0.94
  | .know => 0.93
  | .beAnnoyed => 0.92
  | .admit => 0.91
  | .acknowledge => 0.90
  | .establish => 0.90
  | .reveal => 0.90
  | .confess => 0.89
  | .demonstrate => 0.85
  | .inform => 0.83
  | .announce => 0.81
  | .say => 0.68
  | .hear => 0.50
  | .suggest => 0.34
  | .think => 0.32
  | .pretend => 0.12

/-! ### No categorical projection distinction (definition 3a) -/

/-- The exp 1a certainty ratings do not separate the canonically factive class:
    the optionally factive *inform* (0.81) outrates the factive *reveal* (0.70). -/
theorem certainty1a_not_separated :
    ¬ Separates (traditionalClass · = .factive) certainty1a :=
  not_separates (p := .reveal) (q := .inform) rfl (by decide) (by norm_num [certainty1a])

/-- Hence no threshold recovers the classification from the exp 1a ratings — the
    paper's "a nonarbitrary line between canonically factive and optionally factive
    predicates cannot be drawn". -/
theorem certainty1a_no_threshold :
    ¬ ∃ t, ∀ p, traditionalClass p = .factive ↔ t < certainty1a p :=
  fun h => certainty1a_not_separated
    ((separates_iff_exists_threshold ⟨.inform, by decide⟩).mpr h)

/-- The forced-choice replication (exp 1b) does not separate the class either:
    *inform* at 0.90 vs *reveal* at 0.69. -/
theorem certainty1b_not_separated :
    ¬ Separates (traditionalClass · = .factive) certainty1b :=
  not_separates (p := .reveal) (q := .inform) rfl (by decide) (by norm_num [certainty1b])

/-- No threshold recovers the classification from the exp 1b ratings. -/
theorem certainty1b_no_threshold :
    ¬ ∃ t, ∀ p, traditionalClass p = .factive ↔ t < certainty1b p :=
  fun h => certainty1b_not_separated
    ((separates_iff_exists_threshold ⟨.inform, by decide⟩).mpr h)

/-! ### Entailment vs projection (definition 3b) -/

/-- Exp 2a's best contenders for factivity under definition 3b are the least
    projective: *be right* and *prove* carry the top inference ratings (0.96 each,
    level with the entailed controls) yet project below every canonically factive
    predicate (0.18 and 0.30 vs 0.70 at the bottom of the factive class). -/
theorem entailment_projection_dissociation :
    (∀ p, inference2a p ≤ inference2a .beRight ∧ inference2a p ≤ inference2a .prove) ∧
    (∀ p, traditionalClass p = .factive →
      certainty1a .beRight < certainty1a p ∧ certainty1a .prove < certainty1a p) := by
  refine ⟨fun p => ?_, fun p hp => ?_⟩
  · cases p <;> norm_num [inference2a]
  · cases p <;> first
      | exact absurd hp (by decide)
      | norm_num [certainty1a]

/-! ### Fragment bridge -/

section FragmentBridge

open English.Predicates.Verbal English.Predicates.Copular

/-- Canonically factive verbs have `factivePresup = true` in the Fragment,
    matching the classification in (13). "be annoyed" is copular and emotive —
    its presupposition derives from emotive semantics, not doxastic veridicality —
    and is covered by `copular_presup_matches_classification`. -/
theorem factive_entries_have_factivePresup :
    know.factivePresup = true ∧ discover.factivePresup = true ∧
    see.factivePresup = true ∧ reveal.factivePresup = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Nonveridical nonfactive verbs have `factivePresup = false` in the Fragment. -/
theorem nonfactive_entries_lack_factivePresup :
    pretend.factivePresup = false ∧ suggest.factivePresup = false ∧
    say.factivePresup = false ∧ think.factivePresup = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The traditional classification is consistent with Fragment factivity for
    verbal entries: factive verbs have `factivePresup = true`, nonveridical
    nonfactives `false`. -/
theorem traditionalClass_consistent_with_fragment (p : Predicate)
    (v : VerbEntry) (h : toVerbEntry p = some v) :
    (traditionalClass p = .factive → v.factivePresup = true) ∧
    (traditionalClass p = .nonveridicalNonfactive → v.factivePresup = false) := by
  cases p <;> (unfold toVerbEntry at h; cases h) <;>
    refine ⟨fun hc => ?_, fun hc => ?_⟩ <;> first | rfl | simp [traditionalClass] at hc

/-- "be annoyed" is a presupposition trigger (emotive factive) while "be right"
    is not, matching (13): factives trigger presuppositions, veridical
    nonfactives do not. -/
theorem copular_presup_matches_classification :
    (toPredicateCore .beAnnoyed).isPresupTrigger = true ∧
    (toPredicateCore .beRight).isPresupTrigger = false :=
  ⟨rfl, rfl⟩

end FragmentBridge

end DegenTonhauser2022
