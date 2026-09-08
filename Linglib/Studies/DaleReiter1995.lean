import Linglib.Features.PropertyDomain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Dale and Reiter, computational interpretations of the Gricean maxims (1995)

A referring expression is a distinguishing description: a set of attribute-value pairs that
all hold of the intended referent and that together rule out every member of the contrast
set, which makes finding one a set-cover problem and finding a shortest one NP-hard. Dale and
Reiter compare four computational readings of Grice's brevity submaxim, Full Brevity (a
shortest description), the Greedy Heuristic of Dale (1989), the Local Brevity conditions of
Reiter (1990) and their own Incremental Algorithm, which walks a fixed preference list of
attributes and keeps any value that rules out a distractor not yet ruled out, and they argue
for the last on cost and on the psycholinguistic observation that speakers include
unnecessary modifiers.

We define distinguishing descriptions and the four interpretations over a finite knowledge
base, prove that a shortest description satisfies both of Reiter's conditions while the
greedy and incremental algorithms can return unnecessary pairs, evaluate the exhaustive
count of §3.1.1, and run the seven-cup example of §3.1.2, the white-bird example of §3.2.1
and the kennel example of §4.4 through the algorithms of Figs. 3 and 6, whose output we
prove rules out every distractor and always carries a head noun.

## References

* [R. Dale and E. Reiter, *Computational Interpretations of the Gricean Maxims in the
  Generation of Referring Expressions* (1995)][dale-reiter-1995]
* [H. P. Grice, *Logic and Conversation* (1975)][grice-1975]
-/

namespace DaleReiter1995

open Finset

section Brevity

variable {E A V : Type*}

/-! ### Distinguishing descriptions (§2.2) -/

/-- A knowledge base (§4.1): the value an entity has for an attribute, if it has one. -/
abbrev KB (E A V : Type*) := E → A → Option V

/-- The semantic content of a referring expression, a set of attribute-value pairs (§2.2). -/
abbrev Description (A V : Type*) := Finset (A × V)

/-- The pair holds of the entity. -/
def Applies (kb : KB E A V) (x : E) (p : A × V) : Prop := kb x p.1 = some p.2

instance [DecidableEq V] (kb : KB E A V) (x : E) (p : A × V) : Decidable (Applies kb x p) := by
  unfold Applies; infer_instance

/-- A distinguishing description of `r` against the contrast set `C` (3): every pair holds
of `r` (C1) and every distractor fails some pair (C2). -/
def Distinguishing (kb : KB E A V) (r : E) (C : Finset E) (L : Description A V) : Prop :=
  (∀ p ∈ L, Applies kb r p) ∧ ∀ c ∈ C, ∃ p ∈ L, ¬ Applies kb c p

instance [DecidableEq V] (kb : KB E A V) (r : E) (C : Finset E) (L : Description A V) :
    Decidable (Distinguishing kb r C L) := by
  unfold Distinguishing; infer_instance

/-- The members of the contrast set a pair rules out (§2.2). -/
def rulesOut [DecidableEq V] (kb : KB E A V) (C : Finset E) (p : A × V) : Finset E :=
  C.filter (¬ Applies kb · p)

/-- Finding a distinguishing description is a set-cover problem: the pairs' `rulesOut` sets
must cover the contrast set (§2.2). -/
theorem distinguishing_iff_biUnion [DecidableEq E] [DecidableEq V] (kb : KB E A V) (r : E)
    (C : Finset E) (L : Description A V) :
    Distinguishing kb r C L ↔
      (∀ p ∈ L, Applies kb r p) ∧ C ⊆ L.biUnion (rulesOut kb C) := by
  simp only [Distinguishing, rulesOut, subset_iff, mem_biUnion, mem_filter]
  exact and_congr_right λ _ => forall₂_congr λ c hc =>
    exists_congr λ p => and_congr_right λ _ => (and_iff_right hc).symm

/-! ### Four interpretations of brevity (§3.1) -/

variable (kb : KB E A V) (r : E) (C : Finset E) (L : Description A V)

/-- Full Brevity (§3.1.1): a shortest distinguishing description. -/
def IsShortest : Prop :=
  Distinguishing kb r C L ∧ ∀ L', Distinguishing kb r C L' → L.card ≤ L'.card

variable {kb r C L}

/-- A distinguishing description with two pairs is shortest once neither the empty
description nor any single pair distinguishes. -/
theorem isShortest_of_card_two (hL : Distinguishing kb r C L) (h2 : L.card = 2)
    (h0 : ¬ Distinguishing kb r C ∅) (h1 : ∀ p, ¬ Distinguishing kb r C {p}) :
    IsShortest kb r C L := by
  refine ⟨hL, λ L' hL' => ?_⟩
  by_contra hlt
  have : L'.card = 0 ∨ L'.card = 1 := by omega
  rcases this with h | h
  · obtain rfl := card_eq_zero.mp h
    exact h0 hL'
  · obtain ⟨p, rfl⟩ := card_eq_one.mp h
    exact h1 p hL'

variable (kb r C L) [DecidableEq A] [DecidableEq V]

/-- Reiter's No Unnecessary Components (§3.1.3): a distinguishing description none of
whose pairs can be dropped. -/
def NoUnnecessary : Prop :=
  Distinguishing kb r C L ∧ ∀ p ∈ L, ¬ Distinguishing kb r C (L.erase p)

/-- Reiter's Local Brevity (§3.1.3): no set of pairs can be replaced by a single new pair. -/
def LocallyBrief : Prop :=
  NoUnnecessary kb r C L ∧
    ∀ S ⊆ L, 2 ≤ S.card → ∀ p, ¬ Distinguishing kb r C (insert p (L \ S))

instance : Decidable (NoUnnecessary kb r C L) := by unfold NoUnnecessary; infer_instance

variable {kb r C L}

/-- A shortest description has no unnecessary pair: Full Brevity never includes an
unnecessary modifier (§3.2.1). -/
theorem IsShortest.noUnnecessary (h : IsShortest kb r C L) : NoUnnecessary kb r C L :=
  ⟨h.1, λ p hp hd => absurd (h.2 _ hd) (not_le.mpr (by
    have := card_pos.mpr ⟨p, hp⟩
    rw [card_erase_of_mem hp]; omega))⟩

/-- A shortest description is locally brief. -/
theorem IsShortest.locallyBrief (h : IsShortest kb r C L) : LocallyBrief kb r C L :=
  ⟨h.noUnnecessary, λ S hS hS2 p hd => absurd (h.2 _ hd) (not_le.mpr (by
    have h₁ := card_insert_le p (L \ S)
    have h₂ := card_sdiff_of_subset hS
    have h₃ := card_le_card hS
    omega))⟩

/-- Descriptions the exhaustive Full Brevity search checks, with `na` available attributes
and a shortest description of `nl` pairs (§3.1.1). -/
def fullBrevitySteps (na nl : ℕ) : ℕ := ∑ i ∈ Icc 1 nl, na.choose i

/-- The paper's counts: six for the kennel, 175, over 6,000 and over 2,000,000. -/
theorem fullBrevitySteps_values :
    fullBrevitySteps 3 2 = 6 ∧ fullBrevitySteps 10 3 = 175 ∧
      6000 < fullBrevitySteps 20 4 ∧ 2000000 < fullBrevitySteps 50 5 := by
  decide +kernel

/-- The first element of a list minimizing `f`. -/
private def argmin {α : Type*} (f : α → ℕ) : List α → Option α
  | [] => none
  | a :: l => some (l.foldl (λ b c => if f c < f b then c else b) a)

private def greedyAux [DecidableEq E] (kb : KB E A V) :
    ℕ → Finset E → List (A × V) → Description A V → Option (Description A V)
  | 0, C, _, L => if C = ∅ then some L else none
  | n + 1, C, P, L =>
    if C = ∅ then some L
    else match argmin (λ p => (C.filter (Applies kb · p)).card) P with
      | none => none
      | some p => greedyAux kb n (C.filter (Applies kb · p)) (P.erase p) (insert p L)

/-- Fig. 3's Greedy Heuristic: from the properties `P` true of the referent, add the one
leaving the fewest distractors until none remain, failing when `P` runs out. -/
def greedy [DecidableEq E] (kb : KB E A V) (C : Finset E) (P : List (A × V)) :
    Option (Description A V) :=
  greedyAux kb P.length C P ∅

end Brevity

/-! ### The Incremental Algorithm (§4, Fig. 6) -/

section Incremental

variable {E A V : Type*}

/-- The host system's interface (§4.1): the head-noun attribute, basic-level values, the
value taxonomies and the user model. -/
structure Domain (E A V : Type*) where
  /-- The attribute realized as the head noun (§2.2). -/
  type : A
  /-- The depth of the value taxonomies, bounding `findBestValue`'s descent. -/
  depth : ℕ
  /-- The basic-level value of an attribute for an entity (BasicLevelValue). -/
  basicLevel : E → A → Option V
  /-- The child of a value in the attribute's taxonomy that still subsumes the entity's own
  value (MoreSpecificValue). -/
  moreSpecific : E → A → V → Option V
  /-- Whether the user knows the pair to hold of the entity, knows it not to, or neither
  (UserKnows). -/
  userKnows : E → A → V → Option Bool

namespace Domain

variable (d : Domain E A V)

/-- A domain without value taxonomies whose user knows exactly what the knowledge base
records. -/
def flat [DecidableEq V] (kb : KB E A V) (type : A) : Domain E A V where
  type := type
  depth := 0
  basicLevel := kb
  moreSpecific _ _ _ := none
  userKnows x a v := (kb x a).map λ w => decide (w = v)

/-- The remaining distractors the user knows not to bear the pair (Fig. 6, RulesOut). -/
def rulesOut (C : Finset E) (a : A) (v : V) : Finset E :=
  C.filter λ x => d.userKnows x a v = some false

/-- Fig. 6's FindBestValue: the initial value when the user knows it to hold of `r`, refined
to a more specific value only when that rules out more distractors. -/
def findBestValue (r : E) (C : Finset E) (a : A) : ℕ → V → Option V
  | 0, v => if d.userKnows r a v = some true then some v else none
  | n + 1, v =>
    if d.userKnows r a v = some true then
      some <| match d.moreSpecific r a v with
        | none => v
        | some more =>
          match findBestValue r C a n more with
          | none => v
          | some new =>
            if (d.rulesOut C a v).card < (d.rulesOut C a new).card then new else v
    else none

section

variable [DecidableEq A] [DecidableEq V]

/-- One attribute of Fig. 6's loop: the best value for `a` is kept when it rules out a
remaining distractor, and those distractors are removed. -/
def step [DecidableEq E] (r : E) (a : A) (C : Finset E) (L : Description A V) :
    Finset E × Description A V :=
  match d.basicLevel r a >>= d.findBestValue r C a d.depth with
  | none => (C, L)
  | some v =>
    if (d.rulesOut C a v).Nonempty then (C \ d.rulesOut C a v, insert (a, v) L) else (C, L)

/-- Fig. 6's return: a head noun is always included. -/
def withType (r : E) (L : Description A V) : Description A V :=
  if ∃ p ∈ L, p.1 = d.type then L
  else match d.basicLevel r d.type with
    | none => L
    | some b => insert (d.type, b) L

variable [DecidableEq E]

/-- Fig. 6's loop over the preferred attributes. -/
def go (r : E) : Finset E → List A → Description A V → Option (Description A V)
  | _, [], _ => none
  | C, a :: rest, L =>
    let s := d.step r a C L
    if s.1 = ∅ then some (d.withType r s.2) else go r s.1 rest s.2

/-- Fig. 6's MakeReferringExpression: the Incremental Algorithm over the preferred
attributes `P`, failing when they run out before the contrast set does. -/
def makeReferringExpression (r : E) (C : Finset E) (P : List A) :
    Option (Description A V) :=
  d.go r C P ∅

theorem step_subset (r : E) (a : A) (C : Finset E) (L : Description A V) :
    L ⊆ (d.step r a C L).2 := by
  unfold step
  split
  · exact subset_rfl
  · split_ifs
    · exact subset_insert _ _
    · exact subset_rfl

/-- Every distractor a step removes is ruled out by the pair the step adds. -/
theorem step_ruledOut (r : E) (a : A) (C : Finset E) (L : Description A V) {c : E}
    (hc : c ∈ C) (hc' : c ∉ (d.step r a C L).1) :
    ∃ p ∈ (d.step r a C L).2, d.userKnows c p.1 p.2 = some false := by
  unfold step at hc' ⊢
  split at hc'
  · exact absurd hc hc'
  · split_ifs at hc' ⊢
    · refine ⟨_, mem_insert_self _ _, ?_⟩
      have := mem_sdiff.not.mp hc'
      simpa [rulesOut, hc] using this
    · exact absurd hc hc'

omit [DecidableEq E] in
theorem withType_subset (r : E) (L : Description A V) : L ⊆ d.withType r L := by
  unfold withType
  split_ifs
  · exact subset_rfl
  · split
    · exact subset_rfl
    · exact subset_insert _ _

/-- The loop's output extends its accumulator and rules out every remaining distractor. -/
theorem go_spec (r : E) : ∀ (P : List A) (C : Finset E) (L L' : Description A V),
    d.go r C P L = some L' →
      L ⊆ L' ∧ ∀ c ∈ C, ∃ p ∈ L', d.userKnows c p.1 p.2 = some false
  | [], _, _, _, h => by simp [go] at h
  | a :: rest, C, L, L', h => by
    simp only [go] at h
    split_ifs at h with hC
    · obtain rfl := Option.some.inj h
      refine ⟨(d.step_subset r a C L).trans (d.withType_subset r _), λ c hc => ?_⟩
      have hc' : c ∉ (d.step r a C L).1 := by simp [hC]
      obtain ⟨p, hp, hcp⟩ := d.step_ruledOut r a C L hc hc'
      exact ⟨p, d.withType_subset r _ hp, hcp⟩
    · obtain ⟨hsub, hrule⟩ := go_spec r rest _ _ L' h
      refine ⟨(d.step_subset r a C L).trans hsub, λ c hc => ?_⟩
      by_cases hc' : c ∈ (d.step r a C L).1
      · exact hrule c hc'
      · obtain ⟨p, hp, hcp⟩ := d.step_ruledOut r a C L hc hc'
        exact ⟨p, hsub hp, hcp⟩

/-- Fig. 6's output rules out every member of the contrast set (§4.3). -/
theorem makeReferringExpression_rulesOut {r : E} {C : Finset E} {P : List A}
    {L : Description A V} (h : d.makeReferringExpression r C P = some L) :
    ∀ c ∈ C, ∃ p ∈ L, d.userKnows c p.1 p.2 = some false :=
  (d.go_spec r P C ∅ L h).2

/-- The loop returns only through `withType`. -/
theorem go_eq_withType (r : E) : ∀ (P : List A) (C : Finset E) (L L' : Description A V),
    d.go r C P L = some L' → ∃ L₀, L' = d.withType r L₀
  | [], _, _, _, h => by simp [go] at h
  | a :: rest, C, L, L', h => by
    simp only [go] at h
    split_ifs at h with hC
    · exact ⟨_, (Option.some.inj h).symm⟩
    · exact go_eq_withType r rest _ _ L' h

/-- Fig. 6's output carries a head noun whenever the referent has a basic-level type
(§4.3). -/
theorem makeReferringExpression_type {r : E} {C : Finset E} {P : List A}
    {L : Description A V} (h : d.makeReferringExpression r C P = some L)
    (hb : (d.basicLevel r d.type).isSome) : ∃ v, (d.type, v) ∈ L := by
  obtain ⟨L₀, rfl⟩ := d.go_eq_withType r P C ∅ L h
  unfold withType
  split_ifs with hL
  · obtain ⟨⟨a, v⟩, hp, ha⟩ := hL
    exact ⟨v, ha ▸ hp⟩
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hb
    exact ⟨b, by simp [hb]⟩

end

end Domain

end Incremental

/-! ### The paper's examples -/

/-- The attributes of the paper's examples: the head noun and the perceptual properties. -/
inductive Attr where
  | type
  | property (d : Features.PropertyDomain)
  deriving DecidableEq, Repr, Fintype

/-- The values of the paper's examples. -/
inductive Value where
  | dog | cat | chihuahua | siameseCat | bird | cup
  | small | medium | large
  | black | white | red | green | blue
  | plastic | paper
  deriving DecidableEq, Repr, Fintype

/-! #### The two dogs and the cat (§2.2, §4.4) -/

/-- The three animals of §2.2 and §4.4. -/
inductive Animal where
  | object1 | object2 | object3
  deriving DecidableEq, Repr

namespace Animal

/-- The most specific values the system knows (§4.4). -/
def kb : KB Animal Attr Value
  | .object1, .type => some .chihuahua
  | .object1, .property .size => some .small
  | .object1, .property .color => some .black
  | .object2, .type => some .chihuahua
  | .object2, .property .size => some .large
  | .object2, .property .color => some .white
  | .object3, .type => some .siameseCat
  | .object3, .property .size => some .small
  | .object3, .property .color => some .black
  | _, _ => none

/-- The basic-level values of §2.2: dog, dog, cat. -/
def basicLevel (x : Animal) : Attr → Option Value
  | .type => match x with | .object3 => some .cat | _ => some .dog
  | a => kb x a

/-- The taxonomy of §4.4: the breeds sit below the basic-level types. -/
def parent : Value → Option Value
  | .chihuahua => some .dog
  | .siameseCat => some .cat
  | _ => none

/-- The domain of §4.4: the breeds are the only more specific values, and the user knows a
pair to hold exactly when it is accurate under the taxonomy. -/
def domain : Domain Animal Attr Value where
  type := .type
  depth := 1
  basicLevel := basicLevel
  moreSpecific x a v := match kb x a with
    | some w => if parent w = some v then some w else none
    | none => none
  userKnows x a v := (kb x a).map λ w => decide (w = v ∨ parent w = some v)

/-- The contrast set. -/
def contrast : Finset Animal := {.object2, .object3}

/-- *The black dog* and *the small dog* are distinguishing descriptions of Object1 (§2.2). -/
theorem black_dog_distinguishing :
    Distinguishing basicLevel .object1 contrast {(.type, .dog), (.property .color, .black)} ∧
    Distinguishing basicLevel .object1 contrast {(.type, .dog), (.property .size, .small)} := by
  decide +kernel

/-- No single pair distinguishes Object1, so *the black dog* is a shortest description
(§3.1.1's six steps). -/
theorem black_dog_isShortest :
    IsShortest basicLevel .object1 contrast {(.type, .dog), (.property .color, .black)} :=
  isShortest_of_card_two black_dog_distinguishing.1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The breed rules out no more distractors than the basic-level type, so `FindBestValue`
keeps *dog* (§4.4). -/
theorem findBestValue_type :
    domain.findBestValue .object1 contrast .type 1 .dog = some .dog := by decide +kernel

/-- With the preference order type, colour, size the algorithm returns *the black dog*; with
type, size, colour it returns *the small dog* (§4.4). -/
theorem makeReferringExpression_animal :
    domain.makeReferringExpression .object1 contrast
        [.type, .property .color, .property .size] =
      some {(.type, .dog), (.property .color, .black)} ∧
    domain.makeReferringExpression .object1 contrast
        [.type, .property .size, .property .color] =
      some {(.type, .dog), (.property .size, .small)} := by
  decide +kernel

end Animal

/-! #### The seven cups (§3.1.2) -/

/-- The seven cups of §3.1.2. -/
inductive Cup where
  | object1 | object2 | object3 | object4 | object5 | object6 | object7
  deriving DecidableEq, Repr

namespace Cup

/-- Size, colour and material of each cup. -/
def kb : KB Cup Attr Value
  | .object1, .property .size => some .large
  | .object1, .property .color => some .red
  | .object1, .property .material => some .plastic
  | .object2, .property .size => some .small
  | .object2, .property .color => some .red
  | .object2, .property .material => some .plastic
  | .object3, .property .size => some .small
  | .object3, .property .color => some .red
  | .object3, .property .material => some .paper
  | .object4, .property .size => some .medium
  | .object4, .property .color => some .red
  | .object4, .property .material => some .paper
  | .object5, .property .size => some .large
  | .object5, .property .color => some .green
  | .object5, .property .material => some .paper
  | .object6, .property .size => some .large
  | .object6, .property .color => some .blue
  | .object6, .property .material => some .paper
  | .object7, .property .size => some .large
  | .object7, .property .color => some .blue
  | .object7, .property .material => some .plastic
  | _, _ => none

/-- The contrast set for Object1. -/
def contrast : Finset Cup := {.object2, .object3, .object4, .object5, .object6, .object7}

/-- Object1's properties in the paper's order. -/
def properties : List (Attr × Value) :=
  [(.property .size, .large), (.property .color, .red), (.property .material, .plastic)]

/-- The greedy heuristic selects plastic first, then large and red: *the large red plastic
cup* (§3.1.2). -/
theorem greedy_cups :
    greedy kb contrast properties =
      some {(.property .material, .plastic), (.property .size, .large),
        (.property .color, .red)} := by
  decide +kernel

/-- *The large red cup* is the shortest description (§3.1.2). -/
theorem large_red_isShortest :
    IsShortest kb .object1 contrast {(.property .size, .large), (.property .color, .red)} :=
  isShortest_of_card_two (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The greedy result distinguishes Object1 but carries an unnecessary pair (§3.1.2,
§3.2.1). -/
theorem greedy_not_noUnnecessary :
    Distinguishing kb .object1 contrast
        {(.property .material, .plastic), (.property .size, .large),
          (.property .color, .red)} ∧
      ¬ NoUnnecessary kb .object1 contrast
        {(.property .material, .plastic), (.property .size, .large),
          (.property .color, .red)} := by
  decide +kernel

end Cup

/-! #### The white bird (§3.2.1) -/

/-- A picture of a white bird, a black cup and a white cup. -/
inductive Picture where
  | bird | blackCup | whiteCup
  deriving DecidableEq, Repr

namespace Picture

/-- Type and colour of each object. -/
def kb : KB Picture Attr Value
  | .bird, .type => some .bird
  | .bird, .property .color => some .white
  | .blackCup, .type => some .cup
  | .blackCup, .property .color => some .black
  | .whiteCup, .type => some .cup
  | .whiteCup, .property .color => some .white
  | _, _ => none

/-- The contrast set. -/
def contrast : Finset Picture := {.blackCup, .whiteCup}

/-- A speaker who scans the black cup first says *white*, then *bird* to rule out the white
cup, although *bird* alone would do: colour before type yields *the white bird*, type before
colour *the bird* (§3.2.1). -/
theorem makeReferringExpression_picture :
    (Domain.flat kb .type).makeReferringExpression .bird contrast [.property .color, .type] =
      some {(.property .color, .white), (.type, .bird)} ∧
    (Domain.flat kb .type).makeReferringExpression .bird contrast [.type, .property .color] =
      some {(.type, .bird)} := by
  decide +kernel

/-- The colour-first output contains an unnecessary modifier, the behaviour of
Observation 1 that Full Brevity and Local Brevity never produce (§3.2.1). -/
theorem white_bird_not_noUnnecessary :
    ¬ NoUnnecessary kb .bird contrast {(.property .color, .white), (.type, .bird)} ∧
    NoUnnecessary kb .bird contrast {(.type, .bird)} := by
  decide +kernel

end Picture

end DaleReiter1995
