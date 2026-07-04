import Linglib.Core.Probability.Scores
import Linglib.Pragmatics.RSA.Channel

/-!
# [schlotterbeck-wang-2023] — incremental RSA for adjective ordering
[cohn-gordon-goodman-potts-2019] [degen-etal-2020] [waldon-degen-2021]

Schlotterbeck, F. & Wang, H. (2023). An incremental RSA model for adjective
ordering preferences in referential visual context. *SCiL* 6, 121–132.

**Scope.** This file formalizes the *symmetric-PoE sanity-check slice* of
the paper, not its main asymmetric model: the order-independence of the
incremental listener under symmetric per-class semantics, plus
discrimination-driven ordering preferences at the speaker level as
chain-rule trajectory products (per-step normalized; the paper's `S1^inc`
normalizes once globally, and the two agree at the literal layer). Not
formalized: asymmetric per-class semantics, the `P_Lang` grammaticality
filter, and the size-first utterance-prior bias. The paper's α is the
utterance-level softmax temperature; its β (word-level) is 1 in all
reported simulations, matching the exponent-free chain here.

## Main results

* `meaning_perm`: the PoE prefix meaning is order-independent, for every
  lexicon — the paper's listener-level sanity check.
* `size_first_when_size_discriminates` / `color_first_when_color_reliable`:
  the trajectory preference tracks discriminatory power (Scene A) and
  flips to the more reliable dimension under equal discrimination
  (Scene B); `ordering_preference_flips` conjoins them.
* `big_more_informative_A` / `blue_more_informative_B`: the first-word
  preferences driving the flip.
* `both_orderings_identify_target_A`/`_B`: after both adjectives the
  target carries the highest meaning among scene members.

## Implementation notes

The chain is exact ℚ≥0: `lex` is the Bernoulli-channel form of
[degen-etal-2020]'s continuous semantics (reliability if the word truly
applies, the complementary noise floor otherwise), prefix meanings are
`List` products, `l0Score`/`s1Score` normalize via `PMF.normalizeScores`,
and the PMF speaker is `PMF.ofScores`. Trajectories are `Fin`-indexed
products of speaker values, so ordering predictions close by
`PMF.prod_ofScores_lt` with one kernel certificate each.
-/

open scoped ENNReal NNRat

namespace SchlotterbeckWang2023

/-- Referents in the reference game. -/
inductive Referent where
  | bigBlue | bigGreen | smallBlue | smallGreen | smallRed
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Referent := ⟨.bigBlue⟩

/-- Words available to the speaker: size adjectives, color adjectives, noun. -/
inductive Word where
  | big | small | blue | green | red | sticker
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.sticker⟩

/-- Whether a word is veridically true of a referent. -/
def wordApplies : Word → Referent → Bool
  | .big,     .bigBlue  | .big,     .bigGreen  => true
  | .small,   .smallBlue | .small,  .smallGreen | .small, .smallRed => true
  | .blue,    .bigBlue  | .blue,    .smallBlue  => true
  | .green,   .bigGreen | .green,   .smallGreen => true
  | .red,     .smallRed => true
  | .sticker, _         => true
  | _,        _         => false

/-- Per-class perceptual reliability: size words use `sRel`, color words
use `cRel`, the noun applies universally. -/
def rel (sRel cRel : ℚ≥0) : Word → ℚ≥0
  | .big | .small         => sRel
  | .blue | .green | .red => cRel
  | .sticker              => 1

/-- Noisy word meaning: reliability if the word truly applies, the
complementary noise floor otherwise — the Bernoulli-channel form of
[degen-etal-2020]'s continuous semantics. -/
def lex (sRel cRel : ℚ≥0) (w : Word) (r : Referent) : ℚ≥0 :=
  if wordApplies w r then rel sRel cRel w else 1 - rel sRel cRel w

/-- PoE prefix meaning: the product of per-word noisy meanings. -/
def meaning (lex : Word → Referent → ℚ≥0) (us : List Word) (r : Referent) : ℚ≥0 :=
  (us.map (lex · r)).prod

/-- The listener-level sanity check: the PoE prefix meaning is
order-independent, for every lexicon and reliability setting. -/
theorem meaning_perm (lex : Word → Referent → ℚ≥0) {us vs : List Word}
    (h : us.Perm vs) (r : Referent) : meaning lex us r = meaning lex vs r :=
  (h.map (lex · r)).prod_eq

/-! ### Scenes -/

/-- Scene A: size discriminates. Objects {big-blue, small-blue,
small-green, small-red}, so "big" uniquely identifies the target. -/
def sceneA : Referent → Bool
  | .bigBlue | .smallBlue | .smallGreen | .smallRed => true
  | _ => false

/-- Scene B: equal discrimination. Objects {big-blue, big-green,
small-blue, small-green}; "big" and "blue" each narrow to two. -/
def sceneB : Referent → Bool
  | .bigBlue | .bigGreen | .smallBlue | .smallGreen => true
  | _ => false

/-- The target referent in both scenes. -/
def target : Referent := .bigBlue

/-- Scene A lexicon: size more reliable (99/100 vs 95/100). -/
def lexA : Word → Referent → ℚ≥0 := lex (99/100) (95/100)

/-- Scene B lexicon: color more reliable (95/100 vs 80/100). -/
def lexB : Word → Referent → ℚ≥0 := lex (80/100) (95/100)

/-! ### The incremental chain -/

/-- Literal listener over scene referents at each prefix extension. -/
def l0Score (lex : Word → Referent → ℚ≥0) (scene : Referent → Bool)
    (ctx : List Word) (u : Word) : Referent → ℚ≥0 :=
  PMF.normalizeScores fun r => if scene r then meaning lex (ctx ++ [u]) r else 0

/-- Word-level speaker (β = 1, no cost): renormalized literal posteriors. -/
def s1Score (lex : Word → Referent → ℚ≥0) (scene : Referent → Bool)
    (ctx : List Word) (r : Referent) : Word → ℚ≥0 :=
  PMF.normalizeScores fun u => l0Score lex scene ctx u r

/-- Word-by-word speaker at context `ctx`. -/
noncomputable def s1 (lex : Word → Referent → ℚ≥0) (scene : Referent → Bool)
    (ctx : List Word) (r : Referent) : PMF Word :=
  .ofScores .uniform (s1Score lex scene ctx r)

/-- Trajectory probability of an utterance: the chain-rule product of
per-step speaker values along its prefixes. -/
noncomputable def s1Traj (lex : Word → Referent → ℚ≥0)
    (scene : Referent → Bool) (r : Referent) (us : List Word) : ℝ≥0∞ :=
  ∏ i : Fin us.length, s1 lex scene (us.take i.1) r (us.get i)

/-- ℚ≥0 shadow of `s1Traj`. -/
def s1TrajScore (lex : Word → Referent → ℚ≥0) (scene : Referent → Bool)
    (r : Referent) (us : List Word) : ℚ≥0 :=
  ∏ i : Fin us.length,
    PMF.scoresWith .uniform (s1Score lex scene (us.take i.1) r) (us.get i)

theorem s1Traj_lt {lex₁ lex₂ : Word → Referent → ℚ≥0}
    {sc₁ sc₂ : Referent → Bool} {r₁ r₂ : Referent} {us vs : List Word}
    (h : s1TrajScore lex₁ sc₁ r₁ us < s1TrajScore lex₂ sc₂ r₂ vs) :
    s1Traj lex₁ sc₁ r₁ us < s1Traj lex₂ sc₂ r₂ vs := by
  unfold s1Traj s1
  rw [PMF.prod_ofScores_apply, PMF.prod_ofScores_apply]
  exact_mod_cast h

/-! ### Predictions -/

/-- Size-first and color-first orderings for the big-blue target. -/
def sizeFirst : List Word := [.big, .blue, .sticker]

/-- See `sizeFirst`. -/
def colorFirst : List Word := [.blue, .big, .sticker]

/-- When size has the higher discriminatory power (Scene A), the
incremental speaker prefers the size-first ordering. -/
theorem size_first_when_size_discriminates :
    s1Traj lexA sceneA target colorFirst < s1Traj lexA sceneA target sizeFirst :=
  s1Traj_lt (by decide +kernel)

/-- Under equal discrimination with color more reliable (Scene B), the
preference flips to color-first. -/
theorem color_first_when_color_reliable :
    s1Traj lexB sceneB target sizeFirst < s1Traj lexB sceneB target colorFirst :=
  s1Traj_lt (by decide +kernel)

/-- The ordering preference tracks the scene's discriminatory structure,
not a fixed ordering rule. -/
theorem ordering_preference_flips :
    s1Traj lexA sceneA target colorFirst < s1Traj lexA sceneA target sizeFirst ∧
    s1Traj lexB sceneB target sizeFirst < s1Traj lexB sceneB target colorFirst :=
  ⟨size_first_when_size_discriminates, color_first_when_color_reliable⟩

/-- In Scene A, "big" is the more informative first word for the target. -/
theorem big_more_informative_A :
    s1 lexA sceneA [] target .blue < s1 lexA sceneA [] target .big :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- In Scene B, "blue" is the more informative first word. -/
theorem blue_more_informative_B :
    s1 lexB sceneB [] target .big < s1 lexB sceneB [] target .blue :=
  PMF.ofScores_lt _ (by decide +kernel)

/-- After both adjectives, the target carries the highest meaning among
Scene A members. -/
theorem both_orderings_identify_target_A (r : Referent)
    (hr : sceneA r = true) (hne : r ≠ target) :
    meaning lexA [.big, .blue] r < meaning lexA [.big, .blue] target := by
  cases r
  · exact absurd rfl hne
  all_goals first | exact absurd hr (by decide) | decide +kernel

/-- After both adjectives, the target carries the highest meaning among
Scene B members. -/
theorem both_orderings_identify_target_B (r : Referent)
    (hr : sceneB r = true) (hne : r ≠ target) :
    meaning lexB [.big, .blue] r < meaning lexB [.big, .blue] target := by
  cases r
  · exact absurd rfl hne
  all_goals first | exact absurd hr (by decide) | decide +kernel

/-- `lex` is the unified noise channel of `RSA.Noise` at
onMatch = reliability, onMismatch = its complement — the
[degen-etal-2020] parameterization. -/
theorem lex_as_noiseChannel {sRel cRel : ℚ≥0} (hs : sRel ≤ 1) (hc : cRel ≤ 1)
    (w : Word) (r : Referent) :
    (lex sRel cRel w r : ℚ) =
      RSA.Noise.noiseChannel (rel sRel cRel w) (1 - rel sRel cRel w)
        (if wordApplies w r then 1 else 0) := by
  have h1 : rel sRel cRel w ≤ 1 := by cases w <;> simp [rel] <;> assumption
  simp only [lex, RSA.Noise.noiseChannel]
  split <;> push_cast [NNRat.coe_sub h1] <;> ring

end SchlotterbeckWang2023
