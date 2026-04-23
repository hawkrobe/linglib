import Linglib.Phenomena.SocialMeaning.IndexicalField
import Mathlib.Data.Rat.Defs

/-!
# @cite{labov-2006} — The Social Stratification of English in New York City

Cambridge University Press (2nd edition, 2006; first edition 1966).

The foundational study of quantitative sociolinguistics. Labov
establishes that linguistic variation in NYC is not "free" but forms a
highly structured system along two independent dimensions: **social
class** (measured by a composite socioeconomic index) and **contextual
style** (measured by degree of attention to speech).

## Core contributions formalized here

1. **The department store study** (Ch. 3): rapid anonymous survey showing
   (r) stratification across Saks, Macy's, and Klein employees (Table 3.4).

2. **Table 7.8 — Class stratification of the five variables** (Ch. 7,
   p. 140): the centerpiece data matrix. Five phonological variables —
   (r), (æh), (oh), (th), (dh) — measured across three class groups
   (SEC 0–2, 3–5, 6–9) and multiple contextual styles. All five show
   both class stratification and style shifting (with one notable
   exception: the lower class shows no style shifting for (oh)).

3. **The (oh) real deviation** (Ch. 7, p. 146): the lower class (0–2)
   shows no style shifting for (oh) and deviates from class stratification.
   This is the only "real deviation" in the five-variable system, providing
   evidence that (oh) is not socially significant for the lower class.
   Labov: "For the phonological variables, real deviations from class
   stratification are consistently and reciprocally associated with real
   deviations from stylistic stratification."

4. **(ing) stratification** (Ch. 10, Table 10.10): the (ing) variable as a
   Case I-A pattern — stable stigmatized feature with monotone class and
   style stratification. The sc3/sc4 anomaly in casual speech for older
   speakers (upper-middle SEC 9 uses more /in/ than lower-middle SEC 7–8)
   reflects the (ing) crossover in informal contexts.

5. **Variable typology**: all five phonological variables are markers
   (second-order indexicals showing style shifting). (r) is a change from
   above; (æh) and (oh) are changes from below; (th) and (dh) are stable.

## The crossover pattern

The most famous finding is the (r) **crossover**: in formal styles (D, D'),
the lower-middle class (SEC 6–8) *exceeds* the upper-middle class (SEC 9)
in use of the prestige variant, overshooting the target norm. This
hypercorrection is characteristic of variables undergoing change from
above. The crossover requires a finer class division (4+ groups) than
Table 7.8's three-way split, so we formalize it as a structural concept
via `StratificationProfile.hasCrossover` without stipulating the exact
numbers from the finer-grained data.
-/

set_option autoImplicit false

namespace Labov2006

open Phenomena.SocialMeaning.IndexicalField

-- ============================================================================
-- §1. Social class groups (Ch. 7, Table 7.6)
-- ============================================================================

/-- Three-group classification from Table 7.8 (p. 140).
    The 10-point SEC index collapsed into three roughly equal groups
    (N: 23, 28, 30 informants respectively). -/
inductive ClassGroup where
  | lower   -- SEC 0–2
  | working -- SEC 3–5
  | middle  -- SEC 6–9
  deriving DecidableEq, Repr, Inhabited

def ClassGroup.toNat : ClassGroup → Nat
  | .lower => 0 | .working => 1 | .middle => 2

instance : LT ClassGroup where
  lt a b := a.toNat < b.toNat

instance : LE ClassGroup where
  le a b := a.toNat ≤ b.toNat

instance (a b : ClassGroup) : Decidable (a < b) := Nat.decLt a.toNat b.toNat
instance (a b : ClassGroup) : Decidable (a ≤ b) := Nat.decLe a.toNat b.toNat

-- ============================================================================
-- §2. The department store study (Ch. 3, Table 3.4)
-- ============================================================================

/-- NYC department stores ranked by prestige. -/
inductive Store where
  | saks   -- Saks Fifth Avenue (highest prestige)
  | macys  -- Macy's (middle)
  | klein  -- S. Klein (lowest prestige)
  deriving DecidableEq, Repr

/-- Store prestige ranking: Klein < Macy's < Saks. -/
def Store.toNat : Store → Nat
  | .klein => 0 | .macys => 1 | .saks => 2

instance : LT Store where
  lt a b := a.toNat < b.toNat

instance (a b : Store) : Decidable (a < b) := Nat.decLt a.toNat b.toNat

/-- Distribution of (r) for complete responses (Table 3.4).
    Values are percentage of total responses in each category.
    N: Saks 33, Macy's 48, Klein 34. -/
structure DeptStoreResult where
  allR1  : ℚ  -- % using (r-1) in all four positions
  someR1 : ℚ  -- % using (r-1) in some positions
  noR1   : ℚ  -- % using only (r-0)

def deptStore : Store → DeptStoreResult
  | .saks  => ⟨24, 46, 30⟩
  | .macys => ⟨22, 37, 41⟩
  | .klein => ⟨ 6, 12, 82⟩

/-- Any (r-1) usage = allR1 + someR1. -/
def anyR1 (s : Store) : ℚ := (deptStore s).allR1 + (deptStore s).someR1

/-- (r) stratification: Saks > Macy's > Klein in any (r-1) usage. -/
theorem deptStore_stratification :
    anyR1 .saks > anyR1 .macys ∧ anyR1 .macys > anyR1 .klein := by
  exact ⟨by native_decide, by native_decide⟩

/-- (th) stops in *fourth*: Saks 0%, Macy's 4%, Klein 15%.
    Parallel stratification on an independent variable. -/
def thStopRate : Store → ℚ
  | .saks  => 0
  | .macys => 4/100
  | .klein => 15/100

theorem thStop_stratification :
    thStopRate .klein > thStopRate .macys ∧
    thStopRate .macys > thStopRate .saks := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- §3. Table 7.8 — Class stratification of the five variables (Ch. 7, p. 140)
-- ============================================================================

/-! Table 7.8 is the centerpiece of the book: five phonological variables
measured across three class groups (SEC 0–2, 3–5, 6–9) and multiple
contextual styles. Data verified against the 2nd edition PDF (p. 140).

**Index conventions** (important for interpreting directions):
- **(r)**: % (r-1) usage. Higher = more prestige form.
  5 styles (A–D'). Increases with formality and class.
- **(æh)**: vowel height × 10 (scale 10–60). Higher = lower vowel =
  closer to standard. 4 styles (A–D).
- **(oh)**: same convention as (æh). 4 styles (A–D).
- **(th)**, **(dh)**: % non-fricative (affricate + stop) forms × 100.
  Higher = more stigmatized. 3 styles (A–C). -/

section table7_8

-- --------------------------------------------------------------------------
-- (r): postvocalic /r/
-- --------------------------------------------------------------------------

/-- (r) index from Table 7.8. % (r-1) usage; higher = more prestige. -/
def r_index : ClassGroup → ContextualStyle → ℚ
  | .lower,   .casual      => 5/2     -- 02.5
  | .lower,   .careful     => 21/2    -- 10.5
  | .lower,   .reading     => 29/2    -- 14.5
  | .lower,   .wordList    => 47/2    -- 23.5
  | .lower,   .minimalPair => 99/2    -- 49.5
  | .working, .casual      => 4       -- 04.0
  | .working, .careful     => 25/2    -- 12.5
  | .working, .reading     => 21      -- 21.0
  | .working, .wordList    => 35      -- 35.0
  | .working, .minimalPair => 55      -- 55.0
  | .middle,  .casual      => 25/2    -- 12.5
  | .middle,  .careful     => 25      -- 25.0
  | .middle,  .reading     => 29      -- 29.0
  | .middle,  .wordList    => 111/2   -- 55.5
  | .middle,  .minimalPair => 70      -- 70.0

/-- (r) class stratification: middle > working > lower at every style.
    Higher class uses more of the prestige form (r-1) (Figure 7.1). -/
theorem r_class_stratified :
    (∀ s : ContextualStyle, r_index .middle s > r_index .working s) ∧
    (∀ s : ContextualStyle, r_index .working s > r_index .lower s) := by
  exact ⟨by intro s; cases s <;> native_decide,
         by intro s; cases s <;> native_decide⟩

/-- (r) style shifting: every class uses more (r-1) in formal styles. -/
theorem r_style_shift :
    ∀ g : ClassGroup,
      r_index g .casual < r_index g .careful ∧
      r_index g .careful < r_index g .reading ∧
      r_index g .reading < r_index g .wordList ∧
      r_index g .wordList < r_index g .minimalPair := by
  intro g; cases g <;>
    exact ⟨by native_decide, by native_decide,
           by native_decide, by native_decide⟩

-- --------------------------------------------------------------------------
-- (æh): the vowel of *bad, bag, ask, pass, cash, dance*
-- --------------------------------------------------------------------------

/-- (æh) index from Table 7.8, per style. Vowel height × 10;
    higher = lower vowel = closer to standard.
    4 styles (A–D); no minimal pair data. -/
def aeh_A : ClassGroup → ℚ | .lower => 23 | .working => 25 | .middle => 27
def aeh_B : ClassGroup → ℚ | .lower => 27 | .working => 28 | .middle => 30
def aeh_C : ClassGroup → ℚ | .lower => 29 | .working => 61/2 | .middle => 34
def aeh_D : ClassGroup → ℚ | .lower => 32 | .working => 32 | .middle => 35

/-- (æh) class stratification: middle > working > lower at styles A–C
    (higher index = closer to standard = less stigmatized; Figure 7.2).
    At Style D (word lists), lower and working converge (both 32). -/
theorem aeh_class_stratified :
    (aeh_A .lower < aeh_A .working ∧ aeh_A .working < aeh_A .middle) ∧
    (aeh_B .lower < aeh_B .working ∧ aeh_B .working < aeh_B .middle) ∧
    (aeh_C .lower < aeh_C .working ∧ aeh_C .working < aeh_C .middle) ∧
    (aeh_D .lower ≤ aeh_D .working ∧ aeh_D .working < aeh_D .middle) := by
  exact ⟨⟨by native_decide, by native_decide⟩,
         ⟨by native_decide, by native_decide⟩,
         ⟨by native_decide, by native_decide⟩,
         ⟨by native_decide, by native_decide⟩⟩

/-- (æh) style shifting: every class shifts toward standard (higher)
    in more formal styles. A < B < C < D for all three classes. -/
theorem aeh_style_shift :
    ∀ g : ClassGroup,
      aeh_A g < aeh_B g ∧ aeh_B g < aeh_C g ∧ aeh_C g < aeh_D g := by
  intro g; cases g <;>
    exact ⟨by native_decide, by native_decide, by native_decide⟩

-- --------------------------------------------------------------------------
-- (oh): the vowel of *caught, talk, awed, dog, off, lost, all*
-- --------------------------------------------------------------------------

/-- (oh) index from Table 7.8. Same convention as (æh): higher = closer
    to standard. 4 styles (A–D). The lower class (0–2) shows the "real
    deviation" — no style shifting and inverted class stratification. -/
def oh_A : ClassGroup → ℚ | .lower => 23 | .working => 22 | .middle => 20
def oh_B : ClassGroup → ℚ | .lower => 24 | .working => 39/2 | .middle => 47/2
def oh_C : ClassGroup → ℚ | .lower => 24 | .working => 23 | .middle => 53/2
def oh_D : ClassGroup → ℚ | .lower => 21 | .working => 24 | .middle => 59/2

/-- The (oh) *real deviation* (@cite{labov-2006} Ch. 7, p. 146):
    the lower class does not treat (oh) as a socially significant variable.

    Three key properties:
    1. **No style shift**: lower class D (21) < A (23) — they move AWAY from
       standard in formal speech (the opposite of style shifting).
    2. **Middle class style shift**: middle class shifts dramatically from
       20 (A) to 29.5 (D), showing normal style correction.
    3. **Inverted class stratification**: in casual speech (A), the middle
       class (20) has LOWER (oh) values (= more raised = more NYC) than
       the lower class (23), inverting the expected pattern where the
       lower class should be most NYC.

    Labov: "it is oriented neither towards the class structure nor the
    stylistic structure." -/
theorem oh_real_deviation :
    -- 1. Lower class: no style shift (D < A — opposite direction)
    oh_D .lower < oh_A .lower ∧
    -- 2. Middle class: strong style shift (D >> A)
    oh_D .middle > oh_A .middle ∧
    -- 3. Class inversion at Style A: middle more NYC than lower
    oh_A .middle < oh_A .lower := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Despite the real deviation, the working and middle classes show
    regular style shifting for (oh): values increase from A to D
    (shifting toward standard in more formal styles). -/
theorem oh_regular_shift_working_middle :
    (oh_A .working < oh_D .working) ∧
    (oh_A .middle < oh_D .middle) := by
  exact ⟨by native_decide, by native_decide⟩

-- --------------------------------------------------------------------------
-- (th): the initial consonant of *thing, think, through*
-- --------------------------------------------------------------------------

/-- (th) index from Table 7.8. % non-fricative forms × 100;
    higher = more stigmatized. 3 styles only (A–C). -/
def th_A : ClassGroup → ℚ | .lower => 78 | .working => 68 | .middle => 51/2
def th_B : ClassGroup → ℚ | .lower => 65 | .working => 107/2 | .middle => 33/2
def th_C : ClassGroup → ℚ | .lower => 87/2 | .working => 27 | .middle => 10

/-- (th) class stratification: lower > working > middle at every style.
    The three class lines show regular separation (Figure 7.4). -/
theorem th_class_stratified :
    (th_A .lower > th_A .working ∧ th_A .working > th_A .middle) ∧
    (th_B .lower > th_B .working ∧ th_B .working > th_B .middle) ∧
    (th_C .lower > th_C .working ∧ th_C .working > th_C .middle) := by
  exact ⟨⟨by native_decide, by native_decide⟩,
         ⟨by native_decide, by native_decide⟩,
         ⟨by native_decide, by native_decide⟩⟩

/-- (th) style shifting: every class uses fewer stops in more formal
    styles. A > B > C for all three classes. -/
theorem th_style_shift :
    ∀ g : ClassGroup, th_A g > th_B g ∧ th_B g > th_C g := by
  intro g; cases g <;> exact ⟨by native_decide, by native_decide⟩

-- --------------------------------------------------------------------------
-- (dh): the initial consonant of *the, then, they*
-- --------------------------------------------------------------------------

/-- (dh) index from Table 7.8. Same convention as (th). 3 styles (A–C). -/
def dh_A : ClassGroup → ℚ | .lower => 157/2 | .working => 127/2 | .middle => 59/2
def dh_B : ClassGroup → ℚ | .lower => 56 | .working => 89/2 | .middle => 33/2
def dh_C : ClassGroup → ℚ | .lower => 49 | .working => 34 | .middle => 13

/-- (dh) class stratification: lower > working > middle at every style.
    Roughly parallel separation through all three styles (Figure 7.5). -/
theorem dh_class_stratified :
    (dh_A .lower > dh_A .working ∧ dh_A .working > dh_A .middle) ∧
    (dh_B .lower > dh_B .working ∧ dh_B .working > dh_B .middle) ∧
    (dh_C .lower > dh_C .working ∧ dh_C .working > dh_C .middle) := by
  exact ⟨⟨by native_decide, by native_decide⟩,
         ⟨by native_decide, by native_decide⟩,
         ⟨by native_decide, by native_decide⟩⟩

/-- (dh) style shifting: every class uses fewer stops in more formal
    styles. A > B > C for all three classes. -/
theorem dh_style_shift :
    ∀ g : ClassGroup, dh_A g > dh_B g ∧ dh_B g > dh_C g := by
  intro g; cases g <;> exact ⟨by native_decide, by native_decide⟩

end table7_8

-- ============================================================================
-- §4. Variable typology (Ch. 2, Ch. 7, Ch. 10)
-- ============================================================================

/-- The five phonological variables of the NYC study.
    All five show both class stratification and style shifting in Table 7.8,
    making them second-order indexicals (markers). -/
inductive NYCVariable where
  | r    -- postvocalic /r/: binary (0/1)
  | aeh  -- (æh): 6-point height scale
  | oh   -- (oh): 6-point height scale
  | th   -- (th): 3-variant (fricative/affricate/stop)
  | dh   -- (dh): 3-variant (fricative/affricate/stop)
  deriving DecidableEq, Repr

/-- Classification of each variable by indexical order and change
    status, following @cite{labov-2006} Ch. 7.

    All five variables show style shifting (Table 7.8), making them
    markers (second-order). The lower class's "real deviation" for (oh)
    means (oh) is not a marker *for that group*, but the variable is
    a marker for the community overall.

    The change status reflects the direction and social mechanism:
    * (r): new prestige feature spreading from highest-status group →
      change from above
    * (æh): raised variant spreading from interior groups, below
      conscious awareness → change from below
    * (oh): raised variant spreading from interior groups, below
      conscious awareness → change from below
    * (th), (dh): stable stigmatized features, no change in apparent
      time → stable -/
def variableBehavior : NYCVariable → VariableBehavior
  | .r   => ⟨.second, .changeFromAbove⟩
  | .aeh => ⟨.second, .changeFromBelow⟩
  | .oh  => ⟨.second, .changeFromBelow⟩
  | .th  => ⟨.second, .stable⟩
  | .dh  => ⟨.second, .stable⟩

/-- All five NYC variables are markers (second-order indexicals). -/
theorem all_markers (v : NYCVariable) : (variableBehavior v).isMarker := by
  cases v <;> rfl

/-- (r) is undergoing change from above. -/
theorem r_changeFromAbove :
    (variableBehavior .r).change = .changeFromAbove := rfl

/-- (th) and (dh) are stable. -/
theorem th_stable : (variableBehavior .th).change = .stable := rfl
theorem dh_stable : (variableBehavior .dh).change = .stable := rfl

/-- (æh) and (oh) are changes from below. -/
theorem aeh_changeFromBelow :
    (variableBehavior .aeh).change = .changeFromBelow := rfl
theorem oh_changeFromBelow :
    (variableBehavior .oh).change = .changeFromBelow := rfl

-- ============================================================================
-- §5. (ing) stratification (Ch. 10, Table 10.10)
-- ============================================================================

/-- Average (ing) indexes by age and social class for adult white NYC
    informants (Table 10.10, p. 258). The index is percent /in/ forms (0–100).
    SC 1 = SEC 0–2, SC 2 = SEC 3–6, SC 3 = SEC 7–8, SC 4 = SEC 9.

    Note: the SC grouping for (ing) differs from the three-way split in
    Table 7.8 (0–2 / 3–5 / 6–9). Table 10.10 splits the middle range
    differently (3–6 / 7–8) and isolates SEC 9 as its own group. -/
structure INGDatum where
  sc1 : ℚ  -- SEC 0–2 (lower)
  sc2 : ℚ  -- SEC 3–6 (working)
  sc3 : ℚ  -- SEC 7–8 (lower-middle)
  sc4 : ℚ  -- SEC 9 (upper-middle)

/-- (ing) in Style A (casual speech), ages 20–39 (Table 10.10). -/
def ing_A_young : INGDatum where
  sc1 := 90; sc2 := 60; sc3 := 43; sc4 := 0

/-- (ing) in Style A (casual speech), ages 40+ (Table 10.10). -/
def ing_A_older : INGDatum where
  sc1 := 85; sc2 := 48; sc3 := 21; sc4 := 23

/-- (ing) in Style B (careful speech), ages 20–39 (Table 10.10). -/
def ing_B_young : INGDatum where
  sc1 := 75; sc2 := 45; sc3 := 50; sc4 := 2

/-- (ing) in Style B (careful speech), ages 40+ (Table 10.10). -/
def ing_B_older : INGDatum where
  sc1 := 50; sc2 := 27; sc3 := 12; sc4 := 2

/-- (ing) is monotonically stratified in Style A for young speakers:
    lower class > working > lower-middle > upper-middle. -/
theorem ing_A_young_stratified :
    ing_A_young.sc1 > ing_A_young.sc2 ∧
    ing_A_young.sc2 > ing_A_young.sc3 ∧
    ing_A_young.sc3 > ing_A_young.sc4 := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- (ing) stratification in Style A for older speakers: sc1 > sc2 > sc3,
    but sc4 (23) > sc3 (21) — upper-middle class (SEC 9) uses MORE /in/
    than lower-middle class (SEC 7–8) in casual speech. This is the (ing)
    crossover: the lower-middle class hypercorrects even in casual speech
    (dropping /in/ below the upper-middle class rate), while the upper-middle
    class does not. -/
theorem ing_A_older_anomaly :
    ing_A_older.sc1 > ing_A_older.sc2 ∧
    ing_A_older.sc2 > ing_A_older.sc3 ∧
    ing_A_older.sc4 > ing_A_older.sc3 := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- (ing) is monotonically stratified in Style B for older speakers.
    Unlike Style A, there is no sc3/sc4 anomaly. -/
theorem ing_B_older_stratified :
    ing_B_older.sc1 > ing_B_older.sc2 ∧
    ing_B_older.sc2 > ing_B_older.sc3 ∧
    ing_B_older.sc3 ≥ ing_B_older.sc4 := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Style shifting: each class uses less /in/ in careful (B) than
    casual (A) speech, for older speakers. -/
theorem ing_styleShift_older :
    ing_A_older.sc1 > ing_B_older.sc1 ∧
    ing_A_older.sc2 > ing_B_older.sc2 ∧
    ing_A_older.sc3 > ing_B_older.sc3 ∧
    ing_A_older.sc4 > ing_B_older.sc4 := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- --------------------------------------------------------------------------
-- (ing) as StratificationProfile (demonstrating Core infrastructure)
-- --------------------------------------------------------------------------

inductive INGStyle where | A | B
  deriving DecidableEq, Repr

/-- Four-group SEC classification used in the (ing) data.
    (Different grouping from `ClassGroup`: SC2 = SEC 3–6.) -/
inductive INGClass where | sc1 | sc2 | sc3 | sc4
  deriving DecidableEq, Repr

def INGClass.toNat : INGClass → Nat
  | .sc1 => 0 | .sc2 => 1 | .sc3 => 2 | .sc4 => 3

instance : LT INGClass where
  lt a b := a.toNat < b.toNat

instance (a b : INGClass) : Decidable (a < b) := Nat.decLt a.toNat b.toNat

def ingProfile_older : StratificationProfile INGClass INGStyle where
  index c s := match c, s with
    | .sc1, .A => 85 | .sc1, .B => 50
    | .sc2, .A => 48 | .sc2, .B => 27
    | .sc3, .A => 21 | .sc3, .B => 12
    | .sc4, .A => 23 | .sc4, .B =>  2

/-- (ing) style shifting (StratificationProfile predicate): every class
    uses less /in/ in careful (B) than casual (A) speech. -/
theorem ingProfile_hasStyleShift :
    ingProfile_older.index .sc1 .A > ingProfile_older.index .sc1 .B ∧
    ingProfile_older.index .sc2 .A > ingProfile_older.index .sc2 .B ∧
    ingProfile_older.index .sc3 .A > ingProfile_older.index .sc3 .B ∧
    ingProfile_older.index .sc4 .A > ingProfile_older.index .sc4 .B := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- (ing) class stratification in Style B: monotonically decreasing.
    sc1 > sc2 > sc3 ≥ sc4. Unlike Style A, no sc3/sc4 anomaly. -/
theorem ingProfile_classStrat_B :
    ingProfile_older.index .sc1 .B > ingProfile_older.index .sc2 .B ∧
    ingProfile_older.index .sc2 .B > ingProfile_older.index .sc3 .B ∧
    ingProfile_older.index .sc3 .B ≥ ingProfile_older.index .sc4 .B := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- (ing) is a marker (second-order): it shows both social stratification
    and style shifting. Classified as Case I-A by @cite{labov-2006} —
    a stigmatized feature not involved in change. -/
def ing_behavior : VariableBehavior where
  order := .second
  change := .stable

theorem ing_isMarker : ing_behavior.isMarker := rfl

end Labov2006
