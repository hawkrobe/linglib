import Linglib.Theories.Phonology.Constraints
import Linglib.Fragments.Tagalog.Phonology

/-!
# @cite{zuraw-2010}: Factorial Typology of Nasal Substitution

Formalizes the factorial typology of Tagalog-style nasal substitution
from @cite{zuraw-2010} (NLLT 28: 417–472). When a nasal-final prefix
(e.g. maŋ-) is concatenated with an obstruent-initial stem, the nasal
and the obstruent may **coalesce** into a single nasal retaining the
place of the latter:

- `maŋ+bigáj` → `mamigáj` 'to distribute' (nasal substitution = YES)
- `paŋ+tabój` → `pantabój` 'to goad' (faithful cluster = NO)

## Constraint set

Six constraints drive the typology:

- **\*NC** (markedness): penalizes all nasal + obstruent clusters
- **\*NC̥** (markedness): penalizes nasal + voiceless obstruent clusters
- **\*ASSOC** (markedness): penalizes multiple association (coalescence)
- **\*\[ŋ, \*\[n, \*\[m** (markedness, stringent hierarchy): penalizes
  stem-initial nasals resulting from coalescence, with *\[m most inclusive
  (penalizes all nasals) and *\[ŋ least inclusive (penalizes velar only)

The stringent *\[N hierarchy is defined following Prince's (1997)
stringency theory: "*\[n" means "a stem must not begin with n or a
backer nasal", so *\[n penalizes both n and ŋ but not m. Similarly,
*\[m penalizes m, n, and ŋ (all nasals).

## Factorial typology

With 6 constraints, there are 720 rankings generating exactly **10 distinct
substitution patterns** over 6 stem-initial consonants {p, t, k, b, d, g}.
The 10 patterns satisfy two implicational universals:

1. **Voicing effect**: if a voiced C undergoes substitution, the voiceless
   C at the same place also does (e.g., b→YES implies p→YES).
2. **Place effect**: if a backer C undergoes substitution, all fronter Cs
   also do (within voicing class: k→t→p and g→d→b). Labials are easiest
   to substitute (least *\[N cost), velars hardest (most *\[N cost).

## Dictionary data

@cite{zuraw-2010}'s Tagalog dictionary counts confirm the voicing effect:
voiceless stems show higher substitution rates than voiced stems at the
labial place (p: 253/263 vs b: 177/277).
-/

namespace Phenomena.PhonologicalAlternation.Studies.Zuraw2010

open Core.OT Core.ConstraintEvaluation Theories.Phonology.Constraints
open Fragments.Tagalog.Phonology (StemC SubSt NSCand dictRate_p dictRate_b dict_voicing_labial)

-- ============================================================================
-- § 1: Constraints
-- ============================================================================

/-- *NC: penalizes all nasal + obstruent sequences.
    Violated by NO (the faithful output preserves the NC cluster). -/
def starNC : NamedConstraint NSCand :=
  mkMark "*NC" fun | (_, .no) => true | _ => false

/-- *NC̥: penalizes nasal + voiceless obstruent sequences.
    Violated by NO for voiceless stems only. -/
def starNCvoiceless : NamedConstraint NSCand :=
  mkMark "*NC̥" fun | (.p, .no) | (.t, .no) | (.k, .no) => true | _ => false

/-- *ASSOC: penalizes multiple association (coalescence).
    Violated by YES for all stems. On this 6-consonant domain, *ASSOC
    has the same violation profile as *\[m (both assign 1 to every YES
    candidate). They remain distinct constraints because they encode
    different linguistic generalizations and their co-presence affects
    factorial percentages. -/
def starAssoc : NamedConstraint NSCand :=
  mkMark "*ASSOC" fun | (_, .yes) => true | _ => false

/-- *\[ŋ: "A stem must not begin with ŋ or a backer nasal."
    Least inclusive member of the stringent *\[N hierarchy.
    Violated by YES for velar stems only (coalescence yields ŋ). -/
def starInitVelar : NamedConstraint NSCand :=
  mkMark "*[ŋ" fun | (.k, .yes) | (.g, .yes) => true | _ => false

/-- *\[n: "A stem must not begin with n or a backer nasal."
    Middle member of the stringent *\[N hierarchy.
    Violated by YES for coronal and velar stems (coalescence yields
    n or ŋ, both at or backer than n). -/
def starInitCorVel : NamedConstraint NSCand :=
  mkMark "*[n" fun
    | (.t, .yes) | (.d, .yes) | (.k, .yes) | (.g, .yes) => true | _ => false

/-- *\[m: "A stem must not begin with m or a backer nasal."
    Most inclusive member of the stringent *\[N hierarchy.
    Violated by YES for all stems (coalescence always yields a nasal,
    and every nasal is m or backer). -/
def starInitAll : NamedConstraint NSCand :=
  mkMark "*[m" fun | (_, .yes) => true | _ => false

/-- The six constraints forming the factorial typology. -/
def allConstraints : List (NamedConstraint NSCand) :=
  [starNC, starNCvoiceless, starAssoc, starInitVelar, starInitCorVel, starInitAll]

-- ============================================================================
-- § 2: Constraint Violation Profiles
-- ============================================================================

/-- The stringent *\[N hierarchy assigns increasing violation counts
    to nasals at backer places: labial m incurs 1 violation (*\[m only),
    coronal n incurs 2 (*\[n + *\[m), velar ŋ incurs 3 (*\[ŋ + *\[n + *\[m).
    This makes labials easiest to substitute and velars hardest. -/
theorem stringency_violations :
    starInitAll.eval (.p, .yes) + starInitCorVel.eval (.p, .yes) +
      starInitVelar.eval (.p, .yes) = 1 ∧
    starInitAll.eval (.t, .yes) + starInitCorVel.eval (.t, .yes) +
      starInitVelar.eval (.t, .yes) = 2 ∧
    starInitAll.eval (.k, .yes) + starInitCorVel.eval (.k, .yes) +
      starInitVelar.eval (.k, .yes) = 3 := by decide

/-- *ASSOC and *\[m have identical violation profiles on the 6-consonant
    domain (both penalize every YES candidate). -/
theorem assoc_eq_initAll (c : StemC) (s : SubSt) :
    starAssoc.eval (c, s) = starInitAll.eval (c, s) := by
  cases c <;> cases s <;> rfl

-- ============================================================================
-- § 3: Factorial Typology
-- ============================================================================

/-- A substitution pattern: for each of the 6 consonants, whether
    substitution is optimal (true = YES wins). -/
structure SubPattern where
  sub_p : Bool
  sub_t : Bool
  sub_k : Bool
  sub_b : Bool
  sub_d : Bool
  sub_g : Bool
  deriving DecidableEq, Repr

/-- Determine whether YES wins over NO for a given consonant under a ranking. -/
def subWins (ranking : List (NamedConstraint NSCand)) (c : StemC) : Bool :=
  lexLT (buildProfile ranking (c, .yes)) (buildProfile ranking (c, .no))

/-- Extract the substitution pattern for a given ranking. -/
def patternOf (ranking : List (NamedConstraint NSCand)) : SubPattern where
  sub_p := subWins ranking .p
  sub_t := subWins ranking .t
  sub_k := subWins ranking .k
  sub_b := subWins ranking .b
  sub_d := subWins ranking .d
  sub_g := subWins ranking .g

/-- All distinct substitution patterns generated by the factorial typology. -/
def factorialPatterns : List SubPattern :=
  ((permutations allConstraints).map patternOf).eraseDups

/-- The factorial typology generates exactly 10 language types (Table 5). -/
theorem ten_language_types : factorialPatterns.length = 10 := by native_decide

-- ============================================================================
-- § 4: Named Patterns (Table 5)
-- ============================================================================

/-- Pattern a: no substitution for any consonant. -/
def pat_a : SubPattern where
  sub_p := false; sub_t := false; sub_k := false
  sub_b := false; sub_d := false; sub_g := false

/-- Pattern b: substitution for labial voiceless only (p).
    Attested in Da'a (@cite{zuraw-2010} Table 5). -/
def pat_b : SubPattern where
  sub_p := true; sub_t := false; sub_k := false
  sub_b := false; sub_d := false; sub_g := false

/-- Pattern c: substitution for both labials (p, b).
    Attested in Wolio (@cite{zuraw-2010} Table 5). -/
def pat_c : SubPattern where
  sub_p := true; sub_t := false; sub_k := false
  sub_b := true; sub_d := false; sub_g := false

/-- Pattern d: substitution for voiceless labial + coronal (p, t).
    Attested in Balantak (@cite{zuraw-2010} Table 5). -/
def pat_d : SubPattern where
  sub_p := true; sub_t := true; sub_k := false
  sub_b := false; sub_d := false; sub_g := false

/-- Pattern e: substitution for p, t, b.
    Attested in Toba Batak (@cite{zuraw-2010} Table 5). -/
def pat_e : SubPattern where
  sub_p := true; sub_t := true; sub_k := false
  sub_b := true; sub_d := false; sub_g := false

/-- Pattern f: substitution for p, t, b, d.
    Attested in Cebuano (@cite{zuraw-2010} Table 5). -/
def pat_f : SubPattern where
  sub_p := true; sub_t := true; sub_k := false
  sub_b := true; sub_d := true; sub_g := false

/-- Pattern g: substitution for all voiceless (p, t, k).
    Attested in Bolaang Mongondow (@cite{zuraw-2010} Table 5). -/
def pat_g : SubPattern where
  sub_p := true; sub_t := true; sub_k := true
  sub_b := false; sub_d := false; sub_g := false

/-- Pattern h: substitution for p, t, k, b.
    Attested in Ratahan (@cite{zuraw-2010} Table 5). -/
def pat_h : SubPattern where
  sub_p := true; sub_t := true; sub_k := true
  sub_b := true; sub_d := false; sub_g := false

/-- Pattern i: substitution for p, t, k, b, d.
    Attested in Pendau (@cite{zuraw-2010} Table 5). -/
def pat_i : SubPattern where
  sub_p := true; sub_t := true; sub_k := true
  sub_b := true; sub_d := true; sub_g := false

/-- Pattern j: substitution for all consonants.
    Attested in Tagalog, Indonesian, Malay (@cite{zuraw-2010} Table 5). -/
def pat_j : SubPattern where
  sub_p := true; sub_t := true; sub_k := true
  sub_b := true; sub_d := true; sub_g := true

/-- All 10 named patterns appear in the factorial typology. -/
theorem all_patterns_attested :
    [pat_j, pat_g, pat_a, pat_i, pat_f, pat_d, pat_h, pat_e, pat_c, pat_b] =
    factorialPatterns := by native_decide

-- ============================================================================
-- § 5: Implicational Universals
-- ============================================================================

/-- **Voicing effect**: for every pattern in the typology, if a voiced
    consonant undergoes substitution then its voiceless counterpart does too.
    E.g., b→YES implies p→YES. -/
theorem voicing_effect : ∀ pat ∈ factorialPatterns,
    (pat.sub_b → pat.sub_p) ∧ (pat.sub_d → pat.sub_t) ∧
    (pat.sub_g → pat.sub_k) := by native_decide

/-- **Place effect (voiceless)**: among voiceless consonants, if a backer
    place undergoes substitution then all fronter places do too.
    k→YES implies t→YES implies p→YES. -/
theorem place_effect_voiceless : ∀ pat ∈ factorialPatterns,
    (pat.sub_k → pat.sub_t) ∧ (pat.sub_t → pat.sub_p) := by native_decide

/-- **Place effect (voiced)**: among voiced consonants, if a backer
    place undergoes substitution then all fronter places do too.
    g→YES implies d→YES implies b→YES. -/
theorem place_effect_voiced : ∀ pat ∈ factorialPatterns,
    (pat.sub_g → pat.sub_d) ∧ (pat.sub_d → pat.sub_b) := by native_decide

/-- The voicing and place effects together imply that if g undergoes
    substitution, every other consonant does too (pattern j is the only
    pattern where g = YES). -/
theorem g_implies_all : ∀ pat ∈ factorialPatterns,
    pat.sub_g → pat.sub_p ∧ pat.sub_t ∧ pat.sub_k ∧
                 pat.sub_b ∧ pat.sub_d ∧ pat.sub_g := by native_decide

-- ============================================================================
-- § 6: Factorial Percentages
-- ============================================================================

/-- Count how many of the 720 rankings produce substitution for consonant c. -/
def subCount (c : StemC) : Nat :=
  ((permutations allConstraints).filter fun r => subWins r c).length

/-- Factorial percentage of rankings favoring substitution for each
    consonant. The percentages strictly decrease from labials to velars
    within each voicing class, and voiceless > voiced at each place.
    Values match @cite{zuraw-2010} footnote 17. -/
theorem factorial_percentages :
    subCount .p = 360 ∧ subCount .t = 288 ∧ subCount .k = 240 ∧
    subCount .b = 240 ∧ subCount .d = 180 ∧ subCount .g = 144 := by native_decide

/-- The factorial percentages as fractions of 720 total rankings:
    p=50%, t=40%, k=33⅓%, b=33⅓%, d=25%, g=20%. -/
theorem factorial_rates :
    (subCount .p : ℚ) / 720 = 1/2 ∧
    (subCount .t : ℚ) / 720 = 2/5 ∧
    (subCount .k : ℚ) / 720 = 1/3 ∧
    (subCount .b : ℚ) / 720 = 1/3 ∧
    (subCount .d : ℚ) / 720 = 1/4 ∧
    (subCount .g : ℚ) / 720 = 1/5 := by native_decide

/-- Place monotonicity: the factorial percentage strictly decreases
    from labial to velar within each voicing class. -/
theorem place_monotonicity :
    subCount .p > subCount .t ∧ subCount .t > subCount .k ∧
    subCount .b > subCount .d ∧ subCount .d > subCount .g := by native_decide

/-- Voicing monotonicity: voiceless substitution percentage is at least
    as high as voiced at every place. -/
theorem voicing_monotonicity :
    subCount .p ≥ subCount .b ∧ subCount .t ≥ subCount .d ∧
    subCount .k ≥ subCount .g := by native_decide

-- ============================================================================
-- § 7: Connection to Tagalog
-- ============================================================================

-- Dictionary data (dictRate_p, dictRate_b, dict_voicing_labial) is in
-- `Fragments.Tagalog.Phonology` and re-exported via the `open` above.

/-- Tagalog exhibits nasal substitution for all six consonants,
    corresponding to pattern j — the maximal substitution pattern.
    This is consistent with @cite{zuraw-2010}'s analysis where
    Tagalog's grammar ranks both *NC and *NC̥ above all anti-substitution
    constraints. The Tagalog fragment in `Fragments.Tagalog.Phonology`
    models the probabilistic (gradient) version of this pattern using
    @cite{magri-2025}'s MaxEnt analysis. -/
theorem tagalog_is_pattern_j : factorialPatterns.contains pat_j = true := by native_decide

end Phenomena.PhonologicalAlternation.Studies.Zuraw2010
