import Linglib.Semantics.Tense.Licensing
import Linglib.Semantics.Attitudes.Acquaintance
import Mathlib.Order.Interval.Set.OrdConnected
import Linglib.Data.Examples.Abusch1997

/-!
# Sequence of tense and temporal de re

Abusch's independent theory evaluates every tense relative to the utterance time, treats tenses as
anaphoric pronouns, and interprets a tense anaphoric across an attitude de re, through an
acquaintance relation to the res time. The simultaneous reading of *Mary believed it was raining*
is then de re with the identity relation, which collapses the believed centered proposition to
rain at the believer's now (`simultaneous_deRe`). The theory cannot explain the missing
forward-shifted readings — *he thought that a burglar attacked him* cannot report a thought about
a later attack — nor past morphology without precedence, so the paper adds the upper limit
constraint (no tense denotes a time after its local evaluation time;
`forwardShifted_not_upperLimit`) and a semantics of tense over transmitted temporal relations
(`Tense.PastConstraint`,
`Tense.PresentConstraint`). The simultaneous LF is licensed non-locally by the matrix past
(`simultaneous_nonLocal`), the scope of a relative clause decides whether its past can reach a
future time (`narrowScope_forward`, `wideScope_precedes`), a present matrix forces local licensing
(`expects_local`, `expects_no_simultaneous`), and the de re and non-local LFs of the simultaneous
reading are logically equivalent (`deRe_eq_nonLocal`).

Present under past is the paper's synthesis: the non-de-re LF of *John believed that Mary is
pregnant* requires one relation both to be precedence and to exclude it
(`presentUnderPast_false`), so the present must scope out de re; the scoped tense overlaps the
utterance time, its trace obeys the upper limit constraint at the believer's now, and the
counterpart correspondence between base world and belief world eliminates every reading but the
double access one (`doubleAccess_of_counterpart`).

## References

* [abusch-1997]
* [heim-1994-comments]
* [lewis-1979-attitudes]
* [cresswell-vonstechow-1982]
* [partee-1973]
* [ogihara-1989]
-/

namespace Abusch1997

open Tense Acquaintance

variable {E W T : Type*}

/-! ### De re interpretation across attitude contexts -/

/-- The simultaneous reading of *Mary believed it was raining*: the embedded past is anaphoric
to the matrix past, hence de re, with identity to the now as acquaintance relation; the believed
centered proposition is rain at the believer's now. -/
theorem simultaneous_deRe (rain : T → W → Prop) :
    deRe (identity (E := E)) (fun t _ w => rain t w) = fun _ t w => rain t w :=
  deRe_identity _

/-! ### Transmitted temporal relations

Relation variables are numbered by the paper's superscripts, times by its indices: `0` is the
utterance time, `2` the local evaluation time of an attitude complement. -/

/-- The matrix past of *Mary believed* and *John promised*: `R¹(t₁, t₀)`. -/
def matrixPast : TemporalArgument ℕ := ⟨1, 1, 0⟩

/-- The embedded past of *it was raining* coindexed with the complement's evaluation time:
`R²(t₂, t₂)`. -/
def embeddedPast : TemporalArgument ℕ := ⟨2, 2, 2⟩

variable {ρ : RelationAssignment ℕ T} {g : ℕ → T}

/-- The simultaneous reading is licensed non-locally: the embedded relation is reflexive at the
now, so the matrix relation must be precedence — the believing precedes the utterance time and
the raining is at the believer's now. -/
theorem simultaneous_nonLocal [Preorder T] (h₁ : matrixPast.Con ρ g)
    (h₂ : embeddedPast.Con ρ g) (hp₁ : PastConstraint ρ {1}) (hp₂ : PastConstraint ρ {1, 2}) :
    g 1 < g 0 ∧ embeddedPast.NonLocallyLicensed ρ {1, 2} :=
  ⟨by simpa [matrixPast, TemporalArgument.Con, pastConstraint_singleton.1 hp₁] using h₁,
    hp₂.nonLocallyLicensed_of_coindexed h₂ rfl⟩

/-- The narrow-scope LF of *John promised to talk about the topic that the participants were
interested in*: the relative-clause past, coindexed with the talking time, is licensed by the
matrix relation, so the interest may lie after the utterance time. -/
theorem narrowScope_forward (k : ℕ) (hk : k ≠ 1) :
    ∃ (ρ : RelationAssignment ℕ ℤ) (g : ℕ → ℤ), matrixPast.Con ρ g ∧
      (⟨k, 2, 2⟩ : TemporalArgument ℕ).Con ρ g ∧ PastConstraint ρ {1} ∧
      PastConstraint ρ {1, k} ∧ (⟨k, 2, 2⟩ : TemporalArgument ℕ).UpperLimit g ∧ g 0 < g 2 :=
  ⟨fun r => if r = 1 then (· < ·) else (· = ·), fun | 0 => 0 | 1 => -5 | _ => 10,
    by show (-5 : ℤ) < 0; decide,
    by show (if k = 1 then (· < ·) else (· = ·)) (10 : ℤ) 10; simp [hk],
    pastConstraint_singleton.2 rfl, .of_mem (r := 1) (Finset.mem_insert_self _ _) rfl,
    le_refl (10 : ℤ), by show (0 : ℤ) < 10; decide⟩

/-- The wide-scope LF: the relative clause is outside the attitude, so its past has access only
to its own relation, evaluated at the utterance time — the interest precedes the utterance. -/
theorem wideScope_precedes [Preorder T] {k i : ℕ}
    (hcon : (⟨k, i, 0⟩ : TemporalArgument ℕ).Con ρ g) (hp : PastConstraint ρ {k}) : g i < g 0 := by
  simpa [TemporalArgument.Con, pastConstraint_singleton.1 hp] using hcon

/-- The matrix present of *Sue expects*: `R¹(t₁, t₀)`. -/
def matrixPresent : TemporalArgument ℕ := ⟨1, 1, 0⟩

/-- A present matrix forces local licensing: the past of *a man she met recently* must itself be
precedence, so the meeting precedes the marrying. -/
theorem expects_local [Preorder T] (h₁ : matrixPresent.Con ρ g)
    (hq : PresentConstraint ρ {1}) (hp : PastConstraint ρ {1, 3})
    (h₃ : (⟨3, 3, 2⟩ : TemporalArgument ℕ).Con ρ g) : g 3 < g 2 := by
  obtain ⟨r, hr, hρ⟩ := hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  obtain rfl | rfl := hr
  · exact absurd hρ (hq.ne_lt (Finset.mem_singleton_self _) h₁)
  · simpa [TemporalArgument.Con, hρ] using h₃

/-- *Sue expects to marry a man she loved* has no simultaneous reading: coindexing the embedded
past with the marrying time leaves no relation to license it. -/
theorem expects_no_simultaneous [Preorder T] (h₁ : matrixPresent.Con ρ g)
    (hq : PresentConstraint ρ {1}) (hp : PastConstraint ρ {1, 3})
    (h₃ : (⟨3, 2, 2⟩ : TemporalArgument ℕ).Con ρ g) : False := by
  obtain ⟨r, hr, hρ⟩ := hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  obtain rfl | rfl := hr
  · exact hq.ne_lt (Finset.mem_singleton_self _) h₁ hρ
  · exact (⟨3, 2, 2⟩ : TemporalArgument ℕ).not_locallyLicensed_of_coindexed h₃ rfl hρ

/-- The two LFs of the simultaneous reading — de re with the identity relation, and non-locally
licensed with the embedded past coindexed with the now — ascribe the same centered
proposition. -/
theorem deRe_eq_nonLocal (rain : T → W → Prop) :
    deRe (identity (E := E)) (fun t _ w => rain t w) = fun (_ : E) (t : T) w => rain t w :=
  simultaneous_deRe rain

/-! ### The upper limit constraint -/

/-- The forward-shifted reading of *he thought that a burglar attacked him*: an embedded past
anaphoric to the later opening violates the upper limit constraint at the thinking time. -/
theorem forwardShifted_not_upperLimit [LinearOrder T] {a : TemporalArgument ℕ}
    (h : g a.evalIndex < g a.index) : ¬ a.UpperLimit g :=
  not_le.2 h

/-! ### Present under past -/

/-- The embedded present of *John believed that Mary is pregnant* in its non-de-re LF:
`R³(t₃, t₂)`, with access to the matrix relation. -/
def embeddedPresent : TemporalArgument ℕ := ⟨3, 3, 2⟩

/-- The non-de-re LF is contradictory: the matrix past makes `R¹` precedence, the embedded
present requires it to exclude precedence. -/
theorem presentUnderPast_false [Preorder T] (h₁ : matrixPast.Con ρ g)
    (hp : PastConstraint ρ {1}) (hq : PresentConstraint ρ {1, 3}) : False :=
  hp.false_of_presentConstraint hq (by simp) h₁

/-- The double access reading: the scoped present denotes an interval `I` overlapping the
utterance time; its trace denotes `J` in the belief world, bounded by the upper limit constraint
at the believer's now; and the counterpart correspondence — `I` follows the believing time iff `J`
follows the now, `I` overlaps it iff `J` overlaps the now — leaves only the reading where `I`
overlaps the believing time as well. -/
theorem doubleAccess_of_counterpart [LinearOrder T] {I J : Set T} (hI : I.OrdConnected)
    {believing utterance now : T} (hlt : believing < utterance) (hU : utterance ∈ I)
    (hulc : ∃ s ∈ J, s ≤ now)
    (hafter : (∀ s ∈ I, believing < s) ↔ ∀ s ∈ J, now < s)
    (hoverlap : believing ∈ I ↔ now ∈ J) :
    DoubleAccess I believing utterance ∧ now ∈ J := by
  have hb : believing ∈ I := by
    by_contra hb
    obtain ⟨s, hs, hsn⟩ := hulc
    refine (hafter.1 fun s hs => lt_of_not_ge fun hsb => hb ?_) s hs |>.not_ge hsn
    exact hI.out hs hU ⟨hsb, hlt.le⟩
  exact ⟨⟨hb, hU⟩, hoverlap.1 hb⟩

end Abusch1997
