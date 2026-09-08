import Linglib.Data.Examples.ChanShen2026
import Linglib.Fragments.Mandarin.Questions
import Linglib.Fragments.Singlish.Questions

/-!
# Chan and Shen (2026): Conditions on *wh-the-hell* licensing

A Singlish single wh-question fronts its wh-phrase, moves it to an intermediate Spec-CP, or
leaves it in situ, and [chan-shen-2026]'s acceptability experiment, a pair of 2×2 designs in
the manner of [sprouse-et-al-2012], finds that *the-hell* survives the first two and not the
third: the in-situ comparison shows the superadditive interaction of a penalty, the
partial-movement one only additive costs. This follows from two independent pieces.
*The-hell* carries an unvalued point-of-view feature checked against the operator in matrix
C, which ascribes its negative attitude (surprise, ignorance, doubt of every answer:
[pesetsky-1987], [martin-2020], [rawlins-2008], [ippolito-2024]) to the speaker
([chou-2012]); and as a modifier adjoined to the wh-head it moves only with the wh-phrase
([merchant-2002]). Full and partial movement put the wh-phrase in matrix Spec-CP, the latter
by a covert second step, while an in-situ wh-phrase is bound unselectively and never leaves
([sato-ngui-2017], with the island facts of [cole-hermon-1998]'s Malay). Mandarin *daodi*
moves on its own and so tolerates an in-situ host.

The intervention account of [den-dikken-giannakidou-2002] licenses *the-hell* in the
immediate scope of the question operator ([linebarger-1987]) and so admits Singlish in-situ
questions, where nothing intervenes; the attitude-phrase account of [vu-lohiniva-2020], after
[huang-ochi-2004], base-generates *the-hell* in the matrix clause and so cannot generate the
partial-movement order. The paper's Table 5 is the three accounts against the data.

## References

* [chan-shen-2026]
* [chou-2012]
* [merchant-2002]
* [sato-2013]
* [sato-ngui-2017]
* [cole-hermon-1998]
* [pesetsky-1987]
* [martin-2020]
* [rawlins-2008]
* [ippolito-2024]
* [den-dikken-giannakidou-2002]
* [linebarger-1987]
* [vu-lohiniva-2020]
* [huang-ochi-2004]
* [sprouse-et-al-2012]
-/

namespace ChanShen2026

open Data.Examples WhModifier Syntax.Question Singlish.Questions

/-- The wh-phrase hosting the modifier: how it is interpreted, and how many wh-phrases stand
between the question operator and it. -/
structure Host where
  mechanism : WhInterpMechanism
  interveners : ℕ := 0
  deriving DecidableEq

/-! ### Negative attitude ascription (§3.2–3.3) -/

/-- The modifier's point-of-view feature is checked in matrix Spec-CP, so it is licensed iff it
gets there: with its host, or on its own. -/
def Licensed (m : WhModifier) (h : Host) : Prop :=
  WhModifier.Licensed m h.mechanism.ReachesSpecCP

instance (m : WhModifier) (h : Host) : Decidable (Licensed m h) :=
  inferInstanceAs (Decidable (WhModifier.Licensed _ _))

variable (h : Host)

/-- *The-hell* is licensed iff its host reaches matrix Spec-CP ((20), (21), (24)). -/
theorem licensed_theHell_iff : Licensed theHell h ↔ h.mechanism.ReachesSpecCP :=
  licensed_iff_of_parasitic _ rfl

/-- *Daodi* is licensed whatever its host does ((19)). -/
theorem licensed_daodi : Licensed Mandarin.Questions.daodi h :=
  licensed_of_independent _ rfl

/-- Across the three strategies, *the-hell* is out exactly in situ ((3a–c)). -/
theorem licensed_theHell_strategies :
    ∀ m ∈ strategies, Licensed theHell ⟨m, 0⟩ ↔ m ≠ .unselectiveBinding := by
  decide

/-! ### Rival accounts (§3.4) -/

/-- [den-dikken-giannakidou-2002]: *wh-the-hell* is a polarity item licensed in the immediate
scope of the question operator ([linebarger-1987]), which a wh-phrase between them blocks. -/
def Intervention.Licensed : Prop := h.interveners = 0

instance : Decidable (Intervention.Licensed h) := inferInstanceAs (Decidable (_ = _))

/-- [vu-lohiniva-2020]: *the-hell* is base-generated in the specifier of a matrix attitude
phrase, whose [+wh] feature the nearest wh-phrase checks by moving there before the pair moves
to Spec-CP; a *wh-the-hell* string therefore surfaces only under overt movement to the matrix
clause. -/
def AttP.Licensed : Prop := h.mechanism = .overtMovement

instance : Decidable (AttP.Licensed h) := inferInstanceAs (Decidable (_ = _))

/-- In English a wh-phrase stays in situ only in a multiple question, under the fronted one, so
in situ and intervened coincide and ascription agrees with intervention ((1), (25)–(26)); the
two part only where a single question leaves its wh-phrase in situ. -/
theorem licensed_theHell_iff_intervention (hE : h.mechanism.ReachesSpecCP ↔ h.interveners = 0) :
    Licensed theHell h ↔ Intervention.Licensed h :=
  (licensed_theHell_iff h).trans hE

/-! ### The data -/

/-- A row's strategy. -/
def mechanismOf (e : LinguisticExample) : Option WhInterpMechanism :=
  match e.feature? "strategy" with
  | some "full" => some .overtMovement
  | some "partial" => some .partialMovement
  | some "inSitu" => some .unselectiveBinding
  | _ => none

/-- A row's host. -/
def hostOf (e : LinguisticExample) : Option Host :=
  (mechanismOf e).map λ m => ⟨m, (e.nat? "interveners").getD 0⟩

/-- A row's modifier. -/
def modifierOf (e : LinguisticExample) : Option WhModifier :=
  match e.feature? "modifier" with
  | some "theHell" => some theHell
  | some "daodi" => some Mandarin.Questions.daodi
  | _ => none

/-- Extraction from a complex NP fails exactly under an island-sensitive mechanism: the covert
step of partial movement crosses the island, unselective binding does not ((11), (15), Malay
(17)). -/
theorem island_rows :
    ∀ e ∈ Examples.all, e.feature? "island" = some "complexNP" →
      ∀ m ∈ mechanismOf e, (m.IslandSensitive ↔ e.judgment ≠ .acceptable) := by
  decide

/-- Ascription predicts every modifier row: English (1), (25)–(26), the experiment's (4) and
(6), the subject question (22), and Mandarin (19). -/
theorem ascription_rows :
    ∀ e ∈ Examples.all, ∀ m ∈ modifierOf e, ∀ h ∈ hostOf e,
      (Licensed m h ↔ e.judgment = .acceptable) := by
  decide

/-- Intervention is right except on the in-situ single questions ((4d), (22b)): nothing
intervenes, yet *the-hell* is out. -/
theorem intervention_rows :
    ∀ e ∈ Examples.all, e.feature? "modifier" = some "theHell" → ∀ h ∈ hostOf e,
      ((Intervention.Licensed h ↔ e.judgment = .acceptable) ↔
        (h.mechanism.ReachesSpecCP ∨ h.interveners ≠ 0)) := by
  decide

/-- The attitude phrase is right except under partial movement ((6d)). -/
theorem attP_rows :
    ∀ e ∈ Examples.all, e.feature? "modifier" = some "theHell" → ∀ h ∈ hostOf e,
      ((AttP.Licensed h ↔ e.judgment = .acceptable) ↔ h.mechanism ≠ .partialMovement) := by
  decide

end ChanShen2026
