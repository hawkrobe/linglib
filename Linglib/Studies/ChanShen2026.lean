module

public import Linglib.Data.Examples.ChanShen2026
public import Linglib.Fragments.Mandarin.Questions
public import Linglib.Fragments.Singlish.Questions
public import Linglib.Syntax.Minimalist.Linearization.Spellout

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
([merchant-2002]). The three strategies are three structures (7), (14), (8), each a chain of
copies of the wh-phrase: full movement pronounces the top of the chain in matrix Spec-CP;
partial movement pronounces a copy in the intermediate Spec-CP below a deleted one there, the
covert second step; and an in-situ wh-phrase is bound unselectively, a single copy that never
leaves ([sato-ngui-2017]). *The-hell* is licensed exactly when the top of its host's chain is
matrix Spec-CP. Islands constrain the links of a chain, so extraction from a complex NP fails
under full and partial movement and not in situ ((11), (15), with [cole-hermon-1998]'s Malay);
covert movement of the in-situ wh-phrase ([huang-1982]), a deleted copy in matrix Spec-CP over
the pronounced one, would cross the island and license *the-hell* in situ, against (11b) and
(4d). Mandarin *daodi* moves on its own and so tolerates an in-situ host.

The intervention account of [den-dikken-giannakidou-2002] licenses *the-hell* in the
immediate scope of the question operator ([linebarger-1987]) and so admits Singlish in-situ
questions, where nothing intervenes; the attitude-phrase account of [vu-lohiniva-2020], after
[huang-ochi-2004], base-generates *the-hell* in the matrix clause and so cannot generate the
partial-movement order. The paper's Table 5 is the three accounts against the data.

## Implementation notes

The rows are mapped to structures by their strategy and whether they sit in a complex NP; the
structures are schematic Singlish questions (2), (11), and the English, Malay and Mandarin rows
share them, since what the accounts read, the chain of the wh-phrase and where it is pronounced,
is the same. *The-hell* adjoined to the wh-head is not built: it is carried by the wh-phrase, so
its position is its host's. The intervention account reads the number of interveners the rows
record. The schematic clauses have no T, so C selects the verb phrase and each verb selects its
subject as well as its complement, and every constituent has a selection or raising head.

## References

* [chan-shen-2026]
* [chou-2012]
* [merchant-2002]
* [sato-2013]
* [sato-ngui-2017]
* [huang-1982]
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

@[expose] public section

namespace ChanShen2026

open WhModifier Singlish.Questions Minimalist Core.Order

/-! ### The three strategies (7), (8), (14) -/

/-- A token of the schematic questions. -/
def tok (id : ℕ) (cat : Cat) (sel : SelStack := []) (phon : String := "") (wh : Bool := false) :
    LIToken :=
  ⟨LexicalItem.simple cat sel phon wh false, id⟩

/-- The wh-phrase; *the-hell*, adjoined to it, goes where it goes. -/
def what := tok 0 .D (phon := "what") (wh := true)
/-- The matrix interrogative C and the embedded C. -/
def c₁ := tok 1 .C [.V]
def c₂ := tok 2 .C [.V]
def you := tok 3 .D (phon := "you")
def think := tok 4 .V [.C, .D] "think"
def natalie := tok 5 .D (phon := "Natalie")
def baking := tok 6 .V [.D, .D] "baking"
/-- The complex NP of (11): *John like the man that think Mary eat …*. -/
def john := tok 7 .D (phon := "John")
def like := tok 8 .V [.D, .D] "like"
def the := tok 9 .D [.N] "the"
def man := tok 10 .N [.C] "man"
def that := tok 11 .C [.V] "that"
def mary := tok 12 .D (phon := "Mary")
def eat := tok 13 .V [.D, .D] "eat"
/-- *Think* in the relative clause, whose subject is relativized. -/
def thinkRel := tok 14 .V [.C] "think"

/-- The embedded CP, *Natalie baking x* or, in the island, *Mary eat x*, with `spec` in its
specifier. -/
def embedded (island : Bool) (spec : Option PlanarSyntacticObject) (x : PlanarSyntacticObject) :
    PlanarSyntacticObject :=
  let tp := if island then mary * (eat * x) else natalie * (baking * x)
  (spec.map (· * (c₂ * tp))).getD (c₂ * tp)

/-- The matrix CP over the embedded one, *you think …* or, in the island, *John like the man that
think …*, with `spec` in matrix Spec-CP. -/
def matrix (island : Bool) (spec : Option PlanarSyntacticObject) (emb : PlanarSyntacticObject) :
    PlanarSyntacticObject :=
  let vp := if island then john * (like * (the * (man * (that * (thinkRel * emb)))))
    else you * (think * emb)
  (spec.map (· * (c₁ * vp))).getD (c₁ * vp)

/-- (7): full movement, successive cyclic, the top copy pronounced. -/
def full (island : Bool) : PlanarSyntacticObject :=
  matrix island (some what) (embedded island (some (.traceOf what)) (.traceOf what))

/-- (14): partial movement, overt to the intermediate Spec-CP and covert from there. -/
def partialMovement (island : Bool) : PlanarSyntacticObject :=
  matrix island (some (.traceOf what)) (embedded island (some what) (.traceOf what))

/-- (8): the wh-phrase in situ, bound by the question operator: one copy. -/
def bound (island : Bool) : PlanarSyntacticObject :=
  matrix island none (embedded island none what)

/-- The LF-movement analysis of wh-in-situ ([huang-1982]): a deleted copy in matrix Spec-CP over
the pronounced one. -/
def covert (island : Bool) : PlanarSyntacticObject :=
  matrix island (some (.traceOf what)) (embedded island none what)

/-- The wh-phrase takes scope in matrix Spec-CP: the top of its chain is there. -/
def ReachesScope (t : PlanarSyntacticObject) : Prop := ⟨[0]⟩ ∈ chainTop t what

instance (t : PlanarSyntacticObject) : Decidable (ReachesScope t) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- The wh-phrase is pronounced in matrix Spec-CP. -/
def PronouncedAtScope (t : PlanarSyntacticObject) : Prop := ⟨[0]⟩ ∈ occurrences t what

instance (t : PlanarSyntacticObject) : Decidable (PronouncedAtScope t) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Full and partial movement reach matrix Spec-CP, the latter pronounced lower; the bound
wh-phrase stays in situ ((7), (14), (8)). -/
example : (ReachesScope (full false) ∧ PronouncedAtScope (full false)) ∧
    (ReachesScope (partialMovement false) ∧ ¬ PronouncedAtScope (partialMovement false)) ∧
    ¬ ReachesScope (bound false) := by
  decide

/-- Covert movement pronounces the in-situ string. -/
example (island : Bool) : pfYield (covert island) = pfYield (bound island) := by
  cases island <;> decide

/-! ### Negative attitude ascription (§3.2–3.3) -/

/-- The wh-phrase hosting the modifier: its structure, and how many wh-phrases stand between the
question operator and it. -/
structure Host where
  tree : PlanarSyntacticObject
  interveners : ℕ := 0

/-- The modifier's point-of-view feature is checked in matrix Spec-CP, so it is licensed iff it
gets there: with its host, when the host's chain reaches it, or on its own. -/
def Licensed (m : WhModifier) (h : Host) : Prop := WhModifier.Licensed m (ReachesScope h.tree)

instance (m : WhModifier) (h : Host) : Decidable (Licensed m h) :=
  inferInstanceAs (Decidable (WhModifier.Licensed _ _))

variable (h : Host)

/-- *The-hell* is licensed iff its host's chain reaches matrix Spec-CP ((20), (21), (24)). -/
theorem licensed_theHell_iff : Licensed theHell h ↔ ReachesScope h.tree :=
  licensed_iff_of_parasitic _ rfl

/-- *Daodi* is licensed whatever its host does ((19)). -/
theorem licensed_daodi : Licensed Mandarin.Questions.daodi h :=
  licensed_of_independent _ rfl

/-- Across the three strategies, *the-hell* is out exactly in situ ((3a–c)). -/
theorem licensed_theHell_strategies :
    Licensed theHell ⟨full false, 0⟩ ∧ Licensed theHell ⟨partialMovement false, 0⟩ ∧
      ¬ Licensed theHell ⟨bound false, 0⟩ := by
  decide

/-! ### Rival accounts (§3.4) -/

/-- [den-dikken-giannakidou-2002]: *wh-the-hell* is a polarity item licensed in the immediate
scope of the question operator ([linebarger-1987]), which a wh-phrase between them blocks. -/
def Intervention.Licensed : Prop := h.interveners = 0

instance : Decidable (Intervention.Licensed h) := inferInstanceAs (Decidable (_ = _))

/-- [vu-lohiniva-2020]: *the-hell* is base-generated in the specifier of a matrix attitude
phrase, whose [+wh] feature the nearest wh-phrase checks by moving there before the pair moves
to Spec-CP; a *wh-the-hell* string therefore surfaces only with the wh-phrase pronounced in matrix
Spec-CP. -/
def AttP.Licensed : Prop := PronouncedAtScope h.tree

instance : Decidable (AttP.Licensed h) := inferInstanceAs (Decidable (PronouncedAtScope _))

/-- In English a wh-phrase stays in situ only in a multiple question, under the fronted one, so
in situ and intervened coincide and ascription agrees with intervention ((1), (25)–(26)); the
two part only where a single question leaves its wh-phrase in situ. -/
theorem licensed_theHell_iff_intervention (hE : ReachesScope h.tree ↔ h.interveners = 0) :
    Licensed theHell h ↔ Intervention.Licensed h :=
  (licensed_theHell_iff h).trans hE

/-! ### The data -/

/-- The structure of a row: its strategy, in a complex NP or not, with an in-situ wh-phrase
construed by `inSitu`. -/
def structureOf (inSitu : Bool → PlanarSyntacticObject) (e : Datum) :
    Option PlanarSyntacticObject :=
  let island := e.feature? "island" = some "complexNP"
  e.parse? "strategy"
    [("full", full island), ("partial", partialMovement island), ("inSitu", inSitu island)]

/-- A row's host on the analysis `inSitu`: its structure and the number of wh-phrases between the
question operator and the modifier, which the row records. -/
def hostOf (inSitu : Bool → PlanarSyntacticObject) (e : Datum) : Option Host := do
  pure ⟨← structureOf inSitu e, ← e.nat? "interveners"⟩

/-- A row's modifier. -/
def modifierOf (e : Datum) : Option WhModifier :=
  e.parse? "modifier" [("theHell", theHell), ("daodi", Mandarin.Questions.daodi)]

/-- Every row with a modifier records its host, so the statements over `hostOf` below range over
all of them. -/
theorem hostOf_isSome : ∀ e ∈ Examples.all, (modifierOf e).isSome → (hostOf bound e).isSome := by
  decide

/-- Extraction fails when a link of the wh-phrase's chain leaves the complex NP. -/
def CrossesIsland (t : PlanarSyntacticObject) : Prop :=
  ∃ h ∈ occurrences t the, Escapes t what (projectionAt t h)

instance (t : PlanarSyntacticObject) : Decidable (CrossesIsland t) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Extraction from a complex NP fails exactly where a link of the chain leaves it: under full
movement, and under partial movement by its covert step, but not in situ ((11), (15), Malay
(17)). -/
theorem island_rows : ∀ e ∈ Examples.all, e.feature? "island" = some "complexNP" →
    ∀ t ∈ structureOf bound e, (CrossesIsland t ↔ e.judgment ≠ .acceptable) := by
  decide

/-- Ascription predicts every modifier row: English (1), (25)–(26), the experiment's (4) and
(6), the subject question (22), and Mandarin (19). -/
theorem ascription_rows :
    ∀ e ∈ Examples.all, ∀ m ∈ modifierOf e, ∀ h ∈ hostOf bound e,
      (Licensed m h ↔ e.judgment = .acceptable) := by
  decide

/-- Covert movement of the in-situ wh-phrase crosses the complex NP of (11b) and licenses
*the-hell* in the in-situ question (4d), both acceptable and unacceptable the other way round:
the island facts and the modifier facts each choose binding ([sato-ngui-2017]). -/
theorem covert_mispredicts :
    (∃ t ∈ structureOf covert Examples.ex11b, CrossesIsland t) ∧
      Examples.ex11b.judgment = .acceptable ∧
      (∃ m ∈ modifierOf Examples.ex4d, ∃ h ∈ hostOf covert Examples.ex4d, Licensed m h) ∧
      Examples.ex4d.judgment = .unacceptable := by
  decide

/-- Intervention is right except on the in-situ single questions ((4d), (22b)): nothing
intervenes, yet *the-hell* is out. -/
theorem intervention_rows :
    ∀ e ∈ Examples.all, e.feature? "modifier" = some "theHell" → ∀ h ∈ hostOf bound e,
      ((Intervention.Licensed h ↔ e.judgment = .acceptable) ↔
        (ReachesScope h.tree ∨ h.interveners ≠ 0)) := by
  decide

/-- The attitude phrase is right except where the wh-phrase takes scope from a position it is not
pronounced in, under partial movement ((6d)). -/
theorem attP_rows :
    ∀ e ∈ Examples.all, e.feature? "modifier" = some "theHell" → ∀ h ∈ hostOf bound e,
      ((AttP.Licensed h ↔ e.judgment = .acceptable) ↔
        ¬ (ReachesScope h.tree ∧ ¬ PronouncedAtScope h.tree)) := by
  decide

end ChanShen2026
