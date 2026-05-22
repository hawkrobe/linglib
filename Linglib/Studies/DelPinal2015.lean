import Linglib.Theories.Semantics.Gradability.Classification
import Linglib.Theories.Semantics.Composition.Coercion
import Linglib.Studies.Kamp1975
import Linglib.Studies.Partee2010
import Linglib.Data.Examples.Schema

/-!
# Del Pinal (2015): Dual Content Semantics
@cite{delpinal-2015}

Dual-content reanalysis of privative adjectives: nouns have
E-structure + qualia C-structure (@cite{pustejovsky-1995});
privatives operate on C-structure. Sibling to `Partee2010.lean`
(same data, opposite mechanism: Partee re-types fake as subsective
plus noun-coercion, DC keeps fake's Kamp-privative typing and pairs
it with C-structure).

## Main definitions

* `Qualia`, `NounMeaning`, `DCAdjMeaning`: dual-content lexical-entry types.
* `DelPinalReanalysis`: stand-alone operator-typed reanalysis structure.
* `fakeDC`, `counterfeitDC`, `artificialDC`: the privative trio (paper
  eqs. 16, 11, 12); `fakeDelPinal`, `counterfeitDelPinal`: constructive
  witnesses. `artificialDC` is *not* a `DelPinalReanalysis` (it admits
  no look-like-N inference) — see `artificialDC_not_DelPinalReanalysis`.
* `AdjMeaning.toDCAdjMeaning`: lift a classical `AdjMeaning` to a
  `DCAdjMeaning` by inheriting noun qualia.
* `DelPinalReanalysis.no_LicensedCoercion`: cross-framework divergence
  with @cite{partee-2010} (any DC reanalysis projects to a Kamp-privative
  `AdjMeaning`, hence admits no NVP-licensed coercion).
* `Kamp1975_fakeAdj_lift_not_DelPinalReanalysis`: Kamp's classical typing
  of `fake` is genuinely impoverished — the lift to `DCAdjMeaning` fails
  to satisfy the look-like-N constraint that DC's `fake` enforces.

## Implementation notes

Paper qualia values involve event quantifiers (`λx.GEN e[SHOOTING(e) ∧
INSTRUMENT(e,x)]`, `∃e[MAKING(e) ∧ GOAL(e, Q_F(N)(x))]`); these are
flattened to characteristic predicates of type `Property W E`. The
AGENTIVE clause of `fakeDC` is approximated as `N.qualia.formal` (the
GOAL projects the formal quale), which loses the *existential
commitment* about an event of making — a found object can look like a
gun without being made-to-look-like one. This proxy is adequate at the
predicate-level fidelity of the current substrate; faithful encoding
would require an event substrate. Counterfeit's AGENTIVE goal is
`Q_F ∧ Q_T`; artificial's is `Q_T` alone.

The dual FA_DC compositional rule (paper §3: E-side standard FA, C-side
pointwise FA via qualia functions) is elided — operators here are flat
`NounMeaning → NounMeaning` functions rather than structured pairs of
E-functions and C-functions. The trade-off is exposed by
`artificialDC_not_DelPinalReanalysis`: not every privative-like operator
satisfies `extension_implies_formal`.

## References

* @cite{pustejovsky-1995} (qualia roles).
* @cite{partee-2010} (sibling reanalysis).
-/

namespace DelPinal2015

open Semantics.Gradability.Classification
open Semantics.Composition.Coercion (LicensedCoercion)

/-- Pustejovsky-style four-role qualia profile. -/
structure Qualia (W E : Type*) where
  constitutive : Property W E
  formal       : Property W E
  telic        : Property W E
  agentive     : Property W E

/-- DC lexical entry: extension plus qualia profile. -/
structure NounMeaning (W E : Type*) where
  extension : Property W E
  qualia    : Qualia W E

/-- Adjective as a DC operator on noun meanings. -/
abbrev DCAdjMeaning (W E : Type*) := NounMeaning W E → NounMeaning W E

variable {W E : Type*}

/-- DC reanalysis: a `DCAdjMeaning` operator with privative E-structure
    and formal-quale entailment (the "looks like N" inference). -/
structure DelPinalReanalysis (W E : Type*) where
  operator : DCAdjMeaning W E
  extension_privative : ∀ (N : NounMeaning W E) (w : W) (x : E),
    (operator N).extension w x → ¬ N.extension w x
  extension_implies_formal : ∀ (N : NounMeaning W E) (w : W) (x : E),
    (operator N).extension w x → N.qualia.formal w x

/-! ### The privative trio: fake, counterfeit, artificial -/

/-- DC `fake` operator (paper eq. 16). -/
def fakeDC : DCAdjMeaning W E := fun N =>
  { extension := fun w x =>
      ¬ N.extension w x ∧
      ¬ N.qualia.agentive w x ∧
      N.qualia.formal w x
    qualia :=
      { constitutive := N.qualia.constitutive
        formal       := N.qualia.formal
        telic        := fun w x => ¬ N.qualia.telic w x
        agentive     := N.qualia.formal } }

/-- DC `counterfeit` operator (paper eq. 11). The AGENTIVE goal is to
    look AND function like N (made-to-look-and-function). TELIC
    preserved (not negated). -/
def counterfeitDC : DCAdjMeaning W E := fun N =>
  { extension := fun w x =>
      ¬ N.extension w x ∧
      ¬ N.qualia.agentive w x ∧
      N.qualia.formal w x ∧
      N.qualia.telic w x
    qualia :=
      { constitutive := N.qualia.constitutive
        formal       := N.qualia.formal
        telic        := N.qualia.telic
        agentive     := fun w x => N.qualia.formal w x ∧ N.qualia.telic w x } }

/-- DC `artificial` operator (paper eq. 12). The AGENTIVE goal is to
    function like N (no look-like commitment). FORMAL is preserved in
    qualia but is *not* asserted in extension. -/
def artificialDC : DCAdjMeaning W E := fun N =>
  { extension := fun w x =>
      ¬ N.extension w x ∧
      ¬ N.qualia.agentive w x ∧
      N.qualia.telic w x
    qualia :=
      { constitutive := N.qualia.constitutive
        formal       := N.qualia.formal
        telic        := N.qualia.telic
        agentive     := N.qualia.telic } }

/-- `fakeDC` is a `DelPinalReanalysis`. -/
def fakeDelPinal : DelPinalReanalysis W E where
  operator := fakeDC
  extension_privative _ _ _ h := h.1
  extension_implies_formal _ _ _ h := h.2.2

/-- `counterfeitDC` is a `DelPinalReanalysis`. -/
def counterfeitDelPinal : DelPinalReanalysis W E where
  operator := counterfeitDC
  extension_privative _ _ _ h := h.1
  extension_implies_formal _ _ _ h := h.2.2.1

/-- `artificialDC` is *not* a `DelPinalReanalysis`: artificial N does
    not entail the look-like inference (paper §3: artificial heart
    need not look like a heart). Counterexample noun shows that the
    extension can be inhabited while the input formal quale is empty. -/
theorem artificialDC_not_DelPinalReanalysis :
    ¬ ∃ (r : DelPinalReanalysis Unit Unit), r.operator = artificialDC := by
  rintro ⟨r, hr⟩
  let N : NounMeaning Unit Unit :=
    { extension := fun _ _ => False
      qualia :=
        { constitutive := fun _ _ => True
          formal       := fun _ _ => False
          telic        := fun _ _ => True
          agentive     := fun _ _ => False } }
  have hext : (r.operator N).extension () () := by
    rw [hr]; exact ⟨id, id, trivial⟩
  exact r.extension_implies_formal N () () hext

/-! ### Cross-framework divergence with @cite{partee-2010} -/

/-- Classical-`AdjMeaning` projection of a DC operator under a
    per-noun qualia assignment `Q`. -/
def DelPinalReanalysis.toAdjMeaning (r : DelPinalReanalysis W E)
    (Q : Property W E → Qualia W E) : AdjMeaning W E :=
  fun N w x => (r.operator ⟨N, Q N⟩).extension w x

theorem DelPinalReanalysis.toAdjMeaning_isPrivative
    (r : DelPinalReanalysis W E) (Q : Property W E → Qualia W E) :
    isPrivative (r.toAdjMeaning Q) :=
  fun N w x h => r.extension_privative ⟨N, Q N⟩ w x h

/-- The classical projection of any DC reanalysis admits no
    `LicensedCoercion`. The two frameworks make incompatible type-level
    commitments about privatives. -/
theorem DelPinalReanalysis.no_LicensedCoercion
    (r : DelPinalReanalysis W E) (Q : Property W E → Qualia W E)
    (N : Property W E) (w : W) :
    IsEmpty (LicensedCoercion N (r.toAdjMeaning Q) w) :=
  Partee2010.isPrivative_no_LicensedCoercion
    (r.toAdjMeaning_isPrivative Q) N w

/-! ### Classical lift; impoverishment of Kamp-typed `fake` -/

/-- Lift a classical `AdjMeaning` to a `DCAdjMeaning` by computing the
    extension via the classical adj and inheriting the input noun's
    qualia (the C-structure passes through unchanged). -/
def _root_.Semantics.Gradability.Classification.AdjMeaning.toDCAdjMeaning
    (adj : AdjMeaning W E) : DCAdjMeaning W E :=
  fun N => { extension := adj N.extension, qualia := N.qualia }

/-- `Kamp1975.fakeAdj` lifted to a `DCAdjMeaning` is *not* a
    `DelPinalReanalysis`: the classical typing preserves the Kamp-
    privative E-structure but cannot in general guarantee the
    look-like-N inference (the input noun's formal quale need not
    hold at the fake-witness entity). Formal counterpart to Del
    Pinal's argument that the classical analysis is incomplete. -/
theorem Kamp1975_fakeAdj_lift_not_DelPinalReanalysis :
    ¬ ∃ (r : DelPinalReanalysis Kamp1975.W2 Kamp1975.E3),
      r.operator = Kamp1975.fakeAdj.toDCAdjMeaning := by
  rintro ⟨r, hr⟩
  let N : NounMeaning Kamp1975.W2 Kamp1975.E3 :=
    { extension := fun _ _ => False
      qualia :=
        { constitutive := fun _ _ => True
          formal       := fun _ _ => False
          telic        := fun _ _ => True
          agentive     := fun _ _ => False } }
  have hext : (r.operator N).extension Kamp1975.W2.w₁ Kamp1975.E3.b := by
    rw [hr]; exact ⟨trivial, id⟩
  exact r.extension_implies_formal N Kamp1975.W2.w₁ Kamp1975.E3.b hext

/-! ### `RevisedClass` classification: DC side -/

/-- Under Del Pinal's framework, `Kamp1975.fakeAdj` keeps its
    Kamp-privative typing and falls in `RevisedClass.nonSubsective`.
    Contrast with `Partee2010.fakeReanalysis.is_subsective`: Partee
    reclassifies the *reanalyzed* meaning into `RevisedClass.subsective`.
    The two frameworks attribute different `RevisedClass` values to
    the lexical item 'fake' because they posit different formal
    objects for it. -/
theorem Kamp1975_fakeAdj_RevisedClass_nonSubsective :
    RevisedClass.nonSubsective.satisfies Kamp1975.fakeAdj :=
  privative_not_subsective Kamp1975.fake_privative
    ⟨fun _ _ => False, Kamp1975.W2.w₁, Kamp1975.E3.b, trivial, id⟩

/-! ### Output-qualia witness theorems

Per paper eqs. 11, 12, 16/17, the three operators produce distinct
qualia outputs. The `Iff.rfl` theorems below verify the structural
discrimination, justifying the 4-field `Qualia` shape. -/

theorem fakeDC_telic_negates (N : NounMeaning W E) (w : W) (x : E) :
    (fakeDC N).qualia.telic w x ↔ ¬ N.qualia.telic w x := Iff.rfl

theorem counterfeitDC_telic_preserved (N : NounMeaning W E) (w : W) (x : E) :
    (counterfeitDC N).qualia.telic w x ↔ N.qualia.telic w x := Iff.rfl

theorem artificialDC_telic_preserved (N : NounMeaning W E) (w : W) (x : E) :
    (artificialDC N).qualia.telic w x ↔ N.qualia.telic w x := Iff.rfl

theorem fakeDC_agentive_is_formal (N : NounMeaning W E) (w : W) (x : E) :
    (fakeDC N).qualia.agentive w x ↔ N.qualia.formal w x := Iff.rfl

theorem counterfeitDC_agentive_is_formal_and_telic
    (N : NounMeaning W E) (w : W) (x : E) :
    (counterfeitDC N).qualia.agentive w x ↔
    (N.qualia.formal w x ∧ N.qualia.telic w x) := Iff.rfl

theorem artificialDC_agentive_is_telic (N : NounMeaning W E) (w : W) (x : E) :
    (artificialDC N).qualia.agentive w x ↔ N.qualia.telic w x := Iff.rfl

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/DelPinal2015.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def fake_gun : LinguisticExample :=
  { id := "delpinal2015_fake_gun"
    source := ⟨"delpinal-2015", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fake gun"
    discourseSegments := []
    glossedTokens := [("fake", "fake"), ("gun", "gun")]
    translation := "fake gun"
    context := "Paper eq. 17 worked composition: fake gun's E-structure asserts ¬gun(x), ¬made-as-gun, ∃e[MAKING(e) ∧ GOAL(e, perceptual-gun(x))]. C-structure: TELIC negated (not for shooting), FORMAL preserved (looks like gun), AGENTIVE = made-to-look-like-gun. The canonical privative."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Del Pinal §3 eq. 17. Illustrates the full DC composition for the privative paradigm case. The TELIC-negation entailment (fake gun is not for shooting) distinguishes DC from a coarser Kamp-privative analysis that only commits to ¬gun."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def counterfeit_rolex : LinguisticExample :=
  { id := "delpinal2015_counterfeit_rolex"
    source := ⟨"delpinal-2015", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "counterfeit Rolex"
    discourseSegments := []
    glossedTokens := [("counterfeit", "counterfeit"), ("Rolex", "Rolex")]
    translation := "counterfeit Rolex"
    context := "Paper eq. 11: counterfeit differs from fake in TELIC. A counterfeit Rolex is made to BOTH look AND function like a Rolex (GOAL includes Q_F AND Q_T); a fake Rolex would only need to look like one."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Del Pinal §3 eq. 11. Discriminates counterfeit from fake at the C-structure level: counterfeit's AGENTIVE asserts MAKING with GOAL = (Q_F ∧ Q_T)(N), fake's asserts MAKING with GOAL = Q_F(N) only. This three-way contrast (fake/counterfeit/artificial) is the DC-specific empirical wedge against any account that lumps all privatives."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def artificial_heart : LinguisticExample :=
  { id := "delpinal2015_artificial_heart"
    source := ⟨"delpinal-2015", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "artificial heart"
    discourseSegments := []
    glossedTokens := [("artificial", "artificial"), ("heart", "heart")]
    translation := "artificial heart"
    context := "Paper eq. 12: artificial differs from fake in NOT negating FORMAL. An artificial heart need not look like a heart but is made with the intention that it function like a heart (GOAL = Q_T, not Q_F). Some find ¬Q_E itself unstable for 'artificial' (paper notes mixed intuitions about whether artificial legs are 'really' legs)."
    judgment := .acceptable
    alternatives := []
    readings := [("strict privative (¬Q_E preserved)", .acceptable), ("non-privative (Q_E preserved)", .marginal)]
    paperFeatures := []
    comment := "Del Pinal §3 eq. 12. Completes the fake/counterfeit/artificial trio. The reading-level annotation captures Del Pinal's own observation (p. 17) that mature speakers give 'mixed and unstable intuitions' about whether artificial N is a kind of N — a graded privativity that no purely-binary classification can model."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def fake_chanel_handbag : LinguisticExample :=
  { id := "delpinal2015_fake_chanel_handbag"
    source := ⟨"delpinal-2015", "fn. 12"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fake Chanel handbag"
    discourseSegments := []
    glossedTokens := [("fake", "fake"), ("Chanel", "Chanel"), ("handbag", "handbag")]
    translation := "fake Chanel handbag"
    context := "Paper footnote 12: structural-scope ambiguity diagnostic. (i) [fake [Chanel handbag]]: a counterfeit Chanel handbag (negates AGENTIVE of 'Chanel handbag' = the brand-source quale). (ii) [[fake Chanel] handbag]: a handbag whose 'Chanel' attribution is fake (could be a real handbag, falsely branded). Distinguishes DC from coarser noun-coercion accounts that don't distinguish the two scopes."
    judgment := .acceptable
    alternatives := []
    readings := [("[fake [Chanel handbag]] (counterfeit)", .acceptable), ("[[fake Chanel] handbag] (falsely-branded)", .acceptable)]
    paperFeatures := []
    comment := "Del Pinal §3 footnote 12. The scope ambiguity is structurally derivable in DC because both 'Chanel' (a brand-name modifier, adding to AGENTIVE) and 'fake' (a semantic restructuring operator) compose via FA_DC at different bracketings. Partee's noun-coercion account does not naturally yield the two readings — the canonical diagnostic for the DC-vs-Partee divergence on iterated privatives."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [fake_gun, counterfeit_rolex, artificial_heart, fake_chanel_handbag]

end Examples
-- END GENERATED EXAMPLES

end DelPinal2015
