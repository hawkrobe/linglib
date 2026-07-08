import Linglib.Semantics.Plurality.Reciprocal

/-!
# Winter (2018): Symmetric Predicates and Reciprocal Alternations

[winter-2018]

Semantics & Pragmatics 11(1): 1–52.

Reciprocal alternations pair a unary-collective predicate P (*Sue and Dan
dated*) with a binary predicate R (*Sue dated Dan*). Winter's
**Reciprocity-Symmetry Generalization** (RSG, def. 18): the alternation is
*plain* — P(x+y) ⇔ R(x,y) ∧ R(y,x) (def. 7) — iff R is truth-conditionally
symmetric. The RSG is not a logical necessity (an artificial ★Xhug refutes
it, fn. 12); Winter derives it lexically: symmetric predicates take the
collective meaning as *basic* and obtain the binary form as its symmetric
image R := λx λy. P(x+y) (def. 22). This reverses the derivation direction
of [dimitriadis-2008] and [siloni-2012], which map binary meanings to
reciprocal ones (fn. 14) — a genuine divergence from
`Studies/Siloni2012.lean`, where lexical reciprocal verbs are derived from
transitive alternates by bundling.

Non-symmetric reciprocals (*hug*, *fight*, *collide*) satisfy no plain
equivalence; §3.3 charts their logical patterns (Pr₁–Pr₅, Table 3), of
which only the weak disjunctive Pr₅ — P(x+y) ⇒ R(x,y) ∨ R(y,x) — is shared
by all reciprocal alternations. Their full semantics is preferential
(typicality-based, §3.5, supported by experimental judgment data on Dutch
contact and communication verbs), beyond the event-free logical core
formalized here.

Sums of two distinct atoms are encoded as pair `Finset`s `{x, y}`,
matching the `(R, X)` signature of `Semantics.Plurality.Reciprocal`.

## Main declarations

* `PlainReciprocity` (def. 7), `TCSymmetric`, `symmetricImage` (def. 22)
* `symmetricImage_tcSymmetric`, `plainReciprocity_symmetricImage` —
  the symmetric image is symmetric and plain: principle P1, which
  derives the RSG for collective-basic predicates
* `plainReciprocity_iff_pr1_pr2` — plain reciprocity decomposes exactly
  into Pr₁ ∧ Pr₂
* `exists_plainReciprocity_not_tcSymmetric` — plainR alone does not
  force symmetry (fn. 12's ★Xhug): the RSG is a lexicon fact, not logic
* `AlternationProfile` + `table3` — Table 3's per-verb Pr-patterns, with
  the Pr₅ universal and the Pr₄ ⇒ Pr₁ consistency check
-/

namespace Winter2018

variable {A : Type*} [DecidableEq A]

/-- Def. (7), plain reciprocity: for distinct atoms, the collective holds
    of the pair-sum iff the binary holds in both directions
    ("A and B dated" ⇔ "A dated B and B dated A"). -/
def PlainReciprocity (P : Finset A → Prop) (R : A → A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → (P {x, y} ↔ R x y ∧ R y x)

/-- Truth-conditional symmetry of a binary predicate (§2.2; Strawson
    effects like *sister*'s gender presupposition are factored out). -/
def TCSymmetric (R : A → A → Prop) : Prop := ∀ x y, R x y ↔ R y x

/-- Def. (22), the symmetric image of a collective predicate:
    `R x y` iff `P` holds of the pair-sum (*similar to* from
    collective *similar*). -/
def symmetricImage (P : Finset A → Prop) : A → A → Prop :=
  fun x y => P {x, y}

/-- The symmetric image is truth-conditionally symmetric — by
    commutativity of sum formation (Winter's point (i) on def. 7). -/
theorem symmetricImage_tcSymmetric (P : Finset A → Prop) :
    TCSymmetric (symmetricImage P) := by
  intro x y
  simp [symmetricImage, Finset.pair_comm]

/-- Principle P1: the symmetric image stands in plain reciprocity with
    its source collective. With `symmetricImage_tcSymmetric` this
    derives the RSG for predicates whose binary form is the symmetric
    image of a basic collective meaning. -/
theorem plainReciprocity_symmetricImage (P : Finset A → Prop) :
    PlainReciprocity P (symmetricImage P) := by
  intro x y _
  constructor
  · exact fun h => ⟨h, by simpa [symmetricImage, Finset.pair_comm] using h⟩
  · exact fun h => h.1

/-- The RSG is not logically forced: a plain alternation with a
    non-symmetric binary predicate exists (fn. 12's ★Xhug — a one-way
    *hug* paired with the everywhere-false collective is vacuously
    plain). The RSG is thus a generalization about natural-language
    lexicons, not a consequence of the notion of reciprocity. -/
theorem exists_plainReciprocity_not_tcSymmetric :
    ∃ (R : Bool → Bool → Prop) (P : Finset Bool → Prop),
      PlainReciprocity P R ∧ ¬ TCSymmetric R := by
  refine ⟨fun x y => x = true ∧ y = false, fun _ => False, ?_, ?_⟩
  · intro x y hxy
    constructor
    · exact False.elim
    · rintro ⟨⟨rfl, rfl⟩, h₂, -⟩
      exact Bool.noConfusion h₂
  · intro h
    have := (h true false).mp ⟨rfl, rfl⟩
    exact Bool.noConfusion this.1

/-! ### The Pr-patterns of non-plain alternations (§3.3) -/

/-- (Pr₁): bidirectional `R` yields the collective. Fails for *hug*
    (separate unidirectional hugs do not make a mutual hug). -/
def Pr1 (P : Finset A → Prop) (R : A → A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → R x y → R y x → P {x, y}

/-- (Pr₂): the collective yields `R` — in both directions, by sum
    commutativity (`Pr2.both`). Holds for *be in love* and Hebrew
    *makir*; experimental judgments refute it for *hug*-type verbs. -/
def Pr2 (P : Finset A → Prop) (R : A → A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → P {x, y} → R x y

/-- (Pr₄): one-directional `R` already yields the collective
    (*break up*, *divorce*). -/
def Pr4 (P : Finset A → Prop) (R : A → A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → R x y → P {x, y}

/-- (Pr₅): the collective yields `R` in at least one direction — the
    weak disjunctive pattern shared by ALL reciprocal alternations,
    plain and non-plain alike. -/
def Pr5 (P : Finset A → Prop) (R : A → A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → P {x, y} → (R x y ∨ R y x)

/-- Pr₂ delivers both directions, since `{x, y} = {y, x}`. -/
theorem Pr2.both {P : Finset A → Prop} {R : A → A → Prop}
    (h : Pr2 P R) {x y : A} (hxy : x ≠ y) (hP : P {x, y}) :
    R x y ∧ R y x :=
  ⟨h x y hxy hP, h y x hxy.symm (Finset.pair_comm x y ▸ hP)⟩

/-- Pr₄ is logically stronger than Pr₁ (§3.3). -/
theorem Pr4.pr1 {P : Finset A → Prop} {R : A → A → Prop}
    (h : Pr4 P R) : Pr1 P R :=
  fun x y hxy hR _ => h x y hxy hR

/-- Pr₂ is logically stronger than Pr₅. -/
theorem Pr2.pr5 {P : Finset A → Prop} {R : A → A → Prop}
    (h : Pr2 P R) : Pr5 P R :=
  fun x y hxy hP => Or.inl (h x y hxy hP)

/-- Plain reciprocity entails the weak universal Pr₅. -/
theorem PlainReciprocity.pr5 {P : Finset A → Prop} {R : A → A → Prop}
    (h : PlainReciprocity P R) : Pr5 P R :=
  fun x y hxy hP => Or.inl ((h x y hxy).mp hP).1

/-- Plain reciprocity decomposes exactly into Pr₁ together with Pr₂. -/
theorem plainReciprocity_iff_pr1_pr2
    {P : Finset A → Prop} {R : A → A → Prop} :
    PlainReciprocity P R ↔ (Pr1 P R ∧ Pr2 P R) := by
  constructor
  · exact fun h => ⟨fun x y hxy hR hR' => (h x y hxy).mpr ⟨hR, hR'⟩,
      fun x y hxy hP => ((h x y hxy).mp hP).1⟩
  · rintro ⟨h1, h2⟩ x y hxy
    exact ⟨fun hP => h2.both hxy hP, fun h => h1 x y hxy h.1 h.2⟩

/-! ### Table 3: logical patterns per verb -/

/-- A row of Winter's Table 3: which Pr-patterns a non-plain reciprocal
    alternation exhibits (`none` where the paper leaves the cell
    undetermined). Pr₃ — bidirectional `R` *plus simultaneity* yields
    the collective — is event-level and recorded as data only. -/
structure AlternationProfile where
  predicate : String
  pr1 : Option Bool
  pr2 : Option Bool
  pr3 : Bool
  pr4 : Bool
  pr5 : Bool
  deriving DecidableEq, Repr

def hug : AlternationProfile :=
  ⟨"hug", some false, some false, true, false, true⟩
def kiss : AlternationProfile :=
  ⟨"kiss", some false, none, true, false, true⟩
def fight : AlternationProfile :=
  ⟨"fight", some false, some false, true, false, true⟩
def breakUp : AlternationProfile :=
  ⟨"break up", some true, some false, true, true, true⟩
def divorce : AlternationProfile :=
  ⟨"divorce", some true, some false, true, true, true⟩
def collide : AlternationProfile :=
  ⟨"collide", none, some false, true, false, true⟩
def inLove : AlternationProfile :=
  ⟨"be/fall in love", some false, some true, false, false, true⟩
def talk : AlternationProfile :=
  ⟨"talk", some false, some false, false, false, true⟩
def makir : AlternationProfile :=
  ⟨"makir (Hebrew 'know')", some false, some true, false, false, true⟩

def table3 : List AlternationProfile :=
  [hug, kiss, fight, breakUp, divorce, collide, inLove, talk, makir]

/-- §3.3's universal: every alternation in Table 3 satisfies the weak
    disjunctive Pr₅. -/
theorem table3_pr5 : table3.all (·.pr5) := by decide

/-- Data-logic consistency: rows claiming Pr₄ also claim Pr₁, as
    `Pr4.pr1` requires (*break up*, *divorce*). -/
theorem table3_pr4_consistent :
    table3.all (fun r => !r.pr4 || r.pr1 == some true) := by decide

end Winter2018
