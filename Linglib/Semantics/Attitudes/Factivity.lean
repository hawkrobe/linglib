import Mathlib.Tactic.TypeStar

/-!
# Factive and non-factive attitude semantics

The factive/non-factive distinction of [kiparsky-kiparsky-1970] and
[karttunen-1971] over Boolean world models: a world type carries
orthogonal dimensions — `HasComplement` (is the complement true?) and
`HasBelief` (does the agent believe it?) — and the know-type and
think-type verbs differ in whether the complement dimension enters the
lexical semantics:

| Verb form         | Semantics  | Factivity   |
|-------------------|------------|-------------|
| "X knows C"       | BEL ∧ C    | factive     |
| "X doesn't know"  | ¬(BEL ∧ C) | factive     |
| "X thinks C"      | BEL        | non-factive |
| "X doesn't think" | ¬BEL       | non-factive |

Factivity is veridicality of the positive form
(`factivePos_entails_c`), and know is strictly stronger than think
(`factive_entails_nonfactive`). `QUD` is the two-question space of the
projection experiments (BEL? and C?), and `assumesComplement` renders
"the speaker assumes C" as C holding throughout a belief state.

The semantics is `Bool`-valued deliberately: these meanings feed the
ℚ-valued RSA tables of [scontras-tonhauser-2025] (`Studies/
ScontrasTonhauser2025.lean`) and [grove-white-2025]-style models
(`Studies/GroveWhite2025.lean`) as literal-listener truth tables; the
Prop migration is coupled to the planned RSA measures migration.
-/

namespace Factivity

/-- The world type carries a complement dimension: is the complement
    true at `w`? -/
class HasComplement (W : Type*) where
  c : W → Bool

/-- The world type carries a belief dimension: does the agent believe
    the complement at `w`? -/
class HasBelief (W : Type*) where
  bel : W → Bool

variable {W : Type*}

/-! ### Lexical semantics -/

/-- Factive positive: "X knows C" is `BEL ∧ C`. -/
def factivePos [HasBelief W] [HasComplement W] (w : W) : Bool :=
  HasBelief.bel w && HasComplement.c w

/-- Factive negative: "X doesn't know C" is `¬(BEL ∧ C)`. -/
def factiveNeg [HasBelief W] [HasComplement W] (w : W) : Bool :=
  !(HasBelief.bel w && HasComplement.c w)

/-- Non-factive positive: "X thinks C" is `BEL`. -/
def nonFactivePos [HasBelief W] (w : W) : Bool :=
  HasBelief.bel w

/-- Non-factive negative: "X doesn't think C" is `¬BEL`. -/
def nonFactiveNeg [HasBelief W] (w : W) : Bool :=
  !HasBelief.bel w

/-! ### Entailment -/

/-- Factive positive entails the complement — the defining property of
    factivity. -/
theorem factivePos_entails_c [HasBelief W] [HasComplement W] (w : W)
    (h : factivePos w = true) : HasComplement.c w = true :=
  (Bool.and_eq_true _ _ |>.mp h).2

/-- Factive positive entails belief. -/
theorem factivePos_entails_bel [HasBelief W] [HasComplement W] (w : W)
    (h : factivePos w = true) : HasBelief.bel w = true :=
  (Bool.and_eq_true _ _ |>.mp h).1

/-- Know entails think: factivity is strictly stronger than belief. -/
theorem factive_entails_nonfactive [HasBelief W] [HasComplement W] (w : W)
    (h : factivePos w = true) : nonFactivePos w = true :=
  (Bool.and_eq_true _ _ |>.mp h).1

/-! ### Question under discussion -/

/-- The two-question space of the projection experiments: BEL? and
    C? — the orthogonal dimensions of a `HasBelief`/`HasComplement`
    world. -/
inductive QUD where
  /-- "Does X believe C?" -/
  | bel
  /-- "Is C true?" -/
  | c
  deriving DecidableEq, Repr, Inhabited

/-- The speaker assumes the complement: C holds at every world of the
    belief state. -/
def assumesComplement [HasComplement W] (membership : W → Bool)
    (allWorlds : List W) : Bool :=
  allWorlds.all fun w => !membership w || HasComplement.c w

end Factivity
