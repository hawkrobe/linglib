import Linglib.Syntax.Mereological.AngularLocality
import Linglib.Data.Examples.Adger2025

/-!
# Mereological syntax: phrase structure, cyclicity, and islands

Adger replaces set-theoretic Merge by Subjoin, which makes one syntactic object a proper part
of another in one of two dimensions: the first subjunction to an object yields its 1-part, the
extended-projection complement, the second its 2-part, the specifier (`Parthood`). Parthood is
transitive within a dimension only, and Angular Locality lets a part subjoin to a target only
through a single angle: it must be an n-part of some 1-part of the target (`CanSubjoin`). The
book's list of consequences is verified on its own structures: the complement of a head cannot
resubjoin to it (`antilocality`), and subjunction to an unattached object, to a specifier, or
downward fails because the target must contain the mover (`parallel`, `sideward`, `lowering`,
`asked_who`); a 2-part of a 2-part of an object in the target's extended projection subjoins,
while a 1-part of that 2-part does not (`angle`), so that a subjunction blocked from inside a
specifier becomes possible once the mover has subjoined to that specifier (`escape_hatch`). This
is successive cyclicity without phases: *who* reaches the matrix C of *guess who you said fell*
only after subjoining to the embedded C (`said_fell`).

Islands follow from the same mechanism with Dimensionality. Extraction from a nominal runs
through D, so it needs D's 2-part: an indefinite leaves it free and *who did you buy a statue
of* derives (`statue_indefinite`), while a definite fills it with Det and the wh-expression can
neither subjoin to D nor skip it (`statue_definite`). Subjects are not islands as such: a
subject subjoins to T itself (`subject_itself`), and under T[uD] the wh-expression subjoins to D
and on to C (`subject_thetic`), but T[uFam] requires a [Fam]-bearing Det to fill D's 2-part
first, which freezes the topic subject (`subject_topic`). Wh-islands, the WIRE effect, adjunct
islands, *-linearization, and the cross-linguistic feature settings of chapters 5–7 are not
formalized.

## References

* [adger-2025]
-/

namespace Adger2025

open MereologicalSyntax MereologicalSyntax.Parthood

/-! ### Consequences of Angular Locality -/

/-- The objects of the schematic structures. -/
inductive Obj
  | a | b | c | d | e | f | g | u | w | x | y | z
  deriving DecidableEq, Fintype, Repr

/-- `a` with `b` as its 1-part. -/
def superlocal : Parthood Obj where
  onePart | .a => some .b | _ => none
  twoPart _ := none

/-- The complement `b` cannot resubjoin to `a`. -/
theorem antilocality : ¬ superlocal.CanSubjoin .b .a :=
  not_canSubjoin_of_imm_one (acyclic_of_rank (fun | .a => 1 | _ => 0) (by decide)) rfl

/-- Two roots: `d` with 1-part `e`, and `b` with 2-part `a` and 1-part `c`. -/
def parallel : Parthood Obj where
  onePart | .d => some .e | .b => some .c | _ => none
  twoPart | .b => some .a | _ => none

/-- `a` cannot subjoin to the unattached `d`. -/
theorem parallel_blocked : ¬ parallel.CanSubjoin .a .d :=
  not_canSubjoin_of_le (fun | .b => 2 | .a | .d => 1 | _ => 0) (by decide) (by decide)

/-- `c` with 2-part `b` and 1-part `a`. -/
def sideward : Parthood Obj where
  onePart | .c => some .a | _ => none
  twoPart | .c => some .b | _ => none

/-- Neither part of `c` subjoins to the other. -/
theorem sideward_blocked : ¬ sideward.CanSubjoin .a .b ∧ ¬ sideward.CanSubjoin .b .a :=
  ⟨not_canSubjoin_of_le (fun | .c => 1 | _ => 0) (by decide) (by decide),
    not_canSubjoin_of_le (fun | .c => 1 | _ => 0) (by decide) (by decide)⟩

/-- `e` with 2-part `a` and 1-part `f`; `a` with 2-part `d` and 1-part `b`, whose 1-part chain
continues `c`, `g`. -/
def lowering : Parthood Obj where
  onePart | .e => some .f | .a => some .b | .b => some .c | .c => some .g | _ => none
  twoPart | .e => some .a | .a => some .d | _ => none

/-- `d` cannot subjoin downward to `c`. -/
theorem lowering_blocked : ¬ lowering.CanSubjoin .d .c :=
  not_canSubjoin_of_le (fun | .e => 4 | .a => 3 | .b => 2 | .c | .d => 1 | _ => 0) (by decide)
    (by decide)

/-- `y` with 1-part `e`; `e` with 2-part `u` and 1-part `w`; `u` with 2-part `z` and 1-part
`x`. -/
def angle : Parthood Obj where
  onePart | .y => some .e | .e => some .w | .u => some .x | _ => none
  twoPart | .e => some .u | .u => some .z | _ => none

/-- `z`, a 2-part of the 2-part `u` of `e`, subjoins to `y`; `x`, the 1-part of `u`, does not. -/
theorem angle_turns_once : angle.CanSubjoin .z .y ∧ ¬ angle.CanSubjoin .x .y :=
  ⟨⟨.e, .inr (.tail (b := .u) (.single (by decide)) (by decide)), .single (by decide)⟩,
    not_canSubjoin_of_not_nPart_two (S := {.u, .z, .x}) (b := .u) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (not_nPart_of_unique (n := .one) (u := .u) (by decide) (by decide) _)⟩

/-- As `angle`, but `u` has only the 1-part `x`, whose 2-part is `z` and whose 1-part is `g`. -/
def escape : Parthood Obj where
  onePart | .y => some .e | .e => some .w | .u => some .x | .x => some .g | _ => none
  twoPart | .e => some .u | .x => some .z | _ => none

/-- `escape` after `z` subjoins to `u`. -/
def escape' : Parthood Obj where
  onePart | .y => some .e | .e => some .w | .u => some .x | .x => some .g | _ => none
  twoPart | .e => some .u | .x => some .z | .u => some .z | _ => none

/-- `z` cannot subjoin to `y` from inside `u`, but can once it has subjoined to `u`. -/
theorem escape_hatch :
    ¬ escape.CanSubjoin .z .y ∧ escape.subjoin .z .u = some escape' ∧ escape'.CanSubjoin .z .y :=
  ⟨not_canSubjoin_of_not_nPart_two (S := {.u, .x, .z, .g}) (b := .u) (by decide) (by decide)
      (by decide) (by decide) (by decide) fun h =>
        ((nPart_iff_of_unique (n := .two) (u := .x) (by decide) (by decide)).1 h).elim (by decide)
          (not_nPart_of_unique (n := .one) (u := .u) (by decide) (by decide) _),
    by decide, ⟨.e, .inr (.tail (b := .u) (.single (by decide)) (by decide)), .single (by decide)⟩⟩

/-! ### Clausal derivations -/

/-- The categories of the clausal structures; primes mark the embedded clause. -/
inductive Node
  | C | T | v | O | V | Appl | C' | T' | v' | O' | who | you | D | Det | rel | rel' | P | N
  deriving DecidableEq, Fintype, Repr

/-- *We asked who Anson wrote the book*: `who` is the 2-part of `Appl`, whose 1-part `O` has the
embedded `C` as its 2-part. -/
def asked : Parthood Node where
  onePart | .Appl => some .O | .O => some .V | .C => some .T | _ => none
  twoPart | .Appl => some .who | .O => some .C | _ => none

/-- `who` cannot subjoin downward to the embedded `C`. -/
theorem asked_who : ¬ asked.CanSubjoin .who .C :=
  not_canSubjoin_of_le (fun | .Appl => 3 | .O => 2 | .C | .who => 1 | _ => 0) (by decide)
    (by decide)

/-- *Guess who you said fell*: the clausal complement is the 2-part of `O`, and `who` the 2-part
of the embedded `O'`. -/
def said : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .O
    | .C' => some .T' | .T' => some .v' | .v' => some .O' | _ => none
  twoPart | .v => some .you | .O => some .C' | .O' => some .who | _ => none

/-- `said` after `who` subjoins to the embedded `C'`. -/
def said' : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .O
    | .C' => some .T' | .T' => some .v' | .v' => some .O' | _ => none
  twoPart | .v => some .you | .O => some .C' | .O' => some .who | .C' => some .who | _ => none

/-- `who` cannot reach the matrix `C` directly; it subjoins to the embedded `C'`, and from there
reaches `C`. -/
theorem said_fell :
    ¬ said.CanSubjoin .who .C ∧ said.CanSubjoin .who .C' ∧
      said.subjoin .who .C' = some said' ∧ said'.CanSubjoin .who .C :=
  ⟨not_canSubjoin_of_not_nPart_two (S := {.C', .T', .v', .O', .who}) (b := .C') (by decide)
      (by decide) (by decide) (by decide) (by decide) fun h =>
        ((nPart_iff_of_unique (n := .two) (u := .O') (by decide) (by decide)).1 h).elim (by decide)
          (not_nPart_of_unique (n := .one) (u := .v') (by decide) (by decide) _),
    ⟨.O', .inr (.single (by decide)),
      .tail (b := .T') (.tail (b := .v') (.single (by decide)) (by decide)) (by decide)⟩,
    by decide,
    ⟨.O, .inr (.tail (b := .C') (.single (by decide)) (by decide)),
      .tail (b := .T) (.tail (b := .v) (.single (by decide)) (by decide)) (by decide)⟩⟩

/-! ### Nominal islands -/

/-- *Who did you buy a statue of*: the object `D` is the 2-part of `O`; its 1-part is the
relational `rel`, with 2-part `P` (to which `who` has subjoined) and 1-part `N`. -/
def statue : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .O | .D => some .rel | .rel => some .N
    | _ => none
  twoPart | .v => some .you | .O => some .D | .rel => some .P | .P => some .who | _ => none

/-- `statue` after `who` subjoins to the indefinite `D`. -/
def statue' : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .O | .D => some .rel | .rel => some .N
    | _ => none
  twoPart
    | .v => some .you | .O => some .D | .rel => some .P | .P => some .who | .D => some .who
    | _ => none

/-- *Who did you buy the statue of*: `Det` has subjoined to `D`. -/
def theStatue : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .O | .D => some .rel | .rel => some .N
    | _ => none
  twoPart
    | .v => some .you | .O => some .D | .rel => some .P | .P => some .who | .D => some .Det
    | _ => none

/-- `who` is a 2-part of `rel` and cannot reach `C` from there, but it subjoins to the indefinite
`D`, becoming a 2-part of `O`, and then reaches `C`. -/
theorem statue_indefinite :
    ¬ statue.CanSubjoin .who .C ∧ statue.CanSubjoin .who .D ∧
      statue.subjoin .who .D = some statue' ∧ statue'.CanSubjoin .who .C :=
  ⟨not_canSubjoin_of_not_nPart_two (S := {.D, .rel, .P, .N, .who}) (b := .D) (by decide)
      (by decide) (by decide) (by decide) (by decide) fun h =>
        ((nPart_iff_of_unique (n := .two) (u := .P) (by decide) (by decide)).1 h).elim (by decide)
          fun h => ((nPart_iff_of_unique (n := .two) (u := .rel) (by decide) (by decide)).1 h).elim
            (by decide) (not_nPart_of_unique (n := .one) (u := .D) (by decide) (by decide) _),
    ⟨.rel, .inr (.tail (b := .P) (.single (by decide)) (by decide)), .single (by decide)⟩,
    by decide,
    ⟨.O, .inr (.tail (b := .D) (.single (by decide)) (by decide)),
      .tail (b := .T) (.tail (b := .v) (.single (by decide)) (by decide)) (by decide)⟩⟩

/-- With `Det` in `D`'s 2-part, Angular Locality still admits `who` at `D` but Dimensionality
refuses it, and `C` is out of reach. -/
theorem statue_definite :
    theStatue.CanSubjoin .who .D ∧ theStatue.subjoin .who .D = none ∧
      ¬ theStatue.CanSubjoin .who .C :=
  ⟨⟨.rel, .inr (.tail (b := .P) (.single (by decide)) (by decide)), .single (by decide)⟩,
    subjoin_eq_none_of_full rfl rfl,
    not_canSubjoin_of_not_nPart_two (S := {.D, .Det, .rel, .P, .N, .who}) (b := .D) (by decide)
      (by decide) (by decide) (by decide) (by decide) fun h =>
        ((nPart_iff_of_unique (n := .two) (u := .P) (by decide) (by decide)).1 h).elim (by decide)
          fun h => ((nPart_iff_of_unique (n := .two) (u := .rel) (by decide) (by decide)).1 h).elim
            (by decide) (not_nPart_of_unique (n := .one) (u := .D) (by decide) (by decide) _)⟩

/-! ### Subject islands -/

/-- A subject `D` in the 2-part of `v`: its 1-part `rel` has 2-part `Det` and 1-part `rel'`, whose
2-part is `who`. -/
def subject : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .V | .D => some .rel | .rel => some .rel'
    | .rel' => some .N | _ => none
  twoPart | .v => some .D | .rel => some .Det | .rel' => some .who | _ => none

/-- `subject` after `who` subjoins to `D`, under `T[uD]`. -/
def thetic : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .V | .D => some .rel | .rel => some .rel'
    | .rel' => some .N | _ => none
  twoPart
    | .v => some .D | .rel => some .Det | .rel' => some .who | .D => some .who | _ => none

/-- `subject` after `Det[uD, Fam]` subjoins to `D`, as `T[uFam]` requires. -/
def topic : Parthood Node where
  onePart
    | .C => some .T | .T => some .v | .v => some .V | .D => some .rel | .rel => some .rel'
    | .rel' => some .N | _ => none
  twoPart | .v => some .D | .rel => some .Det | .rel' => some .who | .D => some .Det | _ => none

/-- The subject subjoins to `T` whether or not `Det` has filled its 2-part. -/
theorem subject_itself : subject.CanSubjoin .D .T ∧ topic.CanSubjoin .D .T :=
  ⟨⟨.v, .inr (.single (by decide)), .single (by decide)⟩,
    ⟨.v, .inr (.single (by decide)), .single (by decide)⟩⟩

/-- Under `T[uD]`, `who` subjoins to `D` and then to `C`. -/
theorem subject_thetic :
    subject.CanSubjoin .who .D ∧ subject.subjoin .who .D = some thetic ∧
      thetic.CanSubjoin .who .C :=
  ⟨⟨.rel', .inr (.single (by decide)), .tail (b := .rel) (.single (by decide)) (by decide)⟩,
    by decide,
    ⟨.v, .inr (.tail (b := .D) (.single (by decide)) (by decide)),
      .tail (b := .T) (.single (by decide)) (by decide)⟩⟩

/-- Under `T[uFam]`, `Det` fills `D`'s 2-part, and `who` can neither subjoin to `D` nor reach
`C`. -/
theorem subject_topic :
    subject.subjoin .Det .D = some topic ∧ topic.subjoin .who .D = none ∧
      ¬ topic.CanSubjoin .who .C :=
  ⟨by decide, subjoin_eq_none_of_full rfl rfl,
    not_canSubjoin_of_not_nPart_two (S := {.D, .Det, .rel, .rel', .N, .who}) (b := .D)
      (by decide) (by decide) (by decide) (by decide) (by decide) fun h =>
        ((nPart_iff_of_unique (n := .two) (u := .rel') (by decide) (by decide)).1 h).elim
          (by decide) (not_nPart_of_unique (n := .one) (u := .rel) (by decide) (by decide) _)⟩

end Adger2025
