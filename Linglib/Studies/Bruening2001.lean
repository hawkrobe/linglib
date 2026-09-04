import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.SyntacticObject.Subterm

/-!
# Bruening 2001: QR obeys Superiority

This file formalizes the account of frozen scope in [bruening-2001]. *I gave a child each doll* has
only the surface reading while its dative counterpart *I gave a doll to each child* is ambiguous,
and the freezing is not an inability to move: it holds between two objects but not between an
object and the subject, and it disappears under passivization. Bruening derives this from Shortest
([richards-1997]): a quantifier raises by attraction to a head bearing a P-feature, the attractor
must take the structurally highest candidate first, and later movements tuck in beneath, so the
attraction order — and with it the scope order — is the base order.

The contrast then follows from structure alone. In the double object construction the first object
asymmetrically c-commands the second ([barss-lasnik-1986], [larson-1988], [pylkkanen-2008]), so
only the goal can be attracted first and scope is frozen; in the locative the direct object and the
PP are co-arguments that c-command each other, so either may go first and scope is free. The
subject sits outside the attracting head's domain, which is why the second object can still scope
over it, and why a passivized double object construction is ambiguous again.

## Main definitions

* `Attractable`, `LicensedFirst` — attraction by a P-feature-bearing head, restricted by Shortest
* `Ambiguous` — two candidates may be attracted first, so the derivation fixes no scope order

## Main results

* `not_licensedFirst_of_asymCCommand` — an asymmetrically c-commanded candidate never goes first
* `ambiguous_of_mutual_cCommand` — mutually c-commanding candidates both may
* `doc_frozen`, `locative_ambiguous` — the double object construction freezes, the locative does not
* `subject_not_attractable`, `passive_ambiguous` — the freezing is relativized to the two objects

## References

* [bruening-2001]
* [richards-1997]
* [barss-lasnik-1986]
* [larson-1988]
* [pylkkanen-2008]
-/

namespace Bruening2001

open Minimalist Minimalist.SyntacticObject

/-! ### Attraction under Shortest -/

variable {tree head x y : SyntacticObject} {qs : List SyntacticObject}

/-- A quantifier the P-feature-bearing head can attract: one in its c-command domain. The subject,
merged in the head's specifier, is not among them. -/
def Attractable (tree head x : SyntacticObject) : Prop := cCommandsIn tree head x

/-- Shortest: attracting `x` first is licensed only when no other candidate asymmetrically
c-commands it — such a candidate would form a smaller well-formed pair with the attractor. -/
def LicensedFirst (tree head : SyntacticObject) (qs : List SyntacticObject)
    (x : SyntacticObject) : Prop :=
  x ∈ qs ∧ Attractable tree head x ∧
    ∀ y ∈ qs, Attractable tree head y → ¬ asymCCommandsIn tree y x

instance : Decidable (Attractable tree head x) := inferInstanceAs (Decidable (cCommandsIn _ _ _))

instance [DecidableEq SyntacticObject] : Decidable (LicensedFirst tree head qs x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Since later movements tuck in beneath earlier ones, the quantifier attracted first takes widest
scope: scope is ambiguous exactly when two candidates may be attracted first. -/
def Ambiguous (tree head : SyntacticObject) (qs : List SyntacticObject) : Prop :=
  ∃ x ∈ qs, ∃ y ∈ qs, x ≠ y ∧ LicensedFirst tree head qs x ∧ LicensedFirst tree head qs y

/-- A candidate that some other candidate asymmetrically c-commands can never be attracted first,
whatever interpretation moving it first would produce. -/
theorem not_licensedFirst_of_asymCCommand (hy : y ∈ qs) (hattr : Attractable tree head y)
    (hasym : asymCCommandsIn tree y x) : ¬ LicensedFirst tree head qs x := by
  rintro ⟨-, -, h⟩
  exact h y hy hattr hasym

/-- Two candidates that c-command each other both satisfy Shortest, so either may be attracted
first: the pairs they form with the attractor are equivalent. -/
theorem ambiguous_of_mutual_cCommand (hx : x ∈ qs) (hy : y ∈ qs) (hne : x ≠ y)
    (hattrx : Attractable tree head x) (hattry : Attractable tree head y)
    (hxy : cCommandsIn tree x y) (hyx : cCommandsIn tree y x)
    (hother : ∀ z ∈ qs, z = x ∨ z = y) : Ambiguous tree head qs := by
  have key : ∀ a ∈ qs, ∀ b ∈ qs, Attractable tree head a → ¬ asymCCommandsIn tree b a := by
    rintro a ha b hb - ⟨hba, hab⟩
    rcases hother a ha with rfl | rfl <;> rcases hother b hb with rfl | rfl
    exacts [hab hba, hab hxy, hab hyx, hab hba]
  exact ⟨x, hx, y, hy, hne, ⟨hx, hattrx, fun b hb hattrb => key x hx b hb hattrx⟩,
    ⟨hy, hattry, fun b hb hattrb => key y hy b hb hattry⟩⟩

/-! ### The double object construction -/

/-- The light verb bearing the P-feature that attracts quantifiers ([kratzer-1996]'s Voice). -/
def v_tok : LIToken := ⟨.simple .Voice [.V] "v[P]", 400⟩
/-- The applicative head introducing the first object ([pylkkanen-2008]). -/
def appl_tok : LIToken := ⟨.simple .Appl [.D] "Appl", 402⟩
/-- The ditransitive verb. -/
def gave_tok : LIToken := ⟨.simple .V [.Appl] "gave", 404⟩
/-- The subject. -/
def subj_tok : LIToken := ⟨.simple .D [] "Ozzy", 406⟩
/-- The first object — the goal. -/
def goal_tok : LIToken := ⟨.simple .D [] "a girl", 407⟩
/-- The second object — the theme. -/
def theme_tok : LIToken := ⟨.simple .D [] "every telescope", 408⟩
/-- The preposition of the locative variant. -/
def to_tok : LIToken := ⟨.simple .P [.D] "to", 409⟩

/-- The double object structure `[Ozzy [v [gave [a girl [Appl every telescope]]]]]`: the first
object is the argument of the applicative head, merged above the projection containing the second,
so it asymmetrically c-commands it. -/
def docTree : PlanarSyntacticObject :=
  (subj_tok * (v_tok * (gave_tok * (goal_tok * (appl_tok * theme_tok)))))

/-- The quantifiers competing for attraction in the double object construction. -/
def docQuantifiers : List SyntacticObject := [leaf goal_tok, leaf theme_tok]

/-- The first object asymmetrically c-commands the second ([barss-lasnik-1986]). -/
theorem doc_goal_asym_theme :
    asymCCommandsIn docTree (leaf goal_tok) (leaf theme_tok) := by decide

/-- Only the first object may be attracted first, so the derivation fixes the base order and the
second object cannot come to scope over the first: *I gave a (#different) child each doll*. -/
theorem doc_frozen :
    LicensedFirst docTree (leaf v_tok) docQuantifiers (leaf goal_tok) ∧
      ¬ LicensedFirst docTree (leaf v_tok) docQuantifiers (leaf theme_tok) :=
  ⟨by decide,
    not_licensedFirst_of_asymCCommand (y := leaf goal_tok) (by simp [docQuantifiers])
      (by decide) doc_goal_asym_theme⟩

/-- No two candidates may be attracted first: the double object construction is unambiguous. -/
theorem doc_not_ambiguous : ¬ Ambiguous docTree (leaf v_tok) docQuantifiers := by
  rintro ⟨x, hx, y, hy, hne, hlx, hly⟩
  have hcases : ∀ z ∈ docQuantifiers, z = leaf goal_tok ∨ z = leaf theme_tok := by
    simp [docQuantifiers]
  rcases hcases x hx with rfl | rfl <;> rcases hcases y hy with rfl | rfl
  exacts [hne rfl, doc_frozen.2 hly, doc_frozen.2 hlx, hne rfl]

/-! ### The locative variant -/

/-- The locative structure `[Ozzy [v [gave [every telescope [to a girl]]]]]`: the direct object and
the PP are co-arguments of the same head, hence sisters, and c-command each other. -/
def locativeTree : PlanarSyntacticObject :=
  (subj_tok * (v_tok * (gave_tok * (theme_tok * (to_tok * goal_tok)))))

/-- The PP that pied-pipes the goal. -/
def ppToGoal : PlanarSyntacticObject := to_tok * goal_tok

/-- The candidates in the locative: the direct object, and the PP that pied-pipes the goal. -/
def locativeQuantifiers : List SyntacticObject := [leaf theme_tok, ppToGoal]

/-- Direct object and PP c-command each other, so neither asymmetrically c-commands the other. -/
theorem locative_mutual_cCommand :
    cCommandsIn locativeTree (leaf theme_tok) ppToGoal ∧
      cCommandsIn locativeTree ppToGoal (leaf theme_tok) := by
  constructor <;> decide

/-- Either candidate may be attracted first, so the locative is ambiguous: *I gave a doll to each
child* has both readings. -/
theorem locative_ambiguous : Ambiguous locativeTree (leaf v_tok) locativeQuantifiers := by
  refine ambiguous_of_mutual_cCommand (by simp [locativeQuantifiers])
    (by simp [locativeQuantifiers]) (by decide) (by decide) (by decide)
    locative_mutual_cCommand.1 locative_mutual_cCommand.2 ?_
  simp [locativeQuantifiers]

/-! ### The freezing is relativized -/

/-- The subject is merged in the attractor's specifier, outside its c-command domain, so it never
competes with the objects for attraction — which is why either object can take scope over it even
where the two objects' relative scope is frozen. -/
theorem subject_not_attractable :
    ¬ Attractable docTree (leaf v_tok) (leaf subj_tok) := by decide

/-- The passive of a double object construction: with no external argument, the goal raises to the
subject position, out of the attractor's domain, leaving the theme as the only candidate. -/
def passiveTree : PlanarSyntacticObject :=
  (goal_tok * (v_tok * (gave_tok * (appl_tok * theme_tok))))

/-- In the passive the derived subject is no longer attractable while the theme is, so Shortest
imposes no order between them and the ambiguity returns: *a (different) girl was given every
telescope*. -/
theorem passive_ambiguous :
    ¬ Attractable passiveTree (leaf v_tok) (leaf goal_tok) ∧
      Attractable passiveTree (leaf v_tok) (leaf theme_tok) := by
  constructor <;> decide

end Bruening2001
