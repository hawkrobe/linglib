module

public import Linglib.Data.Examples.Schema

/-!
# `MoensSteedman1988` — typed example data

Auto-generated from `Linglib/Data/Examples/MoensSteedman1988.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace MoensSteedman1988.Examples`.
-/

@[expose] public section

namespace MoensSteedman1988.Examples

open Data.Examples

def when_state : Datum :=
  { id := "moenssteedman1988_when_state"
    source := ⟨"moens-steedman-1988", "UNVERIFIED §4.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When John knew the answer, he raised his hand."
    glossedTokens := []
    context := "*When* with a stative embedded clause: the state is homogeneous, so any subinterval supplies the reference point and no coercion is needed."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "when"), ("clause", "embedded"), ("vendler_class", "state")] }

def when_activity : Datum :=
  { id := "moenssteedman1988_when_activity"
    source := ⟨"moens-steedman-1988", "UNVERIFIED §4.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When John ran, the crowd cheered."
    glossedTokens := []
    context := "*When* with an activity (process) embedded clause: interpreted as 'just when John started running' — the activity is coerced to its onset point."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "when"), ("clause", "embedded"), ("vendler_class", "activity"), ("coercion", "inception"), ("result_class", "achievement")] }

def when_accomplishment : Datum :=
  { id := "moenssteedman1988_when_accomplishment"
    source := ⟨"moens-steedman-1988", "UNVERIFIED §4.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When John built the house, he sold it."
    glossedTokens := []
    context := "*When* with an accomplishment (culminated process) embedded clause: interpreted as 'when John finished building' — the accomplishment is coerced to its culmination point."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "when"), ("clause", "embedded"), ("vendler_class", "accomplishment"), ("coercion", "culmination"), ("result_class", "achievement")] }

def when_achievement : Datum :=
  { id := "moenssteedman1988_when_achievement"
    source := ⟨"moens-steedman-1988", "UNVERIFIED §4.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When John arrived, Mary left."
    glossedTokens := []
    context := "*When* with an achievement (culmination) embedded clause: already punctual, so it directly supplies the reference point and no coercion is needed."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "when"), ("clause", "embedded"), ("vendler_class", "achievement")] }

def all : List Datum := [when_state, when_activity, when_accomplishment, when_achievement]

end MoensSteedman1988.Examples
