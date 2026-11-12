/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Json
public section

open Lean

namespace SubVerso.Highlighting.Timings

/-- A reported category of highlighting work for purposes of timings. -/
inductive Category where
  | other
  | setup
  | signatures
  | variableTypes
  | withType
  | goalHypotheses
  | goalTargets
  | messages
deriving Inhabited, BEq, Repr

def Category.all : Array Category :=
  #[.other, .setup, .signatures, .variableTypes, .withType, .goalHypotheses, .goalTargets, .messages]

def Category.index : Category → Nat
  | .other => 0
  | .setup => 1
  | .signatures => 2
  | .variableTypes => 3
  | .withType => 4
  | .goalHypotheses => 5
  | .goalTargets => 6
  | .messages => 7

def Category.name : Category → String
  | .other => "other"
  | .setup => "setup"
  | .signatures => "signatures"
  | .variableTypes => "variableTypes"
  | .withType => "withType"
  | .goalHypotheses => "goalHypotheses"
  | .goalTargets => "goalTargets"
  | .messages => "messages"

inductive Counter where
  | delaboratorCalls
  | runMetaMCalls
  | termCacheHits
  | termCacheMisses
  | termCacheUncached
  | varTypeCacheHits
  | varTypeCacheMisses
  | termCacheEvictions
  | varTypeCacheEvictions
  | goalCacheHits
  | goalCacheMisses
  | goalCacheUncached
  | hypCacheHits
  | hypCacheMisses
  | hypCacheUncached
  | hypCacheEvictions
deriving Inhabited, BEq, Repr

def Counter.all : Array Counter :=
  #[.delaboratorCalls, .runMetaMCalls, .termCacheHits, .termCacheMisses, .termCacheUncached,
    .varTypeCacheHits, .varTypeCacheMisses, .termCacheEvictions, .varTypeCacheEvictions,
    .goalCacheHits, .goalCacheMisses, .goalCacheUncached, .hypCacheHits, .hypCacheMisses,
    .hypCacheUncached, .hypCacheEvictions]

def Counter.index : Counter → Nat
  | .delaboratorCalls => 0
  | .runMetaMCalls => 1
  | .termCacheHits => 2
  | .termCacheMisses => 3
  | .termCacheUncached => 4
  | .varTypeCacheHits => 5
  | .varTypeCacheMisses => 6
  | .termCacheEvictions => 7
  | .varTypeCacheEvictions => 8
  | .goalCacheHits => 9
  | .goalCacheMisses => 10
  | .goalCacheUncached => 11
  | .hypCacheHits => 12
  | .hypCacheMisses => 13
  | .hypCacheUncached => 14
  | .hypCacheEvictions => 15

def Counter.name : Counter → String
  | .delaboratorCalls => "delaboratorCalls"
  | .runMetaMCalls => "runMetaMCalls"
  | .termCacheHits => "termCacheHits"
  | .termCacheMisses => "termCacheMisses"
  | .termCacheUncached => "termCacheUncached"
  | .varTypeCacheHits => "varTypeCacheHits"
  | .varTypeCacheMisses => "varTypeCacheMisses"
  | .termCacheEvictions => "termCacheEvictions"
  | .varTypeCacheEvictions => "varTypeCacheEvictions"
  | .goalCacheHits => "goalCacheHits"
  | .goalCacheMisses => "goalCacheMisses"
  | .goalCacheUncached => "goalCacheUncached"
  | .hypCacheHits => "hypCacheHits"
  | .hypCacheMisses => "hypCacheMisses"
  | .hypCacheUncached => "hypCacheUncached"
  | .hypCacheEvictions => "hypCacheEvictions"

end Timings

open Timings in
structure Timings where
  stack : Array Category := #[]
  since : Nat := 0
  exclusive : Array Nat := Category.all.map fun _ => 0
  counters : Array Nat := Counter.all.map fun _ => 0
deriving Inhabited

namespace Timings

/-- Adds the time since the last event to the category at the top of the stack, if there is one. -/
def charge (st : Timings) (now : Nat) : Timings :=
  match st.stack.back? with
  | some c => { st with exclusive := st.exclusive.modify c.index (· + (now - st.since)), since := now }
  | none => { st with since := now }

def bump (st : Timings) (c : Counter) : Timings :=
  { st with counters := st.counters.modify c.index (· + 1) }

/-- Creates a new timer state initialized to `now`. -/
def startCategories (ref : IO.Ref Timings) (now : Nat) : IO Unit :=
  ref.modify fun st => { st with stack := #[.other], since := now }

/-- Stops a timer, clearing its stack. -/
def stopCategories (ref : IO.Ref Timings) (now : Nat) : IO Unit :=
  ref.modify fun st => { st.charge now with stack := #[] }

/-- Indicates that work is now in category `c` -/
def enter (ref : IO.Ref Timings) (c : Category) : IO Nat := do
  let now ← IO.monoNanosNow
  ref.modifyGet fun st =>
    let st := st.charge now
    (st.stack.size, { st with stack := st.stack.push c })

/-- Indicates that work has returned to the parent category. -/
def exit (ref : IO.Ref Timings) (depth : Nat) : IO Unit := do
  let now ← IO.monoNanosNow
  ref.modify fun st =>
    let st := st.charge now
    { st with stack := st.stack.extract 0 depth }

/-- Converts a nanosecond count to a JSON value. -/
def seconds (nanos : Nat) : Json :=
  .num ⟨Int.ofNat (nanos / 1000), 6⟩
