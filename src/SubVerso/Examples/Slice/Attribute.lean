/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.Data.Position
public import Lean.Syntax
public import Lean.KeyedDeclsAttribute
public meta import Lean.KeyedDeclsAttribute
public import SubVerso.Compat
public section

namespace SubVerso.Examples.Slice.Attribute

open Lean

private unsafe def mkSliceExpanderAttrUnsafe (attrName typeName : Name) (descr : String) (attrDeclName : Name) : IO (KeyedDeclsAttribute α) :=
  KeyedDeclsAttribute.init {
    name := attrName,
    descr := descr,
    valueTypeName := typeName
  } attrDeclName

@[implemented_by mkSliceExpanderAttrUnsafe]
private opaque mkSliceExpanderAttributeSafe (attrName typeName : Name) (desc : String) (attrDeclName : Name) : IO (KeyedDeclsAttribute α)

private def mkSliceExpanderAttribute (attrName typeName : Name) (desc : String) (attrDeclName : Name := by exact decl_name%) : IO (KeyedDeclsAttribute α) :=
  mkSliceExpanderAttributeSafe attrName typeName desc attrDeclName

abbrev Slicer := (Syntax → Syntax) → Syntax → Array Compat.Syntax.Range → Option Syntax

initialize slicerAttr : KeyedDeclsAttribute Slicer ←
  mkSliceExpanderAttribute `slicer ``Slicer "Indicates that this function is used to slice the given syntax kind"

unsafe def slicersForUnsafe [Monad m] [MonadEnv m] (x : Name) : m (List Slicer) := do
  let expanders := slicerAttr.getEntries (← getEnv) x
  return expanders.map (·.value)

@[implemented_by slicersForUnsafe]
opaque slicersFor [Monad m] [MonadEnv m] (x : Name) : m (List Slicer)


unsafe def slicersInEnvUnsafe (env : Environment) (x : Name) : List Slicer :=
  let expanders := slicerAttr.getEntries env x
  expanders.map (·.value)

@[implemented_by slicersInEnvUnsafe]
opaque slicersInEnv (env : Environment) (x : Name) : List Slicer
