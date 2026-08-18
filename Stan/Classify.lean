/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
module

public meta import Lean

/-!
# Declaration classification and resolution

Provides a fine-grained classification of non-user-facing declarations
and a recursive resolution function that maps any declaration to its
user-facing parent.

Each `NonUserReason` constructor carries enough data to resolve
the declaration to its user-facing parent in one step.
-/

public meta section

open Lean Meta

namespace Stan

/-- Why a declaration is not user-facing, carrying enough info to resolve to the parent. -/
inductive NonUserReason where
  /-- Name starts with `_` (e.g. `_private`, `_proof_1`). Parent: `getPrefix`. -/
  | isInternal
  /-- Name ends with `_impl`, `_uniq`, etc. Parent: `getPrefix`. -/
  | isImplDetail
  /-- Structure field projection. Parent: the structure. -/
  | isProjection   (structName : Name)
  /-- Auxiliary recursor: `.casesOn`, `.recOn`, `.below`, `.brecOn`. Parent: `getPrefix`. -/
  | isAuxRec
  /-- `.noConfusion`. Parent: `getPrefix`. -/
  | isNoConf
  /-- Match auxiliary: `.match_N`. Parent: `getPrefix`. -/
  | isMatcher
  /-- `.ctorIdx` function. Parent: the inductive type. -/
  | isCtorIdx      (inductName : Name)
  /-- Constructor (e.g. `.mk`). Parent: the inductive type. -/
  | isCtor         (inductName : Name)
  /-- Recursor (e.g. `.rec`). Parent: the inductive type. -/
  | isRec          (inductName : Name)
  /-- Quotient constant. Parent: `getPrefix`. -/
  | isQuot
  /-- Equation lemma (`.eq_1`, `.eq_def`, etc.). Parent: the source definition. -/
  | isEqnLemma     (defName : Name)
  /-- Reserved name (`.congr_simp`, `.hcongr_N`, etc.). Parent: `getPrefix`. -/
  | isReserved
  /-- Constructor derivative (`.inj`, `.injEq`, `.sizeOf_spec`). Parent: the inductive type. -/
  | isCtorDeriv    (inductName : Name)
  /-- `.noConfusionType`. Parent: `getPrefix` (the inductive type). -/
  | isNoConfTy

/-- Given a `NonUserReason`, return the parent name that this declaration derives from. -/
def NonUserReason.parent (name : Name) : NonUserReason → Name
  | .isProjection structName    => structName
  | .isCtor inductName          => inductName
  | .isRec inductName           => inductName
  | .isCtorIdx inductName       => inductName
  | .isCtorDeriv inductName     => inductName
  | .isEqnLemma defName        => defName
  | _                           => name.getPrefix

/-- Check if `name` is a `.ctorIdx` function for an inductive type.
    Inlines the logic from `isCtorIdxCore?` which may not be directly accessible. -/
private def checkCtorIdx? (env : Environment) (name : Name) : Option NonUserReason :=
  match name with
  | .str indName s =>
    if s == "ctorIdx" || s == "toCtorIdx" || s == "ctorElimType" then
      match isInductiveCore? env indName with
      | some iv => some (.isCtorIdx iv.name)
      | none    => none
    else none
  | _ => none

/-- Check if `name` is a constructor derivative (`.inj`, `.injEq`, `.sizeOf_spec`)
    by verifying the suffix AND that the parent is a constructor. -/
private def checkCtorDeriv? (env : Environment) (name : Name) : Option NonUserReason :=
  match name with
  | .str p s =>
    if s == "inj" || s == "injEq" || s == "sizeOf_spec" then
      match env.find? p with
      | some (.ctorInfo cv) => some (.isCtorDeriv cv.induct)
      | _                   => none
    else none
  | _ => none

/-- Classify a declaration as non-user-facing.
    Returns `some reason` if it is compiler-generated or auxiliary,
    `none` if it is user-facing.

    Classification order:
    1. Internal names / implementation details (pure name checks)
    2. Projections (structural API: `getProjectionFnInfo?`)
    3. Aux recursors, noConfusion (structural API)
    4. Matchers (structural API: `isMatcherCore`)
    5. ctorIdx (structural check on name + `isInductiveCore?`)
    6. Constructors, recursors, quotients (ConstantInfo kind)
    7. Equation lemmas (structural API: `declFromEqLikeName`)
    8. Reserved names (structural API: `isReservedName`)
    9. Constructor derivatives `.inj`, `.injEq`, `.sizeOf_spec`
       (suffix + structural validation: parent must be a constructor)
    10. `.noConfusionType` (suffix check)
-/
def classifyNonUser (env : Environment) (name : Name) : Option NonUserReason :=
  -- 1. Internal / implementation detail
  if name.isInternal then some .isInternal
  else if name.isImplementationDetail then some .isImplDetail
  -- 2. Projections
  else if let some info := env.getProjectionFnInfo? name then
    some <| .isProjection <| match env.find? info.ctorName with
      | some (.ctorInfo cv) => cv.induct
      | _                   => name.getPrefix
  -- 3. Aux recursors & noConfusion
  else if isAuxRecursor env name then some .isAuxRec
  else if isNoConfusion env name then some .isNoConf
  -- 4. Matchers
  else if isMatcherCore env name then some .isMatcher
  -- 5. ctorIdx
  else if let some r := checkCtorIdx? env name then some r
  -- 6. ConstantInfo kind
  else match env.find? name with
    | some (.ctorInfo cv) => some (.isCtor cv.induct)
    | some (.recInfo rv)  => some (.isRec (rv.all.head?.getD name.getPrefix))
    | some (.quotInfo _)  => some .isQuot
    | _ =>
      -- 7. Equation lemmas
      if let some (defName, _) := declFromEqLikeName env name then some (.isEqnLemma defName)
      -- 8. Reserved names (.congr_simp, .hcongr_N, etc.)
      else if isReservedName env name then some .isReserved
      -- 9. Constructor derivatives
      else if let some r := checkCtorDeriv? env name then some r
      -- 10. noConfusionType
      else match name with
        | .str _ "noConfusionType" => some .isNoConfTy
        | _ => none

/-- Recursively resolve a name to its user-facing parent declaration.
    Strips `_private` wrappers, then follows `classifyNonUser` until the name
    is user-facing or fuel runs out. -/
def resolveToUser (env : Environment) (name : Name) (fuel : Nat := 8) : Name :=
  let name := (privateToUserName? name).getD name
  match fuel, classifyNonUser env name with
  | 0, _            => name
  | _, none          => name
  | n+1, some reason => resolveToUser env (reason.parent name) n

end Stan

end
