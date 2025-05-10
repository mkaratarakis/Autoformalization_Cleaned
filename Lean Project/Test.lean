import Lean
import Mathlib
open Lean Meta Elab Tactic

elab "#listNamespace" nsIdent:ident : command => do
  let env ← getEnv
  let ns := nsIdent.getId
  let constList := env.constants.toList
  let matchingDecls := constList.filterMap fun (name, constInfo) =>
    if ns.isPrefixOf name then
      let kind := match constInfo with
        | .axiomInfo _ => "[axiom]"
        | .defnInfo _ => "[def]"
        | .thmInfo _ => "[thm]"
        | .opaqueInfo _ => "[opaque]"
        | .quotInfo _ => "[quot]"
        | .inductInfo _ => "[inductive]"
        | .ctorInfo _ => "[ctor]"
        | .recInfo _ => "[recursor]"
      some (s!"{kind} {name.toStringWithSep "." true}")
    else
      none
  let listStr := "[" ++ (matchingDecls.intersperse ", ").foldl (· ++ ·) "" ++ "]"
  logInfo m!"Declarations in namespace `{ns}`:\n{listStr}"

#listNamespace Topology
