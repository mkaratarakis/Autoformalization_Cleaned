import Lean
import Mathlib
open Lean Meta Elab Tactic

elab "#listNamespace" nsIdent:ident : command => do
  let env ← getEnv
  let ns := nsIdent.getId
  let constList := env.constants.toList
  let matchingDecls := constList.filterMap fun (name, constInfo) =>
    if ¬ ns.isPrefixOf name then
      none
    else match name with
      | .str _ s =>
          if s.endsWith "_cstage1" || s.endsWith "_cstage2" || s == "eq_1" then
            none
          else
            let kind := match constInfo with
              | .axiomInfo _ => "[axiom]"
              | .thmInfo _ => "[thm]"
              | .opaqueInfo _ => "[opaque]"
              | .quotInfo _ => "[quot]"
              | .inductInfo _ => "[inductive]"
              | .ctorInfo _ => "[ctor]"
              | .recInfo _ => "[recursor]"
              | .defnInfo defnVal =>
                match defnVal.safety with
                | DefinitionSafety.partial => "[def:partial]"
                | DefinitionSafety.safe => "[def:safe]"
                | DefinitionSafety.unsafe => "[def:unsafe]"
            some (s!"{kind} {name.toStringWithSep "." true}")
      | _ => none
  let listStr := "[" ++ (matchingDecls.intersperse ", ").foldl (· ++ ·) "" ++ "]"
  logInfo m!"Declarations in namespace `{ns}`:
{listStr}"

  let prettyLines := (matchingDecls.toArray.qsort (· < ·)).toList.map (· ++ "
")
  let prettyStr := prettyLines.foldl (· ++ ·) ""
  let output := s!"Declarations in namespace `{ns}`:

{prettyStr}"

  logInfo output

  let outputPath := "namespaces/thms_RingHom.txt"
  IO.FS.writeFile outputPath s!"Declarations in namespace `{ns}`:
{listStr}"
  
#listNamespace RingHom
    