open Tactic_learner_internal
open TS
open Constr
open Monad_util
open Map_all_the_things
open Genarg
open Glob_term

(* This file has the purpose of dealing with side effects of the abstract tactic. This is all very
   uninteresting, but has to be dealt with because the constants 'abstract' generates disappear, which
   result in lookup errors.

   Several options to fix this:
   1. Inline constants into terms using Safe_typing.inline_private_constants. This kind of works, but results
   in large terms because the constants are always inlined, even if they are not referenced. Not what we want.
   Additionally, we have no way of inlining in tactics.

   2. Just replace private constants with a placeholder. We choose this for its simplicity.

*)

module TacticFinderDef = struct
  include MapDefTemplate (IdentityMonad)
  let map_sort = "tactic-finder"
  let warnProblem wit =
    Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                              str "the following tactic. Please report. " ++
                              pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}
end
module TacticFinderMapper = MakeMapper(TacticFinderDef)
open TacticFinderDef

let inline_tactic env t =
  let rec glob_term_inline c = match DAst.get c with
    | GRef (ConstRef const, _) ->
      if Environ.mem_constant const env then c else
        DAst.make @@ GEvar (Names.Id.of_string "private_constant_placeholder", [])
    | _ -> Glob_ops.map_glob_constr glob_term_inline c in

  (* We prefer to replace private constant with an evar, but if that is not possible, we replace it
     with the identity function 'private_constant_placeholder' defined in Record.v *)
  let mapper = { TacticFinderDef.default_mapper with
                 glob_constr = (fun t c -> c @@ DAst.get @@ glob_term_inline (DAst.make t))
               ; constant = (fun const ->
                     if Environ.mem_constant const env then const else
                       (match Coqlib.lib_ref "tactician.private_constant_placeholder" with
                        | Names.GlobRef.ConstRef const -> const
                        | _ -> assert false)
                   )
               } in
  TacticFinderMapper.glob_tactic_expr_map mapper t

let inline env { outcomes; tactic; name; status; path } =
  let rec inline_constr c = match Constr.kind c with
    | Const (const, u) ->
      if Environ.mem_constant const env then c else
        (* Total hack of course, because this is not typable. However, since Tactician generally does not
           store sigma contexts, evars are not typable anyway. When that changes, this should be fixed. *)
        of_kind @@ Evar (Evar.unsafe_of_int 0, [||])
    | _ -> Constr.map inline_constr c in
  let inline_proof_state (ctx, goal) =
    let ctx = List.map (Context.Named.Declaration.map_constr inline_constr) ctx in
    let goal = inline_constr goal in
    (ctx, goal) in
  let rec inline_proof_dag = function
    | End -> End
    | Step step -> Step (inline_proof_step step)
  and inline_proof_step { executions; tactic } =
    { executions = List.map (fun (pse, psp) -> inline_proof_state pse, inline_proof_dag psp) executions
    ; tactic = tactic } in
  let inline_outcome { parents; siblings; before; after } =
    { parents = List.map (fun (pse, psp) -> inline_proof_state pse, inline_proof_step psp) parents
    ; siblings = inline_proof_dag siblings
    ; before = inline_proof_state before
    ; after = List.map inline_proof_state after } in
  { outcomes = List.map inline_outcome outcomes
  ; tactic = tactic_make @@ inline_tactic env @@ tactic_repr tactic
  ; name; status; path }

let inline env sideff t =
  if sideff = Safe_typing.empty_private_constants then t else inline env t
