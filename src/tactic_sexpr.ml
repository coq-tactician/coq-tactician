open Ltac_plugin
open Tactician_util
open Map_all_the_things
open Genarg
open Mapping_helpers
open Tacexpr
open Sexpr
open Constrexpr
open Glob_term
open Pattern

let constr_pattern_name (pat : constr_pattern) = match pat with
  | PRef _ -> ["PRef"]
  | PVar _ -> ["PVar"]
  | PEvar (_, _) -> ["PEvar"]
  | PRel _ -> ["PRel"]
  | PApp (_, _) -> ["PApp"]
  | PSoApp (_, _) -> ["PSoApp"]
  | PProj (_, _) -> ["PProj"]
  | PLambda (_, _, _) -> ["PLambda"]
  | PProd (_, _, _) -> ["PProd"]
  | PLetIn (_, _, _, _) -> ["PLetIn"]
  | PSort _ -> ["PSort"]
  | PMeta _ -> ["PMeta"]
  | PIf (_, _, _) -> ["PIf"]
  | PCase (_, _, _, _) -> ["PCase"]
  | PFix (_, _) -> ["PFix"]
  | PCoFix (_, _) -> ["PCoFix"]
  | PInt _ -> ["PInt"]
  | PFloat _ -> ["PFloat"]
  | PArray (_, _, _) -> ["PArray"]

let constr_expr_r_name (expr : constr_expr_r) = match expr with
  | CRef (_, _) -> ["CRef"]
  | CFix (_, _) -> ["CFix"]
  | CCoFix (_, _) -> ["CCoFix"]
  | CProdN (_, _) -> ["CProdN"]
  | CLambdaN (_, _) -> ["CLambdaN"]
  | CLetIn (_, _, _, _) -> ["CLetIn"]
  | CAppExpl (_, _) -> ["CAppExpl"]
  | CApp (_, _) -> ["CApp"]
  | CRecord _ -> ["CRecord"]
  | CCases (_, _, _, _) -> ["CCases"]
  | CLetTuple (_, _, _, _) -> ["CLetTuple"]
  | CIf (_, _, _, _) -> ["CIf"]
  | CHole (_, _, _) -> ["CHole"]
  | CPatVar _ -> ["CPatVar"]
  | CEvar (_, _) -> ["CEvar"]
  | CSort _ -> ["CSort"]
  | CCast (_, _) -> ["CCast"]
  | CNotation (_, _, _) -> ["CNotation"]
  | CGeneralization (_, _, _) -> ["CGeneralization"]
  | CPrim _ -> ["CPrim"]
  | CDelimiters (_, _) -> ["CDelimiters"]
  | CArray (_, _, _, _) -> ["CArray"]

let glob_constr_r_name (expr : 'a glob_constr_r) = match expr with
  | GRef (_, _) -> ["GRef"]
  | GVar _ -> ["GVar"]
  | GEvar (_, _) -> ["GEvar"]
  | GPatVar _ -> ["GPatVar"]
  | GApp (_, _) -> ["GApp"]
  | GLambda (_, _, _, _) -> ["GLambda"]
  | GProd (_, _, _, _) -> ["GProd"]
  | GLetIn (_, _, _, _) -> ["GLetIn"]
  | GCases (_, _, _, _) -> ["GCases"]
  | GLetTuple (_, _, _, _) -> ["GLetTuple"]
  | GIf (_, _, _, _) -> ["GIf"]
  | GRec (_, _, _, _, _) -> ["GRec"]
  | GSort _ -> ["GSort"]
  | GHole (_, _, _) -> ["GHole"]
  | GCast (_, _) -> ["GCast"]
  | GInt _ -> ["GInt"]
  | GFloat _ -> ["GFloat"]
  | GArray (_, _, _, _) -> ["GArray"]

let gen_tactic_arg_name (arg : 'a gen_tactic_arg) = match arg with
  | TacGeneric _ -> ["TacGeneric"]
  | ConstrMayEval _ -> ["ConstrMayEval"]
  | Reference _ -> ["Reference"]
  | TacCall _ -> ["TacCall"]
  | TacFreshId _ -> ["TacFreshId"]
  | Tacexp _ -> ["Tacexp"]
  | TacPretype _ -> ["TacPretype"]
  | TacNumgoals -> ["TacNumgoals"]

let glob_tactic_arg_name (arg : glob_tactic_arg) = match arg with
  | TacCall CAst.{v=(r, _); _} ->
    let name = match r with
      | Locus.ArgArg (_, c) -> Names.KerName.to_string c
      | Locus.ArgVar CAst.{v; _} -> Names.Id.to_string v in
    ["TacCall"; name]
  | _ -> gen_tactic_arg_name arg

let raw_tactic_arg_name (arg : raw_tactic_arg) = match arg with
  | TacCall CAst.{v=(r, _); _} ->
    let name = Libnames.string_of_qualid r in
    ["TacCall"; name]
  | _ -> gen_tactic_arg_name arg

let gen_atomic_tactic_expr_name (tac : 'a gen_atomic_tactic_expr) = match tac with
  | TacIntroPattern (_, _) -> ["TacIntroPattern"]
  | TacApply (_, _, _, _) -> ["TacApply"]
  | TacElim (_, _, _) -> ["TacElim"]
  | TacCase (_, _) -> ["TacCase"]
  | TacMutualFix (_, _, _) -> ["TacMutualFix"]
  | TacMutualCofix (_, _) -> ["TacMutualCofix"]
  | TacAssert (_, _, _, _, _) -> ["TacAssert"]
  | TacGeneralize _ -> ["TacGeneralize"]
  | TacLetTac (_, _, _, _, _, _) -> ["TacLetTac"]
  | TacInductionDestruct (_, _, _) -> ["TacInductionDestruct"]
  | TacReduce (_, _) -> ["TacReduce"]
  | TacChange (_, _, _, _) -> ["TacChange"]
  | TacRewrite (_, _, _, _) -> ["TacRewrite"]
  | TacInversion (_, _) -> ["TacInversion"]

let gen_tactic_expr_r_name r (tac : 'a gen_tactic_expr_r) = match tac with
  | TacAtom _ -> [s2s "TacAtom"]
  | TacThen (_, _) -> [s2s "TacThen"]
  | TacDispatch _ -> [s2s "TacDispatch"]
  | TacExtendTac (_, _, _) -> [s2s "TacExtendTac"]
  | TacThens (_, _) -> [s2s "TacThens"]
  | TacThens3parts (_, _, _, _) -> [s2s "TacThens3parts"]
  | TacFirst _ -> [s2s "TacFirst"]
  | TacComplete _ -> [s2s "TacComplete"]
  | TacSolve _ -> [s2s "TacSolve"]
  | TacTry _ -> [s2s "TacTry"]
  | TacOr (_, _) -> [s2s "TacOr"]
  | TacOnce _ -> [s2s "TacOnce"]
  | TacExactlyOnce _ -> [s2s "TacExactlyOnce"]
  | TacIfThenCatch (_, _, _) -> [s2s "TacIfThenCatch"]
  | TacOrelse (_, _) -> [s2s "TacOrelse"]
  | TacDo (_, _) -> [s2s "TacDo"]
  | TacTimeout (_, _) -> [s2s "TacTimeout"]
  | TacTime (_, _) -> [s2s "TacTime"]
  | TacRepeat _ -> [s2s "TacRepeat"]
  | TacProgress _ -> [s2s "TacProgress"]
  | TacShowHyps _ -> [s2s "TacShowHyps"]
  | TacAbstract (_, _) -> [s2s "TacAbstract"]
  | TacId _ -> [s2s "TacId"]
  | TacFail (_, _, _) -> [s2s "TacFail"]
  | TacLetIn (_, _, _) -> [s2s "TacLetIn"]
  | TacMatch (_, _, _) -> [s2s "TacMatch"]
  | TacMatchGoal (_, _, _) -> [s2s "TacMatchGoal"]
  | TacFun _ -> [s2s "TacFun"]
  | TacArg _ -> [s2s "TacArg"]
  | TacSelect (_, _) -> [s2s "TacSelect"]
  | TacML _ -> [s2s "TacML"]
  | TacAlias (c, _) ->
    let al = Tacenv.interp_alias c in
    [s2s "TacAlias"; s2s @@ Names.KerName.debug_to_string c; r al.alias_body]

module SexprDef = struct
  module M = WriterMonad
      (struct type w = sexpr list let id = [] let comb = List.append end)
  include MapDefTemplate (M)
  let map_sort = "sexpr"
  let warnProblem wit =
    Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                              str "the following tactic. Please report. " ++
                              pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}
end
module SexprMapper = MakeMapper(SexprDef)
open SexprDef
open Helpers(SexprDef)

type 'a k = 'a SexprDef.t

let mapper r =
  { SexprDef.default_mapper with
    glob_tactic = (fun t g ->
        let name = gen_tactic_expr_r_name r t in
        M.censor (fun ls -> [Node (name @ ls)]) (g t))
  ; raw_tactic = (fun t g ->
        let name = gen_tactic_expr_r_name r t in
        M.censor (fun ls -> [Node (name @ ls)]) (g t))
  ; glob_tactic_arg = (fun t g ->
        let name = glob_tactic_arg_name t in
        M.censor (fun ls -> [Node (List.map s2s name @ ls)]) (g t))
  ; raw_tactic_arg = (fun t g ->
        let name = raw_tactic_arg_name t in
        M.censor (fun ls -> [Node (List.map s2s name @ ls)]) (g t))
  ; glob_atomic_tactic = (fun t g ->
        let name = gen_atomic_tactic_expr_name t in
        M.censor (fun ls -> [Node (List.map s2s name @ ls)]) (g t))
  ; raw_atomic_tactic = (fun t g ->
        let name = gen_atomic_tactic_expr_name t in
        M.censor (fun ls -> [Node (List.map s2s name @ ls)]) (g t))
  ; cast = (fun c -> M.censor (fun ls -> [Node (s2s "CAst" :: ls)]) c)
  ; constant = (fun c -> M.tell (s2s @@ Names.Constant.to_string c) >> return c)
  ; mutind = (fun c -> M.tell (s2s @@ Names.MutInd.to_string c) >> return c)
  (* ; short_name = (fun c -> M.tell (s2s "short_name") >> return c) *)
  ; located = (fun c -> M.tell (s2s "Located") >> c)
  ; variable = (fun c -> M.tell (s2s @@ Names.Id.to_string c) >> return c)
  ; qualid = (fun (p, id) ->
      M.tell (s2s @@ Libnames.string_of_path @@ Libnames.make_path p id) >> return (p, id))
  ; constr_pattern = (fun t g ->
        let name = constr_pattern_name t in
        M.censor (fun ls -> [Node (List.map s2s name @ ls)]) (g t))
  ; constr_expr = (fun t g ->
        let name = constr_expr_r_name t in
        M.censor (fun ls -> [Node (List.map s2s name @ ls)]) (g t))
  ; glob_constr = (fun t g ->
        let name = glob_constr_r_name t in
        M.censor (fun ls -> [Node (List.map s2s name @ ls)]) (g t))
  ; glob_constr_and_expr = (fun t g ->
      let name = "GC&E" in
      M.censor (fun ls -> [Node (s2s name :: ls)]) (g t))
  ; glob_constr_pattern_and_expr = (fun t g ->
      let name = "GCP&E" in
      M.censor (fun ls -> [Node (s2s name :: ls)]) (g t))
  }

(* TODO: For now, this function is only for debugging purposes. Many syntactic elements from the AST
   are missing. In particular, non-recursive information is mostly not included. This includes no-recursive
   tactic extensions, binders, etc. *)
let rec tactic_sexpr t = Node (fst @@ SexprMapper.glob_tactic_expr_map (mapper tactic_sexpr) t)
