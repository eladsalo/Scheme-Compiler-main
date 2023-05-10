(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let list_eq eq l1 l2 = (List.length l1) = (List.length l2) && List.for_all2 eq l1 l2;;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        list_eq expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;

let unannotate_lexical_address = function
| (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name

let rec unanalyze expr' =
match expr' with
  | ScmConst' s -> ScmConst(s)
  | ScmVar' var -> unannotate_lexical_address var
  | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
  | ScmBoxGet' var -> unannotate_lexical_address var
  | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmIf' (test, dit, dif) -> ScmIf (unanalyze test, unanalyze dit, unanalyze dif)
  | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
  | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
  | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
  | ScmLambdaSimple' (params, expr') ->
        ScmLambdaSimple (params, unanalyze expr')
  | ScmLambdaOpt'(params, param, expr') ->
        ScmLambdaOpt (params, param, unanalyze expr')
  | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
        ScmApplic (unanalyze expr', List.map unanalyze expr's);;

let string_of_expr' expr' =
    string_of_expr (unanalyze expr');;

module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
  val string_of_expr' : expr' -> string
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let unannotate_lexical_address = function
    | (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name

  let rec unanalyze expr' =
    match expr' with
      | ScmConst' s -> ScmConst(s)
      | ScmVar' var -> unannotate_lexical_address var
      | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
      | ScmBoxGet' var -> unannotate_lexical_address var
      | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
      | ScmIf' (test, dit, dif) -> ScmIf (unanalyze test, unanalyze dit, unanalyze dif)
      | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
      | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
      | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
      | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
      | ScmLambdaSimple' (params, expr') ->
            ScmLambdaSimple (params, unanalyze expr')
      | ScmLambdaOpt'(params, param, expr') ->
            ScmLambdaOpt (params, param, unanalyze expr')
      | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
            ScmApplic (unanalyze expr', List.map unanalyze expr's);;


  let string_of_expr' expr' =
      string_of_expr (unanalyze expr');;


  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;


  (* run this first! *)
let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with
      | ScmVar(a) -> ScmVar'(tag_lexical_address_for_var a params env)
      | ScmConst(a) -> ScmConst'(a)
      | ScmSeq(p) -> ScmSeq'(List.map (fun (x)-> (run x params env)) p)
      | ScmLambdaSimple(ls,p) ->
                let ex = run p ls (params::env) in
                ScmLambdaSimple'(ls,ex)
      | ScmLambdaOpt(ls,fi,b) ->
                let s = ls @ [fi] in 
                let res = run b s (params::env) in
                ScmLambdaOpt'(ls,fi,res)
      | ScmDef(ScmVar(a),b) -> ScmDef'(tag_lexical_address_for_var a params env,run b params env)
      | ScmIf(test,t,f) -> ScmIf'((run test params env),(run t params env),(run f params env))
      | ScmApplic(fir, en) ->
                let fir = run fir params env in
                let en = List.map (fun (x)-> (run x params env)) en in
                ScmApplic'(fir,en)
      | ScmSet(ScmVar(a),b) -> ScmSet'(tag_lexical_address_for_var a params env,run b params env)
      | ScmOr(p) -> ScmOr'(List.map (fun (x)-> (run x params env)) p) 
      | _ -> raise X_this_should_not_happen
   in 
   run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  
  let annotate_tail_calls pe =
    let rec run pe in_tail =
        match pe with
        | ScmOr'(l) -> 
                  let (rest,lastOne) = rdc_rac l in
                  let rest = List.map (fun (x) -> run x false) rest in
                  let lastOne =( match in_tail with 
                                | true -> (run lastOne true)
                                | false -> (run lastOne false)) in                 
                  let lastOne= [lastOne] in 
                  ScmOr'(List.append rest lastOne)        
        | ScmLambdaSimple'(ls,b)-> simple ls b
        | ScmLambdaOpt'(ls,p,b)-> opt ls p b
        | ScmSet'(var,b) -> ScmSet'(var,run b false)
        | ScmDef'(var, b) -> ScmDef'(var,run b false)
        | ScmSeq'(ls) -> seq ls in_tail
        | ScmIf'(test,t,f) -> ScmIf'(run test false,run t in_tail,run f in_tail)
        | ScmApplic'(fu,ls) -> applic fu ls in_tail

        | expr -> expr 

    and applic fu ls in_tail = 
      match in_tail with 
      true -> ScmApplicTP'((run fu false),(List.map (fun (x)-> run x false) ls ))
      |false -> ScmApplic'((run fu false),(List.map (fun (x)-> run x false) ls ))
    
    and seq lst in_tail =
      let (ex,en) = rdc_rac lst in
      let ex = List.map (fun (x) -> run x false) ex in
      let en = run en in_tail in
      let en = [en] in
      ScmSeq'(List.append ex en) 

    and simple ls b =
        let b = run b true in
        ScmLambdaSimple'(ls,b)
    and opt ls p b = 
        let b = run b true in
            ScmLambdaOpt'(ls,p,b)
      in
  run pe false;;

  (* boxing *)

let rec find_write name enclosing_lambda expr boolCond = 
      match expr with
      | ScmIf'(test,doIfTrue,doIfFalse) -> let check_doIfFalse = find_write name enclosing_lambda doIfFalse boolCond in
                                          let check_doIfTrue = find_write name enclosing_lambda doIfTrue boolCond in
                                          let check_test = find_write name enclosing_lambda test boolCond in                                                            
                                          (List.append(List.append check_test check_doIfTrue) check_doIfFalse)
      | ScmOr'(allCondExp) -> let l= [] in 
            (List.fold_left (fun init s -> 
            (List.append init (find_write name enclosing_lambda s boolCond))) l allCondExp) 
      | ScmDef'(v, bodyExp) -> find_write name enclosing_lambda bodyExp boolCond
      | ScmLambdaSimple'(p,b)-> let cond = (List.mem name p) in  
                                        (
                                          match cond with   
                                        | true -> []
                                        | false -> (match boolCond with
                                                  | true ->find_write name enclosing_lambda b boolCond
                                                  | false-> find_write name expr b true
                                                    )  
                                                  ) 
      | ScmLambdaOpt'(p,specialArg,b)-> let cond1 = (List.mem name p) in
                                      let cond2 = (name = specialArg) in
                                      let c1Andc2= (cond1 || cond2) in 
                                      (match c1Andc2 with
                                      | true ->[]
                                      | false -> (
                                                  match boolCond with
                                                  | true ->find_write name enclosing_lambda b boolCond
                                                  | false-> find_write name expr b true
                                      )
                                      )
      | ScmSet'(v,body) ->    (match v with
                              | VarFree(vt) ->  (match (String.equal vt name) with 
                                              | true -> (List.append [enclosing_lambda] (find_write name enclosing_lambda body boolCond))
                                              | false -> (find_write name enclosing_lambda body boolCond) )
                              | VarParam(vt,minor) -> (match (String.equal vt name) with 
                                              | true -> (List.append [enclosing_lambda] (find_write name enclosing_lambda body boolCond))
                                              | false -> (find_write name enclosing_lambda body boolCond))
                              | VarBound(vt,minor,major) -> (match (String.equal vt name) with 
                                              | true -> (List.append [enclosing_lambda] (find_write name enclosing_lambda body boolCond))
                                              | false -> (find_write name enclosing_lambda body boolCond))
                              )
      | ScmSeq'(allCondExp) -> let l= [] in 
                          (List.fold_left (fun init s -> 
                           (List.append init (find_write name enclosing_lambda s boolCond))) l allCondExp) 

      | ScmApplic'(lambda,argsExp) -> let l= [] in 
                          let x= (List.fold_left (fun init s -> 
                           (List.append init (find_write name enclosing_lambda s boolCond))) l argsExp) in  
      (List.append (find_write name enclosing_lambda lambda boolCond) x) 



      | ScmApplicTP'(lambda,argsExp) -> let l= [] in 
                                           let x= (List.fold_left (fun init s -> 
                                         (List.append init (find_write name enclosing_lambda s boolCond))) l argsExp) in  
                                       (List.append (find_write name enclosing_lambda lambda boolCond) x)    
      | _ -> [] 
     ;;  

let rec find_reads name enclosing_lambda expr boolCond =      
      match expr with
      | ScmIf'(test,doIfTrue,doIfFalse) -> let check_doIfFalse = find_reads name enclosing_lambda doIfFalse boolCond in
                                          let check_doIfTrue = find_reads name enclosing_lambda doIfTrue boolCond in
                                          let check_test = find_reads name enclosing_lambda test boolCond in                                                            
                                          (List.append(List.append check_test check_doIfTrue) check_doIfFalse)
      
      | ScmOr'(allCondExp) -> let l= [] in 
                  (List.fold_left (fun init s -> 
                  (List.append init (find_reads name enclosing_lambda s boolCond))) l allCondExp)
      
      
      
      | ScmDef'(v, bodyExp) -> find_reads name enclosing_lambda bodyExp boolCond

      | ScmLambdaSimple'(p,b)-> let cond = (List.mem name p) in  
                                        (
                                          match cond with   
                                        | true -> []
                                        | false -> (match boolCond with
                                                  | true ->find_reads name enclosing_lambda b boolCond
                                                  | false-> find_reads name expr b true
                                                    )
                                                  ) 
      | ScmLambdaOpt'(p,specialArg,b)-> let cond1 = (List.mem name p) in
                                      let cond2 = (name = specialArg) in
                                      let c1Andc2= (cond1 || cond2) in 
                                      (match c1Andc2 with
                                      | true ->[]
                                      | false -> (
                                                  match boolCond with
                                                  | true ->find_reads name enclosing_lambda b boolCond
                                                  | false-> find_reads name expr b true
                                      )
                                      )

      | ScmApplic'(lambda,argsExp) -> let l= [] in 
                          let x= (List.fold_left (fun init s -> 
                           (List.append init (find_reads name enclosing_lambda s boolCond))) l argsExp) in  
                          (List.append (find_reads name enclosing_lambda lambda boolCond) x) 
      | ScmApplicTP'(lambda,argsExp) -> let l= [] in 
                                           let x= (List.fold_left (fun init s -> 
                                         (List.append init (find_reads name enclosing_lambda s boolCond))) l argsExp) in  
                                       (List.append (find_reads name enclosing_lambda lambda boolCond) x)  
      | ScmSeq'(allExp) -> let l= [] in 
                          (List.fold_left (fun init s -> 
                           (List.append init (find_reads name enclosing_lambda s boolCond))) l allExp) 
      
      | ScmSet'(var,body) -> (find_reads name enclosing_lambda body boolCond)

      | ScmVar'(v) ->(match v with
                          | VarFree(vt) ->  (match (String.equal vt name) with 
                                                  | true -> [enclosing_lambda] 
                                                  | false -> [])
                          | VarParam(vt,minor) -> (match (String.equal vt name) with 
                                                  | true -> [enclosing_lambda] 
                                                  | false -> [])
                          | VarBound(vt,minor,major) -> (match (String.equal vt name) with 
                                                  | true -> [enclosing_lambda] 
                                                  | false -> [])
                        )

      | _ -> []
    

  let rec changeToBox expr name = 
    match expr with
    | ScmIf'(test,check_doIfTrue,check_doIfFalse) -> let check_test = changeToBox test name in
                                                      let check_doIfTrue = changeToBox check_doIfTrue name in
                                                      let check_doIfFalse = changeToBox check_doIfFalse name in
                                                      ScmIf'(check_test,check_doIfTrue,check_doIfFalse)
    | ScmOr'(allCondExp) ->  let f = (fun x -> changeToBox x name) in 
                            ScmOr'( List.map f allCondExp )
    | ScmDef'(v, b) -> ScmDef'(v,changeToBox b name)  

    | ScmLambdaSimple'(p,b)-> let isParm= (List.mem name p) in 
                                      (match isParm with 
                                      | true -> expr
                                      | false -> ScmLambdaSimple'(p,changeToBox b name)
                                      )           
                                      
    | ScmLambdaOpt'(p,spicealArg,body)-> let isParm= (List.mem name p) in
                                     let isSpicealArg= ( String.equal spicealArg name) in 
                                     (match isParm,isSpicealArg with 
                                    | false, false ->  (ScmLambdaOpt'(p,spicealArg,changeToBox body name))
                                    | _ -> expr)
    | ScmApplic'(lambdaPart,argList) -> ScmApplic'((changeToBox lambdaPart name),(List.map (fun x -> changeToBox x name) argList))
                            
    | ScmApplicTP'(lambdaPart,argList) -> ScmApplicTP'((changeToBox lambdaPart name),(List.map (fun x -> changeToBox x name) argList))


    | ScmSeq'(allExp) -> let f = (fun x -> changeToBox x name) in 
                        ScmSeq'(List.map f allExp)


    | ScmSet'(v,b) -> (match v with
                          | VarParam(parm,minor) -> if (String.equal parm name) then ScmBoxSet'(v,(changeToBox b name)) else ScmSet'(v,(changeToBox b name))
                          | VarFree(parm) -> if (String.equal parm name) then ScmBoxSet'(v,(changeToBox b name)) else ScmSet'(v,(changeToBox b name))
                          | VarBound (parm,minor,major) -> if (String.equal parm name) then ScmBoxSet'(v,(changeToBox b name)) else ScmSet'(v,(changeToBox b name))
                          )                                                                                                                           
    | ScmVar'(var) -> let isNameOfVar= (match var with
                                      | VarParam(parm,minor) -> (String.equal parm name ) 
                                      | VarFree(parm) -> (String.equal parm name )
                                      | VarBound (parm,minor,major) -> (String.equal parm name )
                                      ) in 
                                      (match isNameOfVar with 
                                      | true -> ScmBoxGet'(var)
                                      | _ -> ScmVar'(var)
                                      )
    | ScmBoxSet'(var,body) -> ScmBoxSet'(var,(changeToBox body name)) 
    | s -> s 
 


  let rec box_set expr = 
    match expr with
    | ScmIf'(test,doIfTrue,doIfFalse) -> ScmIf'(box_set test,box_set doIfTrue,box_set doIfFalse)
    | ScmOr'(allCondExp) -> ScmOr'(List.map (fun (x) -> box_set x) allCondExp)
    | ScmSeq'(allExp) -> ScmSeq'(List.map (fun (x) -> box_set x) allExp)     
    | ScmSet'(v,exp) -> ScmSet'(v,box_set exp)
    | ScmDef'(v,exp) -> ScmDef'(v,box_set exp)
    | ScmApplicTP'(ex,ls) -> ScmApplicTP'(box_set ex,List.map (fun (l) -> box_set l) ls)
    | ScmApplic'(ex,ls) -> ScmApplic'(box_set ex,List.map (fun (l) -> box_set l) ls)    
    | ScmLambdaSimple'(p,b)-> (match p with
                                      | [] -> (noNeedForBoxCheck p b )
                                      | _ ->  (needCheckingForPotentialBox p b expr  ) )
                                                    
    | ScmLambdaOpt'(paramters,specialArg,b)-> let paramsLength= (List.length paramters) in 
                                      (match paramsLength with 
                                      | 0 -> let (name,sucsses) = search_b b expr specialArg in
                                              (match sucsses with
                                              | true-> let body = changeToBox b name in
                                                       let body = match body with       
                                                        | ScmSeq'(b) -> ScmSeq'(List.append [(ScmSet'(VarParam(name,0),ScmBox'(VarParam(name,0))))] b)
                                                        | _ -> ScmSeq'(List.append [(ScmSet'(VarParam(name,0),ScmBox'(VarParam(name,0))))] [body]) in
                                                                ScmLambdaOpt'(paramters,specialArg,box_set body)
                                              | false-> ScmLambdaOpt'(paramters,specialArg,box_set b)
                                              )
                                      | _ ->   ScmLambdaOpt'(paramters,specialArg,(case_opt paramters b expr specialArg)) 
                                      ) 
    | ScmBoxSet'(var,body) -> ScmBoxSet'(var,(box_set body))                             
    | e -> e

  and noNeedForBoxCheck p b =
      ScmLambdaSimple'(p,(box_set b))
  and needCheckingForPotentialBox p b expr =
      ScmLambdaSimple'(p,(case_simple p b expr ))


  and case_simple params body lamP = 
      let all_params = List.map (search_b body lamP) params in
      let should_box_pairs= (List.filter (fun (name,bool) -> bool = true) all_params) in 
      let should_box = ( List.map (fun (name,bool) -> name) should_box_pairs) in 
      
      let should_box_length = (List.length should_box) in 
      match should_box_length with
       | 0 -> (box_set body)
       | _ -> (
      
      let rec count_location paramsList counter name  = (match paramsList with
                                                    | [] -> raise X_this_should_not_happen
                                                    | start :: rest -> if (String.equal start name) then (start,counter) else (count_location rest (counter + 1) name )) in 
      let s = List.map (fun (name,minor) -> ScmSet'(VarParam(name,minor),ScmBox'(VarParam(name,minor)))) 
      (List.map (count_location params 0 ) should_box) in
      let fu1 = (fun b name -> (changeToBox b name)) in
      let b = List.fold_left fu1 body should_box in
      let b = match b with  
        | ScmSeq'(x) -> ScmSeq'(List.append s x)
        | _ -> doSec s b in
      (box_set b))
      

  and case_opt  params body lamP p= 
      let all_params = (List.append (List.map (search_b body lamP) params) [(search_b body lamP p)] )in
      let should_box_pairs= (List.filter (fun (name,bool) -> bool = true) all_params) in 
      let should_box = ( List.map (fun (name,bool) -> name) should_box_pairs) in 

      let should_box_length = (List.length should_box) in 
      match should_box_length with
       | 0 -> (box_set body)
       | _ -> (
      
      let rec count_location paramsList counter name  = (match paramsList with
                                                    | [] -> raise X_this_should_not_happen
                                                    | start :: rest -> if (String.equal start name) then (start,counter) else (count_location rest (counter + 1) name )) in 
      let s = List.map (fun (name,minor) -> ScmSet'(VarParam(name,minor),ScmBox'(VarParam(name,minor)))) 
      (List.map (count_location params 0 ) should_box) in
      let fu1 = (fun b name -> (changeToBox b name)) in
      let b = List.fold_left fu1 body should_box in
      let b = match b with  
        | ScmSeq'(x) -> ScmSeq'(List.append s x)
        | _ -> doSec s b in
      (box_set b))


  and doSec ls b = 
     ScmSeq'(ls@[b])

  
  and search_b body lamP name  =  
      if ((List.length (find_reads name lamP body false) == 0) ||
          (List.length (find_write name lamP body false) == 0))  then (name,false) 
        else 
        let shouldDoBoxing = list_che (find_reads name lamP body false ) (find_write name lamP body false) in
        if(shouldDoBoxing) then (name,true) else (name,false)

  and list_che fir sec = match fir with    
    | [] -> false                                                      
    | f::s -> (let nt = List.exists (fun (x)-> (not(x == f))) sec in 
              match nt with
                  | true -> true              
                  | false -> list_che s sec        
    )    
  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;;
 (* end of module Semantic_Analysis *)