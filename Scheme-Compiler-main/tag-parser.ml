#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;
  
let rec tag_parse_expression sexpr =
  let sexpr = macro_expand sexpr in
  match sexpr with
  | ScmChar(c) -> ScmConst(ScmChar(c))
  | ScmNumber(n) -> ScmConst(ScmNumber(n))
  | ScmSymbol(sym) -> tag_pasre_var sym
  | ScmNil -> ScmConst(ScmNil)
  | ScmString(str) -> ScmConst(ScmString(str))
  | ScmBoolean(bool) -> ScmConst(ScmBoolean(bool))
  | ScmVoid -> ScmConst(ScmVoid)
  | ScmPair(ScmSymbol("or"), sexp) -> tag_parse_or sexpr
  | ScmPair(ScmSymbol("set!"), sexp)-> tag_parse_set sexpr
  | ScmPair(ScmSymbol("define"), sexp)-> tag_parse_define sexpr
  | ScmPair(ScmSymbol("begin"), sexp)-> tag_parse_begin sexpr
  | ScmPair(ScmSymbol("if"), sexp) -> tag_parse_if sexpr
  | ScmPair(ScmSymbol("lambda"), sexp)-> tag_parse_lambda sexpr
  | ScmPair(ScmSymbol("quote"),ScmPair(sexp,ScmNil)) -> ScmConst(sexp)
  | ScmPair (first , rest) -> ScmApplic ((tag_parse_expression first), (List.map tag_parse_expression (scm_list_to_list rest)))        
  | _ -> raise (X_syntax_error (sexpr, "Wrong syntax"))

and tag_pasre_var s = 
    let var= if (List.mem s reserved_word_list) then raise (X_reserved_word s) else ScmVar(s) in
    var
    
and tag_parse_or sexpr =
    let or_expr = match sexpr with 
     ScmPair(ScmSymbol("or"), s)-> s 
     | _-> (ScmSymbol "") in 
    
    let or_exp= match or_expr with 
    ScmPair(any,ScmNil) -> tag_parse_expression any
    | ScmPair(any) -> let list = scm_list_to_list (ScmPair(any)) in 
                          ScmOr(List.map tag_parse_expression list )
    | ScmNil -> ScmConst(ScmBoolean false)
    | _ -> raise (X_syntax_error (sexpr, "Wrong syntax")) in
    or_exp

and tag_parse_set sexpr = 
  let set_expr = match sexpr with 
      ScmPair(ScmSymbol("set!"), s)-> s 
      | _-> (ScmSymbol "") in 
  let set_exp= match set_expr with
  | ScmPair(ScmSymbol(def), ScmPair(definition,ScmNil)) ->
                    ScmSet((tag_parse_expression (ScmSymbol(def))), (tag_parse_expression definition))
  | ScmPair(ScmSymbol(def), definition) -> 
                    ScmSet((tag_parse_expression (ScmSymbol(def))), (tag_parse_expression definition))
  | _ -> raise (X_syntax_error (sexpr, "Expected variable on LHS of set!")) in 
  set_exp

and tag_parse_define s = 
  let define_expr = match s with 
      ScmPair(ScmSymbol("define"), sexp)-> sexp 
      | _-> (ScmSymbol "") in 
  let define_exp= match define_expr with
   ScmPair(ScmSymbol(def),ScmPair(definition,ScmNil)) -> 
                  ScmDef( (tag_parse_expression (ScmSymbol def)), tag_parse_expression definition)
  | _ ->  raise (X_syntax_error (s, "Expected variable on LHS of define or missing data on RHS")) in
  define_exp


and tag_parse_begin s =
  let begin_expr = match s with 
      ScmPair(ScmSymbol("begin"), sexp)-> sexp 
      | _-> (ScmSymbol "") in
  let seq = if ((scm_list_length begin_expr) != 0) then scm_list_to_list begin_expr 
  else raise (X_syntax_error(begin_expr, "empty body of sequence")) in
  let seq = List.map tag_parse_expression seq in
  if ((List.length seq) > 1) then ScmSeq(seq) else (List.hd seq)

and tag_parse_if s = 
  let if_expr = match s with 
        ScmPair(ScmSymbol("if"), sexp)-> sexp 
        | _-> (ScmSymbol "") in
  let if_exp= match if_expr with 
   ScmPair(test,ScmPair(doIfTrue,ScmNil)) -> 
              ScmIf(tag_parse_expression test, tag_parse_expression doIfTrue, ScmConst(ScmVoid))
  | ScmPair(test,ScmPair(doIfTrue,ScmPair(doIfFalse,ScmNil))) ->
              ScmIf(tag_parse_expression test, tag_parse_expression doIfTrue, tag_parse_expression doIfFalse)
  | _ -> raise (X_syntax_error (if_expr, "Wrong syntax")) in 
  if_exp 


and tag_parse_lambda sexpr = 
  let lambda_expr = match sexpr with 
        ScmPair(ScmSymbol("lambda"), sexp)-> sexp 
        | _-> (ScmSymbol "") in
  let lambda_exp= match lambda_expr with
  | ScmPair(ScmSymbol(p),body) -> variadic_fun lambda_expr
  | ScmPair(para,body) -> if ((scm_is_list para)==false) then (optional_fun lambda_expr) else (simple_fun lambda_expr) 
  | _ -> raise (X_syntax_error (lambda_expr, "Wrong syntax")) in 
   lambda_exp

and variadic_fun x =
    let para = match x with 
     ScmPair(ScmSymbol(p),b)-> p 
     | _-> "" in 
    let body = match x with 
     ScmPair(ScmSymbol(p),b)-> b  
    | _-> (ScmSymbol "") in 
    let bodyList= scm_list_to_list body in 
    let expr_body = match bodyList with 
      [] -> raise (X_syntax_error (body, "empty body"))
    | _-> List.map (fun a -> tag_parse_expression a) bodyList in
    let lambda = if (List.length expr_body)!= 1 then ScmLambdaOpt([],para,ScmSeq(expr_body)) 
                    else ScmLambdaOpt([],para,List.hd expr_body)  in
    lambda

and simple_fun x =
  let para = match x with 
     ScmPair(p,b)-> p 
     | _-> (ScmSymbol "") in 
  let body = match x with 
     ScmPair(p,b)-> b  
    | _-> (ScmSymbol "") in 
  let funA = (fun a -> match a with
                             ScmSymbol(x) -> x
                            | ScmPair(ScmSymbol(x),y) -> raise (X_syntax_error (a, "Wrong syntax")) 
                            | _ -> raise (X_syntax_error (a, "Wrong syntax"))) in 
  let paraVal = List.map funA (scm_list_to_list para) in
  let bodyList= scm_list_to_list body in 
  let expr_body = match bodyList with 
      [] -> raise (X_syntax_error (body, "empty body"))
    | _-> List.map (fun x -> tag_parse_expression x) bodyList in
  let lambda = if (List.length expr_body) != 1 then ScmLambdaSimple(paraVal,ScmSeq(expr_body)) else ScmLambdaSimple(paraVal,List.hd expr_body) in
  lambda

and optional_fun x =
  let para = match x with 
     ScmPair(p,b)-> p 
     | _-> (ScmSymbol "") in 
  let body = match x with 
     ScmPair(p,b)-> b  
    | _-> (ScmSymbol "") in 
  let rec fromSexprTreeToList s = 
    match s with
     ScmPair(ScmSymbol(first),ScmPair(rest)) -> (List.append [first] (fromSexprTreeToList (ScmPair rest)))
    | ScmPair(ScmSymbol(first),ScmSymbol(second)) -> [first]
    | _ -> raise (X_syntax_error(s, "wrong syntax")) in
  let paraVal = fromSexprTreeToList para in
  let rec is_more_than_one = function
    | [] -> false
    | hd::tl -> if (List.mem hd tl) then true else is_more_than_one tl in 
  let rec replica = function
    | [] -> ("")
    | hd::tl -> if (List.mem hd tl) then hd else replica tl in 
  let is_more = is_more_than_one paraVal in
  let repo= replica paraVal in
  let v_rest_search_from_pair s = match s with
    ScmPair(ScmSymbol(x),ScmSymbol(y)) -> y
    | _ -> raise (X_syntax_error(s, "not right syntax for proper list")) in
  let rec v_rest_search s  = match s with
    |ScmPair(ScmSymbol(x),ScmPair(y)) -> (v_rest_search (ScmPair y))
    | _ -> (v_rest_search_from_pair s)  in 
  let v_rest = v_rest_search para in
  let more_condition= (List.mem v_rest paraVal) in  
  let is_more= more_condition || is_more in 
  let bodyList= scm_list_to_list body in
  let expr_body = match bodyList with 
      [] -> raise (X_syntax_error (body, "empty body"))
    | _-> List.map (fun x -> tag_parse_expression x) bodyList in
  let exp_body = if (is_more==false) then (expr_body)
                     else (raise (X_syntax_error(ScmSymbol(repo),"more than one from the same symbol"))) in
  let lambda =  if (List.length exp_body) != 1 then ScmLambdaOpt(paraVal,v_rest,ScmSeq(exp_body))  
                      else ScmLambdaOpt(paraVal,v_rest,List.hd exp_body) in
  lambda



and macro_expand_structual_let binds body =
  let bindings_length= scm_list_length binds in 
  let x = if(bindings_length>1) 
  then let ans= macro_expand (ScmPair (ScmSymbol "let", ScmPair (ScmPair (
       (function
        | ScmPair (first, second) -> first
        | any -> raise (X_syntax_error (any, "Wrong syntax should get correct list")))
         binds, ScmNil)
         ,ScmPair (ScmPair (ScmSymbol "let*", ScmPair ((  
           (function
            | ScmPair (first, second) -> second
            | any -> raise (X_syntax_error (any, "Wrong syntax should get correct list")))
             binds), body)), ScmNil))))in 
         ans
         else macro_expand (ScmPair (ScmSymbol "let", ScmPair (binds , body))) in 
  x 
and expand_letrec sexp = 
  let bindings = match sexp with 
     ScmPair(ScmSymbol("letrec"),ScmPair(binds,body))-> binds 
     | _-> (ScmSymbol "") in 
  let body_sexp = match sexp with 
     ScmPair(ScmSymbol("letrec"),ScmPair(binds,body))-> body  
    | _-> (ScmSymbol "") in
  let set_bind  =  set_bindings bindings in
  let rec scm_append_body list sexpr =
      match list with
      | ScmNil -> sexpr
      | ScmPair (x, y) -> ScmPair (x, scm_append_body y sexpr)
      | _ -> raise (X_syntax_error (list, "wrong syntax")) in 
  ScmPair(ScmSymbol("let"),ScmPair((make_bindings bindings),(scm_append_body set_bind body_sexp)))

and set_bindings bindings =
  let make_bind= scm_zip 
                  (fun x y -> match x, y with
                        | ScmSymbol(name), value -> ScmPair(ScmSymbol("set!"), ScmPair(ScmSymbol(name),ScmPair(value,ScmNil)))
                        | _ -> raise (X_syntax_error(bindings,"Wrong syntax for letrec")))  
                        (free_names bindings ) 
                        (free_values_from_struct bindings) in 
  make_bind

and expand_let bindings body_exp =
  let values = scm_map free_values bindings in
  let variables = scm_map free_variables bindings in
  ScmPair (ScmPair (ScmSymbol "lambda",ScmPair (variables , body_exp)), values)

and free_variables = function 
     ScmPair (first, rest) -> first
    | x -> raise (X_syntax_error ( x , "Wrong bindigs syntax"))

and free_values = function
     ScmPair (first, ScmPair (v, z)) -> v
    | x -> raise (X_syntax_error ( x , "Wrong bindigs syntax"))

and free_values_from_struct bindings=
    let values_parts= scm_map 
                    (function  
                      (ScmPair(var_name,ScmPair(v,ScmNil)))-> v 
                    | any -> raise (X_syntax_error(any,"Wrong syntax for letrec"))) 
                    bindings in 
    values_parts
and make_bindings bindings =
  let  new_bindings= scm_map 
                    (function 
                     (ScmPair(var_name,v))-> ScmPair(var_name,ScmPair(ScmPair (ScmSymbol "quote", ScmPair (ScmSymbol "whatever", ScmNil)),ScmNil)) 
                    | any -> raise (X_syntax_error(any,"Wrong syntax for letrec"))) 
                    bindings in
  new_bindings
and free_names bindings = 
  let var_names = scm_map 
              (function 
                    | (ScmPair(var_name,v))-> var_name 
                    | any -> raise (X_syntax_error(any,"Wrong syntax for letrec"))) 
               bindings in 
  var_names


and case1 sexpr = 
  ScmPair (ScmSymbol "quote", ScmPair (ScmNil, ScmNil))

and caseQ s = ScmPair (ScmSymbol "quote", ScmPair (ScmSymbol(s), ScmNil)) 

and case2 s = ScmPair(ScmSymbol "quote",ScmPair(ScmPair(ScmSymbol "unquote-splicing", ScmPair (s, ScmNil)),ScmNil))

and case3 arg =  let expandlst = macro_expand_quansiqoute (list_to_proper_list arg) in
                 ScmPair(ScmSymbol("list->vector"), ScmPair(expandlst,ScmNil))

and case4 arg s =   ScmPair(ScmSymbol "append", ScmPair (arg, ScmPair ((macro_expand_quansiqoute s), ScmNil)))

and case5 first sec = ScmPair(ScmSymbol "cons",ScmPair ((macro_expand_quansiqoute first), ScmPair ((macro_expand_quansiqoute sec), ScmNil)))


and macro_expand_quansiqoute sexpr = 
  match sexpr with
  | ScmSymbol(arg) -> caseQ arg
  | ScmNil -> case1 sexpr 
  | ScmVector(arg) -> case3 arg 
  | ScmPair (ScmSymbol "unquote", ScmPair (arg, ScmNil)) ->  arg  
  | ScmPair (ScmSymbol "unquote-splicing", ScmPair (arg, ScmNil)) -> case2 arg
  | ScmPair(ScmPair (ScmSymbol "unquote-splicing", ScmPair (exp, ScmNil)),b) -> case4 exp b
  | ScmPair(first,sec) -> case5 first sec
  | _ -> sexpr



and expand_cond ribs = match ribs with
  | ScmNil -> ScmVoid
  | ScmPair(ScmPair(t,ScmPair(ScmSymbol("=>"),b)),r) -> 
                  if ((scm_list_length b) != 0) 
                  then case_2 (ScmPair(ScmPair(t,ScmPair(ScmSymbol("=>"),b)),r))
                  else raise (X_syntax_error(ribs,"Wrong syntax"))  
  | ScmPair(ScmPair(ScmSymbol("else"), b),r)-> 
                  if ((scm_list_length b) != 0) 
                  then case_3 (ScmPair(ScmPair(ScmSymbol("else"), b),r))
                  else raise (X_syntax_error(ribs,"empty body after else")) 
  | ScmPair(ScmPair(t,b),r) ->
          let rib_continuation= (ScmPair((expand_cond r),ScmNil)) in 
          let test_sexp= macro_expand t in 
          let rec scm_append_body list sexpr =
              match list with
              | ScmNil -> sexpr
              | ScmPair (x, y) -> ScmPair (x, scm_append_body y sexpr)
              | _ -> raise (X_syntax_error (list, "wrong syntax")) in
          scm_append_body (ScmPair(ScmSymbol "if",ScmPair(test_sexp,
          ScmPair(ScmPair (ScmSymbol "begin", (macro_expand b)),ScmNil)))) rib_continuation 
  | _ -> raise (X_syntax_error(ribs,"Wrong syntax for cond"))

and case_3 sexp= 
  let body = match sexp with 
     ScmPair(ScmPair(ScmSymbol("else"), b),r)-> b 
     | _-> (ScmSymbol "")  in
  ScmPair(ScmSymbol("begin"),(macro_expand body))

and case_2 sexp =
  let body = match sexp with 
     ScmPair(ScmPair(t,ScmPair(ScmSymbol("=>"),b)),r)-> b 
     | _-> (ScmSymbol "") in 
  let test = match sexp with 
     ScmPair(ScmPair(t,ScmPair(ScmSymbol("=>"),b)),r)-> t  
    | _-> (ScmSymbol "") in
  let rest = match sexp with 
     ScmPair(ScmPair(t,ScmPair(ScmSymbol("=>"),b)),r)-> r  
    | _-> (ScmSymbol "") in    
  let var_for_test= ScmPair(ScmSymbol "value", ScmPair ((macro_expand test), ScmNil)) in 
  let var_for_exprf_lambda= ScmPair(ScmSymbol "f", ScmPair 
  (ScmPair(ScmSymbol "lambda", ScmPair (ScmNil,(macro_expand body))),ScmNil)) in
  let var_for_rest= ScmPair(ScmPair(ScmSymbol "rest",ScmPair 
          (ScmPair(ScmSymbol "lambda", ScmPair (ScmNil,(ScmPair ((expand_cond rest), ScmNil)))),ScmNil)),
           ScmNil) in
  macro_expand (ScmPair(ScmSymbol("let"),ScmPair(ScmPair( var_for_test,ScmPair( var_for_exprf_lambda,var_for_rest
  )),ScmPair(ScmPair(ScmSymbol "if",ScmPair(ScmSymbol "value",ScmPair(ScmPair(ScmPair 
           (ScmSymbol "f", ScmNil), ScmPair (ScmSymbol "value", ScmNil)), ScmPair (ScmPair 
           (ScmSymbol "rest", ScmNil), ScmNil)))),ScmNil))))


and expand_define sexp =
  let vars = match sexp with 
     ScmPair(ScmSymbol("define"), ScmPair(ScmPair(v,p),b))-> v 
     | _-> (ScmSymbol "") in 
  let parameters = match sexp with 
     ScmPair(ScmSymbol("define"), ScmPair(ScmPair(v,p),b))-> p  
    | _-> (ScmSymbol "") in
  let body = match sexp with 
     ScmPair(ScmSymbol("define"), ScmPair(ScmPair(v,p),b))-> b 
     | _-> (ScmSymbol "") in 
  ScmPair(ScmSymbol("define"), ScmPair(vars,ScmPair(ScmPair(ScmSymbol("lambda"),
  ScmPair(parameters,body)),ScmNil)))

and expand_and s = 
  let first = match s with 
     ScmPair(ScmSymbol("and"), ScmPair(r,rs))-> r 
     | _-> (ScmSymbol "") in 
  let rest = match s with 
     ScmPair(ScmSymbol("and"), ScmPair(r,rs))-> rs  
    | _-> (ScmSymbol "") in
  let ans= match rest with
    | ScmNil -> first
    | r-> ScmPair(ScmSymbol("if"),ScmPair(first,ScmPair(macro_expand 
    (ScmPair(ScmSymbol("and"),rest)),ScmPair(ScmBoolean(false),ScmNil)))) in 
    ans

and macro_expand sexpr =
match sexpr with
  | ScmPair(ScmSymbol("let"), ScmPair(binds,body)) -> expand_let binds body
  | ScmPair (ScmSymbol "let*", ScmPair (binds , body)) -> macro_expand_structual_let binds body
  | ScmPair(ScmSymbol("letrec"),ScmPair(binds,body)) -> macro_expand (expand_letrec (ScmPair(ScmSymbol("letrec"),ScmPair(binds,body))))
  | ScmPair(ScmSymbol("and"), ScmNil) -> ScmBoolean(true)
  | ScmPair(ScmSymbol("and"), ScmPair(rib,ribs)) ->  (expand_and (ScmPair(ScmSymbol("and"), ScmPair(rib,ribs))))                           
  | ScmPair(ScmSymbol("cond"), r) -> if (scm_list_length r) != 0 
                                        then expand_cond r
                                        else raise (X_syntax_error(sexpr,"Wrong syntax for cond")) 
  | ScmPair(ScmSymbol("define"), ScmPair(ScmPair(var,args),body)) -> 
                                      (expand_define (ScmPair(ScmSymbol("define"), ScmPair(ScmPair(var,args),body))))
  | ScmPair(ScmSymbol("quasiquote"),ScmPair(x,ScmNil)) -> macro_expand_quansiqoute x
  | _ -> sexpr

end;; 


