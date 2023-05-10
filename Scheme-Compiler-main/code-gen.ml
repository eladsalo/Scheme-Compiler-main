#use "semantic-analyser.ml";;
exception X_this_should_not_happen;;


module type CODE_GEN = sig  

  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

 
 
  val make_fvars_tbl : expr' list -> (string * int) list

 
 
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;


module Code_Gen : CODE_GEN = struct
  
    let freeV =   
    [
    "boolean?"; "flonum?"; "rational?";
    "pair?"; "null?"; "char?"; "string?";
    "procedure?"; "symbol?";
    "string-length"; "string-ref"; "string-set!";
    "make-string"; "symbol->string";
    "char->integer"; "integer->char"; "exact->inexact";
    "eq?";
    "+"; "*"; "/"; "="; "<";
    "numerator"; "denominator"; "gcd";
    "cons";"car";"cdr";"set-car!";"set-cdr!";"apply"
    ];;



  let rec extract_sexp ast =
    match ast with
    | ScmConst'(v) -> [v]
    | ScmIf'(t, doIfTrue, doIfFalse) -> (List.append (extract_sexp t)(List.append (extract_sexp doIfTrue) (extract_sexp doIfFalse)))
    | ScmLambdaSimple'(p,b) -> extract_sexp b
    | ScmLambdaOpt'(p,o,b) -> extract_sexp b
    | ScmSeq'(e) -> List.flatten(List.map extract_sexp e)
    | ScmSet'(v,e) -> extract_sexp e
    | ScmDef'(v,e) -> extract_sexp e
    | ScmOr'(l) -> List.fold_left (fun free_lst exp -> (free_lst @ (extract_sexp exp))) [] l
    | ScmApplic'(v,e) ->  (List.flatten(List.map extract_sexp ([v]@e)))
    | ScmBoxSet'(s,t) -> extract_sexp t
    | ScmApplicTP'(v,e) -> (List.flatten(List.map extract_sexp ([v]@e)))
    | _ -> []
  
  let rec extractFreeV ast=    
    match ast with
    | ScmVar'(v) -> (match v with
                          | VarFree(x) -> [x]
                          | _-> [])
    | ScmSeq'(l) -> List.fold_left (fun const_lst exp -> (List.append const_lst (extractFreeV exp))) [] l
    | ScmDef'(v,e) ->  List.append (match v with
                                        | VarFree(x) -> [x]
                                        | _-> []) (extractFreeV e)
    | ScmOr'(l) -> List.flatten(List.map extractFreeV l)
    | ScmLambdaSimple'(p,b) -> extractFreeV b
    | ScmBoxSet'(s,t) -> extractFreeV t
    | ScmIf'(test, tr, fa) -> List.append (extractFreeV test) (List.append(extractFreeV tr) (extractFreeV fa))
    | ScmLambdaOpt'(p,o,b) -> extractFreeV b
    | ScmApplic'(v,e) -> (List.flatten(List.map extractFreeV (List.append [v] e)))
    | ScmSet'(v,e) -> (List.append (match v with
                                      | VarFree(x) -> [x]
                                      | _-> []) (extractFreeV e)
                                      )
    | ScmApplicTP'(v,e) -> (List.flatten(List.map extractFreeV (List.append [v] e)))
    | _ -> []



  
  

    let get_size s=   
    let void_nil = 0 in
    let boolean_char = 1 in
    let object_sym = 8 in
    let word_size = 8 in
    let pair_ratio = 16 in
    (match s with
      | ScmVoid -> void_nil 
      | ScmString(exp) -> (String.length exp) +object_sym
      | ScmSymbol(exp)-> object_sym
      | ScmBoolean(exp) -> boolean_char
      | ScmNil -> void_nil
      | ScmVector(exp)->  ((List.length exp)*word_size)+ object_sym
      | ScmChar(exp) -> boolean_char
      | ScmNumber(ScmReal(exp))-> object_sym
      | ScmNumber(ScmRational(exp,exp1))-> pair_ratio
      | ScmPair(exp,exp1) -> pair_ratio) 


  let offsetMaker lst sexpr = fst (List.assoc sexpr lst);; 
  

  let allocate_const s lst oS= 
    match s with
    | ScmNumber(ScmRational(a,b))-> (List.append lst [(s,(oS,(Printf.sprintf "\n db 0x3 \n dq %d \n dq %d" a b)))], (oS+(get_size s)+1) )    
    | ScmChar(x) ->  (List.append lst [(s,(oS,(Printf.sprintf "\n db 6 \n db %d" (int_of_char x))))] , (oS+(get_size s)+1) )
    | ScmPair(a,b) -> (List.append lst [(s,(oS, (Printf.sprintf "\n db 10 \n dq (const_tbl+%d) \n dq (const_tbl+%d)" (fst(List.assoc a lst)) (fst(List.assoc b lst)))))], (oS+(get_size s)+1) )
    | ScmBoolean(x) -> 
      let allo = (match x with 
                | true -> "\n db 0x5, 1"
                | false-> "\n db 0x5, 0") in
    (List.append lst [(s,(oS,allo))] , (oS+(get_size s)+1) )
    | ScmNumber(ScmReal(x))-> (List.append lst [(s,(oS, (Printf.sprintf "\n db 4 \n dq %s" (string_of_float x))))],(oS+(get_size s)+1) )
    | ScmVoid -> (List.append lst [(s,(oS, "\n db 0x1"))] , (oS+(get_size s)+1) )
    | ScmString(x) -> (List.append lst [(s,(oS,(Printf.sprintf "MAKE_LITERAL_STRING \"%s\"" x)))],(oS+(get_size s)+1) )
    | ScmSymbol(x)->  (List.append lst [(s,(oS, (Printf.sprintf "\n db 8 \n dq (const_tbl+%d)" (fst(List.assoc (ScmString(x)) lst)) )))], (oS+(get_size s)+1) )
    | ScmNil ->  (List.append lst [(s,(oS, "\n db 0x2"))] , (oS+(get_size s)+1) )
    | ScmVector(a)->
        let rec createVec s l=  
        match s with
          | [] -> ""
          | [first] -> "const_tbl+" ^ (string_of_int( fst (List.assoc first l)))
          | first :: more -> ("const_tbl+" ^(string_of_int(fst (List.assoc first l)))^", " ^(createVec more l)) in         
        (List.append lst [(s,(oS, (Printf.sprintf "MAKE_LITERAL_VECTOR %s" (createVec a lst))))], (oS+(get_size s)+1) )
  
        
  let deal_tup argu =
    let rec execFun argu offS =
    let def_size = 8 in
    match argu with
    | f :: s -> [(f,offS)]@(execFun s (offS+def_size))
    | [] -> []
    in
    execFun argu 0;;

  let first_step asti = List.fold_left (fun x ast -> x @ extract_sexp ast) [] asti   (*kob  *)


  let rec extract_sub sexpr =     
    match sexpr with
    | ScmSymbol(exp) -> List.append [ScmString(exp)] [sexpr]
    | ScmVector(exprs) -> List.append (List.flatten(List.map extract_sub exprs)) [sexpr]
    | ScmPair(f,s) -> (List.append(extract_sub f) (List.append (extract_sub s) [sexpr]))
    | _-> [sexpr] 


  let make_consts_tbl asts =     
    let step2 = (List.fold_left (fun l sexpr -> if ((List.mem sexpr l)) then l else (List.append l [sexpr])) [] (first_step asts)) in 
    let step3 = List.flatten( List.map extract_sub step2)  in 
    let step4 = List.append [ScmVoid;ScmNil;ScmBoolean false;ScmBoolean true] step3 in 
    let step4 = (List.fold_left (fun l sexpr -> if ((List.mem sexpr l)) then l else (List.append l [sexpr])) [] step4) in 
    let tmp=0 in 
    let (c,o) = List.fold_left (fun (lst,o) sexpr ->  (allocate_const sexpr lst o)) ([],tmp) step4 in                                                  
    c;;

  let helpFvar lst ast = lst@ extractFreeV ast   

  let make_fvars_tbl asts =       
    let create_free = List.fold_left (helpFvar) [] asts in 
    let create_free = deal_tup (List.fold_left (fun l sexpr -> if ((List.mem sexpr l)) then l else (List.append l [sexpr])) [] (freeV @ create_free)) in 
    create_free;;


let rec genHelperF vl =
    match vl with
    | [s] -> ([], s)
    | _ -> match vl with
           |  s :: vl ->
                let (z, t) = genHelperF vl
                in (s :: z, t)
           | _ -> raise X_this_should_not_happen;;


let pointee = ref 0;;
let createTask () =
  let k = 1 in
  let t = !pointee in
  (pointee := !pointee + k); (string_of_int t)


  let generate consts fvars e =                  
    let rec run e getSi =
    match e with
      | ScmConst'(f) -> let oF = offsetMaker consts f in             
                         "\n mov rax" ^ ", ( const_tbl"^" +"^(string_of_int oF) ^ ")"
      | ScmVar'(VarParam(x,y)) -> 
          (Printf.sprintf "mov rax, qword [rbp+%d*(%d+%d)]" 8 4 y)

      | ScmVar'(VarFree(x)) -> 
          let offset = List.assoc x fvars in
          Printf.sprintf "mov rax, qword [fvar_tbl+%d]" offset

      | ScmVar'(VarBound(x,y,z)) -> 
          (Printf.sprintf "mov rax, qword [rbp+%d]\n" 16 ) ^
          Printf.sprintf "mov rax, qword [rax+%d*%d]\n" 8 y ^
          Printf.sprintf "mov rax, qword [rax+%d*%d]" 8 z


 
      | ScmIf'(test,dit,dif) ->     let point = createTask () in
                                    let label_of_exit = "Lexit"^point in
                                    let label_of_else = "Lelse"^point in
                                    let generateIf = (run test getSi) ^ "\n" ^"cmp rax, SOB_FALSE_ADDRESS\n" ^
                                   "\n"^"je "^ (Printf.sprintf "%s" label_of_else) ^"\n"^(run dit getSi) ^  
                                   "\n" ^"jmp "^ label_of_exit ^ "\n"^ label_of_else ^":"^"\n"^ (run dif getSi) ^ 
                                   "\n" ^(Printf.sprintf "%s" label_of_exit)^":" in
                                   (generateIf)
    
      | ScmBoxSet'(x,y) ->    
                                    (run y getSi) ^ "\n" ^ "push rdi\n"^"push rax\n" ^
                                   (take_Var x) ^ "\n" ^"pop qword [rax]\n" ^
                                   "mov rax, SOB_VOID_ADDRESS\n" ^"mov rdi, rax" ^""^"\n" ^ "pop rdi\n"


      | ScmSeq'(x) ->    (List.fold_left (fun acc expr -> acc^(run expr getSi)^ "\n") "" x) ^ "\n"

      | ScmSet'(x,y) -> change_var x y getSi

      | ScmOr'(inp) ->     let (expr_lst,last_expr) = genHelperF inp in
                             let point = createTask () in
                             let label_of_exit = ""^"Lexit"^point in
                             let coditionin = Printf.sprintf "cmp rax,"^" " ^  "SOB_FALSE_ADDRESS"^"\n" ^"jne "^label_of_exit^"\n" in
                            let gs1 = run last_expr getSi in
                            let gs2 = List.fold_left (fun acc expr -> acc ^ (run expr getSi) ^ "\n" ^ coditionin) "" expr_lst in
                            let asm_or = gs2^gs1^ "\n"^""^ label_of_exit ^":"^"" in
                            (asm_or)
      | ScmBox'(VarParam(x,y)) ->    
                                             Printf.sprintf "\n mov rbx, qword [rbp+8*(4+%d)]" y ^"\n"^
                                             "MALLOC rax,"^" 8" ^
                                             "\n" ^ "mov qword [rax], rbx" ^ "\n"^ "inc rdi"^"\n"
      | ScmLambdaSimple'(params,body) -> lambda_fun_s params body getSi (createTask())
      | ScmBoxGet'(var) ->       
                                  let asm_var = (take_Var var) ^ "\n"in
                                    asm_var ^ "push rsi\n" ^"mov rax, qword [rax]\n"^ "mov rsi, rax\n inc rsi\n pop rsi"
      | ScmDef'(x,y) ->    let v = change_var x y getSi in
                                v    
      | ScmLambdaOpt'(params,opt,body) -> lambda_opt_fun params opt body getSi (createTask())
      | ScmApplic'(proc,args) -> applic_fun proc args getSi
      | ScmApplicTP'(proc,args) -> applic_fun_tp proc args getSi
      | _ -> raise X_this_should_not_happen


  and varHelper x y s =     match x with
    | VarFree(x) -> let asm_expr = run y s in
      let offset = List.assoc x fvars in
      asm_expr^"\n"^
      (Printf.sprintf "mov qword [fvar_tbl+%d], rax\n" offset) ^
      "mov rax, SOB_VOID_ADDRESS"
    | _ -> raise X_this_should_not_happen
        

  
  and change_var var y s =
    match var with
    | VarParam(x,minor) -> 
      let asm_expr = run y s in
      asm_expr^"\n"^
      (Printf.sprintf "mov qword [rbp+%d*(4+%d)], rax\n" 8 minor ) ^
       "mov rax, SOB_VOID_ADDRESS"
       
    | VarBound(x,ma,mi) -> 
      let asm_expr = run y s in

      asm_expr^"\n"^
      (Printf.sprintf "mov rbx, qword [rbp+%d]" 16)^"\n"^
      Printf.sprintf "mov rbx, qword [rbx+%d*%d]\n" 8 ma ^
      Printf.sprintf "mov qword [rbx+%d*%d], rax\n" 8 mi ^
      "mov rax, SOB_VOID_ADDRESS"
    | _ -> varHelper var y s

  and take_Var = function
    | VarParam(x,y) -> 
        (Printf.sprintf "mov rax, qword [rbp+%d*(%d+%d)]" 8 4 y)

    | VarFree(x) -> 
        let offset = List.assoc x fvars in
        Printf.sprintf "mov rax, qword [fvar_tbl+%d]" offset

    | VarBound(x,y,z) -> 
        (Printf.sprintf "mov rax, qword [rbp+%d]\n" 16 ) ^
        Printf.sprintf "mov rax, qword [rax+%d*%d]\n" 8 y ^
        Printf.sprintf "mov rax, qword [rax+%d*%d]" 8 z

and lambda_opt_fun ex p ins getSi pointe =
      ";; kobi started lamda opt " ^ (string_of_int getSi) ^" "^"\n" ^
     (lambda_reg_fun getSi pointe) ^ 
     (lcode_opt_fun ex ins getSi pointe)

  and lcode_opt_fun ex ins getSi pointe =
    let deal_with_st = 
    "mov rdx, qword [rbp+24]"^"\n" ^"push rsi\n"^"mov r10, rdx"^"\n" ^ "inc rsi\n"^ 
    "dec rdx"^"\n" ^"pop rsi\n"^
    "lea rcx, [rdx-"^ (string_of_int (List.length ex))^"] "^"\n"^"cmp rcx, 0\n" ^
    "jle settin"^pointe^"\n" ^"\n" ^
    "dec rdx"^"\n" ^ (Printf.sprintf "mov rbx, qword [rbp+%d*(4+rdx)]" 8) ^"\n" ^"\n"^ 
    "MAKE_PAIR(rax,rbx,SOB_NIL_ADDRESS)"^"\n"^
    "dec rdx"^"\n"^"dec rcx"^"\n"^"push rsi\n"^"inc rsi\n"^"pop rsi\n"^
    "createLs" ^ pointe ^ ":"^"\n" ^"\tcmp rcx, 0"^"\n" ^
    "\tje"^" stopLs"^pointe^"\n"^"\t"^"mov rbx, qword [rbp+8*(4+rdx)]"^"\n" ^ 
    "MAKE_PAIR(r12,rbx,rax)"^"\n" ^
    "mov rax,r12"^"\n" ^
    "dec rdx"^"\n" ^"push rsi\n"^"dec rsi\n"^"pop rsi\n"^
    "dec rcx"^"\n"^ 
    "jmp createLs" ^ pointe ^"\n" ^
    "stopLs"^pointe^":"^"\n" ^"inc rsi\n"^"\n" ^
    "push SOB_NIL_ADDRESS"^"\n"^"inc rsi\n"^"push rax"^"\n"^
    (Printf.sprintf "lea r11, [rdx+%d] "3)^"\n" ^
    "argsCase"^pointe^":"^"\n"^"\t"^"cmp rdx, 0 \n" ^
    "\t"^"jl stopCAs"^pointe^"\n"^"\t"^" push PVAR(rdx)"^"\n"^
    "\t"^"dec rdx"^"\n"^"\t"^"jmp argsCase"^pointe^"\n"^
    "stopCAs"^pointe^":"^"\n"^"\n" ^ "push r11\n"^
    "push qword [16+rbp]\n"^(Printf.sprintf "push qword [%d+rbp]\n" 8) ^
    "push qword [rbp]\n" ^"\n" ^
    (Printf.sprintf"add r11, %d\n \n" 4 )^
    "SHIFTING r11"^"\n" ^"pop rbp\n"^
    (Printf.sprintf"lea rsp, [rsp+WORD_SIZE*(r10+%d)] \n" 4)^
    "push rbp"^"\n"^ "mov rbp, rsp"^"\n"^ "settin"^pointe^":"^"\n" in
    "Lcode"^pointe^":\n" ^ "\tpush rbp"^"\n" ^
    "\tmov rbp, rsp"^"\n" ^ deal_with_st ^(run ins (getSi + 1)) ^ "\n" ^
    "\t"^"leave"^"\n" ^"\t"^"ret\n" ^"Lcont"^pointe^":\n"
  

  and lambda_reg_fun e c =
      let cur= e+1 in
      let word_size= 8 in 
      let ans=0 in 
      (Printf.sprintf "mov rcx,%d \n " e) ^
      "cmp rcx, 0 \n"^
      (Printf.sprintf "je empty_env%s \n" c)^
      (Printf.sprintf "MALLOC rax, %s \n" (string_of_int ((cur)*word_size))) ^
      "mov rbx, 0  \n"^
      (Printf.sprintf "mov rdx, %d  \n" 1) ^
      "mov r8, qword [16+rbp]  \n" ^ 
      (Printf.sprintf "loop_rec%s:\n" c) ^
      "cmp rbx, rcx    \n"^
      (Printf.sprintf "jge loop_finish_rec%s \n" c ) ^
      "mov r9, qword [r8+8*rbx]     \n" ^  
      "mov qword [rax+8*rdx], r9  \n" ^
      "add rbx,2    \n" ^
      "add rdx, 1    \n" ^
      "dec rbx   \n" ^
      (Printf.sprintf "jmp loop_rec%s \n"  c ) ^
      (Printf.sprintf "loop_finish_rec%s:\n" c)  ^
      "mov rcx, qword [24+rbp]  \n" ^
      "shl rcx, 1 \n" ^
      "shl rcx, 2 \n" ^
      "MALLOC rbx, rcx \n" ^
      "\n push rsi" ^ 
      "\n push rdi"^
      " \n mov rsi,rax "^
      " \n mov rdi,rsi \n inc rsi \n dec rdi \n pop rdi \n pop rsi \n" ^
      "mov rcx, qword [24+rbp] \n" ^ 
      (Printf.sprintf "mov rdx, %d  \n" ans) ^
      (Printf.sprintf "loop_rec_second%s:\n" c) ^
      "cmp rdx, rcx\n" ^
      (Printf.sprintf "jge loop_rec_second_finish%s \n " c ) ^
      "mov r8, qword [8*(4+rdx)+rbp]   \n"^
      "mov qword [WORD_SIZE*rdx+rbx], r8    \n"^  
      "add rdx,1    \n" ^
      (Printf.sprintf "jmp loop_rec_second%s \n" c) ^
      (Printf.sprintf "loop_rec_second_finish%s: \n" c)^
      "mov qword [rax], rbx   \n" ^  
      "\n push rax" ^ 
      "\n push rdi"^
      " \n mov rax,rax "^
      " \n mov rdi,rax \n inc rax \n dec rdi \n pop rdi \n pop rax \n" ^    
      "mov rbx, rax    \n" ^
      (Printf.sprintf "MAKE_CLOSURE(rax,rbx,Lcode%s)  \n" c) ^
      (Printf.sprintf "jmp Lcont%s  \n" c) ^
      (Printf.sprintf "empty_env%s:  \n" c) ^
      "\n push rsi" ^ 
      "\n push rdi"^
      " \n mov rsi,rax "^
      " \n mov rdi,rsi \n inc rsi \n dec rdi \n pop rdi \n pop rsi \n" ^
      (Printf.sprintf "MALLOC rbx, %d \n" 8) ^
      "mov qword [rbx], SOB_NIL_ADDRESS   \n" ^
      (Printf.sprintf "MAKE_CLOSURE(rax,rbx,Lcode%s)\n" c)  ^
      (Printf.sprintf "jmp Lcont%s \n" c)

  and lambda_fun_s p b e c =
     (lambda_reg_fun e c) ^
     "\n push rsi \n push rcx \n mov rsi,rax \n mov rcx,rsi \n inc rsi \n dec rcx \n"^
     "pop rcx \n pop rsi \n" ^
      (lambda_code_l b e c)

    
    and lambda_code_l b e c =
      let tmp=1 in
      (Printf.sprintf "Lcode%s:\n" c) ^
      "push rbp\n" ^
      "mov rbp, rsp\n" ^
      "push rsi \n" ^
      "push rcx \n" ^
      "mov rcx,[rbp] \n" ^
      "mov rsi,rcx \n" ^
      "pop rcx \n" ^
      "inc rsi \n" ^
      "pop rsi \n" ^
      (run b (e + tmp)) ^ "\n" ^
      "leave\n" ^
      "ret\n" ^
      "Lcont"^c^":\n" 


    and applic_fun f p e =
      let tmp= "" in
      let cur= (fun arg str -> str^(run arg e)^"\n push rax\n") in
      "\n push rsi \n mov rsi,rax \n pop rsi \n push SOB_NIL_ADDRESS \n"^
      (List.fold_right cur p tmp) ^
      (Printf.sprintf "push %d \n " (List.length p + 1)) ^
      (run f e)^"\n" ^
      "cmp byte [rax], 0x9 \n"^
      "jne otherError\n" ^
      "\n push rsi \n" ^
      "mov rbx, qword [1+rax]  \n" ^
      "\n mov rsi, rbx \n" ^ 
      "\n dec rsi \n" ^
      "\n pop rsi \n" ^
      "push rbx  \n" ^
      "mov rax, qword [9+rax]  \n" ^
      "call rax   \n" ^
      (Printf.sprintf "add rsp, %d" 6 ) ^ "\n"^
      "inc rsp \n" ^
      "inc rsp \n" ^
      "pop rbx  \n" ^
      (Printf.sprintf "lea rsp, [rsp+%d*rbx]\n" 8 )

    and applic_fun_tp f p e =
      let tmp= "" in
      let cur= (fun arg str -> str^(run arg e)^"\npush rax\n") in
      let cur_c=5 in    
      "\n push rsi \n mov rsi,rax \n pop rsi \n push SOB_NIL_ADDRESS \n"^
      (List.fold_right cur p tmp) ^
      (Printf.sprintf "push %d\n" (List.length p + 1)) ^
      "\n" ^(run f e)^"\n" ^
      "\n push rdi \n mov rdi,rax \n inc rdi \n cmp byte [rax], 0x9  \n pop rdi \n"^
      "\n" ^"jne otherError\n" ^
      "\n push rsi \n" ^
      "mov rcx, qword [24+rbp]  \n" ^
      "\n mov rsi, rbx \n" ^
      "\n inc rsi \n" ^
      "mov rbx, qword [rax+1]  \n" ^
      "\n pop rsi \n" ^
      "push rbx \n" ^
      "mov rax, qword [9+rax]  \n" ^   
      "push qword [8+rbp]\n" ^
      "push qword [rbp]  \n" ^
      " \n" ^
      "SHIFTR " ^ (string_of_int ((List.length p) + cur_c)) ^ "\n" ^
      "pop rbp\n" ^
      (Printf.sprintf "lea rsp, [rsp + %d*(rcx+4)]" 8 ) ^ "\n" ^
      "jmp rax\n"
    in
    run e 0;;
end;;

