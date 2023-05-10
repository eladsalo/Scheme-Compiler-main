(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

 #use "pc.ml";;

 let rec gcd a b =
   match (a, b) with
   | (0, b) -> b
   | (a, 0) -> a
   | (a, b) -> gcd b (a mod b);;
 
 type scm_number =
   | ScmRational of (int * int)
   | ScmReal of float;;
 
 type sexpr =
   | ScmVoid
   | ScmNil
   | ScmBoolean of bool
   | ScmChar of char
   | ScmString of string
   | ScmSymbol of string
   | ScmNumber of scm_number
   | ScmVector of (sexpr list)
   | ScmPair of (sexpr * sexpr);;
 
 module type READER = sig
     val nt_sexpr : sexpr PC.parser
 end;; (* end of READER signature *)
 
 module Reader : READER = struct
 open PC;;
 
 let unitify nt = pack nt (fun _ -> ());;
 

 let rec nt_whitespace str =
   const (fun ch -> ch <= ' ') str
 and nt_end_of_line_or_file str =
   let nt1 = unitify (char '\n') in
   let nt2 = unitify nt_end_of_input in
   let nt1 = disj nt1 nt2 in
   nt1 str
and nt_natural str =
  let nt1= range '0' '9' in
  let nt1 = plus nt1 in 
  let nt1 = pack nt1 (fun (x)-> (int_of_string (list_to_string x))) in
  nt1 str  
and nt_line_comment str =
 let nt1 = char ';' in
 let nt_ex = nt_end_of_line_or_file in 
 let nt2 = diff nt_any nt_ex in
 let nt2 = star nt2 in
 let nt3 = caten nt1 nt2 in
 let nt4 = caten nt3 nt_ex in
 let nt4 = unitify nt4 in
 nt4 str
and nt_paired_comment str =
   let nt1 = disj(unitify nt_char) (disj(unitify nt_string) nt_comment) in
   let nto = char '{' in
   let ntc = char '}' in
   let nt_brac = unitify (disj nto ntc) in 
   let nt_brac = disj nt1 (nt_brac) in 
   let nt2 = diff nt_any nt_brac in
   let nt2 = unitify (nt2) in
   let nt3 = star (disj nt2 nt1) in
   let nt3 = caten nt3 (char '}') in
   let nt_done = unitify (caten (char '{') (nt3)) in
   nt_done str
 and nt_sexpr_comment str = 
   let nt_done = unitify (caten (word "#;") nt_sexpr) in
   nt_done str
 and nt_comment str =
   disj_list
     [nt_line_comment;
      nt_paired_comment;
      nt_sexpr_comment] str
 and nt_skip_star str =
   let nt1 = disj (unitify nt_whitespace) nt_comment in
   let nt1 = unitify (star nt1) in
   nt1 str
 and make_skipped_star (nt : 'a parser) =
   let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
   let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
   nt1
  and nt_int str =
    let nt1 = char '+' in
    let nt2 = char '-' in
    let nt1 = maybe (disj nt1 nt2) in
    let nt1 = pack nt1 (fun(option) -> 
    match option with 
    | Some '-'-> '-'
    | _-> '+') in
    let nt2= range '0' '9' in
    let nt2 = plus nt2 in
    let nt1 = caten nt1 nt2 in
    let nt1= pack nt1 (fun (p, r) -> [p]@r ) in 
    let nt1 = pack nt1 (fun (x)-> (int_of_string (list_to_string x))) in
    nt1 str 
  and nt_frac str =
    let nt1= caten (caten nt_int (char '/')) nt_natural in
    let nt1= pack nt1 (fun ((num1,operatorDivide),num2) -> (num1,(gcd num1 num2),num2 )) in
    let nt1= pack nt1 (fun (num1,gcdNum,num2) -> 
      match num2 with
      0 -> raise PC.X_no_match
      | _-> (ScmRational((num1/gcdNum),(num2/gcdNum)))) in 
    nt1 str 
and nt_integer_part str = 
  nt_natural str

and nt_mantissa str = 
  nt_natural str

and nt_exponent str =
  let nt1= disj_list [(word_ci "e"); (word "*10^") ; (word "*10**") ] in
  let nt1= caten nt1 nt_int in
  let nt1 = pack nt1 (fun (x, num) -> num) in
  nt1 str

and nt_float str = 
  let nt1 = char '+' in
  let nt2 = char '-' in
  let nt1 = maybe (disj nt1 nt2) in
  let ntSign = pack nt1 (fun(option) -> 
  match option with 
  | Some '-'-> '-'
  | _-> '+') in

  let nt_FloatA = caten (caten nt_integer_part (char '.')) (caten (maybe nt_mantissa) (maybe nt_exponent)) in 
  let nt_FloatA = pack nt_FloatA (fun ( ((intPart, dot), (mantissaPart, exponentPart)) ) -> 
      match mantissaPart,exponentPart with
        | Some mantissaPart, Some exponentPart ->  
              (( float_of_string ((string_of_int intPart) ^ "." ^ (string_of_int mantissaPart))) *. (10.0 ** (float_of_int exponentPart))) 
        | Some mantissaPart, _-> 
              ( float_of_string ((string_of_int intPart) ^ "." ^ (string_of_int mantissaPart)))
        | _ ,Some exponentPart -> 
               ((float_of_string ((string_of_int intPart) ^ ".")) *. (10.0 ** (float_of_int exponentPart )))
        | _ ,_ -> 
               (float_of_string ((string_of_int intPart) ^ "."))
      ) in

  let nt_FloatB= caten (char '.') (caten nt_mantissa (maybe nt_exponent)) in 
  let nt_FloatB = pack nt_FloatB (fun ( (dot,(mantissaPart,exponentPart)) ) ->
      match exponentPart with
      | Some exponentPart -> ((float_of_string ("0" ^ "." ^ (string_of_int mantissaPart ))) *. (10.0 ** (float_of_int exponentPart)))
      | _ ->(float_of_string ("0" ^ "." ^ (string_of_int mantissaPart )))) in
  let nt_FloatC= caten nt_integer_part nt_exponent in 
  let nt_FloatC = pack nt_FloatC (fun ( (intPart,exponentPart) ) -> 
              ( (float_of_int intPart) *. (10.0 ** (float_of_int exponentPart ) ))
              ) in

  let nt_FloatA = disj_list [nt_FloatA ; nt_FloatB ; nt_FloatC] in  
  let nt1= caten ntSign nt_FloatA in   
  let nt1= pack nt1 (fun (a,b)-> match a with
                      | '-' -> ( (-1.0) *. b) 
                      | _ -> (b) ) in
  let nt1 = pack nt1 (fun s -> ScmReal(s)) in
  nt1 str 
 and nt_number str = 
   let nt1 = nt_float in
   let nt2 = nt_frac in
   let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
   let nt1 = disj nt1 (disj nt2 nt3) in
   let nt1 = pack nt1 (fun r -> ScmNumber r) in
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str
 and nt_boolean str = 
   let nt_true = pack (word_ci "#T") (fun _ -> ScmBoolean(true)) in
   let nt_false = pack (word_ci "#F") (fun _ -> ScmBoolean(false)) in
   let nt1 = disj nt_true nt_false in
   nt1 str

and nt_char_simple str =
  let nt1= range '!' '~' in 
  let nt1 = pack nt1 (fun c -> ScmChar(c)) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str
  
and make_named_char char_name ch = (pack (word_ci char_name) (fun _ -> ScmChar ch))

 and nt_char_named str =
   let nt1 =
       disj_list [(make_named_char "newline" '\n');
                   (make_named_char "nul" '\000');
                   (make_named_char "page" '\012');
                   (make_named_char "return" '\r');
                   (make_named_char "space" ' ');
                   (make_named_char "tab" '\t')] in
   nt1 str

  and nt_char_hex str =
      
      let nt0_9 = range '0' '9' in
      let nt0_9 = pack nt0_9 ( fun ch -> (int_of_char ch) - 48) in
      let nta_f = range 'a' 'f' in
      let nta_f = pack nta_f (fun ch -> (int_of_char ch) - 87) in
      let ntA_F = range 'A' 'F' in
      let ntA_F = pack ntA_F (fun ch -> (int_of_char ch) - 55) in
      let ntaf_AF= disj nta_f ntA_F in 
      let nt1 = caten nt0_9 ntaf_AF  in 
      let nt1 = pack nt1 (fun(x,y) -> 16 * x + y) in 
      let nt2 = disj nt0_9 ntaf_AF  in
      let nt2 = disj nt1 nt2  in 
      let nt2 = plus nt2 in
      let nt2 = pack nt2 (fun d -> List.fold_left (fun x y -> 16 * x + y) 0 d) in
      let nt_x = char_ci 'x' in
      let nt1 = pack (caten nt_x nt2)(fun (_,x) -> x) in
      let nt1 = only_if nt1 (fun n-> n>=0 && n<=255) in
      let nt1 = pack nt1 (fun ch -> char_of_int ch) in
      nt1 str

  and nt_char str = 
    let nt1 = (word "#\\") in
    let nt3 = pack nt_char_hex (fun s -> ScmChar( s )) in
    let nt2 = caten nt1 (disj_list [nt3; nt_char_simple; nt_char_named]) in
    let nt2 = pack nt2 (fun (x, y) -> y) in
    nt2 str
and nt_symbol_char str = 
  let nt_special_chars = one_of "!$^*-_=+<>?/:" in
  let nt1 = disj nt_special_chars (disj (range_ci 'a' 'z') (range '0' '9')) in 
  nt1 str
 and nt_symbol str =
   let nt1 = plus nt_symbol_char in
   let nt1 = pack nt1 list_to_string in
   let nt1 = pack nt1 (fun name -> ScmSymbol name) in
   let nt1 = diff nt1 nt_number in
   nt1 str


and nt_string_interpolated str = 
  let nt1 = caten (word "~{") (caten (nt_sexpr) (word "}") )  in 
  let nt1 = pack nt1 (fun (_,(sexpr,_)) ->
                       ScmPair (ScmSymbol "format", ScmPair (ScmString "~a", ScmPair (sexpr,ScmNil)))) in
  nt1 str


  and nt_strings str = 
  let string_litearl_char = diff nt_any (disj (char '"') (disj (char '\\') (char '~'))) in
  let nt1 = word_ci "\\\\" in 
  let nt1= pack nt1 (fun _ -> '\\') in
  let nt2 = word_ci "\\\"" in 
  let nt2= pack nt2 (fun _ ->  '\"') in 
  let nt3 =word_ci "\\t" in 
  let nt3 = pack nt3 (fun _-> '\t') in 
  let nt4 = word_ci "\\f" in 
  let nt4 = pack nt4 (fun _-> '\012') in 
  let nt5 = word_ci "\\n" in 
  let nt5 = pack nt5 (fun _-> '\n') in 
  let nt6 = word_ci "\\r" in 
  let nt6 = pack nt6 (fun _-> '\r') in 
  let nt7 = word_ci "~~" in 
  let nt7 = pack nt7 (fun _-> '~') in 
  let nt1= disj_list[nt1;nt2;nt3;nt4;nt5;nt6;nt7] in
  let string_hex_char = pack (caten (char '\\') (caten nt_char_hex (char ';'))) (fun (_,(ch,_)) -> ch) in
  let nt1 = disj_list [nt1;string_litearl_char;string_hex_char] in
  let nt1 =  plus nt1 in
  let nt1 = pack nt1 (fun ls -> ScmString (list_to_string ls)) in 
  nt1 str


 and nt_string str =
   let pairCreatorFunction= (fun x y -> ScmPair(x,y) ) in 
   let nt_s = pack (caten (char '"') (caten (star (disj nt_strings nt_string_interpolated))(char '"')))
                       (fun (_,(ls,_)) -> match ls with
                                   [] -> ScmString ""
                                   |[singleItem ] -> singleItem
                                   |_ ->
                                     let ans = List.fold_right pairCreatorFunction ls ScmNil in
                                      ScmPair(ScmSymbol "string-append",ans)) in
   nt_s str
 and nt_vector str =
   let nt1 = word "#(" in
   let nt2 = caten nt_skip_star (char ')') in
   let nt2 = pack nt2 (fun _ -> ScmVector []) in
   let nt3 = plus nt_sexpr in
   let nt4 = char ')' in
   let nt3 = caten nt3 nt4 in
   let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten nt1 nt2 in
   let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
   nt1 str


and nt_list str =
   let empty_list = pack (caten (caten ( char '(' ) nt_skip_star) ( char ')')) (fun _ -> ScmNil) in
   let p_list = pack ( caten ( char '(' ) (caten  (star nt_sexpr) ( char ')' ) ) )
                     (fun (_,(s_expr,_))-> List.fold_right (fun a b -> ScmPair(a,b) ) s_expr ScmNil) in
   let i_list = pack (caten (caten (caten ( char '(') (plus nt_sexpr)) (caten (char '.' ) nt_sexpr )) ( char ')'))
                 (fun (((_,sexpr_before_dot),(_,single_sexp_after_dot)),_)-> List.fold_right (fun a b -> ScmPair(a,b) ) sexpr_before_dot single_sexp_after_dot) in
   let nt1 = disj empty_list (disj p_list i_list) in
   nt1 str


 and nt_quoted_forms str = 
   let nt_q = caten (char (char_of_int 39)) nt_sexpr in 
   let nt_q = pack nt_q (fun (_,s) -> ScmPair(ScmSymbol "quote",ScmPair(s,ScmNil))) in
   let nt_qq = caten (char (char_of_int 96)) nt_sexpr in 
   let nt_qq = pack nt_qq (fun (_,s) -> ScmPair(ScmSymbol "quasiquote",ScmPair(s,ScmNil))) in
   let nt_uq = caten (char (char_of_int 44)) nt_sexpr in 
   let nt_uq = pack nt_uq (fun (_,s) -> ScmPair(ScmSymbol "unquote",ScmPair(s,ScmNil))) in
   let nt_uq_spl = caten (word_ci ",@") nt_sexpr in 
   let nt_uq_spl = pack nt_uq_spl (fun (_,s) -> ScmPair(ScmSymbol "unquote-splicing",ScmPair(s,ScmNil))) in
   let nt1 = disj nt_q nt_qq in 
   let nt1 = disj nt1 nt_uq in 
   let nt1 = disj nt1 nt_uq_spl in 
   nt1 str

 and nt_sexpr str =
   let nt1 =
     disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
                nt_string; nt_vector; nt_list; nt_quoted_forms] in
   let nt1 = make_skipped_star nt1 in
   nt1 str;;
 end;; (* end of struct Reader *)
 
 
 let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;