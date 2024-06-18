open Program
open Error

(* Our symbol table will be a mapping from 'string' to 'ctype_entry'. *)
type ctype_entry =
  | VarType of ctype
  | FuncType of ctype * ctype list (* return type * argument type list *)

(* Define a module for symbol table *)
module SymbolMap = Map.Make(String)

(* During the semantic analysis, this type can be helpful. Why do we need this
 * even though 'ctype' is already defined? If you encounter a wrong expression
 * during the semantic analysis (for example "1 + true"), you cannot decide its
 * type but still may have to return something. *)
type typ = Void | Int | Bool | Unknown

let ctyp_to_typ ctyp =
  match ctyp with
  | CVoid -> Void
  | CInt -> Int
  | CBool -> Bool

let typ_to_ctyp ctyp =
  match ctyp with
  | Void -> CVoid
  | Int -> CInt
  | Bool -> CBool
  | Unknown -> (* Raise exception *)
      failwith "Not allowed (You should not call this in such situation)"

(* Record the type of variables into the symbol table *)
let rec collect_vars decls sym_tab =
  match decls with
  | [] -> sym_tab
  | head_decl :: tail_decls ->
      let (ctyp, vname) = head_decl in
      let sym_tab = SymbolMap.add vname (VarType ctyp) sym_tab in
      collect_vars tail_decls sym_tab

(* Record the type of functions into the symbol table *)
let rec collect_functions funcs sym_tab =
  match funcs with
  | [] -> sym_tab
  | head_func :: tail_funcs ->
      let (fname, ret_type, args, stmt) = head_func in
      let arg_ctypes = List.map (fun (typ, _) -> typ) args in
      let sym_tab = SymbolMap.add fname (FuncType (ret_type, arg_ctypes)) sym_tab in
      collect_functions tail_funcs sym_tab

(* Record the type of arguments into the symbol table *)
let rec collect_args args sym_tab = 
  match args with
  | [] -> sym_tab
  | head_arg :: tail_args -> 
    let (argc_ctyp, vname) = head_arg in
    let sym_tab = SymbolMap.add vname (VarType argc_ctyp) sym_tab in
    collect_args tail_args sym_tab      
    

  
(* Check expression 'e' and return detected semantic errors, along with the
 * decided type of 'e'. If the type of expression cannot be decided due to
 * semantic error, return 'Unknown' as its type. *)


let rec check_exp sym_tab e =
  match e with
  | ConstBool b -> ([], Bool)
  | ConstInt i -> ([], Int)

  | Var v -> 
    if SymbolMap.mem v sym_tab then
    (match SymbolMap.find v sym_tab with
    | (VarType var_type) -> ([], ctyp_to_typ var_type)
    | (FuncType (ret_type, arg_types)) -> ([UsingFunctionAsVar (v)], ctyp_to_typ ret_type))
    else ([UndefinedName v], Int)

  | Add (exp1, exp2) | Sub (exp1, exp2) | Mul (exp1, exp2) | Div (exp1, exp2)-> 
    let (errors1, type1) = check_exp sym_tab exp1 in
    let (errors2, type2) = check_exp sym_tab exp2 in
    (match (type1, type2) with
    | (Int, Int) -> (errors1 @ errors2, type1)
    | _ -> 
      if List.length errors1 != 0 || List.length errors2 !=0  then (errors1 @ errors2, type1)
      else ([OperandMismatch], Int))

  | Neg exp ->
    let (errors1, type1) = check_exp sym_tab exp in
    (match (type1) with
    | (Int) -> (errors1, Int)
    | _ -> ([OperandMismatch], Int))

  | Equal (exp1, exp2) | NotEq (exp1, exp2) -> 
      let (errors1, type1) = check_exp sym_tab exp1 in
      let (errors2, type2) = check_exp sym_tab exp2 in
      (match (type1, type2) with
      | (Bool, Bool) -> (errors1 @ errors2, Bool)
      | (Int, Int) -> (errors1 @ errors2, Bool)
      | _ -> 
        if List.length errors1 != 0 || List.length errors2 !=0  then (errors1 @ errors2, type1)
        else ([OperandMismatch], Bool))

  | LessEq (exp1, exp2) | LessThan  (exp1, exp2) | GreaterEq (exp1, exp2) | GreaterThan (exp1, exp2) -> 
    let (errors1, type1) = check_exp sym_tab exp1 in
      let (errors2, type2) = check_exp sym_tab exp2 in
      (match (type1, type2) with
      | (Int, Int) -> (errors1 @ errors2, Bool)
      | _ -> 
      if List.length errors1 != 0 || List.length errors2 !=0  then (errors1 @ errors2, type1)
      else ([OperandMismatch], Bool))

  | And (exp1, exp2) | Or (exp1, exp2) -> 
    let (errors1, type1) = check_exp sym_tab exp1 in
      let (errors2, type2) = check_exp sym_tab exp2 in
      (match (type1, type2) with
      | (Bool, Bool) -> (errors1 @ errors2, Bool)
      | _ -> 
      if List.length errors1 != 0 || List.length errors2 !=0  then (errors1 @ errors2, type1)
      else ([OperandMismatch], Bool))

  | Not exp ->
    let (errors1, type1) = check_exp sym_tab exp in
    (match (type1) with
    | (Bool) -> (errors1, Bool)
    | _ -> ([OperandMismatch], Bool))

  | CallExp (fname, exp) ->
    if SymbolMap.mem fname sym_tab then
      (match SymbolMap.find fname sym_tab with
      | (VarType var_type) -> ([CallingVariable (fname)], ctyp_to_typ var_type)
      | (FuncType (ret_type, arg_types)) -> 
        if List.length exp != List.length arg_types then ([ArgNumMismatch], ctyp_to_typ ret_type)
        else (check_args arg_types exp sym_tab,  ctyp_to_typ ret_type))
    else ([UndefinedName fname], Int)

and check_args args exps sym_tab =
  match (args, exps) with
  | ([], []) -> [] 
  | (head_arg :: tail_args, head_exp :: tail_exps) -> 
    let err, type1 = check_exp sym_tab head_exp in
    if List.length err != 0 then err
    else if type1 != (ctyp_to_typ head_arg) then [ArgTypeMismatch (head_arg, typ_to_ctyp type1)]
    else (check_args tail_args tail_exps sym_tab)
  | _ -> []


(* Check functions and return detected semantic errors. *)
let rec check_functions sym_tab funcs =
  List.fold_left (fun errors (fname, ret_type, args, stmts) ->
    let sym_tab = collect_args args sym_tab in
    let errors, sym_tab =
      List.fold_left (fun (errs, sym_tab) stmt ->
        match stmt with
        | LocalDecl (ctyp, vname) ->
          let sym_tab = SymbolMap.add vname (VarType ctyp) sym_tab in
          (errs, sym_tab)

        | Assign (vname, exp) ->
          if SymbolMap.mem vname sym_tab then
            let e1_type, e1_err = (match SymbolMap.find vname sym_tab with
            | VarType var_type -> ctyp_to_typ var_type , true
            | FuncType (ret_type, arg_types) -> ctyp_to_typ ret_type, false) in
            let e2_errors, e2_type = check_exp sym_tab exp in
            if e1_err = false then (errs @ [UsingFunctionAsVar vname], sym_tab)
            else if List.length e2_errors != 0 then (errs @ e2_errors, sym_tab)
            else if e1_type != e2_type then (errs @ [AssignMismatch (typ_to_ctyp e1_type, typ_to_ctyp e2_type)], sym_tab)
            else (errs @ e2_errors, sym_tab)
          else (errs @ [UndefinedName (vname)], sym_tab)

        | Call (fname, exp) ->
          if SymbolMap.mem fname sym_tab then
            let e1_type, e1_err, e1_args_num, e2_err = (match SymbolMap.find fname sym_tab with
            | VarType var_type -> (ctyp_to_typ var_type , false, false, [])
            | FuncType (ret_type, arg_types) -> 
              if List.length exp != List.length arg_types then (ctyp_to_typ ret_type , true, false, [])
              else (ctyp_to_typ ret_type, true, true, (check_args arg_types exp sym_tab))) in

            if e1_err = false then (errs @ [CallingVariable fname], sym_tab)
            else if e1_args_num = false then (errs @ [ArgNumMismatch], sym_tab)
            else (errs @ e2_err, sym_tab)
          else (errs @ [UndefinedName (fname)], sym_tab)

        | Return ->
          if ret_type = Void then (errs, sym_tab)
          else (errs @ [ReturnMismatch (typ_to_ctyp ret_type, typ_to_ctyp Void)], sym_tab)
        
        | ReturnValue (exp) ->
          let e1_errs, e1_type = check_exp sym_tab exp in
          if List.length e1_errs != 0 then (errs @ e1_errs, sym_tab)
          else if e1_type = ret_type then (errs @ e1_errs, sym_tab)
          else (errs @ [ReturnMismatch (typ_to_ctyp ret_type, typ_to_ctyp e1_type)], sym_tab)

        | If (exp, stmt1, stmt2) ->
          let e1_errs, e1_type = check_exp sym_tab exp in
          let e2_errs = check_functions sym_tab [(fname, ret_type, args, stmt1)] in
          let e3_errs = check_functions sym_tab [(fname, ret_type, args, stmt2)] in
          if List.length e1_errs != 0 then (errs @ e1_errs @ e2_errs @ e3_errs, sym_tab)
          else if e1_type != Bool then (errs @ [OperandMismatch] @ e2_errs @ e3_errs, sym_tab)
          else (errs @ e1_errs @ e2_errs @ e3_errs, sym_tab)

        | While (exp, stmt)->
          let e1_errs, e1_type = check_exp sym_tab exp in
          let e2_errs = check_functions sym_tab [(fname, ret_type, args, stmt)] in
          if List.length e1_errs != 0 then (errs @ e1_errs @ e2_errs, sym_tab)
          else if e1_type != Bool then (errs @[OperandMismatch] @ e2_errs, sym_tab)
          else (errs @ e1_errs @ e2_errs, sym_tab)
      ) (errors, sym_tab) stmts
    in
    errors
  ) [] funcs

let print_sym_tab sym_tab =
  SymbolMap.iter (fun key value ->
    match value with
    | VarType ctype -> Printf.printf "Var: %s, Type: %s\n" key (ctype_to_str ctype)
    | FuncType (ret_type, arg_types) ->
        let arg_types_str = String.concat ", " (List.map ctype_to_str arg_types) in
        Printf.printf "Func: %s, Return: %s, Args: [%s]\n" key (ctype_to_str ret_type) arg_types_str
  ) sym_tab

(* Check a program and return detected semantic errors. *)
let run (p: program) : error list =
  let (gdecls, funcs) = p in
  let sym_tab = collect_vars gdecls SymbolMap.empty in
  let sym_tab = collect_functions funcs sym_tab in
  (* At this point, 'sym_tab' must contain global variables & functions *)
  (*print_sym_tab sym_tab;*)
  let funcs_as_args = List.map (fun (fname, ret_type, args, stmts) ->
    (fname, ctyp_to_typ ret_type, args, stmts)
  ) funcs in
  check_functions sym_tab funcs_as_args
  

