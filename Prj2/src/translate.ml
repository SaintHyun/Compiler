open Program
open Ir
open Helper

(* The module for symbol table. Carefully think about what should be stored in
 * the symbol table for this IR translation phase. *)
module SymbolMap = Map.Make(String)
module ArgMap = Map.Make(String)
(* 심볼 테이블에는 변수 이름과 레지스터 이름이 매칭되어야 한다.*)

let const_to_imm ctyp =
  match ctyp with
  | ConstBool b -> ImmBool b
  | ConstInt i -> ImmInt i

let reg_to_opr r = 
  Reg r


(* Let's assume that boolean is 1-byte and integer is 4-byte. *)
let sizeof ctyp =
  match ctyp with
  | CInt -> 4
  | CBool -> 1
  | CIntArr n -> 4 * n
  | CBoolArr n -> n

let rec extract_arg_tab arg_tab args =
  match args with
  | [] -> arg_tab
  | head_arg :: tail_args ->
    let (arg_typ, arg_name) = head_arg in
    let arg_tab = ArgMap.add arg_name arg_typ arg_tab in
    extract_arg_tab arg_tab tail_args

let rec extract_names args =
  match args with
  | [] -> []
  | (arg_typ, arg_name) :: tail_args -> arg_name :: extract_names tail_args


let rec trans_exp sym_tab arg_tab e = 
  match e with
  | ConstBool b -> 
    let r = create_register_name() in
    ([Set (r, const_to_imm e)], r)

  | ConstInt i -> 
    let r = create_register_name() in
    ([Set (r, const_to_imm e)], r)

  | Var vname ->
    if SymbolMap.mem vname sym_tab = true then
      let r = create_register_name() in
      let (reg, typ) = SymbolMap.find vname sym_tab in
      ([Load (r, reg)], r)
    else 
      let typ = ArgMap.find vname arg_tab in
      ([], vname)

  | Arr (vname, exp) ->
    let (reg, typ) = SymbolMap.find vname sym_tab in
    let r1 = create_register_name() in
    let tmp1, r2 = trans_exp sym_tab arg_tab exp in
    let r3 = create_register_name() in
    let r4 = create_register_name() in
    (match typ with
    | CIntArr n ->
      let tmp2 = [BinOp(r1, MulOp, Reg r2, Imm (ImmInt 4))] in
      let tmp_inst = [BinOp(r3, AddOp, Reg reg, Reg r1)] in
      (tmp1 @ tmp2 @ tmp_inst @ [Load(r4, r3)], r4)
    | CBoolArr n ->
      let tmp2 = [BinOp(r1, MulOp, Reg r2, Imm (ImmInt 1))] in
      let tmp_inst = [BinOp(r3, AddOp, Reg reg, Reg r1)] in
      (tmp1 @ tmp2 @ tmp_inst @ [Load(r4, r3)], r4)
    )
      
  | Add (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let tmp_inst = inst1 @ inst2 @ [BinOp (r3, AddOp, reg_to_opr r1, reg_to_opr r2)] in
    (tmp_inst, r3)

  | Sub (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let tmp_inst = inst1 @ inst2 @ [BinOp (r3, SubOp, reg_to_opr r1, reg_to_opr r2)] in
    (tmp_inst, r3)

  | Mul (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let tmp_inst = inst1 @ inst2 @ [BinOp (r3, MulOp, reg_to_opr r1, reg_to_opr r2)] in
    (tmp_inst, r3)

  | Div (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let tmp_inst = inst1 @ inst2 @ [BinOp (r3, DivOp, reg_to_opr r1, reg_to_opr r2)] in
    (tmp_inst, r3)

  | Neg (exp) ->
    let inst, r = trans_exp sym_tab arg_tab exp in
    let r2 = create_register_name() in
    let tmp_inst = inst @ [UnOp (r2, NegOp, reg_to_opr r)] in
    (tmp_inst, r2)
  
  | Equal (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let tmp_inst = inst1 @ inst2 @ [BinOp (r3, EqOp, reg_to_opr r1, reg_to_opr r2)] in
    (tmp_inst, r3)

  | NotEq (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let tmp_inst = inst1 @ inst2 @ [BinOp (r3, NeqOp, reg_to_opr r1, reg_to_opr r2)] in
    (tmp_inst, r3)

  | LessEq (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let tmp_inst = inst1 @ inst2 @ [BinOp (r3, LeqOp, reg_to_opr r1, reg_to_opr r2)] in
    (tmp_inst, r3)

  | LessThan (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let tmp_inst = inst1 @ inst2 @ [BinOp (r3, LtOp, reg_to_opr r1, reg_to_opr r2)] in
    (tmp_inst, r3)

  | GreaterEq (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let tmp_inst = inst1 @ inst2 @ [BinOp (r3, GeqOp, reg_to_opr r1, reg_to_opr r2)] in
    (tmp_inst, r3)

  | GreaterThan (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let tmp_inst = inst1 @ inst2 @ [BinOp (r3, GtOp, reg_to_opr r1, reg_to_opr r2)] in
    (tmp_inst, r3)

  | And (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let r4 = create_register_name() in
    let l1 = create_label() in
    let l2 = create_label() in
    (inst1 @ [GotoIfNot (r1, l1)] @ inst2 @ [Copy (r2, r3)] @ [Goto (l2)] @ [Label (l1)] @ [Set (r3, ImmBool false)] @ [Label (l2)] @ [Copy(r3, r4)], r4)

  | Or (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let r3 = create_register_name() in
    let r4 = create_register_name() in
    let l1 = create_label() in
    let l2 = create_label() in
    (inst1 @ [GotoIf (r1, l1)] @ inst2 @ [Copy (r2, r3)] @ [Goto (l2)] @ [Label (l1)] @ [Set (r3, ImmBool true)] @ [Label (l2)] @ [Copy(r3, r4)], r4)

  | Not (exp) ->
    let inst, r = trans_exp sym_tab arg_tab exp in
    let r2 = create_register_name() in
    let tmp_inst = inst @ [UnOp (r2, NotOp, reg_to_opr r)] in
    (tmp_inst, r2)
  

let rec trans_function sym_tab arg_tab stmts =
  let instrs, sym_tab=
    List.fold_left(fun (irs, sym_tab) stmt ->
        match stmt with
        | LocalDecl (ctyp, vname) ->
          let reg = create_register_name () in
          let size = sizeof ctyp in
          let inst = LocalAlloc (reg, size) in
          let temp_inst = [inst] in
          let sym_tab = SymbolMap.add vname (reg, ctyp) sym_tab in
          (irs @ temp_inst, sym_tab)

        | Assign (lvar, exp) ->
          (match lvar with
          | LVar str -> 
            if SymbolMap.mem str sym_tab = true then
              let (reg, typ) = SymbolMap.find str sym_tab in
              let tmp_ir, result = trans_exp sym_tab arg_tab exp in
              (irs @ tmp_ir @ [Store (reg_to_opr result, reg)], sym_tab)
            else
              let typ = ArgMap.find str arg_tab in
              let tmp_ir, result = trans_exp sym_tab arg_tab exp in
              (irs @ tmp_ir @ [Copy (result, str)], sym_tab)

          | LArr (str, exp2) ->
            let tmp_ir1, rright = trans_exp sym_tab arg_tab exp in
            let tmp_ir2, rleft = trans_exp sym_tab arg_tab exp2 in
            let (reg, typ) = SymbolMap.find str sym_tab in
            let r1 = create_register_name() in
            let r2 = create_register_name() in
            (match typ with
            | CIntArr n ->
              let tmp_ir3 = [BinOp(r1, MulOp, Reg rleft, Imm (ImmInt 4))] in
              let tmp_ir4 = [BinOp(r2, AddOp, Reg reg, Reg r1)] in
              (irs @ tmp_ir1 @ tmp_ir2 @ tmp_ir3 @ tmp_ir4 @ [Store(Reg rright, r2)], sym_tab)
            | CBoolArr n ->
              let tmp_ir3 = [BinOp(r1, MulOp, Reg rleft, Imm (ImmInt 1))] in
              let tmp_ir4 = [BinOp(r2, AddOp, Reg reg, Reg r1)] in
              (irs @ tmp_ir1 @ tmp_ir2 @ tmp_ir3 @ tmp_ir4 @ [Store(Reg rright, r2)], sym_tab)
            )
          )
          
        | ReturnValue exp ->
          let tmp_ir, result = trans_exp sym_tab arg_tab exp in
          (irs @ tmp_ir @ [Ret (Reg result)], sym_tab)
        
        | If (exp, stmt1, stmt2) ->
          let tmp_ir1, rbool = trans_exp sym_tab arg_tab exp in
          let tmp_ir2 = trans_function sym_tab arg_tab stmt1 in
          let tmp_ir3 = trans_function sym_tab arg_tab stmt2 in
          let l1 = create_label() in
          let l2 = create_label() in
          (irs @ tmp_ir1 @ [GotoIf (rbool, l1)] @ tmp_ir3 @ [Goto (l2)] @ [Label (l1)] @ tmp_ir2 @ [Label (l2)], sym_tab)

        | While (exp, stmt) ->
          let tmp_ir1, rbool = trans_exp sym_tab arg_tab exp in
          let tmp_ir2 = trans_function sym_tab arg_tab stmt in
          let l1 = create_label() in
          let l2 = create_label() in
          let l3 = create_label() in
          (irs @ [Label (l1)] @ tmp_ir1 @ [GotoIf (rbool, l2)] @ [Goto (l3)] @ [Label (l2)] @ tmp_ir2 @ [Goto (l1)] @ [Label (l3)] , sym_tab)
      )
      ([], sym_tab) stmts  
  in
  instrs

  
let run (p: program): ir_code =
  let (fname, ret_type, args, stmts) = p in
  let sym_tab = SymbolMap.empty in
  let arg_tab = ArgMap.empty in
  let arg_tab = extract_arg_tab arg_tab args in
  let arg_regs = extract_names args in
  (fname, arg_regs, trans_function sym_tab arg_tab stmts)
