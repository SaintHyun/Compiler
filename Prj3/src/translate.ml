open Program
open Ir
open Helper

(* The module for symbol table. Carefully think about what should be stored in
 * the symbol table for this IR translation phase. *)
module SymbolMap = Map.Make(String)
module ArgMap = Map.Make(String)


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
    ([Set (r, ImmBool b)], r)

  | ConstInt i -> 
    let r = create_register_name() in
    ([Set (r, ImmInt i)], r)

  | Var vname ->
    if SymbolMap.mem vname sym_tab = true then
      let r = create_register_name() in
      let (reg, typ) = SymbolMap.find vname sym_tab in
      ([Load (r, reg)], r)
    else ([], vname)

  | Arr (vname, exp) ->
    let (reg, typ) = SymbolMap.find vname sym_tab in
    (match typ with
    | CIntArr n ->
      let r1 = create_register_name() in
      let tmp1, r2 = trans_exp sym_tab arg_tab exp in
      let r3 = create_register_name() in
      let r4 = create_register_name() in
      let tmp2 = [BinOp(r1, MulOp, Reg r2, Imm (ImmInt 4))] in
      let tmp_inst = [BinOp(r3, AddOp, Reg reg, Reg r1)] in
      (tmp1 @ tmp2 @ tmp_inst @ [Load(r4, r3)], r4)
    | CBoolArr n ->
      let tmp1, r2 = trans_exp sym_tab arg_tab exp in
      let r3 = create_register_name() in
      let r4 = create_register_name() in
      let tmp_inst = [BinOp(r3, AddOp, Reg reg, Reg r2)] in
      (tmp1 @ tmp_inst @ [Load(r4, r3)], r4)
    | _ -> ([], "")
    )
      
  | Add (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, AddOp, Imm (ImmInt r1), Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3, AddOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, r3)
      )
    | _ -> 
      let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, AddOp, Reg r1, Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst1 @ inst2 @ [BinOp (r3, AddOp, Reg r1, Reg r2)] in
        (tmp_inst, r3)
      )
    )

  | Sub (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, SubOp, Imm (ImmInt r1), Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3, SubOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, r3)
      )
    | _ -> 
      let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, SubOp, Reg r1, Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst1 @ inst2 @ [BinOp (r3, SubOp, Reg r1, Reg r2)] in
        (tmp_inst, r3)
      )
    )

  | Mul (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, MulOp, Imm (ImmInt r1), Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3, MulOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, r3)
      )
    | _ -> 
      let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, MulOp, Reg r1, Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst1 @ inst2 @ [BinOp (r3, MulOp, Reg r1, Reg r2)] in
        (tmp_inst, r3)
      )
    )

  | Div (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, DivOp, Imm (ImmInt r1), Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3, DivOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, r3)
      )
    | _ -> 
      let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, DivOp, Reg r1, Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst1 @ inst2 @ [BinOp (r3, DivOp, Reg r1, Reg r2)] in
        (tmp_inst, r3)
      )
    )

  | Neg (exp) ->
    (match exp with
    | ConstInt i ->
      let r1 = i in
      let r2 = create_register_name() in
      ([UnOp (r2, NegOp, Imm (ImmInt r1))], r2)
    | _ ->
      let inst, r1 = trans_exp sym_tab arg_tab exp in
      let r2 = create_register_name() in
      let tmp_inst = inst @ [UnOp (r2, NegOp, Reg r1)] in
      (tmp_inst, r2)
    )
  
  | Equal (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, EqOp, Imm (ImmInt r1), Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3, EqOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, r3)
      )

    | ConstBool i ->
      let r1 = i in
      (match exp2 with
      | ConstBool i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, EqOp, Imm (ImmBool r1), Imm (ImmBool r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3, EqOp, Imm (ImmBool r1), Reg r2)] in
        (tmp_inst, r3)
      )

    | _ -> 
      let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, EqOp, Reg r1, Imm (ImmInt r2))], r3)
      | ConstBool i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, EqOp, Reg r1, Imm (ImmBool r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst1 @ inst2 @ [BinOp (r3, EqOp, Reg r1, Reg r2)] in
        (tmp_inst, r3)
      )
    )

  | NotEq (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, NeqOp, Imm (ImmInt r1), Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3, NeqOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, r3)
      )

    | ConstBool i ->
      let r1 = i in
      (match exp2 with
      | ConstBool i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, NeqOp, Imm (ImmBool r1), Imm (ImmBool r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3, NeqOp, Imm (ImmBool r1), Reg r2)] in
        (tmp_inst, r3)
      )

    | _ -> 
      let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, NeqOp, Reg r1, Imm (ImmInt r2))], r3)
      | ConstBool i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, NeqOp, Reg r1, Imm (ImmBool r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst1 @ inst2 @ [BinOp (r3, NeqOp, Reg r1, Reg r2)] in
        (tmp_inst, r3)
      )
    )

  | LessEq (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, LeqOp, Imm (ImmInt r1), Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3,LeqOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, r3)
      )
    | _ -> 
      let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, LeqOp, Reg r1, Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst1 @ inst2 @ [BinOp (r3, LeqOp, Reg r1, Reg r2)] in
        (tmp_inst, r3)
      )
    )

  | LessThan (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, LtOp, Imm (ImmInt r1), Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3, LtOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, r3)
      )
    | _ -> 
      let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, LtOp, Reg r1, Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst1 @ inst2 @ [BinOp (r3, LtOp, Reg r1, Reg r2)] in
        (tmp_inst, r3)
      )
    )

  | GreaterEq (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, GeqOp, Imm (ImmInt r1), Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3, GeqOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, r3)
      )
    | _ -> 
      let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, GeqOp, Reg r1, Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst1 @ inst2 @ [BinOp (r3, GeqOp, Reg r1, Reg r2)] in
        (tmp_inst, r3)
      )
    )

  | GreaterThan (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        ([BinOp (r3, GtOp, Imm (ImmInt r1), Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst2 @ [BinOp (r3, GtOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, r3)
      )
    | _ -> 
      let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        let r3 = create_register_name() in
        (inst1 @ [BinOp (r3, GtOp, Reg r1, Imm (ImmInt r2))], r3)
      | _ ->
        let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
        let r3 = create_register_name() in
        let tmp_inst = inst1 @ inst2 @ [BinOp (r3, GtOp, Reg r1, Reg r2)] in
        (tmp_inst, r3)
      )
    )

  | And (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let l1 = create_label() in
    let l2 = create_label() in
    (inst1 @ [GotoIfNot (r1, l1)] @ inst2 @ [Goto (l2)] @ [Label (l1)] @ [Set (r2, ImmBool false)] @ [Label (l2)], r2)

  | Or (exp1, exp2) ->
    let inst1, r1 = trans_exp sym_tab arg_tab exp1 in
    let inst2, r2 = trans_exp sym_tab arg_tab exp2 in
    let l1 = create_label() in
    let l2 = create_label() in
    (inst1 @ [GotoIf (r1, l1)] @ inst2 @ [Goto (l2)] @ [Label (l1)] @ [Set (r2, ImmBool true)] @ [Label (l2)], r2)

  | Not (exp) ->
    (match exp with
    | ConstBool b ->
      let r1 = b in
      let r2 = create_register_name() in
      ([UnOp (r2, NotOp, Imm (ImmBool r1))], r2)
    | _ ->
      let inst, r1 = trans_exp sym_tab arg_tab exp in
      let r2 = create_register_name() in
      let tmp_inst = inst @ [UnOp (r2, NotOp, Reg r1)] in
      (tmp_inst, r2)
    )
  
let rec trans_var sym_tab arg_tab e var = 
  match e with
  | ConstBool b -> 
    ([Set (var, ImmBool b)], var)

  | ConstInt i -> 
    ([Set (var, ImmInt i)], var)

  | Var vname ->
    if SymbolMap.mem vname sym_tab = true then
      let r = create_register_name() in
      let (reg, typ) = SymbolMap.find vname sym_tab in
      ([Load (r, reg)], r)
    else ([], vname)

  | Arr (vname, exp) ->
    let (reg, typ) = SymbolMap.find vname sym_tab in
    (match typ with
    | CIntArr n ->
      let r1 = create_register_name() in
      let tmp1, r2 = trans_var sym_tab arg_tab exp var in
      let r3 = create_register_name() in
      let r4 = create_register_name() in
      let tmp2 = [BinOp(r1, MulOp, Reg r2, Imm (ImmInt 4))] in
      let tmp_inst = [BinOp(r3, AddOp, Reg reg, Reg r1)] in
      (tmp1 @ tmp2 @ tmp_inst @ [Load(r4, r3)], r4)
    | CBoolArr n ->
      let tmp1, r2 = trans_var sym_tab arg_tab exp var in
      let r3 = create_register_name() in
      let r4 = create_register_name() in
      let tmp_inst = [BinOp(r3, AddOp, Reg reg, Reg r2)] in
      (tmp1 @ tmp_inst @ [Load(r4, r3)], r4)
    | _ -> ([], "")
    )
      
  | Add (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        ([BinOp (var, AddOp, Imm (ImmInt r1), Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var, AddOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, var)
      )
    | _ -> 
      let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, AddOp, Reg r1, Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst1 @ inst2 @ [BinOp (var, AddOp, Reg r1, Reg r2)] in
        (tmp_inst, var)
      )
    )

  | Sub (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        ([BinOp (var, SubOp, Imm (ImmInt r1), Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var, SubOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, var)
      )
    | _ -> 
      let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, SubOp, Reg r1, Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst1 @ inst2 @ [BinOp (var, SubOp, Reg r1, Reg r2)] in
        (tmp_inst, var)
      )
    )

  | Mul (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        ([BinOp (var, MulOp, Imm (ImmInt r1), Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var, MulOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, var)
      )
    | _ -> 
      let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, MulOp, Reg r1, Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst1 @ inst2 @ [BinOp (var, MulOp, Reg r1, Reg r2)] in
        (tmp_inst, var)
      )
    )

  | Div (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        ([BinOp (var, DivOp, Imm (ImmInt r1), Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var, DivOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, var)
      )
    | _ -> 
      let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, DivOp, Reg r1, Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst1 @ inst2 @ [BinOp (var, DivOp, Reg r1, Reg r2)] in
        (tmp_inst, var)
      )
    )

  | Neg (exp) ->
    (match exp with
    | ConstInt i ->
      let r1 = i in
      ([UnOp (var, NegOp, Imm (ImmInt r1))], var)
    | _ ->
      let inst, r1 = trans_var sym_tab arg_tab exp var in
      let tmp_inst = inst @ [UnOp (var, NegOp, Reg r1)] in
      (tmp_inst, var)
    )
  
  | Equal (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        ([BinOp (var, EqOp, Imm (ImmInt r1), Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var, EqOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, var)
      )

    | ConstBool i ->
      let r1 = i in
      (match exp2 with
      | ConstBool i2 -> 
        let r2 = i2 in
        ([BinOp (var, EqOp, Imm (ImmBool r1), Imm (ImmBool r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var, EqOp, Imm (ImmBool r1), Reg r2)] in
        (tmp_inst, var)
      )

    | _ -> 
      let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, EqOp, Reg r1, Imm (ImmInt r2))], var)
      | ConstBool i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, EqOp, Reg r1, Imm (ImmBool r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst1 @ inst2 @ [BinOp (var, EqOp, Reg r1, Reg r2)] in
        (tmp_inst, var)
      )
    )

  | NotEq (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        ([BinOp (var, NeqOp, Imm (ImmInt r1), Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var, NeqOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, var)
      )

    | ConstBool i ->
      let r1 = i in
      (match exp2 with
      | ConstBool i2 -> 
        let r2 = i2 in
        ([BinOp (var, NeqOp, Imm (ImmBool r1), Imm (ImmBool r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var, NeqOp, Imm (ImmBool r1), Reg r2)] in
        (tmp_inst, var)
      )

    | _ -> 
      let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, NeqOp, Reg r1, Imm (ImmInt r2))], var)
      | ConstBool i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, NeqOp, Reg r1, Imm (ImmBool r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst1 @ inst2 @ [BinOp (var, NeqOp, Reg r1, Reg r2)] in
        (tmp_inst, var)
      )
    )

  | LessEq (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        ([BinOp (var, LeqOp, Imm (ImmInt r1), Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var,LeqOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, var)
      )
    | _ -> 
      let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, LeqOp, Reg r1, Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst1 @ inst2 @ [BinOp (var, LeqOp, Reg r1, Reg r2)] in
        (tmp_inst, var)
      )
    )

  | LessThan (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        ([BinOp (var, LtOp, Imm (ImmInt r1), Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var, LtOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, var)
      )
    | _ -> 
      let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, LtOp, Reg r1, Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst1 @ inst2 @ [BinOp (var, LtOp, Reg r1, Reg r2)] in
        (tmp_inst, var)
      )
    )

  | GreaterEq (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        ([BinOp (var, GeqOp, Imm (ImmInt r1), Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var, GeqOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, var)
      )
    | _ -> 
      let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, GeqOp, Reg r1, Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst1 @ inst2 @ [BinOp (var, GeqOp, Reg r1, Reg r2)] in
        (tmp_inst, var)
      )
    )

  | GreaterThan (exp1, exp2) ->
    (match exp1 with
    | ConstInt i -> 
      let r1 = i in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        ([BinOp (var, GtOp, Imm (ImmInt r1), Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst2 @ [BinOp (var, GtOp, Imm (ImmInt r1), Reg r2)] in
        (tmp_inst, var)
      )
    | _ -> 
      let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
      (match exp2 with
      | ConstInt i2 -> 
        let r2 = i2 in
        (inst1 @ [BinOp (var, GtOp, Reg r1, Imm (ImmInt r2))], var)
      | _ ->
        let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
        let tmp_inst = inst1 @ inst2 @ [BinOp (var, GtOp, Reg r1, Reg r2)] in
        (tmp_inst, var)
      )
    )

  | And (exp1, exp2) ->
    let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
    let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
    let l1 = create_label() in
    let l2 = create_label() in
    (inst1 @ [GotoIfNot (r1, l1)] @ inst2 @ [Goto (l2)] @ [Label (l1)] @ [Set (r2, ImmBool false)] @ [Label (l2)], r2)

  | Or (exp1, exp2) ->
    let inst1, r1 = trans_var sym_tab arg_tab exp1 var in
    let inst2, r2 = trans_var sym_tab arg_tab exp2 var in
    let l1 = create_label() in
    let l2 = create_label() in
    (inst1 @ [GotoIf (r1, l1)] @ inst2 @ [Goto (l2)] @ [Label (l1)] @ [Set (r2, ImmBool true)] @ [Label (l2)], r2)

  | Not (exp) ->
    (match exp with
    | ConstBool b ->
      let r1 = b in
      ([UnOp (var, NotOp, Imm (ImmBool r1))], var)
    | _ ->
      let inst, r1 = trans_var sym_tab arg_tab exp var in
      let tmp_inst = inst @ [UnOp (var, NotOp, Reg r1)] in
      (tmp_inst, var)
    )

let rec trans_function sym_tab arg_tab stmts =
  let instrs, sym_tab, arg_tab=
    List.fold_left(fun (irs, sym_tab, arg_tab) stmt ->
        match stmt with
        | LocalDecl (ctyp, vname) ->
          (match ctyp with
            | CInt | CBool ->
              let arg_tab = ArgMap.add vname ctyp arg_tab in
              (irs, sym_tab, arg_tab)
            | CIntArr n | CBoolArr n ->
              let reg = create_register_name () in
              let size = sizeof ctyp in
              let inst = LocalAlloc (reg, size) in
              let temp_inst = [inst] in
              let sym_tab = SymbolMap.add vname (reg, ctyp) sym_tab in
              (irs @ temp_inst, sym_tab, arg_tab)
          )

        | Assign (lvar, exp) ->
          (match lvar with
          | LVar str -> 
            if SymbolMap.mem str sym_tab = true then
              let (reg, typ) = SymbolMap.find str sym_tab in
              let tmp_ir, result = trans_exp sym_tab arg_tab exp in
              (irs @ tmp_ir @ [Store (Reg result, reg)], sym_tab, arg_tab)
            else
              (match exp with
              | Var vname ->
                (irs @ [Copy (vname, str)], sym_tab, arg_tab)
              | _ ->
                let tmp_ir, result = trans_var sym_tab arg_tab exp str in
                if result = str then (irs @ tmp_ir, sym_tab, arg_tab)
                else (irs @ tmp_ir @ [Copy (result, str)], sym_tab, arg_tab)
              )

          | LArr (str, exp2) ->
            let tmp_ir1, rright = trans_exp sym_tab arg_tab exp in
            let tmp_ir2, rleft = trans_exp sym_tab arg_tab exp2 in
            let (reg, typ) = SymbolMap.find str sym_tab in
            (match typ with
            | CIntArr n ->
              let r1 = create_register_name() in
              let r2 = create_register_name() in
              let tmp_ir3 = [BinOp(r1, MulOp, Reg rleft, Imm (ImmInt 4))] in
              let tmp_ir4 = [BinOp(r2, AddOp, Reg reg, Reg r1)] in
              (irs @ tmp_ir1 @ tmp_ir2 @ tmp_ir3 @ tmp_ir4 @ [Store(Reg rright, r2)], sym_tab, arg_tab)
            | CBoolArr n ->
              let r2 = create_register_name() in
              let tmp_ir3 = [BinOp(r2, AddOp, Reg reg, Reg rleft)] in
              (irs @ tmp_ir1 @ tmp_ir2 @ tmp_ir3 @ [Store(Reg rright, r2)], sym_tab, arg_tab)
            | _ -> (irs, sym_tab, arg_tab)
            )
          )
          
        | ReturnValue exp ->
          let tmp_ir, result = trans_exp sym_tab arg_tab exp in
          (irs @ tmp_ir @ [Ret (Reg result)], sym_tab, arg_tab)
        
        | If (exp, stmt1, stmt2) ->
          let tmp_ir1, rbool = trans_exp sym_tab arg_tab exp in
          let tmp_ir2 = trans_function sym_tab arg_tab stmt1 in
          let tmp_ir3 = trans_function sym_tab arg_tab stmt2 in
          let l1 = create_label() in
          let l2 = create_label() in
          (irs @ tmp_ir1 @ [GotoIf (rbool, l1)] @ tmp_ir3 @ [Goto (l2)] @ [Label (l1)] @ tmp_ir2 @ [Label (l2)], sym_tab, arg_tab)

        | While (exp, stmt) ->
          let tmp_ir1, rbool = trans_exp sym_tab arg_tab exp in
          let tmp_ir2 = trans_function sym_tab arg_tab stmt in
          let l1 = create_label() in
          let l2 = create_label() in
          (irs @ [Label (l1)] @ tmp_ir1 @ [GotoIfNot (rbool, l2)]  @ tmp_ir2 @ [Goto (l1)] @ [Label (l2)] , sym_tab, arg_tab)
      )
      ([], sym_tab, arg_tab) stmts  
  in
  instrs

  
let run (p: program): ir_code =
  let (fname, ret_type, args, stmts) = p in
  let sym_tab = SymbolMap.empty in
  let arg_tab = ArgMap.empty in
  let arg_tab = extract_arg_tab arg_tab args in
  let arg_regs = extract_names args in
  (fname, arg_regs, trans_function sym_tab arg_tab stmts)
