open Program
open Ir
open Printf

(* Example code to illustrate how to define your own custom type and define a
 * Set to store them. *)

type cfg = ((instr * instr list), (instr * instr list) list) Hashtbl.t

let create_cfg () : cfg =
  Hashtbl.create 10

let add_edge g v1 v2 =
  let edges = try Hashtbl.find g v1 with Not_found -> [] in
  Hashtbl.replace g v1 (v2 :: edges)
  
(* Reaching definition (you can fix the following definition, of course). *)
type rdef = instr

(* Now you can define "set of reaching definition" as follow. *)
module RDSet = Set.Make(struct
  type t = instr
  let compare = Pervasives.compare
end)

module RDMap = Map.Make(struct
  type t = (instr * instr list)
  let compare = Pervasives.compare
end)

let rec make_block b instrs = 
  match instrs with
  | [] -> b, []
  | head_instr :: tail_instrs ->
    (match head_instr with
    | Goto _ | GotoIf _ | GotoIfNot _ | Ret _ ->
      let new_block = b @ [head_instr] in
      new_block, tail_instrs
    | Label _ -> 
      if b <> [] then b, instrs
      else 
        let new_block = b @ [head_instr] in
        make_block new_block tail_instrs
    | _ ->
      let new_block = b @ [head_instr] in
      make_block new_block tail_instrs
    )

let rec const_blocks (ir_list: instr list) = 
  match ir_list with
  | [] -> []
  | cur_block ->
    let (cur, next) = make_block [] cur_block in
    cur :: const_blocks next



let head_instr block = 
  match block with
  | x :: _ -> x

let rec last_instr block = 
  match block with
  | [last] -> last
  | head :: tail -> last_instr tail



let rec find_label basic_blocks label =
  match basic_blocks with
  | head :: tail -> 
    if List.mem (Label label) head then (Label label, head) else find_label tail label

let rec const_CFGsub basic_blocks block cur_block next_block cfg = 
  match cur_block with
  | [] -> cfg
  | [head] ->
    (match head with
    | GotoIf (r, label) | GotoIfNot (r, label) -> 
      let label_ir, label_block = find_label basic_blocks label in
      add_edge cfg (head, block) (label_ir, label_block);
      if next_block <> [] then add_edge cfg (head, block) ((head_instr next_block), next_block);
      cfg
    | Goto label ->
      let label_ir, label_block = find_label basic_blocks label in
      add_edge cfg (head, block) (label_ir, label_block);
      cfg
    | _ -> 
      if next_block <> [] then add_edge cfg (head, block) ((head_instr next_block), next_block);
      cfg
    )
  | head :: [next] ->
    (match head with
    | GotoIf (r, label) | GotoIfNot (r, label) -> 
      let label_ir, label_block = find_label basic_blocks label in
      add_edge cfg (head, block) (label_ir, label_block);
      add_edge cfg (head, block) (next, block);
      const_CFGsub basic_blocks block [next] next_block cfg
    | Goto label ->
      let label_ir, label_block = find_label basic_blocks label in
      add_edge cfg (head, block) (label_ir, label_block);
      const_CFGsub basic_blocks block [next] next_block cfg
    | Ret o -> 
      const_CFGsub basic_blocks block [next] next_block cfg
    | _ -> 
      add_edge cfg (head, block) (next, block);
      const_CFGsub basic_blocks block [next] next_block cfg
    )
  | head :: next :: tail ->
    (match head with
    | GotoIf (r, label) | GotoIfNot (r, label) -> 
      let label_ir, label_block = find_label basic_blocks label in
      add_edge cfg (head, block) (label_ir, label_block);
      add_edge cfg (head, block) (next, block);
      const_CFGsub basic_blocks block (next :: tail) next_block cfg
    | Goto label ->
      let label_ir, label_block = find_label basic_blocks label in
      add_edge cfg (head, block) (label_ir, label_block);
      const_CFGsub basic_blocks block (next :: tail) next_block cfg
    | Ret o -> 
      const_CFGsub basic_blocks block (next :: tail) next_block cfg
    | _ -> 
      add_edge cfg (head, block) (next, block);
      const_CFGsub basic_blocks block (next :: tail) next_block cfg
    )

let rec const_CFG basic_blocks cur_blocks cfg = 
  match cur_blocks with
  | [] -> cfg
  | [head] ->
    const_CFGsub basic_blocks head head [] cfg
  | head :: [next] ->
    const_CFG basic_blocks [next] (const_CFGsub basic_blocks head head next cfg)
  | head :: next :: tail ->
    const_CFG basic_blocks (next::tail) (const_CFGsub basic_blocks head head next cfg)

    
let find_r_in_rd_set inst r set =
  RDSet.fold (fun rdef ret_set -> 
    match rdef with
    | Set (r1, _) | Copy (_, r1) | BinOp (r1, _, _, _) | UnOp (r1, _, _) -> 
      if r1 = r then RDSet.add rdef ret_set else ret_set
    | _ -> 
      ret_set
  ) set RDSet.empty

let rec transfer cur_ir cur_rd =  (* 한 instr에서 RDSet을 계산한다 *)
  match cur_ir with
  | Set (r, _) | Copy (_, r) | BinOp (r, _, _, _) | UnOp (r, _, _) ->
    let contain_r = find_r_in_rd_set cur_ir r cur_rd in
    let new_cur_rd = RDSet.diff cur_rd contain_r in
    let new_cur_rd = RDSet.add cur_ir new_cur_rd in
    new_cur_rd
  | _ -> cur_rd
  

let get_pred_RDSet cfg block cur_instr rd_in rd_set = 
  Hashtbl.fold (fun key value acc ->
    if List.mem (cur_instr, block) value then
      try
        let pred_rd = RDMap.find key rd_set in
        RDSet.union acc pred_rd
      with Not_found ->
        acc
    else 
      acc
  ) cfg rd_in
  
let rdmap_equal map1 map2 =
  RDMap.equal (fun set1 set2 -> RDSet.equal set1 set2) map1 map2

let rec compute_RDSetSub cfg block cur_block rd_set = 
  match cur_block with
  | [] -> rd_set
  | head :: tail ->
    let rd_in = get_pred_RDSet cfg block head RDSet.empty rd_set in
    let new_rd_set = RDMap.add (head, block) (transfer head rd_in) rd_set in 
    compute_RDSetSub cfg block tail new_rd_set

let rec compute_RDSet cfg basic_blocks rd_set =
  let rec iterate previous_rd_set =
    let new_rd_set =
      List.fold_left (fun acc_rd_set block ->
        compute_RDSetSub cfg block block acc_rd_set
      ) previous_rd_set basic_blocks
    in
    if rdmap_equal new_rd_set previous_rd_set then
      new_rd_set
    else
      iterate new_rd_set
  in
  iterate rd_set

let rec initial_RDSub block cur_block rd_set = 
  match cur_block with
  | [] -> rd_set
  | head :: tail ->
    let new_rd_set = RDMap.add (head, block) RDSet.empty rd_set in
  initial_RDSub block tail new_rd_set

let rec initial_RDSet basic_blocks rd_set = 
  match basic_blocks with
  | [] -> rd_set
  | head :: tail ->
    initial_RDSet tail (initial_RDSub head head rd_set)

let rec find_RD block reg rd_set = 
  let flag, value = RDSet.fold (fun x (flag, value) -> 
    match x with
    | Set (r, i) ->
      if r = reg then (true, i) else (flag, value)
    | Copy (_, r) | BinOp (r, _, _, _) | UnOp (r, _, _) ->
      if r = reg then (false, value) else (flag, value)
    | _ -> (flag, value)
  ) rd_set (false, ImmInt 0) in
  let flag, value = RDSet.fold (fun x (flag, value) -> 
    match x with
    | Copy (_, r) | BinOp (r, _, _, _) | UnOp (r, _, _) -> if r = reg then (false, value) else (flag, value)
    | _ -> (flag, value)
  ) rd_set (flag, value) in
  flag, value


let rec optimize_block cfg block cur_block rd_set =
  match cur_block with
  | [] -> []
  | head :: tail -> 
    match head with
      | Copy (r, r2) ->
        let rd_block = get_pred_RDSet cfg block head RDSet.empty rd_set in (* head의 rd를 찾음 *)
        let flag, value = find_RD block r rd_block in
        if flag = true then [Set (r2, value)] @ optimize_block cfg block tail rd_set
        else head :: optimize_block cfg block tail rd_set

      | BinOp (r1, r2, r3, r4) ->
        (match r3 with
        | Reg ra ->
          let rd_block = get_pred_RDSet cfg block head RDSet.empty rd_set in
          let flag, value = find_RD block ra rd_block in
          if flag = true then [BinOp (r1, r2, Imm value, r4)] @ optimize_block cfg block tail rd_set
          else (match r4 with
          | Reg rb ->
            let rd_block = get_pred_RDSet cfg block head RDSet.empty rd_set in
            let flag, value = find_RD block rb rd_block in
            if flag = true then [BinOp (r1, r2, r3, Imm value)] @ optimize_block cfg block tail rd_set
            else head :: optimize_block cfg block tail rd_set
          | _ -> head :: optimize_block cfg block tail rd_set)
        | _ -> 
          match r4 with
          | Reg rb ->
            let rd_block = get_pred_RDSet cfg block head RDSet.empty rd_set in
            let flag, value = find_RD block rb rd_block in
            if flag = true then [BinOp (r1, r2, r3, Imm value)] @ optimize_block cfg block tail rd_set
            else head :: optimize_block cfg block tail rd_set
          | _ -> head :: optimize_block cfg block tail rd_set)

      | UnOp (r1, r2, Reg r) ->
        let rd_block = get_pred_RDSet cfg block head RDSet.empty rd_set in
        let flag, value = find_RD block r rd_block in
        if flag = true then [UnOp (r1, r2, Imm value)] @ optimize_block cfg block tail rd_set
        else head :: optimize_block cfg block tail rd_set

      | _ -> head :: optimize_block cfg block tail rd_set

let rec optimize_RD cfg basic_blocks rd_set = 
  match basic_blocks with
  | [] -> []
  | head :: tail ->
    optimize_block cfg head head rd_set @ optimize_RD cfg tail rd_set

let rec constant_folding ir_list =
  match ir_list with
  | [] -> []
  | head :: tail ->
    (match head with
    | BinOp (r, op, r1, r2) ->
      (match (op, r1, r2) with
      | (AddOp, Imm i1, Imm i2) -> 
        let i1_int = match i1 with Ir.ImmInt v1 -> v1 in
        let i2_int = match i2 with Ir.ImmInt v2 -> v2 in
        [Set (r, ImmInt (i1_int + i2_int))] @ constant_folding tail
      | (SubOp, Imm i1, Imm i2) -> 
        let i1_int = match i1 with Ir.ImmInt v1 -> v1 in
        let i2_int = match i2 with Ir.ImmInt v2 -> v2 in
        [Set (r, ImmInt (i1_int - i2_int))] @ constant_folding tail
      | (MulOp, Imm i1, Imm i2) -> 
        let i1_int = match i1 with Ir.ImmInt v1 -> v1 in
        let i2_int = match i2 with Ir.ImmInt v2 -> v2 in
        [Set (r, ImmInt (i1_int * i2_int))] @ constant_folding tail
      | (DivOp, Imm i1, Imm i2) -> 
        let i1_int = match i1 with Ir.ImmInt v1 -> v1 in
        let i2_int = match i2 with Ir.ImmInt v2 -> v2 in
        [Set (r, ImmInt (i1_int / i2_int))] @ constant_folding tail

      | (GtOp, Imm i1, Imm i2) -> 
        let i1_int = match i1 with Ir.ImmInt v1 -> v1 in
        let i2_int = match i2 with Ir.ImmInt v2 -> v2 in
        [Set (r, ImmBool (i1_int > i2_int))] @ constant_folding tail
      | (GeqOp, Imm i1, Imm i2) -> 
        let i1_int = match i1 with Ir.ImmInt v1 -> v1 in
        let i2_int = match i2 with Ir.ImmInt v2 -> v2 in
        [Set (r, ImmBool (i1_int >= i2_int))] @ constant_folding tail
      | (LtOp, Imm i1, Imm i2) -> 
        let i1_int = match i1 with Ir.ImmInt v1 -> v1 in
        let i2_int = match i2 with Ir.ImmInt v2 -> v2 in
        [Set (r, ImmBool (i1_int < i2_int))] @ constant_folding tail
      | (LeqOp, Imm i1, Imm i2) -> 
        let i1_int = match i1 with Ir.ImmInt v1 -> v1 in
        let i2_int = match i2 with Ir.ImmInt v2 -> v2 in
        [Set (r, ImmBool (i1_int <= i2_int))] @ constant_folding tail

      | (EqOp, Imm i1, Imm i2) -> 
        [Set (r, ImmBool (i1 = i2))] @ constant_folding tail
      | (NeqOp, Imm i1, Imm i2) -> 
        [Set (r, ImmBool (i1 <> i2))] @ constant_folding tail
      | _ -> head :: constant_folding tail)
    | _ -> head :: constant_folding tail)


let get_pred_AESet cfg block cur_instr rd_in rd_set = 
  let count = ref 0 in
  let ret = Hashtbl.fold (fun key value acc ->
    if List.mem (cur_instr, block) value then (
      count := !count + 1;
      try
        let pred_rd = RDMap.find key rd_set in
        RDSet.inter acc pred_rd
      with Not_found ->
        acc
    ) else 
      acc
  ) cfg rd_in
  in
  if !count = 0 then RDSet.empty else ret


let string_contains instr_to_str inst_str =
  let len_instr_to_str = String.length instr_to_str in
  let len_inst_str = String.length inst_str in
  let rec aux i =
    if i > len_instr_to_str - len_inst_str then false
    else if String.sub instr_to_str i len_inst_str = inst_str then true
    else aux (i + 1)
  in
  aux 0


let find_r_in_ae_set inst r1 set =
  RDSet.fold (fun rdef ret_set -> 
    if string_contains (instr_to_str rdef) r1 = true then RDSet.add rdef ret_set else ret_set
  ) set RDSet.empty



let rec transfer_AE cur_ir cur_rd =  (* 한 instr에서 RDSet을 계산한다 *)
  match cur_ir with
  | Set (r, _) ->
    let contain_r = find_r_in_ae_set cur_ir r cur_rd in
    let new_cur_rd = RDSet.diff cur_rd contain_r in
    let new_cur_rd = RDSet.add cur_ir new_cur_rd in 
    new_cur_rd
    
  | Copy (r1, r) | Load (r1, r) ->
    let contain_r = find_r_in_ae_set cur_ir r cur_rd in
    let new_cur_rd = RDSet.diff cur_rd contain_r in
    if r = r1 then new_cur_rd 
    else let new_cur_rd = RDSet.add cur_ir new_cur_rd in new_cur_rd

  | BinOp (r, _, r2, r3) ->
    let contain_r = find_r_in_ae_set cur_ir r cur_rd in
    let new_cur_rd = RDSet.diff cur_rd contain_r in
    (match (r2, r3) with
    | (Reg ra, Reg rb) -> 
      if r = ra || r = rb then new_cur_rd 
      else let new_cur_rd = RDSet.add cur_ir new_cur_rd in new_cur_rd
    | (Reg ra, _) ->
      if r = ra then new_cur_rd 
      else let new_cur_rd = RDSet.add cur_ir new_cur_rd in new_cur_rd
    | (_, Reg rb) ->
      if r = rb then new_cur_rd 
      else let new_cur_rd = RDSet.add cur_ir new_cur_rd in new_cur_rd
    | (_, _) -> let new_cur_rd = RDSet.add cur_ir new_cur_rd in new_cur_rd)

  | UnOp (r, _, r1) ->
    let contain_r = find_r_in_ae_set cur_ir r cur_rd in
    let new_cur_rd = RDSet.diff cur_rd contain_r in
    (match r1 with
    | Reg ra ->  
      if r = ra then new_cur_rd 
      else let new_cur_rd = RDSet.add cur_ir new_cur_rd in new_cur_rd
    | _ -> let new_cur_rd = RDSet.add cur_ir new_cur_rd in new_cur_rd)

  | Store (Reg r, r1)  ->
    let contain_r = find_r_in_ae_set cur_ir r cur_rd in
    let new_cur_rd = RDSet.diff cur_rd contain_r in
    if r = r1 then new_cur_rd 
    else let new_cur_rd = RDSet.add cur_ir new_cur_rd in new_cur_rd

  | _ -> cur_rd


  
let print_rdset rdset =
  RDSet.iter (fun instr ->
    print_string (instr_to_str instr); 
    print_newline ()
  ) rdset

let print_rdmap rdmap =
  RDMap.iter (fun key rdset ->
    let key_instr, _ = key in
    printf "RDSet for instr: %s \n" (instr_to_str key_instr);
    print_string "Reaching Definitions:\n";
    print_rdset rdset; 
    print_newline ()
  ) rdmap

let rec compute_AESetSub cfg block cur_block rd_all rd_set = 
  match cur_block with
  | [] -> rd_set
  | head :: tail ->
    let rd_in = get_pred_AESet cfg block head rd_all rd_set in
    let new_rd_set = RDMap.add (head, block) (transfer_AE head rd_in) rd_set in 
    compute_AESetSub cfg block tail rd_all new_rd_set

let rec compute_AESet cfg basic_blocks rd_all rd_set =
  let rec iterate previous_rd_set =
    let new_rd_set =
      List.fold_left (fun acc_rd_set block ->
        compute_AESetSub cfg block block rd_all acc_rd_set
      ) previous_rd_set basic_blocks
    in
    if rdmap_equal new_rd_set previous_rd_set then
      new_rd_set
    else
      iterate new_rd_set
  in
  iterate rd_set



let rec find_AE block ir_inst hh rd_set = 
  let (r1, r2, r3, r4) = ir_inst in
  let left_str = oprnd_to_str r3 in
  let binop_str = binop_to_str r2 in
  let right_str = oprnd_to_str r4 in
  let inst_str = sprintf "%s %s %s" left_str binop_str right_str in
  let flag, value = RDSet.fold (fun x (flag, value) -> 
    if (string_contains (instr_to_str x) r1 = false) && (string_contains (instr_to_str x) inst_str) = true then (true, x)
    else if (string_contains (instr_to_str x) r1 = true) && (string_contains (instr_to_str x) inst_str) = true then (false, value)
    else (flag, value)
  ) rd_set (false, hh) in
  flag, value

let rec optimize_block_ae cfg block cur_block rd_set =
  match cur_block with
  | [] -> []
  | head :: tail -> 
    match head with
    | BinOp (r1, r2, r3, r4) -> 
      let rd_block = get_pred_RDSet cfg block head RDSet.empty rd_set in
      let flag, value = find_AE block (r1, r2, r3, r4) head rd_block in
      if flag = true then 
        match value with
        | BinOp (rr, _, _, _) ->
          [Copy (rr, r1)] @ optimize_block_ae cfg block tail rd_set
        | _ -> head :: optimize_block_ae cfg block tail rd_set
      else head :: optimize_block_ae cfg block tail rd_set
    | _ -> head :: optimize_block_ae cfg block tail rd_set

let rec optimize_AE cfg basic_blocks rd_set = 
  match basic_blocks with
  | [] -> []
  | head :: tail ->
    optimize_block_ae cfg head head rd_set @ optimize_AE cfg tail rd_set
  
let rec all_ae_set ae_set ir_list = 
  match ir_list with
  | [] -> ae_set
  | head :: tail ->
    all_ae_set (RDSet.add head ae_set) tail

let rec run (ir: ir_code): ir_code =
  let fname, arg_regs, ir_list = ir in
  let basic_blocks = const_blocks ir_list in
  let cfg = const_CFG basic_blocks basic_blocks (create_cfg ()) in
  let rd_set = initial_RDSet basic_blocks RDMap.empty in
  let rd_set = compute_RDSet cfg basic_blocks rd_set in
  let ir_RD = optimize_RD cfg basic_blocks rd_set in
  let ir_cf = constant_folding ir_RD in
  if ir_cf = ir_list then
    let basic_blocks = const_blocks ir_cf in
    let cfg = const_CFG basic_blocks basic_blocks (create_cfg ()) in
    let ae_set = initial_RDSet basic_blocks RDMap.empty in
    let ae_all = all_ae_set RDSet.empty ir_cf in
    let ae_set = compute_AESet cfg basic_blocks ae_all ae_set in
    let ir_ae = optimize_AE cfg basic_blocks ae_set in
    let ir_cf = constant_folding ir_ae in
    (* print_rdmap ae_set;  *)
    (fname, arg_regs, ir_cf)
  else
    run (fname, arg_regs, ir_cf)
  
  (* List.iter print_block basic_blocks; *)
  (*print_cfg cfg;*)
  (* print_rdmap ae_set;  *)
  