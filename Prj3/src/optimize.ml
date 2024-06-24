open Program
open Ir
open Printf

exception Error

type cfg = ((instr * instr list), (instr * instr list) list) Hashtbl.t

let create_cfg () : cfg =
  Hashtbl.create 10

let add_edge g v1 v2 =
  let edges = try Hashtbl.find g v1 with Not_found -> [] in
  Hashtbl.replace g v1 (v2 :: edges)
  

module RDSet = Set.Make(struct
  type t = instr
  let compare = Pervasives.compare
end)

module RDMap = Map.Make(struct
  type t = (instr * instr list)
  let compare = Pervasives.compare
end)

module AESet = Set.Make(struct
  type t = instr
  let compare = Pervasives.compare
end)

module AEMap = Map.Make(struct
  type t = (instr * instr list)
  let compare = Pervasives.compare
end)

module LVSet = Set.Make(struct
  type t = register
  let compare = Pervasives.compare
end)

module LVMap = Map.Make(struct
  type t = (instr * instr list)
  let compare = Pervasives.compare
end)

let rdmap_equal map1 map2 =
  RDMap.equal (fun set1 set2 -> RDSet.equal set1 set2) map1 map2

let aemap_equal map1 map2 =
  AEMap.equal (fun set1 set2 -> AESet.equal set1 set2) map1 map2

let lvmap_equal map1 map2 =
  LVMap.equal (fun set1 set2 -> LVSet.equal set1 set2) map1 map2

let rec construct_basic_blocks ir_instructions = 
  let rec create_block current_block instructions = 
    match instructions with
    | [] -> current_block, []
    | instruction :: remaining_instructions ->
      (match instruction with
      | Goto _ | GotoIf _ | GotoIfNot _ | Ret _ ->
        let new_block = current_block @ [instruction] in
        new_block, remaining_instructions
      | Label _ -> 
        if current_block <> [] then current_block, instructions
        else 
          let new_block = current_block @ [instruction] in
          create_block new_block remaining_instructions
      | _ ->
        let new_block = current_block @ [instruction] in
        create_block new_block remaining_instructions
      )
  in
  match ir_instructions with
  | [] -> []
  | remaining_instructions ->
    let (current, next) = create_block [] remaining_instructions in
    current :: construct_basic_blocks next

let first_instruction_of_block block = 
  match block with
  | [] -> raise Error
  | instruction :: _ -> instruction

let rec find_label_in_blocks blocks target_label =
  match blocks with
  | [] -> raise Error
  | current_block :: remaining_blocks -> 
    if List.mem (Label target_label) current_block then (Label target_label, current_block) 
    else find_label_in_blocks remaining_blocks target_label

let rec construct_cfg_sub basic_blocks current_block current_instrs next_block cfg = 
  match current_instrs with
  | [] -> cfg
  | [instr] ->
    (match instr with
    | GotoIf (cond, label) | GotoIfNot (cond, label) -> 
      let label_instr, target_block = find_label_in_blocks basic_blocks label in
      add_edge cfg (instr, current_block) (label_instr, target_block);
      if next_block <> [] then add_edge cfg (instr, current_block) ((first_instruction_of_block next_block), next_block);
      cfg
    | Goto label ->
      let label_instr, target_block = find_label_in_blocks basic_blocks label in
      add_edge cfg (instr, current_block) (label_instr, target_block);
      cfg
    | _ -> 
      if next_block <> [] then add_edge cfg (instr, current_block) ((first_instruction_of_block next_block), next_block);
      cfg
    )
  | instr :: [next_instr] ->
    (match instr with
    | GotoIf (cond, label) | GotoIfNot (cond, label) -> 
      let label_instr, target_block = find_label_in_blocks basic_blocks label in
      add_edge cfg (instr, current_block) (label_instr, target_block);
      add_edge cfg (instr, current_block) (next_instr, current_block);
      construct_cfg_sub basic_blocks current_block [next_instr] next_block cfg
    | Goto label ->
      let label_instr, target_block = find_label_in_blocks basic_blocks label in
      add_edge cfg (instr, current_block) (label_instr, target_block);
      construct_cfg_sub basic_blocks current_block [next_instr] next_block cfg
    | Ret _ -> 
      construct_cfg_sub basic_blocks current_block [next_instr] next_block cfg
    | _ -> 
      add_edge cfg (instr, current_block) (next_instr, current_block);
      construct_cfg_sub basic_blocks current_block [next_instr] next_block cfg
    )
  | instr :: next_instr :: rest_instrs ->
    (match instr with
    | GotoIf (cond, label) | GotoIfNot (cond, label) -> 
      let label_instr, target_block = find_label_in_blocks basic_blocks label in
      add_edge cfg (instr, current_block) (label_instr, target_block);
      add_edge cfg (instr, current_block) (next_instr, current_block);
      construct_cfg_sub basic_blocks current_block (next_instr :: rest_instrs) next_block cfg
    | Goto label ->
      let label_instr, target_block = find_label_in_blocks basic_blocks label in
      add_edge cfg (instr, current_block) (label_instr, target_block);
      construct_cfg_sub basic_blocks current_block (next_instr :: rest_instrs) next_block cfg
    | Ret _ -> 
      construct_cfg_sub basic_blocks current_block (next_instr :: rest_instrs) next_block cfg
    | _ -> 
      add_edge cfg (instr, current_block) (next_instr, current_block);
      construct_cfg_sub basic_blocks current_block (next_instr :: rest_instrs) next_block cfg
    )

let rec construct_cfg basic_blocks current_blocks cfg = 
  match current_blocks with
  | [] -> cfg
  | [current_block] ->
    construct_cfg_sub basic_blocks current_block current_block [] cfg
  | current_block :: [next_block] ->
    construct_cfg basic_blocks [next_block] (construct_cfg_sub basic_blocks current_block current_block next_block cfg)
  | current_block :: next_block :: rest_blocks ->
    construct_cfg basic_blocks (next_block :: rest_blocks) (construct_cfg_sub basic_blocks current_block current_block next_block cfg)

(* 'initialize_rd_set_for_block' 함수는 블록 내의 각 명령어에 대해 RDSet을 초기화한다 *)
let rec initialize_rd_set_for_block block instructions rd_set = 
  match instructions with
  | [] -> rd_set
  | instr :: remaining_instrs ->
    let new_rd_set = RDMap.add (instr, block) RDSet.empty rd_set in
    initialize_rd_set_for_block block remaining_instrs new_rd_set

(* 'initialize_rd_set' 함수는 모든 기본 블록에 대해 RDSet을 초기화한다 *)
let rec initialize_rd_set basic_blocks rd_set = 
  match basic_blocks with
  | [] -> rd_set
  | block :: remaining_blocks ->
    let rd_set = initialize_rd_set_for_block block block rd_set in
    initialize_rd_set remaining_blocks rd_set

(* 'find_reg_in_rd_set' 함수는 RDSet에서 특정 레지스터와 일치하는 정의를 찾는다 *)
let find_reg_in_rd_set instruction reg set =
  RDSet.fold (fun rdef result_set -> 
    match rdef with
    | Set (r1, _) | Copy (_, r1) | BinOp (r1, _, _, _) | UnOp (r1, _, _) -> 
      if r1 = reg then RDSet.add rdef result_set else result_set
    | _ -> 
      result_set
  ) set RDSet.empty

(* 'update_rd_set' 함수는 현재 명령어에서 RDSet을 갱신한다 *)
let rec update_rd_set current_instr current_rd_set =  
  match current_instr with
  | Set (reg, _) | Copy (_, reg) | BinOp (reg, _, _, _) | UnOp (reg, _, _) ->
    let reg_defs = find_reg_in_rd_set current_instr reg current_rd_set in
    let new_rd_set = RDSet.diff current_rd_set reg_defs in
    let new_rd_set = RDSet.add current_instr new_rd_set in
    new_rd_set
  | _ -> current_rd_set
  
(* 'get_rd_set_of_predecessor' 함수는 주어진 명령어의 선행 블록들의 RDSet을 가져온다 *)
let get_rd_set_of_predecessor cfg block current_instr rd_in rd_set = 
  Hashtbl.fold (fun key value acc ->
    if List.mem (current_instr, block) value then
      try
        let pred_rd = RDMap.find key rd_set in
        RDSet.union acc pred_rd
      with Not_found ->
        acc
    else 
      acc
  ) cfg rd_in
  
(* 'compute_rd_set_for_block' 함수는 블록 내의 각 명령어에 대해 RDSet을 계산한다 *)
let rec compute_rd_set_for_block cfg block instructions rd_set = 
  match instructions with
  | [] -> rd_set
  | instr :: remaining_instrs ->
    let rd_in = get_rd_set_of_predecessor cfg block instr RDSet.empty rd_set in
    let new_rd_set = RDMap.add (instr, block) (update_rd_set instr rd_in) rd_set in 
    compute_rd_set_for_block cfg block remaining_instrs new_rd_set

(* 'compute_RDSet' 함수는 모든 기본 블록에 대해 RDSet이 변하지 않을 때까지반복적으로 계산한다 *)
let rec compute_rd_set cfg basic_blocks initial_rd_set =
  let rec iterate previous_rd_set =
    let new_rd_set =
      List.fold_left (fun acc_rd_set block ->
        compute_rd_set_for_block cfg block block acc_rd_set
      ) previous_rd_set basic_blocks
    in
    if rdmap_equal new_rd_set previous_rd_set then
      new_rd_set
    else
      iterate new_rd_set
  in
  iterate initial_rd_set


(* 'find_reaching_definition' 함수는 레지스터의 RDSet 내의 정의를 찾는다 *)
let rec find_reaching_definition block reg rd_set = 
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
    | Set (r, i) ->
      if r = reg && i <> value then (false, i) else (flag, value)
    | Copy (_, r) | BinOp (r, _, _, _) | UnOp (r, _, _) -> 
      if r = reg then (false, value) else (flag, value)
    | _ -> (flag, value)
  ) rd_set (flag, value) in
  flag, value

(* 'optimize_instructions_with_rd' 함수는 블록 내의 각 명령어를 RDSet을 이용하여 최적화한다 *)
let rec optimize_instructions_with_rd cfg block instructions rd_set =
  match instructions with
  | [] -> []
  | instr :: remaining_instrs -> 
    let rd_instr = get_rd_set_of_predecessor cfg block instr RDSet.empty rd_set in
    (match instr with
    | Copy (dest_reg, src_reg) ->
      let flag, value = find_reaching_definition block dest_reg rd_instr in
      if flag = true then 
        Set (src_reg, value) :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
      else 
        instr :: optimize_instructions_with_rd cfg block remaining_instrs rd_set

    | BinOp (dest_reg, op, operand1, operand2) ->
      (match operand1 with
      | Reg reg1 ->
        let flag, value = find_reaching_definition block reg1 rd_instr in
        if flag = true then 
          BinOp (dest_reg, op, Imm value, operand2) :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
        else 
          (match operand2 with
          | Reg reg2 ->
            let flag, value = find_reaching_definition block reg2 rd_instr in
            if flag = true then 
              BinOp (dest_reg, op, operand1, Imm value) :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
            else 
              instr :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
          | _ -> instr :: optimize_instructions_with_rd cfg block remaining_instrs rd_set)
      | _ -> 
        (match operand2 with
        | Reg reg2 ->
          let flag, value = find_reaching_definition block reg2 rd_instr in
          if flag = true then 
            BinOp (dest_reg, op, operand1, Imm value) :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
          else 
            instr :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
        | _ -> instr :: optimize_instructions_with_rd cfg block remaining_instrs rd_set))

    | UnOp (dest_reg, op, Reg reg) ->
      let flag, value = find_reaching_definition block reg rd_instr in
      if flag = true then 
        UnOp (dest_reg, op, Imm value) :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
      else 
        instr :: optimize_instructions_with_rd cfg block remaining_instrs rd_set

    | Store (Reg dest_reg, src_reg) ->
      let flag, value = find_reaching_definition block dest_reg rd_instr in
      if flag = true then 
        Store (Imm value, src_reg) :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
      else 
        instr :: optimize_instructions_with_rd cfg block remaining_instrs rd_set

    | Ret (Reg reg) ->
      let flag, value = find_reaching_definition block reg rd_instr in
      if flag = true then 
        Ret (Imm value) :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
      else 
        instr :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
    
    | GotoIf (reg, l) ->
      let flag, value = find_reaching_definition block reg rd_instr in
      if flag = true then 
        if value = ImmBool false then 
          optimize_instructions_with_rd cfg block remaining_instrs rd_set
        else Goto (l) :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
      else instr :: optimize_instructions_with_rd cfg block remaining_instrs rd_set

    | GotoIfNot (reg, l) ->
      let flag, value = find_reaching_definition block reg rd_instr in
      if flag = true then 
        if value = ImmBool true then 
          optimize_instructions_with_rd cfg block remaining_instrs rd_set
        else Goto (l) :: optimize_instructions_with_rd cfg block remaining_instrs rd_set
      else instr :: optimize_instructions_with_rd cfg block remaining_instrs rd_set

    | _ -> instr :: optimize_instructions_with_rd cfg block remaining_instrs rd_set)

(* 'optimize_blocks_with_rd' 함수는 모든 기본 블록에 대해 RDSet을 이용하여 최적화된 명령어를 반환한다 *)
let rec optimize_blocks_with_rd cfg basic_blocks rd_set = 
  match basic_blocks with
  | [] -> []
  | block :: remaining_blocks ->
    let optimized_block = optimize_instructions_with_rd cfg block block rd_set in
    optimized_block @ optimize_blocks_with_rd cfg remaining_blocks rd_set


let rec constant_folding ir_list =
  let fold_constants r op i1 i2 tail =
    match (i1, i2) with
    | (Ir.ImmInt v1, Ir.ImmInt v2) ->
      let result = match op with
        | AddOp -> Ir.ImmInt (v1 + v2)
        | SubOp -> Ir.ImmInt (v1 - v2)
        | MulOp -> Ir.ImmInt (v1 * v2)
        | DivOp -> Ir.ImmInt (v1 / v2)
        | GtOp -> Ir.ImmBool (v1 > v2)
        | GeqOp -> Ir.ImmBool (v1 >= v2)
        | LtOp -> Ir.ImmBool (v1 < v2)
        | LeqOp -> Ir.ImmBool (v1 <= v2)
        | EqOp -> Ir.ImmBool (v1 = v2)
        | NeqOp -> Ir.ImmBool (v1 <> v2)
        | _ -> raise Error
      in
      [Set (r, result)] @ constant_folding tail
    | (Ir.ImmBool v1, Ir.ImmBool v2) ->
      let result = match op with
        | EqOp -> Ir.ImmBool (v1 = v2)
        | NeqOp -> Ir.ImmBool (v1 <> v2)
        | _ -> raise Error
      in
      [Set (r, result)] @ constant_folding tail
    | _ -> BinOp (r, op, Imm i1, Imm i2) :: constant_folding tail
  in
  match ir_list with
  | [] -> []
  | head :: tail ->
    (match head with
    | BinOp (r, op, Imm i1, Imm i2) -> fold_constants r op i1 i2 tail
    | UnOp (r, NegOp, Imm i1) ->
      (match i1 with
      | Ir.ImmInt v1 -> Set (r, Ir.ImmInt (-v1)) :: constant_folding tail
      | _ -> raise Error)
    | _ -> head :: constant_folding tail)



(* 'initialize_ae_set_for_block' 함수는 블록 내의 각 명령어에 대해 AESet을 초기화한다 *)
let rec initialize_ae_set_for_block block instructions ae_set = 
  match instructions with
  | [] -> ae_set
  | instr :: remaining_instrs ->
    let new_ae_set = AEMap.add (instr, block) AESet.empty ae_set in
    initialize_ae_set_for_block block remaining_instrs new_ae_set

(* 'initialize_ae_set' 함수는 모든 기본 블록에 대해 AESet을 초기화한다 *)
let rec initialize_ae_set basic_blocks ae_set = 
  match basic_blocks with
  | [] -> ae_set
  | block :: remaining_blocks ->
    let ae_set = initialize_ae_set_for_block block block ae_set in
    initialize_ae_set remaining_blocks ae_set

let string_contains main_str sub_str =
  let len_main = String.length main_str in
  let len_sub = String.length sub_str in
  let rec aux i =
    if i > len_main - len_sub then false
    else if String.sub main_str i len_sub = sub_str then true
    else aux (i + 1)
  in
  aux 0


let find_reg_in_ae_set current_instr reg set =
  AESet.fold (fun rdef result_set -> 
    if string_contains (instr_to_str rdef) reg = true then AESet.add rdef result_set else result_set
  ) set AESet.empty



let rec update_ae_set current_instr current_ae_set =  (* 한 instr에서 AESet을 계산한다 *)
  match current_instr with
  | Set (r, _) ->
    let reg_defs = find_reg_in_ae_set current_instr r current_ae_set in
    let new_ae_set = AESet.diff current_ae_set reg_defs in
    let new_ae_set = AESet.add current_instr new_ae_set in 
    new_ae_set
    
  | Copy (r1, r) | Load (r1, r) ->
    let reg_defs = find_reg_in_ae_set current_instr r current_ae_set in
    let new_ae_set = AESet.diff current_ae_set reg_defs in
    if r = r1 then new_ae_set
    else let new_ae_set = AESet.add current_instr new_ae_set in new_ae_set

  | BinOp (r, _, r2, r3) ->
    let reg_defs = find_reg_in_ae_set current_instr r current_ae_set in
    let new_ae_set = AESet.diff current_ae_set reg_defs in
    (match (r2, r3) with
    | (Reg ra, Reg rb) -> 
      if r = ra || r = rb then new_ae_set 
      else let new_ae_set = AESet.add current_instr new_ae_set in new_ae_set
    | (Reg ra, _) ->
      if r = ra then new_ae_set 
      else let new_ae_set = AESet.add current_instr new_ae_set in new_ae_set
    | (_, Reg rb) ->
      if r = rb then new_ae_set 
      else let new_ae_set = AESet.add current_instr new_ae_set in new_ae_set
    | (_, _) -> let new_ae_set = AESet.add current_instr new_ae_set in new_ae_set)

  | UnOp (r, _, r1) ->
    let reg_defs = find_reg_in_ae_set current_instr r current_ae_set in
    let new_ae_set = AESet.diff current_ae_set reg_defs in
    (match r1 with
    | Reg ra ->  
      if r = ra then new_ae_set 
      else let new_ae_set = AESet.add current_instr new_ae_set in new_ae_set
    | _ -> let new_ae_set = AESet.add current_instr new_ae_set in new_ae_set)

  | Store (Reg r, r1)  ->
    let reg_defs = find_reg_in_ae_set current_instr r current_ae_set in
    let new_ae_set = AESet.diff current_ae_set reg_defs in
    if r = r1 then new_ae_set 
    else let new_ae_set = AESet.add current_instr new_ae_set in new_ae_set

  | _ -> current_ae_set


let get_ae_set_of_predecessor cfg block current_instr ae_in ae_set = 
  let count = ref 0 in
  let ret = Hashtbl.fold (fun key value acc ->
    if List.mem (current_instr, block) value then (
      count := !count + 1;
      try
        let pred_ae = AEMap.find key ae_set in
        AESet.inter acc pred_ae
      with Not_found ->
        acc
    ) else 
      acc
  ) cfg ae_in
  in
  if !count = 0 then AESet.empty else ret


let rec compute_ae_set_for_block cfg block instructions ae_all ae_set = 
  match instructions with
  | [] -> ae_set
  | instr :: remaining_instrs->
    let ae_in = get_ae_set_of_predecessor cfg block instr ae_all ae_set in
    let new_ae_set = AEMap.add (instr, block) (update_ae_set instr ae_in) ae_set in 
    compute_ae_set_for_block cfg block remaining_instrs ae_all new_ae_set
    
let rec compute_ae_set cfg basic_blocks ae_all initial_ae_set = 
  let rec iterate previous_ae_set =
    let new_ae_set =
      List.fold_left (fun acc_ae_set block ->
        compute_ae_set_for_block cfg block block ae_all acc_ae_set
      ) previous_ae_set basic_blocks
    in
    if aemap_equal new_ae_set previous_ae_set then
      new_ae_set
    else
      iterate new_ae_set
  in
  iterate initial_ae_set


let rec find_available_expression block instr reg ae_set = 
  let (r1, r2, r3, r4) = instr in
  let left_str = oprnd_to_str r3 in
  let binop_str = binop_to_str r2 in
  let right_str = oprnd_to_str r4 in
  let instr_str = sprintf "%s %s %s" left_str binop_str right_str in
  let flag, value = AESet.fold (fun x (flag, value) -> 
    if (string_contains (instr_to_str x) instr_str) = true then (true, x)
    else (flag, value)
  ) ae_set (false, reg) in
  flag, value
  
let rec optimize_instructions_with_ae cfg block instructions ae_all ae_set =
  match instructions with
  | [] -> []
  | instr :: remaining_instrs -> 
    match instr with
    | BinOp (r1, r2, r3, r4) -> 
      let ae_block = get_ae_set_of_predecessor cfg block instr ae_all ae_set in
      let flag, value = find_available_expression block (r1, r2, r3, r4) instr ae_block in
      if flag = true then 
        match value with
        | BinOp (rr, _, _, _) ->
          [Copy (rr, r1)] @ optimize_instructions_with_ae cfg block remaining_instrs ae_all ae_set
        | _ -> instr :: optimize_instructions_with_ae cfg block remaining_instrs ae_all ae_set
      else instr :: optimize_instructions_with_ae cfg block remaining_instrs ae_all ae_set
    | _ -> instr :: optimize_instructions_with_ae cfg block remaining_instrs ae_all ae_set

let rec optimize_blocks_with_ae cfg basic_blocks ae_all ae_set = 
  match basic_blocks with
  | [] -> []
  | block :: remaining_blocks ->
    optimize_instructions_with_ae cfg block block ae_all ae_set @ optimize_blocks_with_ae cfg remaining_blocks ae_all ae_set
  
let rec all_ae_set ae_set ir_list = 
  match ir_list with
  | [] -> ae_set
  | head :: tail ->
    all_ae_set (AESet.add head ae_set) tail
    

(* 'initialize_lv_set_for_block' 함수는 블록 내의 각 명령어에 대해 LVSet을 초기화한다 *)
let rec initialize_lv_set_for_block block instructions lv_set = 
  match instructions with
  | [] -> lv_set
  | instr :: remaining_instrs ->
    let new_lv_set = LVMap.add (instr, block) LVSet.empty lv_set in
    initialize_lv_set_for_block block remaining_instrs new_lv_set

(* 'initialize_lv_set' 함수는 모든 기본 블록에 대해 LVSet을 초기화한다 *)
let rec initialize_lv_set basic_blocks lv_set = 
  match basic_blocks with
  | [] -> lv_set
  | block :: remaining_blocks ->
    let lv_set = initialize_lv_set_for_block block block lv_set in
    initialize_lv_set remaining_blocks lv_set


let rec lvset succ lv_in lv_set = 
  match succ with
  | [] -> lv_in
  | head :: tail ->
    let inst, _ = head in
    let pred_lv = LVMap.find head lv_set in
    let lv_in = LVSet.union lv_in pred_lv in
    lvset tail lv_in lv_set

(* 'get_lv_set_of_predecessor' 함수는 주어진 명령어의 후행 블록들의 LVSet을 가져온다 *)
let get_lv_set_of_successor cfg block current_instr lv_in lv_set = 
  let successors = 
    try Hashtbl.find cfg (current_instr, block)
    with Not_found -> []
  in
  lvset successors lv_in lv_set


(* 'update_lv_set' 함수는 현재 명령어에서 LVSet을 갱신한다 *)
let rec update_lv_set current_instr current_lv_set =  
  match current_instr with
  | Set (r1, _ ) ->
    let new_lv_set = LVSet.remove r1 current_lv_set in
    new_lv_set

  | Copy (r2, r1) | Load (r1, r2) ->
    let new_lv_set = LVSet.remove r1 current_lv_set in
    let new_lv_set = LVSet.add r2 new_lv_set in
    new_lv_set

  | Store (r2, r1) ->
    let new_lv_set = LVSet.add r1 current_lv_set in
    (match r2 with
    | Reg ra -> 
      let new_lv_set = LVSet.add ra new_lv_set in
      new_lv_set
    | _ -> new_lv_set)

  | UnOp (r1, _, Reg r2)->
    let new_lv_set = LVSet.remove r1 current_lv_set in
    let new_lv_set = LVSet.add r2 new_lv_set in
    new_lv_set

  | BinOp (r1, _, r2, r3)  ->
    let new_lv_set = LVSet.remove r1 current_lv_set in
    (match r2 with
    | Reg ra ->
      let new_lv_set = LVSet.add ra new_lv_set in
      (match r3 with
      | Reg rb -> let new_lv_set = LVSet.add rb new_lv_set in new_lv_set
      | _ -> new_lv_set)
    | _ -> 
      (match r3 with
      | Reg rb -> let new_lv_set = LVSet.add rb new_lv_set in new_lv_set
      | _ -> new_lv_set)
    )
  | Ret (Reg r) -> 
    let new_lv_set = LVSet.add r current_lv_set in
    new_lv_set
  | GotoIf (r, _) | GotoIfNot (r, _) ->
    let new_lv_set = LVSet.add r current_lv_set in
    new_lv_set
  | _ -> current_lv_set

(* 'compute_lv_set_for_block' 함수는 블록 내의 각 명령어에 대해 LVSet을 계산한다 *)
let rec compute_lv_set_for_block cfg block instructions lv_set = 
  match instructions with
  | [] -> lv_set
  | instr :: remaining_instrs ->
    let lv_in = get_lv_set_of_successor cfg block instr LVSet.empty lv_set in
    let new_lv_set = LVMap.add (instr, block) (update_lv_set instr lv_in) lv_set in 
    compute_lv_set_for_block cfg block remaining_instrs new_lv_set


(* 'compute_lv_set' 함수는 모든 기본 블록에 대해 LVSet이 변하지 않을 때 까지 반복적으로 계산한다 *)
let rec compute_lv_set cfg basic_blocks initial_lv_set =
  let rec iterate previous_lv_set =
    let new_lv_set =
      List.fold_right (fun block acc_lv_set ->
        compute_lv_set_for_block cfg block (List.rev block) acc_lv_set
      ) basic_blocks previous_lv_set 
    in
    if lvmap_equal new_lv_set previous_lv_set then
      new_lv_set
    else
      iterate new_lv_set
  in
  iterate initial_lv_set




(* 'get_lv_set_of_predecessor' 함수는 주어진 명령어의 선행 블록들의 lVSet을 가져온다 *)
let get_lv_set_of_predecessor cfg block current_instr lv_in lv_set = 
  Hashtbl.fold (fun key value acc ->
    if List.mem (current_instr, block) value then
      try
        let pred_lv = LVMap.find key lv_set in
        LVSet.union acc pred_lv
      with Not_found ->
        acc
    else 
      acc
  ) cfg lv_in

let find_liveness reg lv_in =
  if LVSet.mem reg lv_in = false then true
  else false

(* 'optimize_instructions_with_lv' 함수는 블록 내의 각 명령어를 LVSet을 이용하여 최적화한다 *)
let rec optimize_instructions_with_lv cfg block instructions lv_set =
  match instructions with
  | [] -> []
  | instr :: remaining_instrs -> 
    match instr with
    | Set (r, _) | Copy (_, r) | BinOp (r, _, _, _) | UnOp (r, _, _)  ->
      let lv_in = get_lv_set_of_successor cfg block instr LVSet.empty lv_set in
      let flag = find_liveness r lv_in in
      if flag = true then [] @ optimize_instructions_with_lv cfg block remaining_instrs lv_set
      else [instr] @ optimize_instructions_with_lv cfg block remaining_instrs lv_set
    | _ -> [instr] @ optimize_instructions_with_lv cfg block remaining_instrs lv_set

(* 'optimize_blocks_with_lv' 함수는 모든 기본 블록에 대해 LVSet을 이용하여 최적화된 명령어를 반환한다 *)
let rec optimize_blocks_with_lv cfg basic_blocks lv_set = 
  match basic_blocks with
  | [] -> []
  | block :: remaining_blocks ->
    let optimized_block = optimize_instructions_with_lv cfg block block lv_set in
    optimized_block @ optimize_blocks_with_lv cfg remaining_blocks lv_set


(* 'find_reaching_definition_cp' copy propagation을 위한 함수이며, `레지스터의 RDSet 내의 정의를 찾아서 최적화 가능 여부를 판정한다. *)
let rec find_reaching_definition_cp block reg rd_set = 
  let flag, value = RDSet.fold (fun x (flag, value) -> 
    match x with
    | Copy (v, r) ->
      if r = reg then (true, v) else (flag, value)
    | Set (r, i) ->
      if r = reg then (false, value) else (flag, value)
    | BinOp (r, _, _, _) | UnOp (r, _, _) ->
      if r = reg then (false, value) else (flag, value)
    | _ -> (flag, value)
  ) rd_set (false, "") in
  flag, value

(* 'copy_propagation_instr' 함수는 블록 내의 각 명령어를 RDSet을 이용하여 최적화한다 *)
let rec copy_propagation_instr cfg block instructions rd_set =
  match instructions with
  | [] -> []
  | instr :: remaining_instrs -> 
    let rd_instr = get_rd_set_of_predecessor cfg block instr RDSet.empty rd_set in
    match instr with
    | UnOp (r1, r2, Reg r) ->  
      let flag, value = find_reaching_definition_cp block r rd_instr in
      if flag = true then [UnOp (r1, r2, Reg value)] @ copy_propagation_instr cfg block remaining_instrs rd_set
      else instr :: copy_propagation_instr cfg block remaining_instrs rd_set
    | BinOp (r1, r2, r3, r4) ->
      (match r3 with
      | Reg ra ->
        let flag, value = find_reaching_definition_cp block ra rd_instr in
        if flag = true then [BinOp (r1, r2, Reg value, r4)] @ copy_propagation_instr cfg block remaining_instrs rd_set
        else 
          (match r4 with
          | Reg rb -> 
            let flag, value = find_reaching_definition_cp block rb rd_instr in
            if flag = true then [BinOp (r1, r2, r3, Reg value)] @ copy_propagation_instr cfg block remaining_instrs rd_set
            else instr :: copy_propagation_instr cfg block remaining_instrs rd_set
          | _ -> instr :: copy_propagation_instr cfg block remaining_instrs rd_set)
      | _ ->
        (match r4 with
          | Reg rb -> 
            let flag, value = find_reaching_definition_cp block rb rd_instr in
            if flag = true then [BinOp (r1, r2, r3, Reg value)] @ copy_propagation_instr cfg block remaining_instrs rd_set
            else instr :: copy_propagation_instr cfg block remaining_instrs rd_set
          | _ -> instr :: copy_propagation_instr cfg block remaining_instrs rd_set)
      ) 
    | _ -> instr :: copy_propagation_instr cfg block remaining_instrs rd_set

(* 'optimize_blocks_with_rd' 함수는 모든 기본 블록에 대해 RDSet을 이용하여 최적화된 명령어를 반환한다 *)
let rec copy_propagation cfg basic_blocks rd_set =  
  match basic_blocks with
  | [] -> []
  | block :: remaining_blocks ->
    let optimized_block = copy_propagation_instr cfg block block rd_set in
    optimized_block @ copy_propagation cfg remaining_blocks rd_set

let rec run (ir: ir_code): ir_code =
  let fname, arg_regs, ir_list = ir in
  let basic_blocks = construct_basic_blocks ir_list in
  let cfg = construct_cfg basic_blocks basic_blocks (create_cfg ()) in
  let rd_set = initialize_rd_set basic_blocks RDMap.empty in
  let rd_set = compute_rd_set cfg basic_blocks rd_set in
  let ir_RD = optimize_blocks_with_rd cfg basic_blocks rd_set in
  let ir_cf = constant_folding ir_RD in

  let basic_blocks = construct_basic_blocks ir_cf in
  let cfg = construct_cfg basic_blocks basic_blocks (create_cfg ()) in
  let ae_set = initialize_ae_set basic_blocks AEMap.empty in
  let ae_all = all_ae_set AESet.empty ir_cf in
  let ae_set = compute_ae_set cfg basic_blocks ae_all ae_set in
  let ir_ae = optimize_blocks_with_ae cfg basic_blocks ae_all ae_set in
  let ir_cf = constant_folding ir_ae in

  let basic_blocks = construct_basic_blocks ir_cf in
  let cfg = construct_cfg basic_blocks basic_blocks (create_cfg ()) in
  let rd_set = initialize_rd_set basic_blocks RDMap.empty in
  let rd_set = compute_rd_set cfg basic_blocks rd_set in
  let ir_cp = copy_propagation cfg basic_blocks rd_set in
  let ir_cf = constant_folding ir_cp in

  let basic_blocks = construct_basic_blocks ir_cp in
  let cfg = construct_cfg basic_blocks basic_blocks (create_cfg ()) in
  let lv_set = initialize_lv_set basic_blocks LVMap.empty in
  let lv_set = compute_lv_set cfg basic_blocks lv_set in
  let ir_lv = optimize_blocks_with_lv cfg basic_blocks lv_set in
  let ir_cf = constant_folding ir_lv in
  
  if ir_cf = ir_list then
    (fname, arg_regs, ir_cf)
  else
    run (fname, arg_regs, ir_cf)
  
  

  