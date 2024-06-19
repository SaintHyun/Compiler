open Program
open Ir
open Printf

(* Example code to illustrate how to define your own custom type and define a
 * Set to store them. *)

type cfg = (instr list, instr list list) Hashtbl.t

let create_cfg () : cfg =
  Hashtbl.create 10

let add_edge g v1 v2 =
  let edges = try Hashtbl.find g v1 with Not_found -> [] in
  Hashtbl.replace g v1 (v2 :: edges)
  
(* Reaching definition (you can fix the following definition, of course). *)
type rdef = instr

(* Now you can define "set of reaching definition" as follow. *)
module RDSet = Set.Make(struct
  type t = rdef
  let compare = Pervasives.compare
end)

module RDMap = Map.Make(struct
  type t = instr list
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
  | [] -> None
  | x :: _ -> Some x

let rec last_instr block = 
  match block with
  | [last] -> last
  | head :: tail -> last_instr tail

let rec find_label blocks label =
  match blocks with
  | [] -> None
  | head :: tail -> 
    (match head_instr head with
    | Some (Label l) when l = label -> Some head
    | _ -> find_label tail label)

let rec const_CFG basic_blocks cur_blocks cfg = 
  match cur_blocks with
  | [] -> cfg
  | [head] ->
    let last_of_block = last_instr head in
    (match last_of_block with
    | GotoIf (r, label) | GotoIfNot (r, label) -> 
      (match find_label basic_blocks label with
      | Some label_block ->
        add_edge cfg head label_block;
        cfg
      | None -> cfg)

    | Goto label ->
      (match find_label basic_blocks label with
      | Some label_block ->
        add_edge cfg head label_block;
        cfg
      | None -> 
        cfg
      )

    | _ -> cfg
    )

  | head :: [next] ->
    let last_of_block = last_instr head in
    (match last_of_block with
    | GotoIf (r, label) | GotoIfNot (r, label) -> 
      (match find_label basic_blocks label with
      | Some label_block ->
        add_edge cfg head label_block;
        add_edge cfg head next;
        const_CFG basic_blocks [next] cfg
      | None -> const_CFG basic_blocks [next] cfg)

    | Goto label ->
      (match find_label basic_blocks label with
      | Some label_block ->
        add_edge cfg head label_block;
        const_CFG basic_blocks [next] cfg
      | None -> 
        const_CFG basic_blocks [next] cfg)

    | Ret o -> 
      const_CFG basic_blocks [next] cfg

    | _ -> 
      add_edge cfg head next;
      const_CFG basic_blocks [next] cfg
    )

  | head :: next :: tail ->
    let last_of_block = last_instr head in
    (match last_of_block with
    | GotoIf (r, label) | GotoIfNot (r, label) -> 
      (match find_label basic_blocks label with
      | Some label_block ->
        add_edge cfg head label_block;
        add_edge cfg head next;
        const_CFG basic_blocks (next :: tail) cfg
      | None -> const_CFG basic_blocks (next :: tail) cfg)

    | Goto label ->
      (match find_label basic_blocks label with
      | Some label_block ->
        add_edge cfg head label_block;
        const_CFG basic_blocks (next :: tail) cfg
      | None -> 
        const_CFG basic_blocks (next :: tail) cfg)

    | Ret o -> 
      const_CFG basic_blocks (next :: tail) cfg

    | _ -> 
      add_edge cfg head next;
      const_CFG basic_blocks (next :: tail) cfg
    )

    
let find_r_in_rd_set inst r set =
  RDSet.fold (fun rdef ret_set -> 
    match rdef with
    | Set (r1, _) | Copy (_, r1) | BinOp (r1, _, _, _) | UnOp (r1, _, _) -> 
      if r1 = r then RDSet.add rdef ret_set else ret_set
    | _ -> 
      ret_set
  ) set RDSet.empty

let rec transfer block cur_rd =  (* 한 block에서 RDSet을 계산한다 *)
  match block with
  | [] -> cur_rd
  | head :: tail ->
    (match head with
    | Set (r, _) | Copy (_, r) | BinOp (r, _, _, _) | UnOp (r, _, _) ->
      let contain_r = find_r_in_rd_set head r cur_rd in
      let new_cur_rd = RDSet.diff cur_rd contain_r in
      let new_cur_rd = RDSet.add head new_cur_rd in
      transfer tail new_cur_rd
    | _ -> transfer tail cur_rd
    )

let rec get_pred_RDSet cfg cur_block rd_in rd_set =
  Hashtbl.fold (fun key value acc ->
    if List.mem cur_block value then
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

let rec compute_RDSet cfg basic_blocks rd_set =
  let rec iterate previous_rd_set =
    let new_rd_set = 
      List.fold_left (fun acc_rd_set block ->
        let rd_in = get_pred_RDSet cfg block RDSet.empty acc_rd_set in
        let new_head_rd_set = transfer block rd_in in
        RDMap.add block new_head_rd_set acc_rd_set
      ) previous_rd_set basic_blocks
    in
    if rdmap_equal new_rd_set previous_rd_set then
      new_rd_set
    else
      iterate new_rd_set
  in
  iterate rd_set

let rec initial_RDSet basic_blocks rd_set = 
  match basic_blocks with
  | [] -> rd_set
  | head :: tail ->
    let new_rd_set = RDMap.add head RDSet.empty rd_set in
    initial_RDSet tail new_rd_set



let print_block block =
  List.iter (fun instr -> print_string (instr_to_str instr); print_newline ()) block;
  print_newline () 

let print_cfg cfg =
  Hashtbl.iter (fun k v_list ->
   let last_i = last_instr k in
    List.iter (fun v ->
      match head_instr v with
      | None -> ()
      | Some first_v ->
        Printf.printf "%s -> %s\n"
          (instr_to_str last_i)
          (instr_to_str first_v)
    ) v_list
  ) cfg



let print_rdset rdset =
  RDSet.iter (fun instr ->
    print_string (instr_to_str instr); 
    print_newline ()
  ) rdset


let print_rdmap rdmap =
  RDMap.iter (fun key rdset ->
    print_string "RDSet for block:\n";
    print_block key;
    print_string "Reaching Definitions:\n";
    print_rdset rdset; 
    print_newline ()
  ) rdmap


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

let rec find_block basic_blocks instruction = 
  match basic_blocks with
  | [] -> []
  | head :: tail ->
    if List.mem instruction head then head
    else find_block tail instruction

let rec optimize_block block cur_block rd_set =
  match cur_block with
  | [] -> []
  | head :: tail -> 
    match head with
      | Copy (r, r2) ->
        let rd_block = RDMap.find block rd_set in (* head의 rd를 찾음 *)
        let flag, value = find_RD block r rd_block in
        if flag = true then [Set (r2, value)] @ optimize_block block tail rd_set
        else head :: optimize_block block tail rd_set

      | BinOp (r1, r2, Reg r, r3) -> 
        let rd_block = RDMap.find block rd_set in (* head의 rd를 찾음 *)
        let flag, value = find_RD block r rd_block in
        if flag = true then [BinOp (r1, r2, Imm value, r3)] @ optimize_block block tail rd_set
        else head :: optimize_block block tail rd_set

      | BinOp (r1, r2, r3, Reg r) -> 
        let rd_block = RDMap.find block rd_set in (* head의 rd를 찾음 *)
        let flag, value = find_RD block r rd_block in
        if flag =true then [BinOp (r1, r2, r3, Imm value)] @ optimize_block block tail rd_set
        else head :: optimize_block block tail rd_set

      | UnOp (r1, r2, Reg r) ->
        let rd_block = RDMap.find block rd_set in (* head의 rd를 찾음 *)
        let flag, value = find_RD block r rd_block in
        if flag = true then [UnOp (r1, r2, Imm value)] @ optimize_block block tail rd_set
        else head :: optimize_block block tail rd_set

      | _ -> head :: optimize_block block tail rd_set

let rec optimize_RD basic_blocks rd_set = 
  match basic_blocks with
  | [] -> []
  | head :: tail ->
    optimize_block head head rd_set @ optimize_RD tail rd_set

let run (ir: ir_code): ir_code =
  let fname, arg_regs, ir_list = ir in
  let basic_blocks = const_blocks ir_list in
  let cfg = const_CFG basic_blocks basic_blocks (create_cfg ()) in
  let rd_set = initial_RDSet basic_blocks RDMap.empty in
  let rd_set = compute_RDSet cfg basic_blocks rd_set in
  (* List.iter print_block basic_blocks; *)
  (* print_cfg cfg; *)
  (* print_rdmap rd_set; *)
  let ir_RD = optimize_RD basic_blocks rd_set in
  (fname, arg_regs, ir_RD)
