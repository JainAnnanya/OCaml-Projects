(* Aya Salama, Annanya Jain*)

open Ds
open Parser_plaf.Ast
open Parser_plaf.Parser
    
let g_store = Store.empty_store 20 (NumVal 0)

let rec addIds fs evs =
  match fs , evs with
  | [] ,[] -> []
  | ( id ,(is_mutable, _)) :: t1 , v :: t2 -> ( id ,( is_mutable , v )) :: addIds t1 t2
  | _ , _ -> failwith " error : lists have different sizes "

let rec eval_expr : expr -> exp_val ea_result = fun e ->
  match e with
  | Int(n) -> return @@ NumVal n
  | Var(id) -> apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return @@ NumVal (n1+n2)
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return @@ NumVal (n1-n2)
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return @@ NumVal (n1*n2)
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return @@ NumVal (n1/n2)
  | Let(v,def,body) ->
    eval_expr def >>= 
    extend_env v >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return @@ BoolVal (n = 0)
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return @@ PairVal(ev1,ev2)
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun p ->
    return @@ fst p 
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun p ->
    return @@ snd p
  | Proc(id,_,e)  ->
    lookup_env >>= fun en ->
    return (ProcVal(id,e,en))
  | App(e1,e2)  -> 
    eval_expr e1 >>= 
    clos_of_procVal >>= fun (id,e,en) ->
    eval_expr e2 >>= fun ev ->
    return en >>+
    extend_env id ev >>+
    eval_expr e
  | Letrec([(id,par,_,_,e)],target) ->
    extend_env_rec id par e >>+
    eval_expr target 
  | NewRef(e) ->
    eval_expr e >>= fun ev ->
    return (RefVal (Store.new_ref g_store ev))
  | DeRef(e) ->
    eval_expr e >>=
    int_of_refVal >>= 
    Store.deref g_store
  | SetRef(e1,e2) ->
    eval_expr e1 >>=
    int_of_refVal >>= fun l ->
    eval_expr e2 >>= fun ev ->
    Store.set_ref g_store l ev >>= fun _ ->
    return UnitVal    
  | BeginEnd([]) ->
    return UnitVal
  | BeginEnd(es) ->
    sequence (List.map eval_expr es) >>= fun l ->
    return (List.hd (List.rev l))
  | Unit -> return UnitVal
  | IsEqual(e1, e2) -> 
    eval_expr e1 >>= 
    int_of_numVal >>= fun p ->
    eval_expr e2 >>= 
    int_of_numVal >>= fun q ->
    if (p = q) 
      then return @@ BoolVal(true) 
      else return @@ BoolVal(false)
  | IsGT(e1, e2) ->
    eval_expr e1 >>= 
    int_of_numVal >>= fun p ->
    eval_expr e2 >>= 
    int_of_numVal >>= fun q ->
      if(p > q) 
        then return @@ BoolVal(true)
    else return @@ BoolVal(false)
  | IsLT(e1, e2) ->
      eval_expr e1 >>= 
      int_of_numVal >>= fun p ->
      eval_expr e2 >>= 
      int_of_numVal >>= fun q ->
        if(p < q) 
          then return @@ BoolVal(true)
      else return @@ BoolVal(false)
  | IsNumber(e) ->
    eval_expr e >>= 
     fun p ->
    begin 
    match p with 
    | NumVal _ -> return @@ BoolVal(true)
    | _ -> return @@ BoolVal(false)
    end
  | Record ( fs ) ->
    sequence (List.map process_field fs ) >>= fun evs ->
    return( RecordVal(addIds fs evs ))
  | Proj(e, id) -> 
    eval_expr e >>= 
    fields_of_recordVal >>= fun p ->
    begin
    match List.assoc_opt id p  with 
    | None -> error "Field not Found"
    | Some (is_mutable, n) ->
      begin 
        match is_mutable with
        | false -> return n
        | true -> 
          int_of_refVal n >>= fun r ->
            Store.deref g_store r
        end
    end
  | SetField(e1, id, e2) ->
    eval_expr e1 >>= 
    fields_of_recordVal >>= fun p ->
    eval_expr e2 >>= fun q ->
    begin
    match List.assoc_opt id p with 
    | None -> error "Field not Found"
    | Some(is_mutable, n) -> 
      begin
      match is_mutable with 
      | false -> error "Field is not mutable"
      | true -> 
        int_of_refVal n >>= fun l ->
          Store.set_ref g_store l q >>= fun _ ->
            return UnitVal    
      end
    end
  | Debug(_e) ->
    string_of_env >>= fun str_env ->
    let str_store = Store.string_of_store string_of_expval g_store 
    in (print_endline (str_env^"\n"^str_store);
    error "Reached breakpoint")
  | _ -> failwith ("Not implemented: "^string_of_expr e)
  and
    process_field(_id,(is_mutable,e)) =
    eval_expr e >>= fun ev ->
    if is_mutable
    then return ( RefVal ( Store.new_ref g_store ev))
    else return ev

let eval_prog (AProg(_,e)) =
  eval_expr e         

(** [interp s] parses [s] and then evaluates it *)
let interp (s:string) : exp_val result =
  let c = s |> parse |> eval_prog
  in run c

(* Interpret an expression read from a file with optional extension . exr *)
let interpf ( s : string ) : exp_val result =
  let s = String.trim s (* remove leading and trailing spaces *)
   in let file_name = (* allow rec to be optional *)
  match String.index_opt s '.' with None -> s ^ ".exr " | _ -> s
   in interp @@ read_file file_name