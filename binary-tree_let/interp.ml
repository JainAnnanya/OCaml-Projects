(**
Name: Annanya Jain
Pledge: I pledge my honor that I have abided by the Stevens Honor System.     
*)

open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds

(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
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
    return (BoolVal (n = 0))
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return (PairVal(ev1,ev2))
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (l,_) ->
    return l
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (_,r) ->
    return r
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | Unpair(id1, id2, e1, e2) ->
    eval_expr e1 >>= pair_of_pairVal >>= fun(ev1,ev2) ->
    extend_env id1 ev1 >>+
    extend_env id2 ev2 >>+ 
    eval_expr e2

  (** creates an Empty tree *)
  | EmptyTree(_t) ->
    return (TreeVal Empty)

  (** returns a boolean indicating whether the e is an empty binary tree *)
  | IsEmpty(e) -> 
      eval_expr e >>= tree_of_treeVal >>= fun t ->
      begin match t with 
      | Empty -> return (BoolVal true)
      | Node(_) -> return (BoolVal false)
      end

  (** creates a new tree with data e1 and left and right subtrees e2 and e3 *)
  | Node(e1,e2,e3) -> 
      eval_expr e1 >>= fun n1 ->
      eval_expr e2 >>= tree_of_treeVal >>= fun left ->
      eval_expr e3 >>= tree_of_treeVal >>= fun right ->
      return (TreeVal (Node(n1, left, right)))
  
  (** acts like a match in OCaml *)
  | CaseT(e1, e2, id1, id2, id3, e3) ->
    eval_expr e1 >>= 
    tree_of_treeVal >>= fun t ->
    begin match t with
    | Empty -> eval_expr e2
    | Node(d, lt, rt) -> 
      extend_env id1 d >>+ extend_env id2 (TreeVal lt) >>+ extend_env id3 (TreeVal rt) >>+
      eval_expr e3
    end
  
  (** Record creates a record with n fields. Field i is assigned the expressed value resulting from evaluating expression. 
      It also reeports an error if there are any duplicate fields using has_duplicates helper function which i defined in ds.ml *)
  | Record(fs) ->
    let (x, y) = (List.split fs) in 
    let (a,b) = (List.split y) in
    if has_duplicates x then 
      error "Record : duplicate fields" 
    else
      (eval_exprs b) >>= fun n1 -> 
      return (RecordVal(List.combine x n1))

  (** e.id projects field id from the record resulting from evaluating e. *)
  | Proj (e, id ) -> 
    eval_expr e >>= fun record ->
      begin match record with
        | RecordVal key_value ->
            begin match List.assoc_opt id key_value with
            | Some value -> return value
            | None -> error "Proj: field does not exist"
            end
        | _ -> error "Expected a record"
      end
  | _ -> failwith "Not implemented yet!"
  and
    eval_exprs : expr list -> ( exp_val list ) ea_result =
    fun es ->
      match es with
      | [] -> return []
      | h :: t -> eval_expr h >>= fun i ->
        eval_exprs t >>= fun l ->
          return ( i :: l )
      
(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e

(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c



