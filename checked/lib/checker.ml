(* Name: Annanya Jain, Aya Salama 
  Pledge: I pledge my honor that I have abided by the Stevens Honor System
*)

open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser
       
let rec chk_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
    chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error
         "LetRec: Type of recursive function does not match
declaration")

  | NewRef(e) ->
    chk_expr e >>= fun t -> return @@ RefType(t)
    
  | DeRef(e) -> 
    chk_expr e >>= fun t -> 
      begin
        match t with 
        | RefType(t) -> return t
        | _ -> error "deref: Expected a reference type"
      end
  
  | SetRef (e1, e2) ->
    chk_expr e1 >>= fun t1 -> 
    chk_expr e2 >>= fun t2 -> 
      begin
        match t1 with 
        | RefType(t) -> if (t == t2) then return @@ UnitType else error "Types don't match"
        | _ -> error "setref: Expected a reference type"
      end

  | BeginEnd ([]) -> 
    return @@ UnitType
    
  | BeginEnd (es) -> 
    chk_exprs es >>= fun t1 -> return @@ List.hd (List.rev t1)
    
  | EmptyList (t) -> 
    begin 
      match t with 
      | None -> error "Expected type declaration"
      | Some t -> return (ListType t)
    end
  | Cons (e1, e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>=
    list_of_listType >>= fun t2 ->
      if t1=t2
      then return (ListType t2)
      else error "cons: type of head and tail do not match"
  | IsEmpty (e) -> 
    chk_expr e >>= fun t ->
    begin 
      match t with
      | ListType _ | TreeType _ -> return BoolType
      | _ -> error "Expected a tree or list"
    end
  | Hd (e) -> 
    chk_expr e >>= 
    list_of_listType >>= fun t ->
    return t
  | Tl (e) -> 
    chk_expr e >>= 
    list_of_listType >>= fun t ->
    return (ListType t)
  | EmptyTree (t) -> 
    begin 
      match t with 
      | None -> error "Expected type declaration"
      | Some t -> return (TreeType t)
    end 
  | Node (de, le, re) -> 
    chk_expr de >>= fun e1 ->
    chk_expr le >>= 
    tree_of_treeType >>= fun e2 ->
    chk_expr re >>= 
    tree_of_treeType >>= fun e3 ->
    if e1=e2 && e1=e3 
    then return (TreeType e1)
    else error "node: type of node and tree do not match"
  | CaseT (target, emptycase, id1, id2, id3, nodecase) -> 
    chk_expr target >>= 
    tree_of_treeType >>= fun t ->
    chk_expr emptycase >>= fun s1 -> 
    extend_tenv id1 t >>+
    extend_tenv id2 (TreeType t) >>+ 
    extend_tenv id3 (TreeType t) >>+ 
    chk_expr nodecase >>= fun s2 ->
    if s1=s2
    then return s1
    else error "caseT: type of emptycase and nodecase do not match"
  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  | _ -> failwith "chk_expr: implement"    
and
  chk_prog (AProg(_,e)) =
  chk_expr e
and 
  chk_exprs es = 
  match es with
  | [] -> return []
  | h :: t -> chk_expr h >>= fun th ->
    chk_exprs t >>= fun l ->
    return (th :: l)

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)

  