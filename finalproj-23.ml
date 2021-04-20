(* Q0  : Get familiar with the external syntax of MiniML *)
let parse_tests : (string * (string, exp) either) list = [
    (* Provide your tests for the parser *)
  ("1;", Right (Int 1))
]


let free_vars_tests : (exp * name list) list = [
  (Int 10, []);
  (Let ([Val (Int 3, "r"); Valtuple (Tuple [Var "p"; Var "l"], ["c"; "m"])],
        Var "r"), ["p";"l"])
]

(* Q1  : Find the free variables in an expression *)
let rec free_vars (e : exp) : name list = match e with
  | Int(_) -> []
  | Bool(_) -> []
  | If (e,e1,e2) -> union (union (free_vars e) (free_vars e1) ) (free_vars e2) 
  | Primop(_,l) -> List.fold_right (fun e1 fv -> union (free_vars e1) fv) l []
  | Tuple(l) -> List.fold_right (fun e1 fv -> union (free_vars e1) fv) l []
  | Fn(n,t,e) -> delete [n] (free_vars e)
  | Rec(n,t,e) -> delete [n] (free_vars e)
  | Let(d, e) -> union (List.fold_right (fun e1 fv -> match e1 with
      | Val(x,n) -> union (free_vars x) fv
      | Valtuple(x,l) -> union (free_vars x) fv
      | ByName(x,n) -> union (free_vars x) fv) d [] 
    ) (delete (List.fold_right (fun e1 fv -> match e1 with
      | Val(_,n) -> n::fv
      | Valtuple(_,l) -> l @ fv
      | ByName(_,n) -> n::fv) d [] 
    ) (free_vars e))
      
  | Apply(e1,e2) -> union (free_vars e1) (free_vars e2) 
  | Var(x) -> [x]
  | Anno(e,t) -> free_vars e
                   
                     


let unused_vars_tests : (exp * name list) list = [
]

(* Q2  : Check variables are in use *)
let rec remove l x = match l with
  | [] -> []
  | h :: t -> if x = h then t
      else
        h :: (remove t x) 
             
let delete1 ds set = 
  match set with
  | [] -> []
  | h :: t ->
      if member h ds then
        delete (remove ds h) t
      else
        h :: delete ds t
          
let rec unused_vars (e : exp) : name list = match e with
  | Int(_) -> []
  | Bool(_) -> []
  | If(e,e1,e2) -> union (union (unused_vars e) (unused_vars e1)) (unused_vars e2)
  | Primop(_,l) -> List.fold_right (fun e1 fv -> union (unused_vars e1) fv) l []
  | Tuple(l) -> List.fold_right (fun e1 fv -> union (unused_vars e1) fv) l []
  | Fn(n,t,e) -> union (if member n (free_vars e) then [] else [n]) (unused_vars e)
  | Rec(n,t,e) -> union (if member n (free_vars e) then [] else [n]) (unused_vars e)
  | Let(d,e1) -> let b = (let n = (List.fold_right (fun e2 fv -> 
      match e2 with
      | Val(e3,name) -> union (name::fv) (unused_vars e3)
      | Valtuple(e3,l) -> union l (unused_vars e3)
      | ByName(e3,name) -> union (name::fv) (unused_vars e3))  d [] )
     in n) in 
      union (delete1 (free_vars e1) b ) (delete b (unused_vars e1))
  | Apply(e1,e2) -> union (unused_vars e1) (unused_vars e2) 
  | Var(x) -> []
  | Anno(e1,_) -> unused_vars e1


let subst_tests : (((exp * name) * exp) * exp) list = [
]

(* Q3  : Substitute a variable *)
let rec rename_ex (n,x) e = (match e with
    | Var y ->
        if x = y then
          Var n
        else
          e
    | Int _ | Bool _ -> e
    | Primop (po, es) -> Primop (po, List.map (rename_ex (n,x)) es)
    | If (e1, e2, e3) -> If (rename_ex (n,x) e1, rename_ex (n,x) e2, rename_ex (n,x) e3)   
    | Tuple es -> Tuple (List.map (rename_ex (n,x)) es)      
    | Anno (e, t) -> Anno (rename_ex (n,x) e, t)     
    | Let(ds, e2) -> (match ds with 
        | [] -> Let(ds,rename_ex (n,x) e2)
        | h::t -> (match h with 
          
            |Val(e1,n1) ->   
                if x = n1 then
            
              
                  let Let(g,he) = rename_ex (n,x) (Let(t,e2))
                  in 
                  Let(Val(rename_ex (n,x) e1, n) :: g, he)
                else
                  let Let(g,he) = rename_ex (n,x) (Let(t,e2))
                  in 
                  Let (Val(rename_ex (n,x) e1, n1) :: g, he)
                  
            |Valtuple(el,nl) ->   
                if member x nl then
            
              
                  let Let(g,he) = rename_ex (n,x) (Let(t,e2))
                      
                  
                  in 
                  Let(Valtuple(rename_ex (n,x) el, (List.map (fun v -> if x = v then n else v) nl)) :: g, he)
                else
                  let Let(g,he) = rename_ex (n,x) (Let(t,e2))
                  in 
                  Let (Valtuple(rename_ex (n,x) el, nl) :: g, he)  
           
            | ByName(e1,n1) ->               
                if x = n1 then 
                  let Let(g,he) = rename_ex (n,x) (Let(t,e2))
                  in 
                  Let(Val(rename_ex (n,x) e1, n) :: g, he)
                else
                  let Let(g,he) = rename_ex (n,x) (Let(t,e2))
                  in 
                  Let (Val(rename_ex (n,x) e1, n1) :: g, he)  
                    
              
          ))
    | Apply(e1,e2) -> Apply(rename_ex (n,x) e1, rename_ex (n,x) e2)
    | Fn (y, t, e1) -> 
        if y = x then Fn(n, t, rename_ex (n,x) e1)
        else
          Fn(y,t, rename_ex (n,x) e1)
    | Rec(y,t,e1) -> 
        if y = x then Rec(n, t, rename_ex (n,x) e1)
        else
          Rec(y,t, rename_ex (n,x) e1)
  )


    
let rec subst ((e', x) : exp * name) (e : exp) : exp =
  
  let hstbl = Hashtbl.create 10 in
  
  match e with
  | Var y ->
      if x = y then
        e'
      else
        Var y

  | Int _ | Bool _ -> e
  | Primop (po, es) -> Primop (po, List.map (subst (e', x)) es)
  | If (e1, e2, e3) -> If (subst (e', x) e1, subst (e', x) e2, subst (e', x) e3)
  | Tuple es -> Tuple (List.map (subst (e', x)) es)
  | Anno (e, t) -> Anno (subst (e', x) e, t)

  | Let (ds, e2) -> (match ds with
      | [] -> Let(ds, subst (e',x) e2)
      | h::t ->  (match h with
          | Val(e1,n) -> if (n = x) then (e)
                                         
              else
              if(member n (free_vars e')) then
                let z = fresh_var n in
                let Let(g,he) =  subst (e',x) (rename_ex (z,n) (Let(t,e2)))
                in 
                Let (Val(subst (e',x) (subst (Var(z), n) e1), z) :: g, he)
                  
              else 
                let Let(g,he) = subst (e',x) (Let(t,e2))
                in 
                Let(Val((subst (e',x) e1), n) :: g, he)
        
          | Valtuple(et, nl) -> if (member x nl) then e
              else
              if (List.exists (fun v -> member v (free_vars e')) nl)
              then
                let n = List.find (fun v -> member v (free_vars e')) nl
                in
                let z = fresh_var n in
                let Let(g,he) = subst (e',x) (rename_ex (z,n) (Let(t,e2)))
                in
                let n2 = List.map (fun v -> if v = n then z else v) nl
                in
                Let (Valtuple(subst (e',x) (subst (Var(z), n) et), n2) :: g, he)
              else
                let Let(g,he) = subst (e',x) (Let(t,e2))
                in 
                Let (Valtuple(subst (e',x) et, nl) :: g, he)
                  
          | ByName(e1,n) -> if (n = x) then (print_string " In ";Format.printf " n is %s and x is %s \n" n x;e)
                                         
              else
              if(member n (free_vars e')) then
                let z = fresh_var n in
                let Let(g,he) =  subst (e',x) (rename_ex (z,n) (Let(t,e2)))
                in 
                Let (Val(subst (e',x) (subst (Var(z), n) e1), z) :: g, he)
                  
              else 
                let Let(g,he) = subst (e',x) (Let(t,e2))
                in 
                Let(Val((subst (e',x) e1), n) :: g, he)
        )
        
    
    
    )
  
   
  | Apply (e1, e2) -> Apply(subst (e', x) e1, subst (e',x) e2)
  | Fn (y, t, e1) -> if (y = x) then Fn(y,t,e1) 
      else
      if (member y (free_vars e')) then (let z = fresh_var y in subst(e',x) (Fn(z,t,subst(Var(z), y) e1)))
      else
        Fn(y,t, subst(e',x) e1)
  | Rec (y, t, e1) -> if (y = x) then Rec(y,t,e1) 
      else
      if (member y (free_vars e')) then (let z = fresh_var y in subst(e',x) (Rec(z,t,subst(Var(z), y) e1)))
      else
        Rec(y,t, subst(e',x) e1)

let eval_tests : (exp * exp) list = [
]

(* Q4  : Evaluate an expression in big-step *)
let eval_op_bool op args = 
  match (op,args) with
  | (And, [Bool b1; Bool b2]) -> Some (Bool (b1 && b2))
  | (Or, [Bool b1; Bool b2]) -> Some (Bool (b1 || b2))
  | _ -> None
    
let rec eval : exp -> exp =
  (* do not change the code from here *)
  let bigstep_depth = ref 0 in
  fun e ->
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "eval (" ^ Print.exp_to_string e ^ ")\n");
    incr bigstep_depth;
  (* to here *)
    let result =
      match e with
      | Int _ | Bool _ -> e
      | Tuple es -> Tuple (List.map eval es)
      | If (e1, e2, e3) ->
          begin match eval e1 with
            | Bool b ->
                if b then
                  eval e2
                else
                  eval e3
            | _ -> stuck "Condition for if expression should be of the type bool"
          end
      | Anno (e, _) -> eval e     (* types are ignored in evaluation *)
      | Var x -> stuck ("Free variable \"" ^ x ^ "\" during evaluation")

      | Fn (x, t, e) -> Fn (x, t, e)
      | Apply (e1, e2) -> (match eval e1 with
          | Fn(x,t,e) -> eval (subst (eval e2,x) e)
          | _ -> stuck "The first argument should be a function")
                 
      | Rec (f, t, e) -> eval (subst (Rec(f,t,e), f) e)
      | Primop (And, es) ->
          let vs = List.map eval es in
          begin match eval_op_bool And vs with
            | None -> stuck "Bad arguments to boolean operation"
            | Some v -> v
          end
          
      | Primop (Or, es) ->
          let vs = List.map eval es in
          begin match eval_op_bool Or vs with
            | None -> stuck "Bad arguments to boolean operation"
            | Some v -> v
          end
      | Primop (op, es) ->
          let vs = List.map eval es in
          begin match eval_op op vs with
            | None -> stuck "Bad arguments to primitive operation"
            | Some v -> v
          end

      | Let (ds, e) -> match List.rev ds with 
        | [] -> eval e
        | h::t -> (match h  with
            | Val(e1, n) -> eval ((subst (eval e1,n) (Let(t, e))))
            | Valtuple(e1, n) -> let vt = eval e1 in
                (match vt with
                 | Tuple(l) -> eval (List.fold_right2 (fun v1 x1 fv ->
                     subst (v1,x1) fv)
                     l n (Let(t,e)))
                 | _ -> stuck "Bad declaration in let expression")
            | ByName(e1, n) -> eval ((subst (e1, n) (Let(t, e))))
          )
            
    in
  (* do not change the code from here *)
    decr bigstep_depth;
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "result of eval (" ^ Print.exp_to_string e ^ ") = "
         ^ Print.exp_to_string result ^ "\n");
  (* to here *)
    result


let infer_tests : ((context * exp) * typ) list = [
]

(* Q5  : Type an expression *)

        
            
          
            
          


let unify_tests : ((typ * typ) * unit) list = [
]

(* find the next function for Q5 *)
(* Q6  : Unify two types *)

let rec occur_check t v = 
  match t with
  | TInt -> false
  | TBool -> false
  | TProduct(l) -> List.for_all (fun x -> not (occur_check x v)) l
  | TArrow(t1,t2) -> if not (occur_check t1 v) then
        occur_check t2 v
      else
        false
  | TVar(x) -> let r = !x in match r with
    |Some d -> d = v
    |None -> false
    
let rec unify (ty1 : typ) (ty2 : typ) : unit = 
  match ty1 ,ty2 with
  | TInt, TInt -> ()
  | TBool, TBool -> ()
  | TProduct(l1), TProduct(l2) -> List.iter2 unify l1 l2
  | TVar(o), b -> if not(occur_check b ty1) && !o = None  then o := Some b
      else type_fail "Error b"
  | b, TVar(o) -> if not(occur_check b ty2) && !o = None then o := Some b
            
      else
        type_fail "Error c"
        
  | TArrow(t1,t2), TArrow(s1,s2) -> unify t1 s1; unify t2 s2
  | _ -> type_fail "Error"
           
           
(* Q7* : Implement the argument type inference
         For this question, move this function below the "unify". *)
let int_op = [Plus; Minus; Times; Div]
let bool_op = [Equals; NotEquals; LessThan; LessEqual; GreaterThan; GreaterEqual]
let b_op = [And; Or]
           
  
let rec infer (ctx : context) (e : exp) : typ = match e with
  | Int(_) -> TInt
  | Bool(_) -> TBool
  | If(e,e1,e2) -> let t = infer ctx e1 in 
      unify TBool (infer ctx e); unify t (infer ctx e2); t
      (*if typ_eq TBool (infer ctx e) && typ_eq t (infer ctx e2) then
         t
       else
         type_fail "Arguments of bad type provided for If"*)
  | Primop(And, l) -> (List.iter (fun v -> unify TBool v (*typ_eq TInt v*)) (List.map (fun v -> infer ctx v) l));
      TBool
          
  | Primop(Or, l) -> (List.iter (fun v -> unify TBool v (*typ_eq TInt v*)) (List.map (fun v -> infer ctx v) l)); 
      TBool
      
  | Primop(op, l) -> if (List.iter (fun v -> unify TInt v (*typ_eq TInt v*)) (List.map (fun v -> infer ctx v) l)); List.mem op int_op  || op = Negate then
      
      
        TInt
      else
          
      if List.mem op bool_op then
        TBool
          
      else 
      if (List.for_all (fun v -> typ_eq TBool v) (List.map (fun v -> infer ctx v) l)) && List.mem op b_op then
        TBool
      else
        type_fail "Bad operator or wrong arguments provided"
         
        
  | Tuple(l) -> TProduct (List.map (fun v -> infer ctx v) l )
  | Fn(n,t,e) -> (match t with 
      |Some t1 -> let t2 = infer (extend ctx (n,t1)) e in TArrow (t1,t2)
      |None -> let t1 = ref None in let tv = TVar(t1) in 
          let t2 = infer (extend ctx (n,tv)) e in
          match !t1 with 
          | Some d -> TArrow(d,t2)
          | None -> (*type_fail "Type could not be inferred"*) TArrow(tv, t2)
                      
    
    )
  | Rec(f,t,e) -> unify t (infer (extend ctx (f,t)) e); t
      
  | Let(dc, e) -> let exc = List.fold_right (fun v fv ->  match v with
      
      | Val(e1,n) -> extend fv (let value = (infer fv e1) in (n,value))
      | Valtuple(e1, l) -> let combined = List.combine l (let TProduct(c) = infer fv e1 in c) in
          extend_list ctx combined
            
      | ByName(e1,n) -> extend ctx (let value = (infer fv e1) in (n,value)) 
    
    ) (List.rev dc) ctx in
      (infer exc e)
  | Apply(e1,e2) -> (match infer ctx e1 with
      | TArrow (t1,t2) -> unify  t1 (infer ctx e2 ); t2
            
      | _ -> type_fail "first argument must be a function")
    
  | Var(x) -> (try ctx_lookup ctx x with NotFound -> type_fail "Variable is not declared")
                                                      
  | Anno(e,t) -> if typ_eq t (infer ctx e) then t
      else type_fail "Bad type given"
          

(* Now you can play with the language that you've implemented! *)
let execute (s: string) : unit =
  match P.parse s with
  | Left s -> print_endline ("parsing failed: " ^ s)
  | Right e ->
      try
       (* first we type check the program *)
        ignore (infer (Ctx []) e);
        let result = eval e in
        print_endline ("program is evaluated to: " ^ Print.exp_to_string result)
      with
      | NotImplemented -> print_endline "code is not fully implemented"
      | Stuck s -> print_endline ("evaluation got stuck: " ^ s)
      | NotFound -> print_endline "variable lookup failed"
      | TypeError s -> print_endline ("type error: " ^ s)
      | e -> print_endline ("unknown failure: " ^ Printexc.to_string e)


(************************************************************
*                     Tester template:                     *
*         Codes to test your interpreter by yourself.      *
                                            *         You can change these to whatever you want.       *
                                                                                           *                We won't grade these codes                *
                                                                              ************************************************************)
let list_to_string el_to_string l : string =
  List.fold_left
    begin fun acc el ->
      if acc = "" then
        el_to_string el
      else
        acc ^ "; " ^ el_to_string el
    end
    ""
    l
  |> fun str -> "[" ^ str ^ "]"

let run_test name f ts stringify : unit =
  List.iteri
    begin fun idx (input, expected_output) ->
      try
        let output = f input in
        if output <> expected_output then
          begin
            print_string (name ^ " test #" ^ string_of_int idx ^ " failed\n");
            print_string (stringify output ^ " <> " ^ stringify expected_output);
            print_newline ()
          end
      with
      | exn ->
          print_string (name ^ " test #" ^ string_of_int idx ^ " raised an exception:\n");
          print_string (Printexc.to_string exn);
          print_newline ()
    end
    ts

let run_free_vars_tests () : unit =
  run_test "free_vars" free_vars free_vars_tests (list_to_string (fun x -> x))

let run_unused_vars_tests () : unit =
  run_test "unused_vars" unused_vars unused_vars_tests (list_to_string (fun x -> x))

let run_subst_tests () : unit =
  run_test "subst" (fun (s, e) -> subst s e) subst_tests Print.exp_to_string

let run_eval_tests () : unit =
  run_test "eval" eval eval_tests Print.exp_to_string

(* You may want to change this to use the unification (unify) instead of equality (<>) *)
let run_infer_tests () : unit =
  run_test "infer" (fun (ctx, e) -> infer ctx e) infer_tests Print.typ_to_string

let run_unify_tests () : unit =
  run_test "unify" (fun (ty1, ty2) -> unify ty1 ty2) unify_tests (fun () -> "()")

let run_all_tests () : unit =
  run_free_vars_tests ();
  run_unused_vars_tests ();
  run_subst_tests ();
  run_eval_tests ();
  run_infer_tests ();
  run_unify_tests ()


