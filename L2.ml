type bop =  
  | Sum | Sub | Mul | Div   (* operações aritméticas *)
  | Eq  | Neq | Lt | Gt   (* operações relacionais  *)
  | And | Or   (* operações lógicas *) 

type tipo = 
  | TyInt
  | TyBool
  | TyRef of tipo
  | TyUnit
    

type expr = 
  | Num of int
  | Bool of bool 
  | Id of string
  | If of expr * expr * expr 
  | Binop of bop * expr * expr
  | Wh of expr * expr 
  | Asg of expr * expr 
  | Let of string * tipo * expr * expr 
  | New of expr
  | Deref of expr 
  | Unit
  | Seq of expr * expr
  | Read
  | Print of expr
  
      

          
          (*         
           
            let  x: int     =  read() in 
            let  z: ref int = new x in 
            let  y: ref int = new 1 in 
            
            (while (!z > 0) (
                   y :=  !y * !z;
                   z :=  !z - 1);
            print (! y))     

*)



let cndwhi = Binop(Gt, Deref (Id "z"),Num 0)
let asgny = Asg(Id "y", Binop(Mul, Deref (Id "y"),Deref(Id "z")))
let asgnz = Asg(Id "z", Binop(Sub, Deref (Id "z"),Num 1))
let bdwhi = Seq(asgny, asgnz) 
let whi = Wh(cndwhi, bdwhi)
let prt = Print(Deref (Id "y"))
let seq = Seq(whi, prt)
    
let fat = Let("x", TyInt, Read, 
              Let("z", TyRef TyInt, New (Id "x"), 
                  Let("y", TyRef TyInt, New (Num 1),
                      seq)))
        



let is_val (e: expr) : bool =
  match e with
  | Num _ | Bool _ | Unit -> true
  | _ -> false
let is_unit (e: expr) : bool =
  match e with 
  | Unit -> true
  | _ -> false

let bop_step (op, e1, e2 : bop*expr*expr) : expr =
  match op, e1, e2 with
  | Sum, Num n1, Num n2 -> Num (n1 + n2)
  | Sub, Num n1, Num n2 -> Num (n1 - n2)
  | Mul, Num n1, Num n2 -> Num (n1 * n2)
  | Div, Num n1, Num n2 when n2 <> 0 -> Num (n1 / n2)
  | Eq, Num n1, Num n2 -> Bool (n1 = n2)
  | Neq, Num n1, Num n2 -> Bool (n1 <> n2)
  | Lt, Num n1, Num n2 -> Bool (n1 < n2)
  | Gt, Num n1, Num n2 -> Bool (n1 > n2)
  | And, Bool b1, Bool b2 -> Bool (b1 && b2)
  | Or, Bool b1, Bool b2 -> Bool (b1 || b2)
  | _ -> failwith "Invalid binary operation"

let empty_pos_mem (mem : (expr * bool) array) : int =
  let i = ref 0 in
  while !i < Array.length mem && snd mem.(!i) do
    i := !i + 1
  done;
  !i

let int_expr (e: expr) : int =
  match e with
  | Num n -> n
  | _ -> failwith "Nao é inteiro"

let rec subst_var (e,var,v : expr*string*expr) : expr =
  match e with
  | Id id when id=var -> v
  | Id _ | Num _ | Bool _ | Unit | Read -> e
  
  | Binop (op, e1, e2) -> Binop (op, subst_var(e1, var, v), subst_var(e2, var, v))
  | Wh (e1, e2) -> Wh (subst_var(e1,var,v), subst_var(e2,var,v))
  | If (e1, e2, e3) -> If(subst_var(e1,var,v), subst_var(e2,var,v), subst_var(e3,var,v))
  | Asg (e1, e2) -> Asg(subst_var(e1,var,v), subst_var(e2, var, v))
  | New (e1) -> New(subst_var(e1, var, v))
  | Deref (e1) -> Deref(subst_var(e1,var,v))
  | Seq(e1, e2) -> Seq(subst_var(e1,var,v),subst_var(e2,var,v))
  | Print(e1) -> Print(subst_var(e1,var,v))
  
  | Let(var1, tp, e1, e2) when var=var1 -> Let(var1, tp, subst_var(e1,var,v), e2)
  | Let(var1, tp, e1, e2) -> Let(var1, tp, subst_var(e1,var,v), subst_var(e2,var,v)) 
                            

let rec small_step ((e, mem, entrada, saida) : expr * (expr * bool) array * int list * int list) : expr * (expr * bool) array * int list * int list =
  match e with
  | Num _ | Bool _ | Unit | Id _ -> (e, mem, entrada, saida)
  | Binop (op, e1, e2) when is_val e1 && is_val e2 ->
      (bop_step (op, e1, e2), mem, entrada, saida)
  | Binop (op, e1, e2) when is_val e1 ->
      let (e2', mem', entrada', saida') = small_step (e2, mem, entrada, saida) in
      (Binop (op, e1, e2'), mem', entrada', saida')
  | Binop (op, e1, e2) ->
      let (e1', mem', entrada', saida') = small_step (e1, mem, entrada, saida) in
      (Binop (op, e1', e2), mem', entrada', saida')
  | If (e1, e2, e3) when is_val e1 ->
      (match e1 with
       | Bool true -> (e2, mem, entrada, saida)
       | Bool false -> (e3, mem, entrada, saida)
       | _ -> failwith "Condition must be a boolean")
  | If (e1, e2, e3) ->
      let (e1', mem', entrada', saida') = small_step (e1, mem, entrada, saida) in
      (If (e1', e2, e3), mem', entrada', saida')
  | Seq (e1, e2) when is_unit e1 ->
      (e2, mem, entrada, saida)
  | Seq (e1, e2) ->
      let (e1', mem', entrada', saida') = small_step (e1, mem, entrada, saida) in
      (Seq (e1', e2), mem', entrada', saida')
  | Wh (e1, e2) ->
      (If (e1, Seq (e2, Wh (e1, e2)), Unit), mem, entrada, saida)
  | Asg (Num addr, v) when is_val v ->
      let new_mem = Array.copy mem in
      new_mem.(addr) <- (v, true);
      (Unit, new_mem, entrada, saida)
  | Asg (e1, e2) when is_val e1 ->
      let (e2', mem', entrada', saida') = small_step (e2, mem, entrada, saida) in
      (Asg (e1, e2'), mem', entrada', saida')
  | Asg (e1, e2) ->
      let (e1', mem', entrada', saida') = small_step (e1, mem, entrada, saida) in
      (Asg (e1', e2), mem', entrada', saida')
  | Let (var, tp, e1, e2) when is_val e1 ->
      (subst_var (e2, var, e1), mem, entrada, saida)
  | Let (var, tp, e1, e2) ->
      let (e1', mem', entrada', saida') = small_step (e1, mem, entrada, saida) in
      (Let (var, tp, e1', e2), mem', entrada', saida')
  | New e1 when is_val e1 ->
      let pos = empty_pos_mem mem in
      let new_mem = Array.copy mem in
      new_mem.(pos) <- (e1, true);
      (Num pos, new_mem, entrada, saida)
  | New e1 ->
      let (e1', mem', entrada', saida') = small_step (e1, mem, entrada, saida) in
      (New e1', mem', entrada', saida')
  | Deref (Num addr) ->
      (fst mem.(addr), mem, entrada, saida)
  | Deref e1 ->
      let (e1', mem', entrada', saida') = small_step (e1, mem, entrada, saida) in
      (Deref e1', mem', entrada', saida')
  | Print e1 when is_val e1 ->
      let valor = int_expr e1 in
      (Unit, mem, entrada, valor :: saida)
  | Print e1 ->
      let (e1', mem', entrada', saida') = small_step (e1, mem, entrada, saida) in
      (Print e1', mem', entrada', saida')
  | Read ->
      (match entrada with
       | [] -> failwith "Entrada vazia!"
       | h :: t -> (Num h, mem, t, saida))


let rec typeInfer (e: expr) : tipo =
  match e with
  | Id _ -> failwith "Type inference for identifiers not implemented"
  | Num _ -> TyInt
  | Bool _ -> TyBool
  | Binop(op, e1, e2) ->
      let t1 = typeInfer e1 in
      let t2 = typeInfer e2 in
      (match op with
       | Sum | Sub | Mul | Div -> if t1 = TyInt && t2 = TyInt then TyInt else failwith "Type error in arithmetic operation"
       | Eq | Neq | Lt | Gt -> if t1 = TyInt && t2 = TyInt then TyBool else failwith "Type error in relational operation"
       | And | Or -> if t1 = TyBool && t2 = TyBool then TyBool else failwith "Type error in logical operation")
  | If (e1, e2, e3) ->
      let t1 = typeInfer e1 in        
      let t2 = typeInfer e2 in
      let t3 = typeInfer e3 in
      if t1 = TyBool && t2 = t3 then t2
      else failwith "Type error in if expression"
  | Wh (e1, e2) ->
      let t1 = typeInfer e1 in  
      let t2 = typeInfer e2 in
      if t1 = TyBool && t2 = TyUnit then TyUnit
      else failwith "Type error in while expression"
  | Asg (e1, e2) ->
      let t1 = typeInfer e1 in
      let t2 = typeInfer e2 in
      (match t1 with
       | TyRef t when t = t2 -> TyUnit
       | _ -> failwith "Type error in assignment")
  | Let (var, tp, e1, e2) ->
      let t1 = typeInfer e1 in
      if t1 = tp then
        let e2' = subst_var (e2, var, e1) in
        typeInfer e2'
      else
        failwith "Type error in let binding"
  | New e1 ->
      let t1 = typeInfer e1 in
      TyRef t1
  | Deref e1 -> 
      let t1 = typeInfer e1 in
      (match t1 with
       | TyRef t -> t
       | _ -> failwith "Type error in dereference") 
  | Unit -> TyUnit
  | Seq (e1, e2) ->
      let t1 = typeInfer e1 in
      let t2 = typeInfer e2 in
      if t1 = TyUnit then t2 else failwith "Type error in sequence"
  | Read -> TyInt
  | Print e1 ->
      let t1 = typeInfer e1 in
      if t1 = TyInt then TyUnit else failwith "Type error in print"

let test_typeInfer () =
  let test_cases = [
    (Num 42, TyInt);
    (Bool true, TyBool);
    (Binop(Sum, Num 1, Num 2), TyInt);
    (If(Bool true, Num 1, Num 2), TyInt);
    (Wh(Bool true, Seq(Asg(Id "x", Num 1), Unit)), TyUnit);
    (Let("x", TyInt, Num 5, Id "x"), TyInt);
    (New (Num 10), TyRef TyInt);
    (Deref (Num 0), TyInt);
    (Seq(Unit, Num 1), TyInt);
    (Print(Num 5), TyUnit)
  ] in
  List.iter (fun (expr, expected_type) ->
      let inferred_type = typeInfer expr in
      assert (inferred_type = expected_type)
    ) test_cases;
  print_endline "All type inference tests passed!"

let main (entrada: int list) =
  (* 1. Initialize the state *)
  let mem = Array.make 100 (Unit, false) in 
  let saida = [] in

  (* 2. The loop must pass the state along in each recursive call *)
  let rec loop (e, mem, entrada, saida) =
    match small_step (e, mem, entrada, saida) with
    | (Unit, _, _, final_saida) -> List.rev final_saida (* Base case: program finished *)
    | (e', mem', entrada', saida') -> loop (e', mem', entrada', saida') (* Recursive step with new state *)
  in

  (* 3. Call the loop with the initial state and capture the result *)
  let result_list = loop (fat, mem, entrada, saida) in

  (* 4. Iterate through the result list and print each element *)
  print_endline "Output:";
  List.iter (fun my_int -> (* The value is already an int *)
      print_int my_int;      (* Print it directly *)
      print_newline ()
    ) result_list;

  test_typeInfer (); (* Run the type inference tests *)
  

  
  