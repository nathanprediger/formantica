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

let bop_step (op: bop, e1: expr, e2: expr) : expr =
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

let empty_pos_mem (mem: int*bool array) : int =
  let i = ref 0 in
  while !i < Array.length mem && snd mem.(!i) do
    i := !i + 1
  done;

let rec small_step ( e: expr, mem: int*bool array, entrada: int list, saida: int list ) : expr * int array * int list * int list =
  match e with
| Num _ | Bool _ | Unit -> (e, mem, entrada, saida)
| Binop (op, e1, e2) : when is_val e1 && is_val e2 ->
    (bop_step(op, e1, e2), mem, entrada, saida)
| Binop (op, e1, e2) -> when is_val e1 ->
    (Binop(op, e1, small_step(e2, mem, entrada, saida)), mem, entrada, saida)
| Binop (op, e1, e2) -> 
    (Binop(op, small_step(e1, mem, entrada, saida), e2), mem, entrada, saida)
| If (e1, e2, e3) when is_val e1 ->
    (match e1 with
     | Bool true -> (e2, mem, entrada, saida)
     | Bool false -> (e3, mem, entrada, saida)
     | _ -> failwith "Condition must be a boolean")
| If (e1, e2, e3) -> 
    (If(small_step(e1, mem, entrada, saida), e2, e3), mem, entrada, saida)
| Seq (e1, e2) -> when is_unit e1 ->
    (e2, mem, entrada, saida)
| Seq (e1, e2) -> 
    (Seq(small_step(e1, mem, entrada, saida),e2), mem, entrada, saida)
| Wh (e1, e2) -> 
    (If(e1, Seq(e2, Wh(e1,e2)), (Unit, mem, entrada, saida)))
| Asg (e1, e2) -> when is_val e1 && is_val e2 ->
    (Unit, mem.(e1)<-(e2, true), entrada, saida)
| Asg (e1, e2) -> when is_val e1 ->
    (Asg(e1, small_step(e2, mem, entrada, saida)), mem, entrada, saida)
| Asg (e1, e2) -> 
    (Asg(small_step(e1, mem, entrada, saida), e2), mem, entrada, saida)
| Let (var, tp, e1, e2) when is_val e1 && is_val e2 ->  

| Let (var, tp, e1, e2) ->
    (Let(var, tp, small_step(e1, mem, entrada, saida), e2), mem, entrada, saida)
| New (e1) -> when is_val e1 ->
    let pos = empty_pos_mem mem in
    let new_mem = Array.copy mem in
    new_mem.(pos) <- (e1, true);


  
    