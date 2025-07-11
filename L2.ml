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
  | For of string * expr * expr * expr * expr 
  
      

          
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
let corpo_do_loop =
  Seq( 
    Asg(Id "y", Binop(Mul, Deref(Id "y"), Deref(Id "i"))), 
    Print(Deref(Id "i"))
  )  
    

let fat2 =
  Let("x", TyInt, Read,
      Let("y", TyRef TyInt, New (Num 1),
          Seq(
        (* for i = 1 to x+1 do y := !y * i *)
            For("i", Num 1, Binop(Sum, Id "x", Num 1), Num 1,
                corpo_do_loop
               ),
            Print(Deref(Id "y"))
          )
         )
     ) 
    
let ex1 =
  Let("x",TyRef(TyInt), New(Num(3)), 
      Seq( 
        Asg(Id("x") , Binop(Sum,Read,Num(1))),
        Print(Deref(Id("x")))   
      )
     );;

            
let ex2 =
  Let("x",TyBool, Bool(true), 
      Seq(
        Let("x",TyInt, Num(3), 
            Print(Binop(Sum,Id("x"),Num(1)))
           )
        ,
        Id("x")
      )
     )   
;;


let ex3 = If(Binop(Lt,Num(3),Num(5)),
             Bool(true),
             Unit)
;;



let ex4 =
  Let("x",TyInt,Num(4),
      Let("y",TyRef TyInt,New(Num(0)),
          Let("a",TyRef TyInt,New(Num(0)),
              Wh(Binop(Lt,Deref(Id("y")),Id("x")),
                 Seq(
                   Asg(Id("y"),Binop(Sum,Deref(Id("y")),Num(1)))
                   , 
                   Asg(Id("a"),Binop(Sum,Deref(Id("a")),Deref(Id("y"))))
                 )
                )
             )
         )
     )
;;

let ex5 =
  Let ("y", TyRef TyBool, New(Bool(true)),
       If( 
         Binop(Lt,Deref(New(Num(5))), Num(2)),
         New(Bool(false)),
         Id("y")
       )
      )
;;


let ex6 =
  Let("x",TyRef TyInt, New(Num(0)),
      Let("a",TyRef TyInt,New(Num(1)),
          Seq(
            Asg(Id("x"), Read)
            ,
            Seq(
              Wh(
                Binop(Neq, Deref(Id("x")), Num(0) )
                ,
                Seq(
                  Asg(Id("a"),Binop(Mul,Deref(Id("a")),Deref(Id("x"))))
                  ,
                  Asg(Id("x"),Binop(Sub,Deref(Id("x")),Num(1)))
                )
              ) 
              ,
              Print(Deref(Id("a")))
            )
          )
         )
     )
;;

let is_val (e: expr) : bool =
  match e with
  | Num _ | Bool _ | Unit | Id _ -> true
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
  | _ -> failwith "Invalid operation!"


let int_expr (e: expr) : int =
  match e with
  | Num n -> n
  | _ -> failwith "Not a integer"

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

  | For (var1, e1, e2, e3, e4) -> For(var1, subst_var(e1, var, v), subst_var(e2, var, v), subst_var(e3, var, v), subst_var(e4, var, v))
  
  | Let(var1, tp, e1, e2) when var=var1 -> Let(var1, tp, subst_var(e1,var,v), e2)
  | Let(var1, tp, e1, e2) -> Let(var1, tp, subst_var(e1,var,v), subst_var(e2,var,v)) 
                            

let rec small_step ((e, mem, entrada, saida) : expr * (int, expr) Hashtbl.t * int list * int list) : expr * (int, expr) Hashtbl.t * int list * int list =
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
       | _ -> failwith "Not a boolean!")
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
      let new_mem = Hashtbl.copy mem in
      Hashtbl.replace new_mem addr v;
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
      let new_mem = Hashtbl.copy mem in
      let pos = Hashtbl.length new_mem in
      Hashtbl.add new_mem pos e1;
      (Num pos, new_mem, entrada, saida)
  | New e1 ->
      let (e1', mem', entrada', saida') = small_step (e1, mem, entrada, saida) in
      (New e1', mem', entrada', saida')
  | Deref (Num addr) ->
      (Hashtbl.find mem addr, mem, entrada, saida)
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
       | [] -> failwith "Empty entry!"
       | h :: t -> (Num h, mem, t, saida))
  | For (var, e_init, e_limit, e_step, e_body) ->
      let for_ =
        Let (var, TyRef TyInt, New(e_init),
             Wh (
               Binop(Lt, Deref(Id var), e_limit),
               Seq (
                 e_body,
                 Asg (Id var, Binop(Sum, Deref(Id var), e_step))
               )
             )
            )
      in
      (for_, mem, entrada, saida)

let rec procura_var (var, contexto: string * (string * tipo) list) : tipo =
  match contexto with
  | [] -> failwith ("Unbound variable: " ^ var)
  | (v, tp) :: tl ->
      if v = var then tp
      else procura_var (var, tl)

let rec typeInfer (e, contexto: expr * (string * tipo) list) : tipo =
  match e with
  | Id var -> procura_var (var, contexto)
  | Num _ -> TyInt
  | Bool _ -> TyBool
  | Binop(op, e1, e2) ->
      let t1 = typeInfer (e1, contexto) in
      let t2 = typeInfer (e2, contexto) in
      (match op with
       | Sum | Sub | Mul | Div -> if t1 = TyInt && t2 = TyInt then TyInt else failwith "Type error in arithmetic operation"
       | Eq | Neq | Lt | Gt -> if t1 = TyInt && t2 = TyInt then TyBool else failwith "Type error in relational operation"
       | And | Or -> if t1 = TyBool && t2 = TyBool then TyBool else failwith "Type error in logical operation")
  | If (e1, e2, e3) ->
      let t1 = typeInfer (e1, contexto) in        
      let t2 = typeInfer (e2, contexto) in
      let t3 = typeInfer (e3, contexto) in
      if t1 = TyBool && t2 = t3 then t2
      else failwith "Type error in if expression"
  | Wh (e1, e2) ->
      let t1 = typeInfer (e1, contexto) in  
      let t2 = typeInfer (e2, contexto) in
      if t1 = TyBool && t2 = TyUnit then TyUnit
      else failwith "Type error in while expression"
  | Asg (e1, e2) ->
      let t1 = typeInfer (e1, contexto) in
      let t2 = typeInfer (e2, contexto) in
      (match t1 with
       | TyRef t when t = t2 -> TyUnit
       | _ -> failwith "Type error in assignment")
  | Let (var, tp, e1, e2) ->
      let t1 = typeInfer (e1, contexto) in
      if t1 = tp then
        let novo_contexto = (var, tp) :: contexto in
        typeInfer (e2, novo_contexto)
      else
        failwith "Type error in let binding"
  | New e1 ->
      let t1 = typeInfer (e1, contexto) in
      TyRef t1
  | Deref e1 -> 
      let t1 = typeInfer (e1, contexto) in
      (match t1 with
       | TyRef t -> t
       | _ -> failwith "Type error in dereference") 
  | Unit -> TyUnit
  | Seq (e1, e2) ->
      let t1 = typeInfer (e1, contexto) in
      let t2 = typeInfer (e2, contexto) in
      if t1 = TyUnit then t2 else failwith "Type error in sequence"
  | Read -> TyInt
  | Print e1 ->
      let t1 = typeInfer (e1, contexto) in
      if t1 = TyInt then TyUnit else failwith "Type error in print"
  | For (var, e_init, e_limit, e_step, e_body) ->
      let t_init = typeInfer(e_init, contexto) in
      let t_limit = typeInfer(e_limit, contexto) in
      let t_step = typeInfer(e_step, contexto) in

      if t_init = TyInt && t_limit = TyInt && t_step = TyInt then
        let new_contexto = (var, TyRef TyInt) :: contexto in
        let t_body = typeInfer(e_body, new_contexto) in

        if t_body = TyUnit then TyUnit
        else failwith "Type error: For loop body must return unit"
      else
        failwith "Type error: For loop parameters (init, limit, step) must be integers"  
let test_typeInfer () =
  let test_cases = [
    (Num 42, TyInt);
    (Bool true, TyBool);
    (Binop(Sum, Num 1, Num 2), TyInt);
    (If(Bool true, Num 1, Num 2), TyInt);
    (Let("x", TyInt, Num 5, Id "x"), TyInt);
    (New(Num 10), TyRef TyInt);
    (Seq(Unit, Num 1), TyInt);
    (Print(Num 1), TyUnit)
  ] in
  List.iter (fun (expr, expected_type) ->
      let inferred_type = typeInfer (expr, []) in
      assert (inferred_type = expected_type)
    ) test_cases;
  print_endline "All type inference tests passed!"

let valor_para_string (v: expr) : string =
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | _ -> failwith "posicao da memoria com valor invalido"

(* Itera sobre a hashtable e imprime o estado da memória *)
let print_mem (mem: (int, expr) Hashtbl.t) : unit =
  print_endline " Memoria";
  if Hashtbl.length mem = 0 then
    print_endline "vazia"
  else
    (* A função iter aplica a função anônima a cada par (chave, valor) na tabela *)
    Hashtbl.iter (fun endereco valor ->
        Printf.printf " mem[%d] -> %s\n" endereco (valor_para_string valor)
      ) mem;
;;

let big_step ((e, mem, entrada, saida) : expr * (int, expr) Hashtbl.t * int list * int list) : (expr * (int, expr) Hashtbl.t * int list * int list) =
  let rec loop (e_atual, mem_atual, entrada_atual, saida_atual) =
    if is_val e_atual then
      (e_atual, mem_atual, entrada_atual, saida_atual)
    else
      let (e_seg, mem_seg, entrada_seg, saida_seg) = small_step(e_atual, mem_atual, entrada_atual, saida_atual) in
      loop(e_seg, mem_seg, entrada_seg, saida_seg)
  in

  let (_, mem_final, _, _) as resultado_final =
    loop (e, mem, entrada, saida)
  in

  print_mem mem_final;

  resultado_final
;;
  
let main (entrada: int list) =

  let mem = Hashtbl.create 0 in 
  let saida = [] in

  let rec loop (e, mem, entrada, saida) =
    match small_step (e, mem, entrada, saida) with
    | (Unit, _, _, final_saida) -> List.rev final_saida 
    | (e', mem', entrada', saida') -> loop (e', mem', entrada', saida') 
  in


  let result_list = loop (fat2, mem, entrada, saida) in

  
  print_endline "Output:";
  List.iter (fun my_int -> 
      print_int my_int;      
      print_newline ()
    ) result_list;

  test_typeInfer (); 
  
  