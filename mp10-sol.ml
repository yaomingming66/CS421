open Common;;

let const_to_val c = 
  match c with
    BoolConst b   -> BoolVal b
  | IntConst i    -> IntVal i
  | FloatConst f  -> FloatVal f
  | StringConst s -> StringVal s
  | NilConst      -> ListVal []
  | UnitConst     -> UnitVal

let monOpApply op v =
  match op, v with
    HdOp, ListVal []        -> Exn 0
  | TlOp, ListVal []        -> Exn 0
  | HdOp, ListVal (v::vs)   -> v 
  | TlOp, ListVal (v::vs)   -> ListVal vs
  | FstOp, PairVal (v1, v2) -> v1
  | SndOp, PairVal (v1, v2) -> v2
  | PrintOp, StringVal s       -> (print_string s; UnitVal)
  | IntNegOp, IntVal i         -> IntVal(-i)
  | _ -> failwith "monOpApply: bad input"

let binOpApply binop (v1,v2) =
  try (
  match binop, v1, v2 with
    ConcatOp, StringVal x, StringVal y -> StringVal (x ^ y)
  | ConsOp,_, ListVal v2_lst -> ListVal (v1::v2_lst)
  | CommaOp,_,_  -> PairVal (v1, v2) 
  | EqOp,_,_  -> BoolVal (v1 = v2)
  | GreaterOp,_,_  -> BoolVal (v1 > v2)
  | _, IntVal x, IntVal y -> IntVal(
      match binop with
        IntPlusOp -> x + y
      | IntMinusOp -> x - y
      | IntTimesOp -> x * y
      | IntDivOp -> x / y
      | ModOp -> x mod y
      | _ -> failwith "binOpApply: bad input"
    )
  | _, FloatVal x, FloatVal y -> FloatVal(
      match binop with
        FloatPlusOp -> x +. y
      | FloatMinusOp -> x -. y
      | FloatTimesOp -> x *. y
      | FloatDivOp -> if y = 0.0 then raise Division_by_zero else x /. y
      | ExpoOp -> x ** y
      | _ -> failwith "binOpApply: bad input"
    )
  | _ -> failwith "binOpApply: bad input"
  ) with Division_by_zero -> Exn 0

let rec eval_exp (exp, m) = 
  match exp with 
    ConstExp t -> const_to_val t
  | VarExp x   -> (
    match lookup_mem m x with
      RecVarVal(f, y, e, m') -> Closure(y, e, ins_mem m' f (RecVarVal(f, y, e, m')))
    | v -> v
    )
  | BinOpAppExp(binop, e1, e2) -> (
    match eval_exp (e1, m) with
      Exn i -> Exn i
    | v1    ->
      match eval_exp (e2, m) with
        Exn i -> Exn i
      | v2    -> binOpApply binop (v1, v2) 
    ) 
  | MonOpAppExp(monop, e1) -> (
    match eval_exp (e1, m) with
      Exn i -> Exn i
    | v1    -> monOpApply monop v1
    )
  | AppExp(e1, e2) -> (
    match eval_exp (e1, m) with
      Exn i -> Exn i
    | v1    -> 
      match eval_exp (e2, m) with
        Exn i -> Exn i
      | v2 ->
        match v1, v2 with
        | Closure (x, e', m'), v' -> eval_exp (e', ins_mem m' x v') 
        | _ -> failwith "eval_exp: case not handled"
    )
  | LetInExp(x, e1, e2) -> (
    match eval_exp (e1, m) with
      Exn i -> Exn i
    | v     -> eval_exp (e2, ins_mem m x v)
    )
  | LetRecInExp(f, x, e1, e2) -> (eval_exp (e2, ins_mem m f (RecVarVal(f, x, e1, m))))
  | FunExp(x, e) -> Closure (x, e, m)
  | IfExp(e1, e2, e3) -> (
    match eval_exp (e1, m) with
      Exn i         -> Exn i
    | BoolVal true  -> eval_exp(e2, m)
    | BoolVal false -> eval_exp(e3, m)
    | _ -> failwith "eval_exp: bad arguments for IfExp"
  )
  | RaiseExp e -> (
    match eval_exp (e, m) with
      Exn i    -> Exn i
    | IntVal i -> Exn i
    | _        -> failwith "eval_exp: raise called on non-int"
    )
  | TryWithExp(e1, intopt1, exp1, match_list) -> (
    match eval_exp (e1, m) with
      Exn i -> (
      try let e = snd(List.find (function (Some j,_) -> j=i | (None,_) -> true)
                     ((intopt1, exp1)::match_list))
          in eval_exp (e, m)
      with Not_found -> Exn i 
      )
    | v     -> v
  )
  | _ -> failwith "eval_exp: case not handled"

let eval_dec (dec, m) =
  match dec with
    Anon e -> ((None, eval_exp (e, m)), m)
  | Let(x, e) -> (
    match eval_exp (e, m) with
      Exn i -> ((None, Exn i), m)
    | v     -> ((Some x, v), ins_mem m x v)
    )
  | LetRec(f, x, e) -> ((Some f, RecVarVal(f, x, e, m)), ins_mem m f (RecVarVal(f, x, e, m)))
  | _ -> failwith "eval_dec: case not handled"
