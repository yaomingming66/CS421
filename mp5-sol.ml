(* File: mp2-sol.ml *)

open Common


(* Problem 1 *)
let rec import_list lst =
    match lst with [] -> ConstExp NilConst
    | (m,n) :: rest ->
      BinOpAppExp(ConsOp, BinOpAppExp(CommaOp, ConstExp (IntConst m),
                                      ConstExp (IntConst n)),
                          import_list rest)

(* Problem 2 *)
 let pair_sums =
 let ps = VarExp "pair_sums" in
 let lst = VarExp "lst" in 
 let nil = ConstExp NilConst in 
 let lsteqnil = BinOpAppExp(EqOp, lst, nil) in
 let hdlst = MonOpAppExp(HdOp,lst) in
 let tllst = MonOpAppExp(TlOp,lst) in
 let x = VarExp "x" in
 let fstx = MonOpAppExp(FstOp, x) in
 let sndx = MonOpAppExp(SndOp, x) in
 let fpluss = BinOpAppExp(IntPlusOp,fstx,sndx) in
 let app_ps = AppExp(ps, tllst) in
 let cons = BinOpAppExp(ConsOp, fpluss, app_ps) in
 let letx = LetInExp("x", hdlst, cons) in
 let ifexp = IfExp(lsteqnil, nil, letx) in
 let final = AppExp(ps, import_list [(7,1);(4,2);(6,3)]) in
LetRecInExp("pair_sums", "lst", ifexp, final)

(* Problem 2: alternate solution, without breaking out pieces *)
let pair_sums : exp =
  LetRecInExp ("pair_sums", "lst",
   IfExp (BinOpAppExp (EqOp, VarExp "lst", ConstExp NilConst),
    ConstExp NilConst,
    LetInExp ("x", MonOpAppExp (HdOp, VarExp "lst"),
     BinOpAppExp (ConsOp,
      BinOpAppExp (IntPlusOp, MonOpAppExp (FstOp, VarExp "x"),
       MonOpAppExp (SndOp, VarExp "x")),
      AppExp (VarExp "pair_sums", MonOpAppExp (TlOp, VarExp "lst"))))),
   AppExp (VarExp "pair_sums",
    BinOpAppExp (ConsOp,
     BinOpAppExp (CommaOp, ConstExp (IntConst 7), ConstExp (IntConst 1)),
     BinOpAppExp (ConsOp,
      BinOpAppExp (CommaOp, ConstExp (IntConst 4), ConstExp (IntConst 2)),
      BinOpAppExp (ConsOp,
       BinOpAppExp (CommaOp, ConstExp (IntConst 6), ConstExp (IntConst 3)),
       ConstExp NilConst)))))


(* Problem 3 *)
let rec count_const_in_exp exp = 
    match exp with VarExp x -> 0
    | ConstExp c -> 1
    | MonOpAppExp (m,e) -> count_const_in_exp e
    | BinOpAppExp (b,e1,e2) -> (count_const_in_exp e1) + (count_const_in_exp e2)
    | IfExp (e1,e2,e3) -> (count_const_in_exp e1) + (count_const_in_exp e2) + 
                          (count_const_in_exp e3)
    | AppExp (e1,e2) -> (count_const_in_exp e1) + (count_const_in_exp e2)
    | FunExp (f,e) -> count_const_in_exp e
    | LetInExp (x,e1,e2) -> (count_const_in_exp e1) + (count_const_in_exp e2)
    | LetRecInExp (f,x,e1,e2) ->
      (count_const_in_exp e1) + (count_const_in_exp e2)

(* Problem 4 *)
let rec freeVarsInExp exp =
    match exp with VarExp x -> [x]
    | ConstExp c -> []
    | MonOpAppExp (m,e) -> freeVarsInExp e
    | BinOpAppExp (b,e1,e2) -> freeVarsInExp e1 @ freeVarsInExp e2
    | IfExp (e1,e2,e3) -> freeVarsInExp e1 @ (freeVarsInExp e2 @ freeVarsInExp e3)
    | AppExp (e1,e2) -> freeVarsInExp e1 @ freeVarsInExp e2
    | FunExp (f,e) -> List.filter (fun y -> not(y = f)) (freeVarsInExp e)
    | LetInExp (x,e1,e2) -> 
       (freeVarsInExp e1) @ (List.filter (fun y -> not(y = x)) (freeVarsInExp e2))
    | LetRecInExp (f,x,e1,e2) ->
      (List.filter (fun y -> not((y = f) || (y = x))) (freeVarsInExp e1)) @
      (List.filter (fun y -> not(y = f)) (freeVarsInExp e2))

(* Problem 5 *)
let rec cps_exp e k = 
   match e with 
(*[[x]]k = k x*)
     VarExp x -> VarCPS (k, x)
(*[[c]]k = k x*)
   | ConstExp n -> ConstCPS (k, n)
(*[[~ e]]k = [[e]]_(fun r -> k (~ r)) *)
   | MonOpAppExp (m, e) ->
      let r = freshFor (freeVarsInContCPS k)
      in cps_exp e (FnContCPS (r, MonOpAppCPS (k, m, r)))
(*[[(e1 + e2)]]k = [[e2]]_ fun s -> [[e1]] _ fun r -> k (r + s)*)
   | BinOpAppExp (b, e1, e2) ->
      let v2 = freshFor (freeVarsInContCPS k @ freeVarsInExp e1)  in 
      let v1 = freshFor (v2 :: (freeVarsInContCPS k)) in 
      let e2CPS =
          cps_exp e1 (FnContCPS (v1, BinOpAppCPS(k, b, v1, v2))) in
      cps_exp e2 (FnContCPS (v2, e2CPS))
(*[[if e1 then e2 else e3]]k = [[e1]]_(fun r -> if r then [[e2]]k else [[e3]]k)*)
   | IfExp (e1,e2,e3) ->
      let r = freshFor (freeVarsInContCPS k @
                        freeVarsInExp e2 @ freeVarsInExp e3) in 
      let e2cps = cps_exp e2 k in
      let e3cps = cps_exp e3 k in 
      cps_exp e1 (FnContCPS(r, IfCPS(r, e2cps, e3cps)))
(*[[e1 e2]]k = [[e2]]_fun v2 -> [[e1]]_fun v1 -> k (v1 v2)*)
   | AppExp (e1,e2) -> 
      let v2 = freshFor (freeVarsInContCPS k @ freeVarsInExp e1) in
      let v1 = freshFor (v2 :: freeVarsInContCPS k) in
      let e1cps = cps_exp e1 (FnContCPS (v1, AppCPS(k, v1, v2))) in
      cps_exp e2 (FnContCPS (v2, e1cps))
(*[[fun x -> e]]k = k(fnk x kx -> [[e]]kx) *)
   | FunExp (x,e) ->
      let ecps = cps_exp e (ContVarCPS Kvar) in
      FunCPS (k, x, Kvar, ecps)
(*[[let x = e1 in e2]]k = [[e1]]_fun x -> [[e2]]k) *)
   | LetInExp (x,e1,e2) -> 
     let e2cps = cps_exp e2 k in
     let fx = FnContCPS (x, e2cps) in
     cps_exp e1 fx
(*[[let rec f x = e1 in e2]]k =
  (FN f -> [[e2]]_k))(FIX f. FUN x -> fn kx => [[e1]]kx) *)
   | LetRecInExp(f,x,e1,e2) -> 
     let e1cps = cps_exp e1 (ContVarCPS Kvar) in
     let e2cps = cps_exp e2 k in
     FixCPS(FnContCPS (f,e2cps),f,x,Kvar,e1cps)
