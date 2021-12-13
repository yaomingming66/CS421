(* File: solution.ml *)

open Common;;

let rec match_lookup l n =
    match l with [] -> None
    | (Some m, v)::more -> if n = m then Some v else match_lookup more n
    | (None, v)::_ -> Some v

let rec app_exn_handler_cont env ce n =
    match ce with EmptyExnContCPS -> UncaughtException n
    |  ExnContVarCPS i ->
      (match lookup_exn_cont env i with None -> Failed
       | Some (ke',env') -> app_exn_handler_cont env' ke' n)
    | UpdateExnContCPS (handler, ce') -> 
      (match match_lookup handler n with
         None -> app_exn_handler_cont env ce' n
       | Some ecps -> Intermediate(env, ecps))

let rec app_cont_to_value env k v =
    match k with ContVarCPS Kvar ->
     (match lookup_cont env Kvar with None -> Failed
      | Some (k',env') -> app_cont_to_value env' k' v)
    | FnContCPS (y, ec) -> Intermediate(ValueBinding(y,v)::env, ec)
    | ExnMatch ke ->
      (match v with IntVal n -> app_exn_handler_cont env ke n
       | _ -> Failed)
    | External -> Final v

let rec one_step_exp_cps_eval env exp_cps =
  match exp_cps with ConstCPS (k,c) ->
    app_cont_to_value env k (const_to_val c)
  | VarCPS(k, x) ->
     (match lookup_value env x with None -> Failed
      | Some v -> app_cont_to_value env k v)
  | MonOpAppCPS (k, monop, x, ke) ->
    (match lookup_value env x with None -> Failed
     | Some u ->
      (match monOpApply monop u with Exn n ->
        app_exn_handler_cont env ke n
       | Value v -> app_cont_to_value env k v))
  | BinOpAppCPS (k, binop, x, y, ke) -> 
   (match (lookup_value env x, lookup_value env y) with (Some w, Some u) ->
    (match binOpApply binop w u with Exn n ->
      app_exn_handler_cont env ke n
     | Value v -> app_cont_to_value env k v)
    | _ -> Failed)
  | IfCPS (b, e1, e2) ->
    (match lookup_value env b with
       Some (BoolVal true) -> Intermediate(env, e1)
     | Some (BoolVal false) -> Intermediate(env, e2)
     | _ -> Failed)
  | FunCPS (k, x, Kvar, i, ecps) ->
    app_cont_to_value env k
     (CPSClosureVal(x, Kvar, i, ecps, env))
  | FixCPS (k, f, x, Kvar, i, ecps) ->
    app_cont_to_value env k
     (CPSRecClosureVal(f, x, Kvar, i, ecps, env))
  | AppCPS (k, f, x, ke) ->
    (match lookup_value env f
     with Some(CPSClosureVal(y, Kvar, i, ecps, env')) ->
      (match lookup_value env x with None -> Failed
       | Some v -> 
         Intermediate
         ((ValueBinding(y, v) :: ContBinding(Kvar,(k,env)) ::
           ExnContBinding (i,(ke, env)) :: env'), ecps))
     | Some(CPSRecClosureVal(g, y, Kvar, i, ecps, env')) ->
      (match lookup_value env x with None -> Failed
       | Some v -> 
         Intermediate
         ((ValueBinding (y, v) ::
           ValueBinding (g, CPSRecClosureVal (g, y, Kvar, i, ecps, env')) ::
           ContBinding (Kvar,(k,env)) ::
           ExnContBinding (i,(ke, env)) :: env'), ecps))
     | _ -> Failed)
