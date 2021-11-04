open Common

(* Problem 1 *)
let asMonoTy1 () = mk_fun_ty bool_ty (mk_list_ty int_ty);;
let asMonoTy2 () =
    mk_fun_ty (fresh()) (mk_fun_ty (fresh()) (mk_fun_ty (fresh()) (fresh())));;
let asMonoTy3 () = mk_fun_ty (fresh()) (mk_list_ty (mk_pair_ty (fresh()) int_ty));;
let asMonoTy4 () = mk_pair_ty string_ty (mk_fun_ty (mk_list_ty (fresh())) (fresh()));;

(* Problem 2 *)
let rec subst_fun subst m =
    match subst with [] -> TyVar m
    | (n,ty) :: more -> if n = m then ty else subst_fun more m

(* Problem 3 *)
let rec monoTy_lift_subst subst monoTy =
    match monoTy
    with TyVar m -> subst_fun subst m
    | TyConst(c, typelist) ->
      TyConst(c, List.map (monoTy_lift_subst subst) typelist)

(* Problem 4 *)
let rec occurs x ty =
    match ty
    with TyVar n -> x = n
    | TyConst(c, typelist) -> List.exists (occurs x) typelist

(* Problem 5 *)
let rec unify eqlst : substitution option =
  let rec addNewEqs lst1 lst2 acc =
    match lst1,lst2 with
      [],[] -> Some acc
    | t::tl, t'::tl' -> addNewEqs tl tl' ((t,t')::acc)
    | _ -> None
  in
  match eqlst with
    [] -> Some([])
  | (s,t)::eqs ->
    (* Delete *)
    if s = t then unify eqs
    else (match (s,t) 
    (* Decompose *)
          with (TyConst(c, tl), TyConst(c', tl')) ->
            if c=c' then (match (addNewEqs tl tl' eqs) with None -> None | Some l -> unify l)
            else None
    (* Orient *)
          | (TyConst(c, tl), TyVar(m)) -> unify ((TyVar(m), TyConst(c, tl))::eqs)
    (* Eliminate *)
          | (TyVar(n),t) ->
             if (occurs n t)
             then None
             else let eqs' =
                      List.map
                      (fun (t1,t2) ->
                           (monoTy_lift_subst [(n,t)] t1, monoTy_lift_subst [(n,t)] t2))
                      eqs
                   in (match unify eqs'
                       with None -> None
                       | Some(phi) -> Some((n, monoTy_lift_subst phi t):: phi)))

