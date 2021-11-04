(* File: ml4-sol.ml *)

open Common

let rec gather_exp_ty_substitution gamma exp tau =
    let judgment = ExpJudgment(gamma, exp, tau) in
    match exp
    with ConstExp c ->
         let tau' = const_signature c in
         (match unify [(tau, freshInstance tau')]
          with None       -> None
             | Some sigma -> Some(Proof([],judgment), sigma))
    | VarExp x -> 
      (match lookup_env gamma x with None -> None
       | Some gamma_x ->
         (match unify [(tau, freshInstance gamma_x)]
          with None       -> None
             | Some sigma -> Some(Proof([],judgment), sigma)))
    | BinOpAppExp (binop, e1,e2) ->
      let tau' = binop_signature binop in
      let tau1 = fresh() in
      let tau2 = fresh() in
      (match gather_exp_ty_substitution gamma e1 tau1
       with None -> None
       | Some(pf1, sigma1) ->
         (match gather_exp_ty_substitution (env_lift_subst sigma1 gamma) e2 tau2
          with None -> None
          | Some (pf2, sigma2) ->
            let sigma21 = subst_compose sigma2 sigma1 in
            (match unify[(monoTy_lift_subst sigma21
                          (mk_fun_ty tau1 (mk_fun_ty tau2 tau)),
                         freshInstance tau')]
             with None -> None
             | Some sigma3 -> 
               Some(Proof([pf1;pf2], judgment),subst_compose sigma3 sigma21))))
    | MonOpAppExp (monop, e1) ->
      let tau' = monop_signature monop in
      let tau1 = fresh() in
      (match gather_exp_ty_substitution gamma e1 tau1
       with None -> None
       | Some(pf, sigma) ->
         (match unify[(monoTy_lift_subst sigma (mk_fun_ty tau1 tau),
                       freshInstance tau')]
          with None -> None
          | Some subst ->
            Some(Proof([pf], judgment),
                 subst_compose subst sigma)))
    | IfExp(e1,e2,e3) ->
      (match gather_exp_ty_substitution gamma e1 bool_ty
       with None -> None
       | Some(pf1, sigma1) ->
         (match gather_exp_ty_substitution
                (env_lift_subst sigma1 gamma) e2 (monoTy_lift_subst sigma1 tau)
          with None -> None
          | Some (pf2, sigma2) ->
            let sigma21 = subst_compose sigma2 sigma1 in
            (match gather_exp_ty_substitution
                   (env_lift_subst sigma21 gamma) e3
                   (monoTy_lift_subst sigma21 tau)
             with  None -> None
             | Some(pf3, sigma3) ->
               Some(Proof([pf1;pf2;pf3], judgment), subst_compose sigma3 sigma21))))
    | FunExp(x,e) ->
      let tau1 = fresh() in
      let tau2 = fresh() in
      (match gather_exp_ty_substitution
             (ins_env gamma x (polyTy_of_monoTy tau1)) e tau2
       with None -> None
       | Some (pf, sigma) ->
         (match unify [(monoTy_lift_subst sigma tau,
                        monoTy_lift_subst sigma (mk_fun_ty tau1 tau2))]
          with None -> None
          | Some sigma1 ->
            Some(Proof([pf],judgment), subst_compose sigma1 sigma)))
    | AppExp(e1,e2) ->
      let tau1 = fresh() in
      (match gather_exp_ty_substitution gamma e1 (mk_fun_ty tau1 tau)
       with None -> None
       | Some(pf1, sigma1) ->
         (match gather_exp_ty_substitution (env_lift_subst sigma1 gamma) e2
                                           (monoTy_lift_subst sigma1 tau1)
          with None -> None
          | Some (pf2, sigma2) ->
            Some(Proof([pf1;pf2], judgment), subst_compose sigma2 sigma1)))
    | RaiseExp e ->
      (match gather_exp_ty_substitution gamma e int_ty
       with None -> None
       | Some(pf, sigma) -> Some(Proof([pf],judgment), sigma))
    | LetInExp(x,e1,e2)  -> 
       let tau1 = fresh() in
       (match gather_exp_ty_substitution gamma e1 tau1
	with None -> None
	   | Some(pf1, sigma1) -> 
	      let delta_env = make_env x (gen (env_lift_subst sigma1 gamma) 
					      (monoTy_lift_subst sigma1 tau1)) in
	      (match gather_exp_ty_substitution 
		       (sum_env delta_env (env_lift_subst sigma1 gamma)) e2
                         (monoTy_lift_subst sigma1 tau)
	       with None -> None
		  | Some (pf2,sigma2) ->
		     let sigma21 = subst_compose sigma2 sigma1 in
		     Some(Proof([pf1;pf2], judgment), sigma21)))
    | LetRecInExp(f,x,e1,e2) ->
       let tau1  = fresh() in
       let tau2 = fresh() in
       let tau1_to_tau2 = mk_fun_ty tau1 tau2 in
       (match gather_exp_ty_substitution
		(ins_env (ins_env gamma f (polyTy_of_monoTy tau1_to_tau2))
			  x (polyTy_of_monoTy tau1))
		e1 tau2
	with None -> None
	   | Some(pf1, sigma1) -> 
              let sigma1_gamma = env_lift_subst sigma1 gamma in
	      let sigma1_tau1_to_tau2 = monoTy_lift_subst sigma1 tau1_to_tau2 in
	      (match gather_exp_ty_substitution
                     (ins_env sigma1_gamma f (gen sigma1_gamma sigma1_tau1_to_tau2))
		     e2 (monoTy_lift_subst sigma1 tau)
	       with None -> None
		  | Some(pf2,sigma2) ->
		     let sigma21 = subst_compose sigma2 sigma1 in
		     Some(Proof([pf1;pf2], judgment),sigma21)))
    | TryWithExp (e,intopt1,e1, match_list) ->
      (match (gather_exp_ty_substitution gamma e tau)
       with None -> None
       | Some (pf, sigma) ->
         (match
           List.fold_left
           (fun part_result -> fun (intopti, ei) ->
            (match part_result with None -> None
             | Some (rev_pflist, comp_sigmas) ->
               (match gather_exp_ty_substitution
                      (env_lift_subst comp_sigmas gamma) ei
                      (monoTy_lift_subst comp_sigmas tau)
                with None -> None
                | Some (pfi, sigmai) ->
                  Some (pfi :: rev_pflist, subst_compose sigmai comp_sigmas))))
           (Some([pf], sigma))
           ((intopt1,e1):: match_list)
           with None -> None
           | Some (rev_pflist, comp_subst) ->
             Some(Proof(List.rev rev_pflist, judgment), comp_subst)))
