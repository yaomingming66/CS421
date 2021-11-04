open Common

(*****************************)
(****** PROBLEMS FOR ML3 *****)
(*****************************)
(***** Problem 1: Warmup (0 Points)  ******)
let consk (x, l) k = k (x :: l)

(* Other's used below
let concatk (s1, s2) k = k ( s1 ^ s2)
let string_of_intk s k = k (string_of_int s)
let truncatek r k = k (truncate r)
*)

(***** Problem 2: Basic CPS *****)
let diff_flipk p k = subk (1, p) (fun a -> mulk (a, p) (fun b -> mulk (2, b) k))

(***** Problem 3: Basic CPS *****)
let quadk (a, b, c) k =
  mulk (4, b)
    (fun u -> mulk (a, a)
      (fun v -> mulk (2, v)
        (fun w -> addk (w, u)
          (fun z -> addk (z, c) k))))

(***** Problem 4: Basic CPS *****)
let three_freezek (s, p) k =
  concatk (s, p) (fun s1 -> concatk (s1, s1) (fun r2 -> concatk (s1, r2) k))

(***** Problem 5: Basic CPS *****)
let shiftk (s, q) k =
  float_addk (q, 1.57)
    (fun r1 -> float_mulk (r1, r1)
      (fun m -> truncatek m
        (fun i -> string_of_intk i
          (fun r4 -> concatk (s, r4)
            (fun r5 -> concatk (r5, s) k)))))

(***** Problem 6a: Recursion & CPS ******)
let rec list_prod l =
  match l with [] -> 1
    | (x :: xs) ->
      let lp = list_prod xs in x * lp

(***** Problem 6b: Recursion & CPS ******)
let rec list_prodk l k =
  match l with [] -> k 1
    | (x::xs) -> list_prodk xs (fun lp -> mulk (x, lp) k)

(***** Problem 7a: Recursion & CPS *****)
let rec all_positive l =
  match l with [] -> true
    | (x::xs) -> if 0 >= x then false else all_positive xs

(***** Problem 7b: Recursion & CPS *****)
let rec all_positivek l k =
  match l with [] -> k true
    | (x :: xs) ->
      geqk (0, x) (fun b -> if b then k false else all_positivek xs k)

(***** Problem 8a: Recursion & CPS *****)
let rec even_count l =
  match l with [] -> 0
    | (x::xs) ->
      let ec =  even_count xs
      in (if x mod 2 = 0 then 1 else 0) + ec

(***** Problem 8b: Recursion & CPS *****)
let rec even_countk l k =
  match l with [] -> k 0
    | (x::xs) ->
      even_countk xs 
        (fun ec -> modk (x, 2)
          (fun m -> eqk (m, 0)
            (fun b -> if b then addk (1, ec) k else addk (0, ec) k)))

(******** Continuations for Higher-Order Functions ********)
(* Problem 9: Continuations for Higher-Order Functions*)
let rec find_all (p,l) =
  match l with [] -> []
    | x::xs -> if p x then x :: find_all (p, xs) else find_all (p, xs)

let rec find_allk (p,l) k =
  match l with [] -> k []
    | x::xs ->
      p x
        (fun b ->
          if b then find_allk (p, xs) (fun r -> consk (x, r) k)
          else find_allk (p, xs) k)

(* Another solution that is strictly forward recursive *)
let rec find_all (p,l) =
  match l with [] -> []
    | x::xs -> let r = find_all (p, xs) in if p x then x :: r else r

let rec find_allk (p,l) k =
  match l with [] -> k []
    | x::xs ->
      find_allk (p, xs)
        (fun r -> p x
          (fun b -> if b then consk (x, r) k  else  k r))
(* Problem 10: Continuations for Higher-Order Functions *)

let rec sum_all (p,l) =
  match l with [] -> 0.0
    | x::xs -> let r = sum_all (p, xs) in if p x then x +. r else r

let rec sum_allk (p,l) k =
  match l with [] -> k 0.0
    | x::xs ->
      sum_allk (p, xs)
        (fun r -> 
          p x (fun b -> if b then float_addk (x, r) k else k r))

(* Problem 11: Continuations for Higher-Order Functions *)
let rec fold_left (f,e,l) =
  match l
  with [] -> e
    | x::xs -> fold_left (f,f (e, x),xs);;

let rec fold_leftk (fk,e,l) k =
  match l
  with [] -> k e 
    | x::xs -> fk (e, x) (fun r -> fold_leftk (fk,r,xs) k);;

(* Problem 12: Continuations for Higher-Order Functions *)

let rec fold_right (f,l,e) =
  match l
  with [] -> e
    | x::xs -> f (x, fold_right (f,xs,e));;

let rec fold_rightk (f,l,e) k =
    match l with
    | [] -> k e 
    | x::xs -> fold_rightk (f,xs,e) (fun b -> f (x,b) k);;

(* Problem 13: Continuations for Higher-Order Functions *)
let rec list_compose fs = 
  match fs with [] -> 0
    | (f::more_fs) -> f(list_compose more_fs)

(*
list_compose [(fun x -> x + 1); (fun x -> x * x) ; (fun x -> x + 2)]
*)

let rec list_composek fsk k =
  match fsk with [] -> k 0
    | (fk::more_fsk) -> list_composek more_fsk (fun rv -> fk rv k)

(*
list_composek [(fun x -> addk (x, 1)); (fun x -> mulk (x, x)) ; (fun x -> addk (x, 2))]
report_int
*)

