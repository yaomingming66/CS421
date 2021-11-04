(* Zone 1. Forward Recursion + Higher-Order Function Use *)

(* Problem 1 *)

let rec even_count_fr l =
  match l with [] -> 0
    | (x::xs) ->
      let ec =  even_count_fr xs
      in (if x mod 2 = 0 then 1 else 0) + ec

let even_count_fr_base = 0
let even_count_fr_rec x ec = (if x mod 2 = 0 then 1 else 0) + ec

(* Problem 2 *)
let rec remove_even list = 
    (match list with [] -> []
      | (n::rest) -> let r = remove_even rest in if n mod 2 = 0 then r else n :: r)

let remove_even_base = [];;
let remove_even_rec n r = if n mod 2 = 0 then r else n :: r;;


(*Zone 2. Forward Recursion, simple *)

(* Problem 3 *)
let rec sift p l =
    match l with [] -> ([], [])
      | (x::xs) ->
           match sift p xs
            with (tl, fl) -> if p x then (x :: tl, fl) else (tl, x :: fl);;

let sift_base = ([],[]);;
let sift_rec p x (tl, fl) = if p x then (x :: tl, fl) else (tl, x :: fl);;


(* Zone 3. Forward Recursion, two lists *)

(* Problem 4 *)
let rec apply_even_odd l f g = 
	match l with [] -> []
	| x::xs -> (f x)::(apply_even_odd xs g f);;


(*Zone 4. Tail Recursion + Higher-Order Function Use *)

(* Problem 5 *)
let even_count_tr l =
  let rec even_count_tr_aux acc_value l =
    match l with [] -> acc_value
      | (x :: xs) ->
        even_count_tr_aux
        (if x mod 2 = 0 then 1 + acc_value
         else acc_value)
          xs
  in even_count_tr_aux 0 l

let even_count_tr_start = 0
let even_count_tr_step acc_value x =
  if x mod 2 = 0 then 1 + acc_value
  else acc_value

(* Problem 6 *)
let split_sum l f =
  let rec split_sum_aux (tr,fs) lst =
    match lst with [] -> (tr,fs)
      | x::xs ->
        split_sum_aux (if f x then (tr+x,fs) else (tr,fs+x)) xs
  in split_sum_aux (0,0) l

let split_sum_start = (0,0)
let split_sum_step f (tr,fs) x = if f x then (tr+x,fs) else (tr,fs+x)

(* Problem 7 *)
let rec all_nonneg list =
  let rec all_nn b l =
    match l with [] -> b
      | (x::xs) -> all_nn (b && x > 0) xs
  in all_nn true list;;

let all_nonneg_start = true;;
let all_nonneg_step r x = r && x > 0;;

(* Problem 8 *)
let count_element l m =
  let rec count_element_aux acc_value l =
    match l with [] -> acc_value
      | (x::xs) ->
        count_element_aux
          (if x = m then acc_value + 1 else acc_value)
          xs
  in count_element_aux 0 l

let count_element_start = 0
let count_element_step m acc_value x =
  (if x = m then acc_value + 1 else acc_value)

(* Problem 9 *)
let concat sep list =
    let rec cat front_str l =
        match l with [] -> front_str
          | (str :: strs) -> cat (front_str ^ sep ^ str) strs
    in match list with [] -> ""
          | (s0 :: ss) -> s0 ^ cat "" ss;;

(* Problem 9 - alternate solution *)
let concat sep l =
  let rec concat_aux lead_str l =
    (match l with [] -> lead_str
      | (st::stl) -> concat_aux (lead_str ^ sep ^ st) stl)
  in match l with [] -> ""
    | [x] -> x
    | (x::xs) -> concat_aux x xs


(* Problem 10 *)
let rec max_index l =
    match l with [] -> []
    | x::xs ->
      let rec max_aux l cur_pos max_val max_pos =
          match l with [] -> max_pos
          | y::ys -> if y > max_val then max_aux ys (cur_pos+1) y [cur_pos]
                     else if y = max_val
                             then max_aux ys (cur_pos+1) max_val (cur_pos::max_pos)
                          else max_aux ys (cur_pos+1) max_val max_pos
      in max_aux xs 1 x [0]

