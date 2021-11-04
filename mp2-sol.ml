(* Zone 1. Pattern Matching, pairs *)

let closer_to_origin (x1, y1) (x2, y2) =
  let d1 = (x1 *. x1 +. y1 *. y1)
  and d2 = (x2 *. x2 +. y2 *. y2)
  in if d1 < d2 then (-1) else if d2 < d1 then 1 else 0

let swap_eq (x1,y1) (x2,y2) = ((x1,x2) = (y2,y1)) 

let twist ((a,b),(c,d)) = ((d,a),(c,b))

let triple_xprod (a,b,c) (x,y) =
  (((a,x),(b,x),(c,x)),((a,y),(b,y),(c,y)))

let two_funs (f, g) (x, y) = (f x, g y)

(* Zone 2. Higher-Order Functions, tuples *)
let triple_app (f,g,h) x = f(g(h x))

let same_arg_twice f x = f x x

let rev_app x f = f x

let map_triple f (a,b,c) = (f a, f b, f c)

(* Zone 3. Pattern Matching, recursion *)

let rec ackermann m n =
  if m < 0 || n < 0 then 0 else
  match (m, n) with
    (0, _) -> n + 1
  | (_, 0) -> ackermann (m - 1) 1
  | _ -> ackermann (m - 1) (ackermann m (n - 1))

let rec collatz n =
  if n <= 1 then 0 else
  if n mod 2 = 0
    then 1 + collatz (n / 2)
    else 1 + collatz (3 * n + 1)

let rec delannoy (m, n) =
  if m < 0 || n < 0 then 0 else
  match (m, n) with
    (0, 0) -> 1
  |      _ -> delannoy (m - 1, n) + delannoy (m, n - 1) + delannoy (m - 1, n - 1)

let rec naive_fibonacci n =
  if n <= 1 then 1 else naive_fibonacci (n - 1) + naive_fibonacci (n -2)

let rec sum_evens_less_eq n =
  if n <= 1 then 0 else (sum_evens_less_eq (n -2)) + (if n mod 2 = 0 then n else n -1 ) 

(* Zone 4. Basic List Recursion *)
let rec product l =
  match l with
    [] -> 1.
  | x::xs -> x *. product xs

let rec double_all l =
  match l with
    [] -> []
  | x::xs -> (2. *. x) :: double_all xs

(*Problem 11*)
let rec pair_with_all x l =
    match l with
      [] -> []
    | y::ys -> (x, y) :: pair_with_all x ys

(* Zone 5. More Complex List Recursion  *)
let rec interleave l1 l2 =
  match l1 with [] -> l2
    | (x ::xs) ->
      (match l2 with [] -> l1
        | _ -> let il = interleave l2 xs in x::il)

let rec sub_list l1 l2 =
    match l2 with [] -> true
    | (x::xs) ->
      (match l1 with [] -> false
       | (y::ys) -> if x = y then sub_list ys xs else sub_list ys l2)
