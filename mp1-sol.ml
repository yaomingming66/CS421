(* File: ml1-sol.ml *)

open Common
  
(* Problem 1: Variable Declaration, string *)
let title = "ML 1 -- Basic OCaml"
let greetings = "Hi there."
let address = "Greetings, my friend!"
let frozen = "Do you want to build a snowman?"
let daffy = "Th, th, that's all, Folks!"

(* Problem 2: Variable Declaration, float *)
let a = 17.5
let pi = 3.14159
let e = 2.71828
let quarter = 0.25
let x = 32.7

(* Problem 3: Basic Functions with Integer Arithmetic  *)
let myFirstFun n = (n + 3) * 4
let firstFun n = (2 * n) + 5
let square n = n * n
let times_13 n = n * 13
let cube n = n * n * n

(* Problem 4: Basic Functions with Float Arithmetic and Variable Use *)
let add_a n = a +. n
let circumference r = 2.0 *. pi *. r
let divide_e_by x = e /. x
let plus_quarter_times_3 y = 3.0 *. (y +. quarter)
let square_plus_x y = (y *. y) +. x

(* Problem 5: Conditional Expressions *)
let salutations name = 
    if name = "Elsa" then print_string "Halt! Who goes there!\n"
    else print_string ("Hail, "^name^". We warmly welcome you!\n")

let hail name =
  if name = "Elsa" then print_string "Wayell, hah theya, Ayelsa!"
  else print_string ("Dear, " ^ name ^ ". I wish you the best in CS421.\n")

let welcome name =
  if name = "Elsa" then print_string "Can you come out to play?\n"
  else print_string ("Aw, come on, "^name^". We're going to have a wonderful time!\n")

let greet name =
  if name = "Elsa" then print_string "Hey Elsa, cool man!"
  else print_string ("Hello, "^name^". I hope you enjoy CS421.\n")

let salute name =
  if name = "Elsa" then print_string "What's the low-down, man?"
  else print_string ("Hey, "^name^"! Give me five, man.")

(* Problem 6: Basic Functions with Float Arithmetic *)
let rectangle_area l w = if (l < 0.0 || w < 0.0) then (-1.0) else l *. w

let diff_square_9 m n =
  if n > m
  then (n *. n) -. 9.0
  else if n < (m *. 0.5) then (m *. m) -. 9.0
  else ((m -. n) *. (m -. n)) -. 9.0

let make_bigger x y =
   if x > 0.0 then x +. y
   else if y < 1.0 then y +. 1.0
   else y *. y

let has_smallest_square m n =
    let mm = square m in
    let nn = square n in
    if mm < nn || (mm = nn && m < n) then m
    else n

let sign_times n m =
  let p = n * m in
    if p > 0 then 1
    else if p = 0 then 0
    else (-1)


