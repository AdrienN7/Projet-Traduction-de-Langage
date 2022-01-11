type typ = Bool | Int | Rat | Undefined | Pointeur of typ | Tident of string


(* ajout de la récursivité pour les pointeurs*)
let rec string_of_type t = 
  match t with
  | Bool ->  "Bool"
  | Int  ->  "Int"
  | Rat  ->  "Rat"
  | Undefined -> "Undefined"
  | Pointeur a -> "Pointeur of "^(string_of_type a)
  | Tident n ->   "Tident of"^n 


let rec est_compatible t1 t2 =
  match t1, t2 with
  | Bool, Bool -> true
  | Int, Int -> true
  | Rat, Rat -> true 
  | Pointeur t, _ -> est_compatible t t2
  | _, Pointeur t -> est_compatible t1 t
  | _ -> false 

let%test _ = est_compatible Bool Bool
let%test _ = est_compatible Int Int
let%test _ = est_compatible Rat Rat
let%test _ = not (est_compatible Int Bool)
let%test _ = not (est_compatible Bool Int)
let%test _ = not (est_compatible Int Rat)
let%test _ = not (est_compatible Rat Int)
let%test _ = not (est_compatible Bool Rat)
let%test _ = not (est_compatible Rat Bool)
let%test _ = not (est_compatible Undefined Int)
let%test _ = not (est_compatible Int Undefined)
let%test _ = not (est_compatible Rat Undefined)
let%test _ = not (est_compatible Bool Undefined)
let%test _ = not (est_compatible Undefined Int)
let%test _ = not (est_compatible Undefined Rat)
let%test _ = not (est_compatible Undefined Bool)

(* test pour pointeur *)
let%test _ = est_compatible Bool (Pointeur Bool)
let%test _ = est_compatible (Pointeur Int) Int
let%test _ = est_compatible (Pointeur Rat) (Pointeur Rat)
let%test _ = est_compatible (Pointeur (Pointeur (Pointeur Int))) (Pointeur Int)
let%test _ = not (est_compatible Bool (Pointeur Int))
let%test _ = not (est_compatible (Pointeur Int) Bool)
let%test _ = not (est_compatible (Pointeur Int) (Pointeur Rat))
let%test _ = not (est_compatible (Pointeur (Pointeur (Pointeur Bool))) (Pointeur Int))


let est_compatible_list lt1 lt2 =
  try
    List.for_all2 est_compatible lt1 lt2
  with Invalid_argument _ -> false

let%test _ = est_compatible_list [] []
let%test _ = est_compatible_list [Int ; Rat] [Int ; Rat]
let%test _ = est_compatible_list [Bool ; Rat ; Bool] [Bool ; Rat ; Bool]
let%test _ = not (est_compatible_list [Int] [Int ; Rat])
let%test _ = not (est_compatible_list [Int] [Rat ; Int])
let%test _ = not (est_compatible_list [Int ; Rat] [Rat ; Int])
let%test _ = not (est_compatible_list [Bool ; Rat ; Bool] [Bool ; Rat ; Bool ; Int])

let getTaille t =
  match t with
  | Int -> 1
  | Bool -> 1
  | Rat -> 2
  | Undefined -> 0
  | Pointeur _ -> 1
  | Tident _ -> failwith("Impossible") (* lors de la gestion de typage Tident est toujours remplacé *)
  
let%test _ = getTaille Int = 1
let%test _ = getTaille Bool = 1
let%test _ = getTaille Rat = 2
(* ajout test pour pointeur *)
let%test _ = getTaille (Pointeur Int) = 1
let%test _ = getTaille (Pointeur Bool) = 1
let%test _ = getTaille (Pointeur Rat) = 1
let%test _ = getTaille (Pointeur (Pointeur Int)) = 1
