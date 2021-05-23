(** val add : int64 -> int64 -> int64 **)

let rec add = Int64.add

(** val mul : int64 -> int64 -> int64 **)

let rec mul = Int64.mul

module Nat =
 struct
  (** val leb : int64 -> int64 -> bool **)

  let rec leb = (fun x y -> Int64.compare x y <= 0)
 end

(** val can_distribute : int64 -> int64 -> int64 -> bool **)

let can_distribute r b d =
  if Nat.leb b
       (mul r (add d ((fun x -> Int64.succ x) Int64.zero)))
  then Nat.leb r
         (mul b (add d ((fun x -> Int64.succ x) Int64.zero)))
  else false


let rec solve = function
  | 0 -> ()
  | n -> let (r,b,d) = Scanf.scanf "%d %d %d\n" (fun a b c -> (Int64.of_int a, Int64.of_int b,Int64.of_int c)) in
         let ans = if can_distribute r b d then "YES" else "NO" in
         print_endline ans; 
         solve (n-1)

let t = read_int();;
solve t;;
