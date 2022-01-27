
(** Specifies that chunks should have capacity [2^bits_per_digit]. *)
module type BITS_PER_DIGIT = sig
  val bits_per_digit : int (* >= 1 *)
end

(*--------------------------------------------------------------*)

module Make (B:BITS_PER_DIGIT) = struct
include B

(* Hack the type system where needed *)
let cast = Obj.magic

(* Base of the numerical representation, same thing as [chunk_size] *)
let base =
  1 lsl bits_per_digit

(* Maximal digit, e.g., [31] when using 5 bits per digit. *)
let max_digit =
  base - 1

(* Last digit of a number [n].
   For example, [2*32*32 + 3*32 + 5] has [5] for last digit. *)
let last_digit n =
  n land max_digit

(* [get_digit k n] returns the [k]-th digit of a number [n].
    For example, [2*32*32 + 3*32 + 5] has [3] for digit [k=1]. *)
let get_digit k n =
  last_digit (n lsr (k * bits_per_digit))

(* let ['a rarray] be a hack to denote the type
   ['a array array ... array] for an arbitrary number of recursively nested arrays *)
type 'a rarray = 'a array

(* Fields are made mutable to allow for some initialization patterns *)
type 'a digits = ('a rarray) array

type 'a t = {
  size : int;
  digits : 'a digits } (* a dummy type for the typechecker *)
  (* The array [digits] is actually of heterenogeous types:
      digits.(0) : 'a array
      digits.(1) : ('a array) array
      digits.(2) : (('a array) array) array
      digits.(3) : ((('a array) array) array) array
      etc. *)

let nb_digits s =
  Array.length s.digits

let length s =
  s.size

let is_empty s =
  s.size = 0

(* [tget k i a] reads the value at index [i] relative to the array [a],
   which is an array of array of ... of array of items. The outer array
   is not full, but all other nested arrays are full.
   This function involves polymorphic recursion, however it is not
   visible from the type due to the use of [Obj.magic], which is required
   for the [digits] array to typecheck. *)
let rec tget k c i =
  let d = get_digit k i in
  if k = 0
    then c.(d)
    else tget (k-1) (cast c.(d)) i

let get s i =
  assert (0 <= i && i < s.size);
  let rec aux k = (* essentially, [for k = nb_digits s - 1 downto 0 do] with a break *)
    if get_digit k i <> get_digit k s.size then begin
       tget k s.digits.(k) i
    end else aux (k-1) in
  aux (nb_digits s - 1)

let rec tset k c i x =
  let d = get_digit k i in
  if k = 0
    then Farray.set c d x
    else let r = tset (k-1) (cast c.(d)) i x in
         Farray.set c d (cast r)

let set s i x =
  assert (0 <= i && i < s.size);
  let rec aux k = (* essentially, [for k = nb_digits s - 1 downto 0 do] with a break *)
    if get_digit k i <> get_digit k s.size then begin
       let r = tset k s.digits.(k) i x in
       { s with digits = Farray.set s.digits k r }
    end else aux (k-1) in
  aux (nb_digits s - 1)

(* Hack to get [empty] of type ['a t] and not ['_a t ] *)
module type EmptySig = sig
   val empty : 'a t
end

module Empty : EmptySig = struct
  let empty = Obj.magic { size = 0; digits = [||] }
end

include Empty

(* [push_aux size digits k v] pushes an object [v] in the [k]-th digit.
   if k=0, this object is a base value, otherwise it is an array. *)
let rec push_aux (type a) (size:int) (digits:a digits) (k:int) (v:a rarray) : a digits =
  if k = Array.length digits then
    Farray.push digits [|cast v|] (* add a new leading "1" digit *)
  else begin
    let c = Farray.push digits.(k) (cast v) in
    if get_digit k size < max_digit then
      Farray.set digits k c (* increment digit without carry propagation *)
    else begin
      let digits2 = push_aux size (cast digits) (k+1) (cast c) in (* propagage carry *)
      Farray.set (cast digits2) k (cast [||]) (* update current digit to zero *)
    end
  end

let push (type a) (s:a t) (v:a) : a t =
  { size = s.size + 1;
    digits = push_aux s.size s.digits 0 (cast v) }

(* [pop_aux size digits k] returns a object stored in [k]-th digit.
   if k=0, this object is a base value, otherwise it is an array. *)
let rec pop_aux (type a) (size:int) (digits:a digits) (k:int) : a rarray * a digits =
  let d = get_digit k size in
  if d = 1 && k = Array.length digits - 1 then begin
    let c, digits2 = Farray.pop digits in (* decrement the leading digit, in case it is one *)
    let v, _ = Farray.pop c in
    (cast v), digits2
  end else begin
    let c, digits2 =
      if d > 0
        then digits.(k), digits (* decrement non-leading digit *)
        else cast (pop_aux size (cast digits) (k+1))  (* unpropagage carry *)
      in
    let v, c2 = Farray.pop c in (* extract element *)
    (cast v), Farray.set digits2 k (cast c2) (* update current digit *)
  end

let pop (type a) (s:a t) : a * a t =
  let v, digits = pop_aux s.size s.digits 0 in
  (cast v), { size = s.size - 1; digits }

(* Unoptimized implementation, not benchmarked *)
let init (type a) (n:int) (f:int->a) : a t =
  let s = ref empty in
  for i = 0 to pred n do
    s := push !s (f i);
  done;
  !s

let make n v =
  init n (fun _i -> v)

(** [titer f k a] iterates [f] over elements stored in [a],
    which is an array of ... array of arrays of base values
    with [k] degrees of nesting (possibly zero).
    All arrays involved are full. *)
let rec titer f k a : unit =
  if k = 0 then begin
    f a
  end else begin
    for i = 0 to pred base do
      titer f (k-1) (cast a.(i))
    done
 end

let iter (type a) (f:a->unit) (s:a t) : unit =
  for k = nb_digits s - 1 downto 0 do
    let d = get_digit k s.size in
    for j = 0 to pred d do
      titer (cast f) k (cast s.digits.(k).(j));
    done;
  done

let rec tprint(type a) (f:a->unit) (k:int) (v:a) : unit =
  let pr = Printf.printf in
  if k = 0 then f v else begin
    pr "[";
    Array.iter (fun w -> tprint (cast f) (k-1) w; pr " ") (cast v);
    pr "]";
  end

let print (type a) (s:a t) : unit =
  let pr = Printf.printf in
  for k = nb_digits s - 1 downto 0 do
    pr "{";
    let d = get_digit k s.size in
    for j = 0 to pred d do
      tprint(cast (fun v -> pr "%d " v)) k s.digits.(k).(j)
    done;
    pr "} ";
  done;
  pr "\n"

end

(*--------------------------------------------------------------*)

module BITS_PER_DIGIT_5 : BITS_PER_DIGIT = struct
  let bits_per_digit : int = 5
end

include Make(BITS_PER_DIGIT_5)

(*--------------------------------------------------------------*)
module Test = struct

include Make(struct
  let bits_per_digit : int = 2
end)

let test =
  let pr = Printf.printf in
  let n = 30 in

  let t : int t = empty in

  print t;

  let t = push t 1 in
  print t;
  let t = push t 2 in
  print t;
  let t = ref (empty) in

  for i = 0 to pred n do
    t := push !t i;
    print !t;
  done;

  let t = make n 0 in
  print t;
  let t = init n (fun i -> i) in
  print t;

  let t = init n (fun i -> i) in
  iter (fun i -> pr "%d " i) t;
    pr "\n";

 let t = init n (fun i -> i) in
  print t;

  for i = 0 to pred n do
    pr "%d " (get t i)
  done;
  pr "\n";

  let t = ref (init n (fun i -> i)) in
  for i = 0 to pred n do
    t := set !t i (50 + i)
  done;
  print !t;

  let t = ref (init n (fun i -> i)) in
  print !t;
  for i = 0 to pred n do
    let v,r = pop !t in
    t := r;
    pr " --> %d\n" v;
    print !t;
  done;
  pr "\n";

end
