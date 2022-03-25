(* Extraction start *)


type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val pow : int -> int -> int **)

let rec pow n m =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> succ 0)
    (fun m0 -> ( * ) n (pow n m0))
    m



(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x::t -> List.append (f x) (flat_map f t)

(** val option_flat_map : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

let option_flat_map f = function
| Some a -> f a
| None -> None

(** val to_digits_func : (int*int) -> int list **)

let rec to_digits_func x =
  let r = fst x in
  let m = snd x in
  let to_digits0 = fun r0 m0 -> to_digits_func (r0,m0) in
  ((fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
     (fun _ ->
     (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
       (fun _ -> [])
       (fun _ -> [])
       m)
     (fun n ->
     (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
       (fun _ ->
       (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
         (fun _ -> [])
         (fun _ -> m::[])
         m)
       (fun _ ->
       (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
         (fun _ -> [])
         (fun _ -> ((mod) m r)::(to_digits0 r ((/) m r)))
         m)
       n)
     r)

(** val to_digits : int -> int -> int list **)

let to_digits r m =
  to_digits_func (r,m)

type 'a sized_list =
| SizedListNil
| SizedListCons of int * 'a * 'a sized_list

(** val sized_list_repeat : int -> 'a1 -> 'a1 sized_list **)

let rec sized_list_repeat n a =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> SizedListNil)
    (fun n' -> SizedListCons (n', a, (sized_list_repeat n' a)))
    n

(** val sized_list_of_list : int -> 'a1 -> 'a1 list -> 'a1 sized_list **)

let rec sized_list_of_list n default l =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> SizedListNil)
    (fun n0 ->
    match l with
    | [] -> sized_list_repeat (succ n0) default
    | x::l' -> SizedListCons (n0, x, (sized_list_of_list n0 default l')))
    n

(** val sized_list_rev_inner :
    int -> int -> 'a1 sized_list -> 'a1 sized_list -> 'a1 sized_list **)

let rec sized_list_rev_inner _ n2 sl1 sl2 =
  match sl1 with
  | SizedListNil -> sl2
  | SizedListCons (n, x, sl1') ->
    sized_list_rev_inner n (succ n2) sl1' (SizedListCons (n2, x, sl2))

(** val sized_list_rev : int -> 'a1 sized_list -> 'a1 sized_list **)

let sized_list_rev n sl =
  sized_list_rev_inner n 0 sl SizedListNil

(** val indexes_sized_list_of_index : int -> int -> int -> int sized_list **)

let indexes_sized_list_of_index r d i =
  sized_list_rev d (sized_list_of_list d 0 (to_digits r i))

(** val array_to_list : int -> 'a1 array -> 'a1 list **)

let array_to_list = fun _ a -> Array.to_list a

(** val array_single : 'a1 -> 'a1 array **)

let array_single = fun x -> [|x|]

(** val array_nth : int -> int -> 'a1 array -> 'a1 option **)

let array_nth = 
  fun _ i a ->
    try Some a.(i)
    with Invalid_argument _ -> None


(** val array_update : int -> int -> 'a1 -> 'a1 array -> 'a1 array option **)

let array_update = 
  fun _ i x a ->
    let a0 = Array.copy a in
    try
      a0.(i) <- x;
      Some a0
    with Invalid_argument _ -> None


(** val array_push : int -> 'a1 -> 'a1 array -> 'a1 array **)

let array_push = 
  fun n x a ->
    let a0 = Array.make (n + 1) x in
    Array.blit a 0 a0 0 n;
    a0


(** val array_pop : int -> 'a1 array -> 'a1 array*'a1 **)

let array_pop = fun n a -> (Array.sub a 0 n, a.(n))

type 'a complete_leaf_tree = __

(** val complete_leaf_tree_to_list :
    int -> int -> 'a1 complete_leaf_tree -> 'a1 list **)

let rec complete_leaf_tree_to_list r d clt =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> (Obj.magic clt)::[])
    (fun d' ->
    flat_map (complete_leaf_tree_to_list r d')
      (array_to_list r (Obj.magic clt)))
    d

type 'a digital_list =
| DigitalListNil
| DigitalListCons of int * int * 'a complete_leaf_tree array * 'a digital_list

type 'a concrete_digital_list =
| ConcreteDigitalList of int * 'a digital_list

(** val digital_list_to_list : int -> int -> 'a1 digital_list -> 'a1 list **)

let rec digital_list_to_list r _ = function
| DigitalListNil -> []
| DigitalListCons (d0, k, a, dl') ->
  List.append
    (flat_map (complete_leaf_tree_to_list r d0) (array_to_list k a))
    (digital_list_to_list r d0 dl')

(** val concrete_digital_list_to_list :
    int -> 'a1 concrete_digital_list -> 'a1 list **)

let concrete_digital_list_to_list r = function
| ConcreteDigitalList (d, dl) -> digital_list_to_list r d dl

(** val digital_list_length : int -> int -> 'a1 digital_list -> int **)

let rec digital_list_length r d = function
| DigitalListNil -> 0
| DigitalListCons (d0, k, _, dl') ->
  (+) (( * ) (pow r (pred d)) k) (digital_list_length r d0 dl')

(** val concrete_digital_list_length :
    int -> 'a1 concrete_digital_list -> int **)

let concrete_digital_list_length r = function
| ConcreteDigitalList (d, dl) -> digital_list_length r d dl

(** val complete_leaf_tree_nth :
    int -> int -> int sized_list -> 'a1 complete_leaf_tree -> 'a1 option **)

let rec complete_leaf_tree_nth r d isl clt =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> Some (Obj.magic clt))
    (fun d' ->
    match isl with
    | SizedListNil -> Obj.magic __ __
    | SizedListCons (_, i, isl'0) ->
      option_flat_map (complete_leaf_tree_nth r d' isl'0)
        (array_nth r i (Obj.magic clt)))
    d

(** val complete_leaf_tree_update :
    int -> int -> int sized_list -> 'a1 -> 'a1 complete_leaf_tree -> 'a1
    complete_leaf_tree option **)

let rec complete_leaf_tree_update r d isl x clt =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> Some (Obj.magic x))
    (fun d' ->
    match isl with
    | SizedListNil -> Obj.magic __ __
    | SizedListCons (_, i, isl'0) ->
      option_flat_map (fun clt' -> Obj.magic array_update r i clt' clt)
        (option_flat_map (complete_leaf_tree_update r d' isl'0 x)
          (array_nth r i (Obj.magic clt))))
    d

(** val complete_leaf_tree_pop :
    int -> int -> 'a1 complete_leaf_tree -> ('a1 digital_list*'a1) option **)

let rec complete_leaf_tree_pop r d clt =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> Some (DigitalListNil,(Obj.magic clt)))
    (fun d' ->
    (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
      (fun _ -> None)
      (fun r' ->
      let sl0,x = array_pop r' (Obj.magic clt) in
      Option.map (fun pat ->
        let dl',y = pat in (DigitalListCons (d', r', sl0, dl')),y)
        (complete_leaf_tree_pop (succ r') d' x))
      r)
    d

(** val digital_list_empty : int -> 'a1 digital_list **)

let digital_list_empty _ =
  DigitalListNil

(** val concrete_digital_list_empty : int -> 'a1 concrete_digital_list **)

let concrete_digital_list_empty r =
  ConcreteDigitalList (0, (digital_list_empty r))

(** val digital_list_nth_inner :
    int -> int -> int sized_list -> 'a1 digital_list -> 'a1 option **)

let rec digital_list_nth_inner r _ isl = function
| DigitalListNil -> None
| DigitalListCons (d', k, a, dl') ->
  (match isl with
   | SizedListNil -> Obj.magic __ __
   | SizedListCons (_, i, isl'0) ->
     if (=) i k
     then digital_list_nth_inner r d' isl'0 dl'
     else option_flat_map (complete_leaf_tree_nth r d' isl'0)
            (array_nth k i a))

(** val digital_list_nth :
    int -> int -> int -> 'a1 digital_list -> 'a1 option **)

let digital_list_nth r d i dl =
  if (<) i (digital_list_length r d dl)
  then digital_list_nth_inner r d (indexes_sized_list_of_index r d i) dl
  else None

(** val concrete_digital_list_nth :
    int -> int -> 'a1 concrete_digital_list -> 'a1 option **)

let concrete_digital_list_nth r i = function
| ConcreteDigitalList (d, dl) -> digital_list_nth r d i dl

(** val digital_list_update_inner :
    int -> int -> int sized_list -> 'a1 -> 'a1 digital_list -> 'a1
    digital_list option **)

let rec digital_list_update_inner r _ isl x = function
| DigitalListNil -> None
| DigitalListCons (d', k, a, dl') ->
  (match isl with
   | SizedListNil -> Obj.magic __ __
   | SizedListCons (_, i, isl'0) ->
     if (=) i k
     then Option.map (fun x0 -> DigitalListCons (d', k, a, x0))
            (digital_list_update_inner r d' isl'0 x dl')
     else Option.map (fun a0 -> DigitalListCons (d', k, a0, dl'))
            (option_flat_map (fun clt' -> array_update k i clt' a)
              (option_flat_map (complete_leaf_tree_update r d' isl'0 x)
                (array_nth k i a))))

(** val digital_list_update :
    int -> int -> int -> 'a1 -> 'a1 digital_list -> 'a1 digital_list option **)

let digital_list_update r d i x dl =
  if (<) i (digital_list_length r d dl)
  then digital_list_update_inner r d (indexes_sized_list_of_index r d i) x dl
  else None

(** val concrete_digital_list_update :
    int -> int -> 'a1 -> 'a1 concrete_digital_list -> 'a1
    concrete_digital_list option **)

let concrete_digital_list_update r i x = function
| ConcreteDigitalList (d, dl) ->
  Option.map (fun x0 -> ConcreteDigitalList (d, x0))
    (digital_list_update r d i x dl)

(** val digital_list_push :
    int -> int -> 'a1 -> 'a1 digital_list -> 'a1 complete_leaf_tree
    option*'a1 digital_list **)

let rec digital_list_push r _ x = function
| DigitalListNil -> (Some (Obj.magic x)),DigitalListNil
| DigitalListCons (d', k, a, dl') ->
  let o,dl'0 = digital_list_push r d' x dl' in
  (match o with
   | Some clt' ->
     if (<) (succ k) r
     then None,(DigitalListCons (d', (succ k), (array_push k clt' a), dl'0))
     else if (=) 0 r
          then None,(DigitalListCons (d', k, a, dl'0))
          else (Some (Obj.magic array_push k clt' a)),(DigitalListCons (d',
                 0, [||], dl'0))
   | None -> None,(DigitalListCons (d', k, a, dl'0)))

(** val concrete_digital_list_push :
    int -> 'a1 -> 'a1 concrete_digital_list -> 'a1 concrete_digital_list **)

let concrete_digital_list_push r x = function
| ConcreteDigitalList (d, dl) ->
  let clt0_o,dl0 = digital_list_push r d x dl in
  (match clt0_o with
   | Some clt0 ->
     if (<) (succ 0) r
     then ConcreteDigitalList ((succ d), (DigitalListCons (d, (succ 0),
            (array_single clt0), dl0)))
     else ConcreteDigitalList (d, dl)
   | None -> ConcreteDigitalList (d, dl0))

(** val digital_list_pop :
    int -> int -> 'a1 digital_list -> ('a1 digital_list*'a1) option **)

let rec digital_list_pop r _ = function
| DigitalListNil -> None
| DigitalListCons (d', k, a, dl') ->
  (match digital_list_pop r d' dl' with
   | Some p -> let dl'0,x = p in Some ((DigitalListCons (d', k, a, dl'0)),x)
   | None ->
     ((fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
        (fun _ -> None)
        (fun k' ->
        let a0,x = array_pop k' a in
        Option.map (fun pat ->
          let dl'0,y = pat in (DigitalListCons (d', k', a0, dl'0)),y)
          (complete_leaf_tree_pop r d' x))
        k))

(** val concrete_digital_list_pop :
    int -> 'a1 concrete_digital_list -> ('a1 concrete_digital_list*'a1) option **)

let concrete_digital_list_pop r = function
| ConcreteDigitalList (d, dl) ->
  Option.map (fun pat -> let dl0,x = pat in (ConcreteDigitalList (d, dl0)),x)
    (digital_list_pop r d dl)

(** val sample : int option*((int*int list)*int) option **)

let sample =
  let r = succ (succ (succ 0)) in
  let cdl0 =
    concrete_digital_list_push r (succ (succ (succ (succ (succ 0)))))
      (concrete_digital_list_empty r)
  in
  (concrete_digital_list_nth r 0 cdl0),(Option.map (fun pat ->
                                         let cdl1,x = pat in
                                         ((concrete_digital_list_length r
                                            cdl1),(concrete_digital_list_to_list
                                                    r cdl1)),x)
                                         (option_flat_map
                                           (concrete_digital_list_pop r)
                                           (concrete_digital_list_update r 0
                                             (succ (succ (succ (succ (succ
                                             (succ (succ 0))))))) cdl0)))


