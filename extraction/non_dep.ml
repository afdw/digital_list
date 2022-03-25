(* Extraction start *)


(** val pow : int -> int -> int **)

let rec pow n m =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> succ 0)
    (fun m0 -> ( * ) n (pow n m0))
    m



(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x::l' -> List.append (rev l') (x::[])

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x::t -> List.append (f x) (flat_map f t)

(** val repeat : 'a1 -> int -> 'a1 list **)

let rec repeat x n =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> [])
    (fun k -> x::(repeat x k))
    n

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

(** val pad_list : int -> 'a1 -> 'a1 list -> 'a1 list **)

let rec pad_list r default l =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> [])
    (fun _ ->
    match l with
    | [] -> repeat default r
    | x::l' -> x::(pad_list (pred r) default l'))
    r

(** val indexes_list_of_index : int -> int -> int -> int list **)

let indexes_list_of_index r d i =
  rev (pad_list d 0 (to_digits r i))

(** val array_length : 'a1 array -> int **)

let array_length = Array.length

(** val array_to_list : 'a1 array -> 'a1 list **)

let array_to_list = Array.to_list

(** val array_single : 'a1 -> 'a1 array **)

let array_single = fun x -> [|x|]

(** val array_nth : int -> 'a1 array -> 'a1 option **)

let array_nth = 
  fun i a ->
    try Some a.(i)
    with Invalid_argument _ -> None


(** val array_update : int -> 'a1 -> 'a1 array -> 'a1 array option **)

let array_update = 
  fun i x a ->
    let a0 = Array.copy a in
    try
      a0.(i) <- x;
      Some a0
    with Invalid_argument _ -> None


(** val array_push : 'a1 -> 'a1 array -> 'a1 array **)

let array_push = 
  fun x a ->
    let n = Array.length a in
    let a0 = Array.make (n + 1) x in
    Array.blit a 0 a0 0 n;
    a0


(** val array_pop : 'a1 array -> ('a1 array*'a1) option **)

let array_pop = 
  fun a ->
    let n = Array.length a in
    if n = 0
    then None
    else Some (Array.sub a 0 (n - 1), a.(n - 1))


type 'a leaf_tree =
| LeafTreeLeaf of 'a
| LeafTreeInternalNode of 'a leaf_tree array

(** val leaf_tree_to_list : 'a1 leaf_tree -> 'a1 list **)

let rec leaf_tree_to_list = function
| LeafTreeLeaf x -> x::[]
| LeafTreeInternalNode a -> flat_map leaf_tree_to_list (array_to_list a)

type 'a digital_list =
| DigitalListNil
| DigitalListCons of 'a leaf_tree array * 'a digital_list

type 'a concrete_digital_list =
| ConcreteDigitalList of int * 'a digital_list

(** val digital_list_to_list : int -> int -> 'a1 digital_list -> 'a1 list **)

let rec digital_list_to_list r d = function
| DigitalListNil -> []
| DigitalListCons (a, dl') ->
  List.append (flat_map leaf_tree_to_list (array_to_list a))
    (digital_list_to_list r (pred d) dl')

(** val concrete_digital_list_to_list :
    int -> 'a1 concrete_digital_list -> 'a1 list **)

let concrete_digital_list_to_list r = function
| ConcreteDigitalList (d, dl) -> digital_list_to_list r d dl

(** val digital_list_length : int -> int -> 'a1 digital_list -> int **)

let rec digital_list_length r d = function
| DigitalListNil -> 0
| DigitalListCons (a, dl') ->
  (+) (( * ) (pow r (pred d)) (array_length a))
    (digital_list_length r (pred d) dl')

(** val concrete_digital_list_length :
    int -> 'a1 concrete_digital_list -> int **)

let concrete_digital_list_length r = function
| ConcreteDigitalList (d, dl) -> digital_list_length r d dl

(** val complete_leaf_tree_nth :
    int -> int list -> 'a1 leaf_tree -> 'a1 option **)

let rec complete_leaf_tree_nth d il lt =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ ->
    match lt with
    | LeafTreeLeaf x -> Some x
    | LeafTreeInternalNode _ -> None)
    (fun d' ->
    match il with
    | [] -> None
    | i::il' ->
      (match lt with
       | LeafTreeLeaf _ -> None
       | LeafTreeInternalNode a ->
         option_flat_map (complete_leaf_tree_nth d' il') (array_nth i a)))
    d

(** val complete_leaf_tree_update :
    int -> int list -> 'a1 -> 'a1 leaf_tree -> 'a1 leaf_tree option **)

let rec complete_leaf_tree_update d il x lt =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> Some (LeafTreeLeaf x))
    (fun d' ->
    match il with
    | [] -> None
    | i::il' ->
      (match lt with
       | LeafTreeLeaf _ -> None
       | LeafTreeInternalNode a ->
         Option.map (fun x0 -> LeafTreeInternalNode x0)
           (option_flat_map (fun lt' -> array_update i lt' a)
             (option_flat_map (complete_leaf_tree_update d' il' x)
               (array_nth i a)))))
    d

(** val complete_leaf_tree_pop :
    int -> 'a1 leaf_tree -> ('a1 digital_list*'a1) option **)

let rec complete_leaf_tree_pop d lt =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ ->
    match lt with
    | LeafTreeLeaf x -> Some (DigitalListNil,x)
    | LeafTreeInternalNode _ -> None)
    (fun d' ->
    match lt with
    | LeafTreeLeaf _ -> None
    | LeafTreeInternalNode a ->
      option_flat_map (fun pat ->
        let sl0,x = pat in
        Option.map (fun pat0 ->
          let dl',y = pat0 in (DigitalListCons (sl0, dl')),y)
          (complete_leaf_tree_pop d' x)) (array_pop a))
    d

(** val digital_list_empty : int -> 'a1 digital_list **)

let digital_list_empty _ =
  DigitalListNil

(** val concrete_digital_list_empty : int -> 'a1 concrete_digital_list **)

let concrete_digital_list_empty r =
  ConcreteDigitalList (0, (digital_list_empty r))

(** val digital_list_nth_inner :
    int -> int list -> 'a1 digital_list -> 'a1 option **)

let rec digital_list_nth_inner d il = function
| DigitalListNil -> None
| DigitalListCons (a, dl') ->
  (match il with
   | [] -> None
   | i::il' ->
     if (=) i (array_length a)
     then digital_list_nth_inner (pred d) il' dl'
     else option_flat_map (complete_leaf_tree_nth (pred d) il')
            (array_nth i a))

(** val digital_list_nth :
    int -> int -> int -> 'a1 digital_list -> 'a1 option **)

let digital_list_nth r d i dl =
  if (<) i (digital_list_length r d dl)
  then digital_list_nth_inner d (indexes_list_of_index r d i) dl
  else None

(** val concrete_digital_list_nth :
    int -> int -> 'a1 concrete_digital_list -> 'a1 option **)

let concrete_digital_list_nth r i = function
| ConcreteDigitalList (d, dl) -> digital_list_nth r d i dl

(** val digital_list_update_inner :
    int -> int list -> 'a1 -> 'a1 digital_list -> 'a1 digital_list option **)

let rec digital_list_update_inner d il x = function
| DigitalListNil -> None
| DigitalListCons (a, dl') ->
  (match il with
   | [] -> None
   | i::il' ->
     if (=) i (array_length a)
     then Option.map (fun x0 -> DigitalListCons (a, x0))
            (digital_list_update_inner (pred d) il' x dl')
     else Option.map (fun a0 -> DigitalListCons (a0, dl'))
            (option_flat_map (fun clt' -> array_update i clt' a)
              (option_flat_map (complete_leaf_tree_update (pred d) il' x)
                (array_nth i a))))

(** val digital_list_update :
    int -> int -> int -> 'a1 -> 'a1 digital_list -> 'a1 digital_list option **)

let digital_list_update r d i x dl =
  if (<) i (digital_list_length r d dl)
  then digital_list_update_inner d (indexes_list_of_index r d i) x dl
  else None

(** val concrete_digital_list_update :
    int -> int -> 'a1 -> 'a1 concrete_digital_list -> 'a1
    concrete_digital_list option **)

let concrete_digital_list_update r i x = function
| ConcreteDigitalList (d, dl) ->
  Option.map (fun x0 -> ConcreteDigitalList (d, x0))
    (digital_list_update r d i x dl)

(** val digital_list_push :
    int -> int -> 'a1 -> 'a1 digital_list -> 'a1 leaf_tree option*'a1
    digital_list **)

let rec digital_list_push r d x = function
| DigitalListNil -> (Some (LeafTreeLeaf x)),DigitalListNil
| DigitalListCons (a, dl') ->
  let o,dl'0 = digital_list_push r (pred d) x dl' in
  (match o with
   | Some clt' ->
     if (<) (succ (array_length a)) r
     then None,(DigitalListCons ((array_push clt' a), dl'0))
     else (Some (LeafTreeInternalNode (array_push clt' a))),(DigitalListCons
            ([||], dl'0))
   | None -> None,(DigitalListCons (a, dl'0)))

(** val concrete_digital_list_push :
    int -> 'a1 -> 'a1 concrete_digital_list -> 'a1 concrete_digital_list **)

let concrete_digital_list_push r x = function
| ConcreteDigitalList (d, dl) ->
  let clt0_o,dl0 = digital_list_push r d x dl in
  (match clt0_o with
   | Some clt0 ->
     ConcreteDigitalList ((succ d), (DigitalListCons ((array_single clt0),
       dl0)))
   | None -> ConcreteDigitalList (d, dl0))

(** val digital_list_pop :
    int -> int -> 'a1 digital_list -> ('a1 digital_list*'a1) option **)

let rec digital_list_pop r d = function
| DigitalListNil -> None
| DigitalListCons (a, dl') ->
  (match digital_list_pop r (pred d) dl' with
   | Some p -> let dl'0,x = p in Some ((DigitalListCons (a, dl'0)),x)
   | None ->
     option_flat_map (fun pat ->
       let a0,x = pat in
       Option.map (fun pat0 ->
         let dl'0,y = pat0 in (DigitalListCons (a0, dl'0)),y)
         (complete_leaf_tree_pop (pred d) x)) (array_pop a))

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


