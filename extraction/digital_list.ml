(* Extraction start *)


type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val pow : int -> int -> int **)

let rec pow n m =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> succ 0)
    (fun m0 -> ( * ) n (pow n m0))
    m



module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
      (fun _ -> m)
      (fun p -> succ (add p m))
      n
 end

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x::t -> List.append (f x) (flat_map f t)

(** val option_flat_map : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

let option_flat_map f = function
| Some a -> f a
| None -> None

(** val sized_list_of_list : int -> 'a1 -> 'a1 list -> 'a1 array **)

let rec sized_list_of_list = 
  fun n default l ->
    let sl = Array.make n default in
    Array.blit (Array.of_list l) 0 sl 0 (min n (List.length l));
    sl


(** val sized_list_rev : int -> 'a1 array -> 'a1 array **)

let sized_list_rev = fun n l -> Array.init n (fun i -> l.(n - i - 1))

(** val sized_list_push : int -> 'a1 -> 'a1 array -> 'a1 array **)

let rec sized_list_push = 
  fun n x sl ->
    let sl0 = Array.make (n + 1) x in
    Array.blit sl 0 sl0 0 n;
    sl0


(** val sized_list_pop : int -> 'a1 array -> 'a1 array*'a1 **)

let rec sized_list_pop = fun n sl -> (Array.sub sl 0 n, sl.(n))

(** val sized_list_nth : int -> 'a1 array -> 'a1 option **)

let rec sized_list_nth = 
  fun i sl ->
    try Some sl.(i)
    with Invalid_argument _ -> None


(** val sized_list_update : int -> 'a1 -> 'a1 array -> 'a1 array option **)

let rec sized_list_update = 
  fun i x sl ->
    let sl0 = Array.copy sl in
    try
      sl0.(i) <- x;
      Some sl0
    with Invalid_argument _ -> None


(** val to_digits_func : (int*int) -> int list **)

let rec to_digits_func x =
  let n = fst x in
  let m = snd x in
  let to_digits0 = fun n0 m0 -> to_digits_func (n0,m0) in
  ((fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
     (fun _ ->
     (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
       (fun _ -> [])
       (fun _ -> [])
       m)
     (fun n0 ->
     (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
       (fun _ ->
       (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
         (fun _ -> [])
         (fun _ -> m::[])
         m)
       (fun _ ->
       (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
         (fun _ -> [])
         (fun _ -> ((mod) m n)::(to_digits0 n ((/) m n)))
         m)
       n0)
     n)

(** val to_digits : int -> int -> int list **)

let to_digits n m =
  to_digits_func (n,m)

(** val indexes_sized_list_of_index : int -> int -> int -> int array **)

let indexes_sized_list_of_index k n m =
  sized_list_rev k (sized_list_of_list k 0 (to_digits n m))

type 'a complete_leaf_tree = __

(** val complete_leaf_tree_to_list :
    int -> int -> 'a1 complete_leaf_tree -> 'a1 list **)

let rec complete_leaf_tree_to_list n d clt =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> (Obj.magic clt)::[])
    (fun d' ->
    flat_map (complete_leaf_tree_to_list n d') (Array.to_list (Obj.magic clt)))
    d

type 'a digital_list =
| DigitalListNil
| DigitalListCons of int * int * 'a complete_leaf_tree array * 'a digital_list

type 'a concrete_digital_list =
| ConcreteDigitalList of int * 'a digital_list

(** val digital_list_to_list : int -> int -> 'a1 digital_list -> 'a1 list **)

let rec digital_list_to_list n _ = function
| DigitalListNil -> []
| DigitalListCons (d0, _, sl, dl') ->
  List.append (flat_map (complete_leaf_tree_to_list n d0) (Array.to_list sl))
    (digital_list_to_list n d0 dl')

(** val concrete_digital_list_to_list :
    int -> 'a1 concrete_digital_list -> 'a1 list **)

let concrete_digital_list_to_list n = function
| ConcreteDigitalList (d, dl) -> digital_list_to_list n d dl

(** val digital_list_length : int -> int -> 'a1 digital_list -> int **)

let rec digital_list_length n d = function
| DigitalListNil -> 0
| DigitalListCons (d0, k, _, dl') ->
  (+) (( * ) (pow n (pred d)) k) (digital_list_length n d0 dl')

(** val concrete_digital_list_length :
    int -> 'a1 concrete_digital_list -> int **)

let concrete_digital_list_length n = function
| ConcreteDigitalList (d, dl) -> digital_list_length n d dl

(** val complete_leaf_tree_nth :
    int -> int -> int array -> 'a1 complete_leaf_tree -> 'a1 option **)

let rec complete_leaf_tree_nth n d isl clt =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> Some (Obj.magic clt))
    (fun d' ->
    (
    fun f_SizedListNil f_SizedListCons sl ->
      try
        let sl' = Array.sub sl 1 (Array.length sl - 1) in
        f_SizedListCons (Array.length sl - 1) sl.(0) sl'
      with Invalid_argument _ -> f_SizedListNil ()
  )
      (fun _ -> Obj.magic __ __)
      (fun _ i isl'0 ->
      option_flat_map (complete_leaf_tree_nth n d' isl'0)
        (sized_list_nth i (Obj.magic clt)))
      isl)
    d

(** val complete_leaf_tree_update :
    int -> int -> int array -> 'a1 -> 'a1 complete_leaf_tree -> 'a1
    complete_leaf_tree option **)

let rec complete_leaf_tree_update n d isl x clt =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> Some (Obj.magic x))
    (fun d' ->
    (
    fun f_SizedListNil f_SizedListCons sl ->
      try
        let sl' = Array.sub sl 1 (Array.length sl - 1) in
        f_SizedListCons (Array.length sl - 1) sl.(0) sl'
      with Invalid_argument _ -> f_SizedListNil ()
  )
      (fun _ -> Obj.magic __ __)
      (fun _ i isl'0 ->
      option_flat_map (fun clt' -> Obj.magic sized_list_update i clt' clt)
        (option_flat_map (complete_leaf_tree_update n d' isl'0 x)
          (sized_list_nth i (Obj.magic clt))))
      isl)
    d

(** val complete_leaf_tree_pop :
    int -> int -> 'a1 complete_leaf_tree -> ('a1 digital_list*'a1) option **)

let rec complete_leaf_tree_pop n d clt =
  (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
    (fun _ -> Some (DigitalListNil,(Obj.magic clt)))
    (fun d' ->
    (fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
      (fun _ -> None)
      (fun n' ->
      let sl0,x = sized_list_pop n' (Obj.magic clt) in
      Option.map (fun pat ->
        let dl',y = pat in (DigitalListCons (d', n', sl0, dl')),y)
        (complete_leaf_tree_pop (succ n') d' x))
      n)
    d

(** val digital_list_empty : int -> 'a1 digital_list **)

let digital_list_empty _ =
  DigitalListNil

(** val concrete_digital_list_empty : int -> 'a1 concrete_digital_list **)

let concrete_digital_list_empty n =
  ConcreteDigitalList (0, (digital_list_empty n))

(** val digital_list_nth_inner :
    int -> int -> int array -> 'a1 digital_list -> 'a1 option **)

let rec digital_list_nth_inner n _ isl = function
| DigitalListNil -> None
| DigitalListCons (d', k, sl, dl') ->
  ((
    fun f_SizedListNil f_SizedListCons sl ->
      try
        let sl' = Array.sub sl 1 (Array.length sl - 1) in
        f_SizedListCons (Array.length sl - 1) sl.(0) sl'
      with Invalid_argument _ -> f_SizedListNil ()
  )
     (fun _ -> Obj.magic __ __)
     (fun _ i isl'0 ->
     if (=) i k
     then digital_list_nth_inner n d' isl'0 dl'
     else option_flat_map (complete_leaf_tree_nth n d' isl'0)
            (sized_list_nth i sl))
     isl)

(** val digital_list_nth :
    int -> int -> int -> 'a1 digital_list -> 'a1 option **)

let digital_list_nth n d i dl =
  if (<) i (digital_list_length n d dl)
  then digital_list_nth_inner n d (indexes_sized_list_of_index d n i) dl
  else None

(** val concrete_digital_list_nth :
    int -> int -> 'a1 concrete_digital_list -> 'a1 option **)

let concrete_digital_list_nth n i = function
| ConcreteDigitalList (d, dl) -> digital_list_nth n d i dl

(** val digital_list_update_inner :
    int -> int -> int array -> 'a1 -> 'a1 digital_list -> 'a1 digital_list
    option **)

let rec digital_list_update_inner n _ isl x = function
| DigitalListNil -> None
| DigitalListCons (d', k, sl, dl') ->
  ((
    fun f_SizedListNil f_SizedListCons sl ->
      try
        let sl' = Array.sub sl 1 (Array.length sl - 1) in
        f_SizedListCons (Array.length sl - 1) sl.(0) sl'
      with Invalid_argument _ -> f_SizedListNil ()
  )
     (fun _ -> Obj.magic __ __)
     (fun _ i isl'0 ->
     if (=) i k
     then Option.map (fun x0 -> DigitalListCons (d', k, sl, x0))
            (digital_list_update_inner n d' isl'0 x dl')
     else Option.map (fun sl0 -> DigitalListCons (d', k, sl0, dl'))
            (option_flat_map (fun clt' -> sized_list_update i clt' sl)
              (option_flat_map (complete_leaf_tree_update n d' isl'0 x)
                (sized_list_nth i sl))))
     isl)

(** val digital_list_update :
    int -> int -> int -> 'a1 -> 'a1 digital_list -> 'a1 digital_list option **)

let digital_list_update n d i x dl =
  if (<) i (digital_list_length n d dl)
  then digital_list_update_inner n d (indexes_sized_list_of_index d n i) x dl
  else None

(** val concrete_digital_list_update :
    int -> int -> 'a1 -> 'a1 concrete_digital_list -> 'a1
    concrete_digital_list option **)

let concrete_digital_list_update n i x = function
| ConcreteDigitalList (d, dl) ->
  Option.map (fun dl0 -> ConcreteDigitalList (d, dl0))
    (digital_list_update n d i x dl)

(** val digital_list_push :
    int -> int -> 'a1 -> 'a1 digital_list -> 'a1 complete_leaf_tree
    option*'a1 digital_list **)

let rec digital_list_push n _ x = function
| DigitalListNil -> (Some (Obj.magic x)),DigitalListNil
| DigitalListCons (d', k, sl, dl') ->
  let o,dl'0 = digital_list_push n d' x dl' in
  (match o with
   | Some clt' ->
     if (<) (succ k) n
     then None,(DigitalListCons (d', (succ k), (sized_list_push k clt' sl),
            dl'0))
     else if (=) 0 n
          then None,(DigitalListCons (d', k, sl, dl'0))
          else (Some (Obj.magic sized_list_push k clt' sl)),(DigitalListCons
                 (d', 0, [||], dl'0))
   | None -> None,(DigitalListCons (d', k, sl, dl'0)))

(** val concrete_digital_list_push :
    int -> 'a1 -> 'a1 concrete_digital_list -> 'a1 concrete_digital_list **)

let concrete_digital_list_push n x = function
| ConcreteDigitalList (d, dl) ->
  let clt0_o,dl0 = digital_list_push n d x dl in
  (match clt0_o with
   | Some clt0 ->
     if (<) (succ 0) n
     then ConcreteDigitalList ((succ d), (DigitalListCons (d, (succ 0),
            ((
      fun (n, x, sl) ->
        let sl0 = Array.make (n + 1) x in
        Array.blit sl 0 sl0 1 n;
        sl0
    )
            (0, clt0, [||])), dl0)))
     else ConcreteDigitalList (d, dl)
   | None -> ConcreteDigitalList (d, dl0))

(** val digital_list_pop :
    int -> int -> 'a1 digital_list -> ('a1 digital_list*'a1) option **)

let rec digital_list_pop n _ = function
| DigitalListNil -> None
| DigitalListCons (d', k, sl, dl') ->
  (match digital_list_pop n d' dl' with
   | Some p -> let dl'0,x = p in Some ((DigitalListCons (d', k, sl, dl'0)),x)
   | None ->
     ((fun f_O f_S n -> if n = 0 then f_O () else f_S (n - 1))
        (fun _ -> None)
        (fun k' ->
        let sl0,x = sized_list_pop k' sl in
        Option.map (fun pat ->
          let dl'0,y = pat in (DigitalListCons (d', k', sl0, dl'0)),y)
          (complete_leaf_tree_pop n d' x))
        k))

(** val concrete_digital_list_pop :
    int -> 'a1 concrete_digital_list -> ('a1 concrete_digital_list*'a1) option **)

let concrete_digital_list_pop n = function
| ConcreteDigitalList (d, dl) ->
  Option.map (fun pat -> let dl0,x = pat in (ConcreteDigitalList (d, dl0)),x)
    (digital_list_pop n d dl)

(** val sample : int option*((int*int list)*int) option **)

let sample =
  let n = succ (succ (succ 0)) in
  let cdl0 =
    concrete_digital_list_push n (succ (succ (succ (succ (succ 0)))))
      (concrete_digital_list_empty n)
  in
  (concrete_digital_list_nth n 0 cdl0),(Option.map (fun pat ->
                                         let cdl1,x = pat in
                                         ((concrete_digital_list_length n
                                            cdl1),(concrete_digital_list_to_list
                                                    n cdl1)),x)
                                         (option_flat_map
                                           (concrete_digital_list_pop n)
                                           (concrete_digital_list_update n 0
                                             (succ (succ (succ (succ (succ
                                             (succ (succ 0))))))) cdl0)))


