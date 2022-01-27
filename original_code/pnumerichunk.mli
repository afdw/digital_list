
(** A sequence of values of type ['a], with push-pop at one end, and random access. *)
type 'a t

(** The number of elements. *)
val length: 'a t -> int

(** [is_empty s] returns [true] iff the sequence is empty. *)
val is_empty: 'a t -> bool

(** [get s i] returns the element at index [i].
    Requires [0 <= i < length t]. *)
val get: 'a t -> int -> 'a

(** [set s i v] updates the element at index [i] with [v].
    Requires [0 <= i < length t]. *)
val set: 'a t -> int -> 'a  -> 'a t

(** [empty] returns an empty sequence, for a default value [d] *)
(*
val empty: 'a t
*)

(** [make n v] return a sequence of length [n], with copies of [v],
    with [d] a default value used for pop operations. *)
val make: int -> 'a -> 'a t

(** [init n f] return a sequence of length [n], with [f i] as [i]-th element. *)
val init: int -> (int -> 'a) -> 'a t

(** [push s v] appends the element [v] at the rear of the sequence [s]. *)
val push: 'a t -> 'a -> 'a t

(** [pop s] extracts the element at the rear of the sequence [s].
    Requires the sequence to be nonempty. *)
val pop: 'a t -> 'a * 'a t

(** [iter f s] applies [f] to each of the elements from the sequence [s]. *)
val iter: ('a -> unit) -> 'a t -> unit

