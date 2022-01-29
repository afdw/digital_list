type 'a concrete_digital_list
val concrete_digital_list_to_list : int -> 'a concrete_digital_list -> 'a list
val concrete_digital_list_length : int -> 'a concrete_digital_list -> int
val concrete_digital_list_empty : int -> 'a concrete_digital_list
val concrete_digital_list_nth : int -> int -> 'a concrete_digital_list -> 'a option
val concrete_digital_list_update : int -> int -> 'a -> 'a concrete_digital_list -> 'a concrete_digital_list option
val concrete_digital_list_push : int -> 'a -> 'a concrete_digital_list -> 'a concrete_digital_list
val concrete_digital_list_pop : int -> 'a concrete_digital_list -> ('a concrete_digital_list * 'a) option
