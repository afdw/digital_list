Load "NonDep/Indexes".

Inductive array {A} :=
  | Array : list A -> array.

Arguments array : clear implicits.

Definition array_length {A} (a : array A) := let '(Array l) := a in length l.

Definition array_to_list {A} (a : array A) := let '(Array l) := a in l.

Theorem array_to_list_length :
  forall {A} (a : array A),
  length (array_to_list a) = array_length a.
Proof.
  intros ? ?. destruct a. auto.
Qed.

Definition array_empty {A} : array A := Array [].

Definition array_single {A} x : array A := Array [x].

Definition array_nth {A} i (a : array A) :=
  let '(Array l) := a in List.nth_error l i.

Definition array_update {A} i x (a : array A) :=
  let '(Array l) := a in option_map Array (list_update i x l).

Definition array_push {A} x (a : array A) :=
  let '(Array l) := a in Array (l ++ [x]).

Definition array_pop {A} (a : array A) : option (array A * A) :=
  let '(Array l) := a in
  option_map (fun '(l0, x) => (Array l0, x)) (list_pop l).
