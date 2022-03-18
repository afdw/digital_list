Load "Dep/Indexes".

Inductive array {A n} :=
  | Array : sized_list A n -> array.

Arguments array : clear implicits.

Definition array_to_list {A n} (a : array A n) :=
  let '(Array sl) := a in sized_list_to_list sl.

Theorem array_to_list_length :
  forall {A n} (a : array A n),
  length (array_to_list a) = n.
Proof.
  intros ? ? ?. destruct a. apply sized_list_to_list_length.
Qed.

Definition array_empty {A} : array A 0 := Array [||].

Definition array_single {A} x : array A 1 := Array [|x|].

Definition array_nth {A n} i (a : array A n) :=
  let '(Array sl) := a in sized_list_nth i sl.

Theorem array_nth_correct :
  forall {A n} i (a : array A n),
  array_nth i a = List.nth_error (array_to_list a) i.
Proof.
  intros ? ? ? ?. destruct a. apply sized_list_nth_correct.
Qed.

Definition array_update {A n} i x (a : array A n) :=
  let '(Array sl) := a in option_map Array (sized_list_update i x sl).

Theorem array_update_correct :
  forall {A n} i x (a : array A n),
  option_map array_to_list (array_update i x a) = list_update i x (array_to_list a).
Proof.
  intros ? ? ? ?. destruct a. unfold array_to_list, array_update. rewrite <- sized_list_update_correct.
  destruct (sized_list_update i x s); auto.
Qed.

Definition array_push {A n} x (a : array A n) : array A (S n) :=
  let '(Array sl) := a in Array (sized_list_push x sl).

Theorem array_push_correct :
  forall {A n} x (a : array A n),
  array_to_list (array_push x a) = array_to_list a ++ [x].
Proof.
  intros ? ? ? ?. destruct a. apply sized_list_push_correct.
Qed.

Definition array_pop {A n} (a : array A (S n)) : array A n * A :=
  let '(Array sl) := a in
  let '(sl0, x) := (sized_list_pop sl) in
  (Array sl0, x).

Theorem array_pop_correct :
  forall {A n} (a : array A (S n)),
  (let (a0, x) := array_pop a in array_to_list a0 ++ [x]) = array_to_list a.
Proof.
  intros ? ? ?. destruct a. unfold array_to_list, array_pop. rewrite <- sized_list_pop_correct.
  remember (let '(sl0, x) := sized_list_pop s in (Array sl0, x)) as sl0_x0. destruct sl0_x0 as (sl_0, x0).
  destruct sl_0. remember (sized_list_pop s) as sl1_x1. destruct sl1_x1 as (sl1, x1).
  injection Heqsl0_x0 as -> ->. auto.
Qed.
