(*
Abbreviations used:
- red - a reduction lemma
- sl - a sized_list
- isl - a sized_list of indexes (digits of the original index)
- a - an array
- clt - a complete_leaf_tree
- dl - a digital_list
- cdl - a concrete_digital_list
*)

Require Coq.Program.Wf.
Require Import Coq.Program.Equality.
Require Import Lia.
Import EqNotations.
Require Coq.Lists.List.
Import List.ListNotations.

Open Scope list_scope.

Ltac unrew :=
  first [
    rewrite <- (Eqdep_dec.eq_rect_eq_dec PeanoNat.Nat.eq_dec) |
    unfold eq_rect_r, eq_rect;
    match goal with
      | [ |- context[match ?unrew_eq with eq_refl => _ end] ] =>
        let unrew_eq_id := fresh "unrew_eq" in
        let unrew_eq_eqn_id := fresh "unrew_eq_eqn" in
        remember unrew_eq as unrew_eq_id eqn:unrew_eq_eqn_id;
        clear unrew_eq_eqn_id;
        destruct unrew_eq_id
    end
  ].

Definition nat_computational_eq {m n} (opaque_eq: m = n) : m = n :=
  match PeanoNat.Nat.eq_dec m n with
  | left transparent_eq => transparent_eq
  | right neq => False_rect _ (neq opaque_eq)
  end.

Theorem nat_strong_induction :
  forall (P : nat -> Prop),
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
  intros ? ? ?. cut (forall m, m <= n -> P m).
  - intros ?. specialize (H0 n). apply H0. lia.
  - induction n.
    + intros ? ?. apply H. intros k ?. lia.
    + intros ? ?. apply H. intros k ?. apply IHn. lia.
Qed.

Theorem option_map_ext :
  forall {A B} (f g : A -> B) o,
  (forall a, f a = g a) ->
  option_map f o = option_map g o.
Proof.
  intros ? ? ? ? ? ?. destruct o; simpl; f_equal; auto.
Qed.

Theorem option_map_option_map :
  forall {A B C} (f : A -> B) (g : B -> C) o,
  option_map g (option_map f o) = option_map (Basics.compose g f) o.
Proof.
  intros ? ? ? ? ? ?. destruct o; auto.
Qed.

Definition option_flat_map {A B} (f : A -> option B) (o : option A) : option B :=
  match o with
  | None => None
  | Some a => f a
  end.

Theorem option_flat_map_ext :
  forall {A B} (f g : A -> option B) o,
  (forall a, f a = g a) ->
  option_flat_map f o = option_flat_map g o.
Proof.
  intros ? ? ? ? ? ?. destruct o; simpl; auto.
Qed.

Theorem option_map_flat_option_map :
  forall {A B C} (f : A -> B) (g : B -> option C) o,
  option_flat_map g (option_map f o) = option_flat_map (Basics.compose g f) o.
Proof.
  intros ? ? ? ? ? ?. destruct o; auto.
Qed.

Theorem option_map_option_flat_map :
  forall {A B C} (f : A -> option B) (g : B -> C) o,
  option_map g (option_flat_map f o) = option_flat_map (fun x => option_map g (f x)) o.
Proof.
  intros ? ? ? ? ? ?. destruct o; auto.
Qed.

Lemma list_nth_error_nil : forall {A} i, List.nth_error ([] : list A) i = None.
Proof.
  intros ? ?. destruct i; auto.
Qed.

Lemma list_nth_error_cons :
  forall {A} x (l : list A) i,
  i <> 0 ->
  List.nth_error (x :: l) i = List.nth_error l (pred i).
Proof.
  intros ? ? ? ? ?. destruct i.
  - lia.
  - auto.
Qed.

Fixpoint list_update {A} i x (l : list A) {struct i} :=
  match l, i with
  | [], _ => None
  | y :: l', 0 => Some (x :: l')
  | y :: l', S i' => option_map (fun l0 => y :: l0) (list_update i' x l')
  end.

Section Example.

Compute list_update 2 10 [0; 1; 2; 3; 4; 5].
Compute list_update 100 10 [0; 1; 2; 3; 4; 5].

End Example.

Lemma list_update_nil : forall {A} i x, list_update i x ([] : list A) = None.
Proof.
  intros ? ? ?. destruct i; auto.
Qed.

Lemma list_update_cons :
  forall {A} x (l : list A) i y,
  i <> 0 ->
  list_update i y (x :: l) = option_map (cons x) (list_update (pred i) y l).
Proof.
  intros ? ? ? ? ? ?. destruct i.
  - lia.
  - auto.
Qed.

Theorem list_update_app_1 :
  forall {A} i x (l1 l2 : list A),
  i < length l1 ->
  list_update i x (l1 ++ l2) = option_map (fun l0 => l0 ++ l2) (list_update i x l1).
Proof.
  intros ? ? ?. induction i; intros ? ? ?.
  - simpl. destruct l1.
    + simpl in H. lia.
    + simpl. auto.
  - simpl. destruct l1.
    + simpl in H. lia.
    + simpl. simpl in H. rewrite IHi; try lia. rewrite ? option_map_option_map. auto.
Qed.

Theorem list_update_app_2 :
  forall {A} i x (l1 l2 : list A),
  length l1 <= i ->
  list_update i x (l1 ++ l2) = option_map (fun l0 => l1 ++ l0) (list_update (i - length l1) x l2).
Proof.
  intros ? ? ?. induction i; intros ? ? ?.
  - simpl. destruct l1.
    + simpl. destruct l2; auto.
    + simpl in H. lia.
  - simpl. destruct l1.
    + simpl. destruct l2.
      * auto.
      * rewrite option_map_option_map. auto.
    + simpl. simpl in H. rewrite IHi; try lia. rewrite ? option_map_option_map. auto.
Qed.

Theorem list_update_list_map :
  forall {A B} (f : A -> B) i x l,
  list_update i (f x) (List.map f l) = option_map (List.map f) (list_update i x l).
Proof.
  intros ? ? ? ? ?. induction i; intros ?.
  - simpl. destruct l; auto.
  - simpl. destruct l.
    + auto.
    + simpl. rewrite IHi. rewrite ? option_map_option_map. auto.
Qed.

Theorem list_update_None :
  forall {A} i x (l : list A),
  list_update i x l = None <-> length l <= i.
Proof.
  intros ? ? ?. induction i; intros ?.
  - destruct l; simpl; intuition (discriminate || lia).
  - destruct l.
    + simpl. intuition (auto || lia).
    + simpl. specialize (IHi l). split.
      * intros. destruct (list_update i x l); intuition (discriminate || lia).
      * intros. apply le_S_n in H. destruct (list_update i x l).
        -- apply IHi in H. discriminate.
        -- apply IHi. auto.
Qed.

Fixpoint list_pop {A} (l : list A) : option (list A * A) :=
  match l with
  | [] => None
  | [x] => Some ([], x)
  | x :: l' => option_map (fun '(l'0, y) => (x :: l'0, y)) (list_pop l')
  end.

Theorem list_pop_app_Some :
  forall {A} x (l1 l2 l20 : list A),
  list_pop l2 = Some (l20, x) ->
  list_pop (l1 ++ l2) = Some (l1 ++ l20, x).
Proof.
  intros ? ? ?. induction l1; intros ? ? ?.
  - auto.
  - simpl. rewrite (IHl1 l2 l20); auto. simpl. destruct l1.
    + simpl. destruct l2.
      * discriminate.
      * auto.
    + auto.
Qed.

Lemma flat_map_length_constant_length_for_type :
  forall {A B} (f : A -> list B) l k,
  (forall a, length (f a) = k) ->
  length (List.flat_map f l) = length l * k.
Proof.
  intros ? ? ? ? ? ?. induction l.
  - auto.
  - simpl. rewrite List.app_length. auto.
Qed.

Lemma flat_map_list_nth_error_constant_length_for_type :
  forall {A B} (f : A -> list B) l k i j,
  (forall a, length (f a) = k) ->
  j < k ->
  List.nth_error (List.flat_map f l) (i * k + j) =
    option_flat_map (fun l0 => List.nth_error (f l0) j) (List.nth_error l i).
Proof.
  intros ? ? ? ? ? ? ? ? ?. generalize dependent i. induction l; intros ?.
  - simpl. do 2 rewrite list_nth_error_nil. auto.
  - simpl. specialize (H a). destruct (PeanoNat.Nat.eqb_spec i 0).
    + subst i. clear IHl. rewrite List.nth_error_app1; try lia. simpl. destruct (List.nth_error (f a) j); auto.
    + rewrite List.nth_error_app2; try nia.
      replace (i * k + j - length (f a)) with ((pred i) * k + j) by nia.
      rewrite IHl; clear IHl. rewrite list_nth_error_cons; auto.
Qed.

Lemma flat_map_list_update_constant_length_for_type :
  forall {A B} (f : A -> list B) l k i j x,
  (forall a, length (f a) = k) ->
  j < k ->
  list_update (i * k + j) x (List.flat_map f l) =
    option_map
      (@List.concat _)
      (
        option_flat_map
        (fun l0 => list_update i l0 (List.map f l))
        (option_flat_map (fun y => list_update j x (f y)) (List.nth_error l i))
      ).
Proof.
  intros ? ? ? ? ? ? ? ? ? ?. generalize dependent i. induction l; intros ?.
  - simpl. rewrite list_nth_error_nil, list_update_nil. simpl. auto.
  - simpl. specialize (H a). destruct (PeanoNat.Nat.eqb_spec i 0).
    + subst i. clear IHl. rewrite list_update_app_1; try lia. simpl.
      rewrite List.flat_map_concat_map. destruct (list_update j x (f a)); auto.
    + rewrite list_update_app_2; try nia.
      replace (i * k + j - length (f a)) with ((pred i) * k + j) by nia.
      rewrite IHl; clear IHl. rewrite list_nth_error_cons; auto.
      remember (option_flat_map (fun y => list_update j x (f y)) (List.nth_error l (Nat.pred i))) as o0.
      destruct o0; auto. simpl. rewrite list_update_cons; auto.
      remember (list_update (Nat.pred i) l0 (List.map f l)) as o1. destruct o1; auto.
Qed.
