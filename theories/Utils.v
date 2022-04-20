(*
Abbreviations used:
- o - an option
- red - a reduction lemma
- l - a list
- sl - a sized_list
- il - a list of indexes (digits of the original index)
- isl - a sized_list of indexes (digits of the original index)
- a - an array
- lt - a leaf_tree
- clt - a complete_leaf_tree
- blt - a binary_leaf_tree
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

Definition option_prop_to_prop (o : option Prop) : Prop :=
  match o with
  | None => True
  | Some p => p
  end.

Fixpoint list_forall {A} f (l : list A) :=
  match l with
  | [] => True
  | x :: l' => f x /\ list_forall f l'
  end.

Lemma list_forall_equiv : forall {A} f (l : list A), list_forall f l <-> List.Forall f l.
Proof.
  intros ? ? ?. induction l.
  - simpl. intuition auto.
  - rename a into x. simpl. split.
    + intros (? & ?). apply List.Forall_cons; intuition auto.
    + intros ?. inversion H. subst x0 l0. intuition auto.
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

Lemma list_rev_injective :
  forall {A} (l1 l2 : list A),
  List.rev l1 = List.rev l2 ->
  l1 = l2.
Proof.
  intros ? ? ? ?. apply (f_equal (@List.rev _)) in H. rewrite ? List.rev_involutive in H. auto.
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

Theorem list_update_length :
  forall {A} i x (l l0 : list A),
  list_update i x l = Some l0 ->
  length l0 = length l.
Proof.
  intros ? ?. induction i; intros ? ? ? ?.
  - destruct l.
    + discriminate.
    + injection H as <-. auto.
  - destruct l.
    + discriminate.
    + rename a into y. simpl in H. remember (list_update i x l) as o. destruct o.
      * destruct l0.
        -- discriminate.
        -- injection H as <- <-. simpl. f_equal. apply (IHi x). symmetry. auto.
      * discriminate.
Qed.

Theorem list_forall_list_update_coarse :
  forall {A} i x (f : A -> Prop) (l l0 : list A),
  f x ->
  list_forall f l ->
  list_update i x l = Some l0 ->
  list_forall f l0.
Proof.
  intros ? ?. induction i; intros ? ? ? ? ? ? ?.
  - destruct l.
    + discriminate.
    + injection H1 as <-. simpl. simpl in H0. intuition auto.
  - destruct l.
    + discriminate.
    + rename a into y. simpl in H1. remember (list_update i x l) as o. destruct o.
      * destruct l0.
        -- discriminate.
        -- injection H1 as <- <-. simpl. destruct H0 as (? & ?). split.
           ++ auto.
           ++ symmetry in Heqo. apply (IHi x f l); auto.
      * discriminate.
Qed.

Fixpoint list_pop {A} (l : list A) : option (list A * A) :=
  match l with
  | [] => None
  | [x] => Some ([], x)
  | x :: l' => option_map (fun '(l'0, y) => (x :: l'0, y)) (list_pop l')
  end.

Theorem list_pop_nil :
  forall {A} (l : list A),
  l = [] ->
  list_pop l = None.
Proof.
  intros ? ? ?. subst l. auto.
Qed.

Theorem list_pop_cons :
  forall {A} x (l l0 : list A),
  l = l0 ++ [x] ->
  list_pop l = Some (l0, x).
Proof.
  intros ? ? ?. induction l; intros ? ?.
  - destruct l0; discriminate.
  - rename a into y. simpl. destruct l.
    + destruct l0.
      * injection H as ->. auto.
      * rename a into z. destruct l0; discriminate.
    + rename a into z. destruct l0.
      * discriminate.
      * injection H as <-. specialize (IHl l0 H). rewrite IHl. auto.
Qed.

Theorem list_pop_cons_exists :
  forall {A} (l : list A),
  l <> [] ->
  exists l0 x, list_pop l = Some (l0, x).
Proof.
  intros ? ?. induction l.
  - congruence.
  - rename a into x. simpl. destruct l.
    + exists [], x. auto.
    + rename a into y. specialize (IHl ltac:(congruence)). destruct IHl as (l0 & z & ?). exists (x :: l0), z.
      rewrite H. auto.
Qed.

Theorem list_pop_None :
  forall {A} (l : list A),
  list_pop l = None ->
  l = [].
Proof.
  destruct l; intros ?.
  - auto.
  - rename a into x. destruct (list_pop_cons_exists (x :: l) ltac:(congruence)) as (l0 & y & ?). congruence.
Qed.

Theorem list_pop_Some :
  forall {A} (l l0 : list A) x,
  list_pop l = Some (l0, x) ->
  l = l0 ++ [x].
Proof.
  intros ? ?. induction l; intros ? ? ?.
  - discriminate.
  - rename a into y. simpl in H. destruct l.
    + injection H as <- <-. auto.
    + rename a into z. remember (list_pop (z :: l)) as o. destruct o as [(l1, w) | ].
      * simpl in H. injection H as <- <-. specialize (IHl l1 w eq_refl). rewrite IHl. auto.
      * discriminate.
Qed.

Theorem list_pop_app_Some :
  forall {A} x (l1 l2 l3 : list A),
  list_pop l2 = Some (l3, x) ->
  list_pop (l1 ++ l2) = Some (l1 ++ l3, x).
Proof.
  intros ? ? ? ? ? ?. apply list_pop_Some in H. apply list_pop_cons. subst l2. apply List.app_assoc.
Qed.

Theorem list_pop_list_forall :
  forall {A} f (l l0 : list A) x,
  list_pop l = Some (l0, x) ->
  list_forall f l ->
  list_forall f l0 /\ f x.
Proof.
  intros ? ? ? ? ? ? ?. apply list_pop_Some in H. subst l.
  rewrite list_forall_equiv. rewrite list_forall_equiv in H0. apply List.Forall_app in H0.
  rewrite <- (list_forall_equiv _ [_]) in H0. simpl in H0. intuition auto.
Qed.

Lemma flat_map_length_constant_length :
  forall {A B} (f : A -> list B) l k,
  (list_forall (fun x => length (f x) = k) l) ->
  length (List.flat_map f l) = length l * k.
Proof.
  intros ? ? ? ? ? ?. induction l.
  - auto.
  - simpl. destruct H as (? & ?). apply IHl in H0; clear IHl. rewrite List.app_length. auto.
Qed.

Lemma flat_map_length_constant_length_for_type :
  forall {A B} (f : A -> list B) l k,
  (forall x, length (f x) = k) ->
  length (List.flat_map f l) = length l * k.
Proof.
  intros ? ? ? ? ? ?. apply flat_map_length_constant_length.
  rewrite list_forall_equiv. rewrite List.Forall_forall. auto.
Qed.

Lemma flat_map_list_nth_error_constant_length :
  forall {A B} (f : A -> list B) l k i j,
  (list_forall (fun x => length (f x) = k) l) ->
  j < k ->
  List.nth_error (List.flat_map f l) (i * k + j) =
    option_flat_map (fun l0 => List.nth_error (f l0) j) (List.nth_error l i).
Proof.
  intros ? ? ? ? ? ? ? ? ?. generalize dependent i. induction l; intros ?.
  - simpl. do 2 rewrite list_nth_error_nil. auto.
  - rename a into x. simpl. destruct H as (? & ?). destruct (PeanoNat.Nat.eqb_spec i 0).
    + subst i. clear IHl. rewrite List.nth_error_app1; try lia. simpl. destruct (List.nth_error (f x) j); auto.
    + rewrite List.nth_error_app2; try nia.
      replace (i * k + j - length (f x)) with ((pred i) * k + j) by nia.
      rewrite IHl; clear IHl.
      * rewrite list_nth_error_cons; auto.
      * auto.
Qed.

Lemma flat_map_list_nth_error_constant_length_for_type :
  forall {A B} (f : A -> list B) l k i j,
  (forall x, length (f x) = k) ->
  j < k ->
  List.nth_error (List.flat_map f l) (i * k + j) =
    option_flat_map (fun l0 => List.nth_error (f l0) j) (List.nth_error l i).
Proof.
  intros ? ? ? ? ? ? ? ? ?. apply flat_map_list_nth_error_constant_length.
  - rewrite list_forall_equiv. rewrite List.Forall_forall. auto.
  - auto.
Qed.

Lemma flat_map_list_update_constant_length :
  forall {A B} (f : A -> list B) l k i j x,
  (list_forall (fun x => length (f x) = k) l) ->
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
  - rename a into y. simpl. destruct H as (? & ?). destruct (PeanoNat.Nat.eqb_spec i 0).
    + subst i. clear IHl. rewrite list_update_app_1; try lia. simpl.
      rewrite List.flat_map_concat_map. destruct (list_update j x (f y)); auto.
    + rewrite list_update_app_2; try nia.
      replace (i * k + j - length (f y)) with ((pred i) * k + j) by nia.
      rewrite IHl; clear IHl.
      * rewrite list_nth_error_cons; auto.
        remember (option_flat_map (fun y => list_update j x (f y)) (List.nth_error l (Nat.pred i))) as o0.
        destruct o0; auto. simpl. rewrite list_update_cons; auto.
        remember (list_update (Nat.pred i) l0 (List.map f l)) as o1. destruct o1; auto.
      * auto.
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
  intros ? ? ? ? ? ? ? ? ? ?. apply flat_map_list_update_constant_length.
  - rewrite list_forall_equiv. rewrite List.Forall_forall. auto.
  - auto.
Qed.

#[program] Fixpoint to_digits r m {measure m} :=
  match r, m with
  | _, 0 => []
  | 0, _ => []
  | 1, _ => [m]
  | _, _ => Nat.modulo m r :: to_digits r (Nat.div m r)
  end.
Next Obligation.
  specialize (H m). specialize (H0 m). specialize (H1 r). apply PeanoNat.Nat.div_lt; lia.
Qed.
Next Obligation.
  intuition lia.
Qed.

Section Example.

Compute to_digits 2 10.

End Example.

Lemma to_digits_red_any_zero : forall r, to_digits r 0 = [].
Proof.
  intros ?. unfold to_digits, to_digits_func.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext. simpl.
  destruct r.
  - auto.
  - destruct r; auto.
Qed.

Lemma to_digits_red_any_nonzero :
  forall r m,
  r > 1 ->
  m <> 0 ->
  to_digits r m = Nat.modulo m r :: to_digits r (Nat.div m r).
Proof.
  intros ? ? ? ?. unfold to_digits, to_digits_func at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext. fold to_digits_func. simpl.
  do 2 (destruct r; try lia). destruct m; try lia. auto.
Qed.
