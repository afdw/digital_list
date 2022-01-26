(*
Abbreviations used:
- red - a reduction lemma
- sl - a sized_list
- isl - a sized_list of indexes (digits of the original index)
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

Inductive sized_list {A} : nat -> Type :=
  | SizedListNil : sized_list 0
  | SizedListCons : forall {n}, A -> sized_list n -> sized_list (S n).

Arguments sized_list : clear implicits.

Notation "x :||: l" := (SizedListCons x l) (at level 51, right associativity).

Notation "[| |]" := SizedListNil (format "[| |]").
Notation "[| x |]" := (SizedListCons x SizedListNil).
Notation "[| x ; y ; .. ; z |]" := (SizedListCons x (SizedListCons y .. (SizedListCons z SizedListNil) ..)).

Section Example.

Check SizedListCons 1 (SizedListCons 2 (SizedListCons 3 SizedListNil)).
Check [|1; 2; 3|].

End Example.

Fixpoint sized_list_to_list {A n} (sl : sized_list A n) :=
  match sl with
  | [||] => []
  | x :||: sl'  => x :: sized_list_to_list sl'
  end.

Fixpoint sized_list_repeat {A n} (a : A) :=
  match n with
  | 0 => [||]
  | S n' => a :||: sized_list_repeat a
  end.

Fixpoint sized_list_of_list {A n} default (l : list A) :=
  match n, l with
  | 0, _ => [||]
  | _, [] => sized_list_repeat default
  | _, x :: l'  => x :||: sized_list_of_list default l'
  end.

Section Example.

Compute sized_list_of_list 0 [1; 2; 3] : sized_list _ 5.
Compute sized_list_of_list 0 [1; 2; 3; 4; 5; 6; 7; 8] : sized_list _ 5.

End Example.

Theorem sized_list_of_to_list_correct :
  forall {A n} default (sl : sized_list A n),
  sized_list_of_list default (sized_list_to_list sl) = sl.
Proof.
  intros ? ? ? ?. induction sl.
  - auto.
  - simpl. f_equal. auto.
Qed.

Theorem sized_list_to_list_cons :
  forall {A n} x (sl : sized_list A n),
  sized_list_to_list (x :||: sl) =
  (x :: sized_list_to_list sl).
Proof.
  auto.
Qed.

Theorem sized_list_of_list_cons :
  forall {A n} default x (l : list A),
  sized_list_of_list default (x :: l) =
  (x :||: sized_list_of_list default l : sized_list A (S n)).
Proof.
  auto.
Qed.

Fixpoint sized_list_forall {A n} f (sl : sized_list A n) :=
  match sl with
  | [||] => True
  | x :||: l' => f x /\ sized_list_forall f l'
  end.

Theorem sized_list_to_list_length :
  forall {A n} (sl : sized_list A n),
  length (sized_list_to_list sl) = n.
Proof.
  intros ? ? ?. induction sl.
  - auto.
  - simpl. f_equal. auto.
Qed.

Fixpoint sized_list_rev_inner {A n1 n2}
  (sl1 : sized_list A n1) (sl2 : sized_list A n2) : sized_list A (n1 + n2) :=
  match sl1 with
  | [||] => sl2
  | x :||: sl1' =>
    rew <- (nat_computational_eq (Plus.plus_Snm_nSm _ _)) in (sized_list_rev_inner sl1' (x :||: sl2))
  end.

Definition sized_list_rev {A n} (sl : sized_list A n) : sized_list A n :=
  rew (nat_computational_eq (PeanoNat.Nat.add_0_r _)) in (sized_list_rev_inner sl [||]).

Section Example.

Compute sized_list_rev [|1; 2; 3; 4; 5|].

End Example.

Lemma sized_list_rev_inner_correct :
  forall {A n1 n2} (sl1 : sized_list A n1) (sl2 : sized_list A n2),
  sized_list_to_list (sized_list_rev_inner sl1 sl2) =
    List.rev (sized_list_to_list sl1) ++ sized_list_to_list sl2.
Proof.
  intros ? ? ? ? ?. generalize dependent n2. induction sl1; intros ? ?.
  - auto.
  - simpl. unrew. rewrite IHsl1; clear IHsl1. simpl. rewrite <- List.app_assoc. auto.
Qed.

Theorem sized_list_rev_correct :
  forall {A n} (sl : sized_list A n),
  sized_list_to_list (sized_list_rev sl) = List.rev (sized_list_to_list sl).
Proof.
  intros ? ? ?. unfold sized_list_rev. unrew. rewrite sized_list_rev_inner_correct.
  simpl. rewrite List.app_nil_r. auto.
Qed.

Theorem sized_list_rev_correct_eq :
  forall {A n} default (sl : sized_list A n),
  sized_list_rev sl = sized_list_of_list default (List.rev (sized_list_to_list sl)).
Proof.
  intros ? ? ? ?. rewrite <- (sized_list_of_to_list_correct default) at 1. f_equal.
  apply sized_list_rev_correct.
Qed.

Lemma sized_list_forall_sized_list_rev_inner :
  forall {A n1 n2} f (sl1 : sized_list A n1) (sl2 : sized_list A n2),
  sized_list_forall f sl1 ->
  sized_list_forall f sl2 ->
  sized_list_forall f (sized_list_rev_inner sl1 sl2).
Proof.
  intros ? ? ? ? ? ?. generalize dependent n2. induction sl1; intros ? ? ? ?.
  - auto.
  - simpl. unrew. inversion H; clear H. apply IHsl1; simpl; auto.
Qed.

Theorem sized_list_forall_sized_list_rev :
  forall {A n} f (sl : sized_list A n),
  sized_list_forall f sl ->
  sized_list_forall f (sized_list_rev sl).
Proof.
  intros ? ? ? ? ?. unfold sized_list_rev. unrew. apply sized_list_forall_sized_list_rev_inner; simpl; auto.
Qed.

Fixpoint sized_list_pop {A n} (sl : sized_list A (S n)) : sized_list A n :=
  match sl with
  | @SizedListCons _ n0 x sl'0 => fun (H : S n0 = S n) =>
    let sl' := rew dependent (eq_add_S _ _ H) in sl'0 in
    match sl' with
    | [||] => fun _ =>
      [||]
    | @SizedListCons _ n' y sl'' => fun (H0 : n = S n') =>
      x :||: sized_list_pop (rew H0 in sl')
    end eq_refl
  end eq_refl.

Theorem sized_list_pop_correct :
  forall {A n} (sl : sized_list A (S n)),
  sized_list_to_list (sized_list_pop sl) = List.removelast (sized_list_to_list sl).
Proof.
  intros ? ? ?.
  replace (@sized_list_to_list A n) with (@sized_list_to_list A (pred (S n))) by auto.
  replace (@sized_list_pop A n sl) with (@sized_list_pop A (pred (S n)) sl) by auto.
  generalize dependent sl.
  cut (
    (fun n0 (H : n0 > 0) => forall (sl : sized_list A n0),
      @sized_list_to_list A (pred n0) (@sized_list_pop A (pred n0) (rew (Lt.S_pred_pos _ H) in sl)) =
      @List.removelast A (@sized_list_to_list A n0 sl)
    ) (S n) (Gt.gt_Sn_O _)
  ).
  - intros ? ?. simpl in H. rewrite <- H; clear H. unrew. auto.
  - remember (Gt.gt_Sn_O n) as H. clear HeqH. remember (S n) as n0. clear Heqn0. intros ?.
    induction sl.
    + lia.
    + simpl. remember (sized_list_to_list sl) as l0. destruct l0.
      * clear IHsl. unrew. destruct sl; intuition discriminate.
      * assert (n0 > 0) by (destruct sl; [discriminate | lia]). rewrite <- (IHsl H0); clear IHsl Heql0.
        unrew. simpl. destruct sl.
        -- lia.
        -- do 2 unrew. rewrite <- sized_list_to_list_cons. auto.
Qed.

Fixpoint sized_list_nth {A n} i (sl : sized_list A n) {struct i} :=
  match sl, i with
  | [||], _ => None
  | x :||: _, 0 => Some x
  | _ :||: sl', S i' => sized_list_nth i' sl'
  end.

Theorem sized_list_nth_correct :
  forall {A n} i (sl : sized_list A n),
  sized_list_nth i sl = List.nth_error (sized_list_to_list sl) i.
Proof.
  intros ? ? ? ?. generalize dependent i. induction sl; intros ?.
  - simpl. destruct i; auto.
  - simpl. destruct i.
    + auto.
    + simpl. apply IHsl.
Qed.

Fixpoint sized_list_update {A n} i x (sl : sized_list A n) {struct i} :=
  match sl, i with
  | [||], _ => None
  | y :||: sl', 0 => Some (x :||: sl')
  | y :||: sl', S i' => option_map (fun sl0 => y :||: sl0) (sized_list_update i' x sl')
  end.

Theorem sized_list_update_correct :
  forall {A n} i x (sl : sized_list A n),
  option_map sized_list_to_list (sized_list_update i x sl) = list_update i x (sized_list_to_list sl).
Proof.
  intros ? ? ? ? ?. generalize dependent i. induction sl; intros ?.
  - simpl. destruct i; auto.
  - simpl. destruct i.
    + auto.
    + simpl. rewrite <- IHsl; clear IHsl. rewrite ? option_map_option_map. apply option_map_ext. auto.
Qed.

Fixpoint complete_leaf_tree A n d :=
  match d with
  | 0 => A
  | S d' => sized_list (complete_leaf_tree A n d') n
  end.

Section Example.

Compute complete_leaf_tree nat 2 3.

Check [|[|[|0; 1|]; [|2; 3|]|]; [|[|4; 5|]; [|6; 7|]|]|] : complete_leaf_tree nat 2 3.

End Example.

Fixpoint complete_leaf_tree_to_list {A n d} (clt : complete_leaf_tree A n d) :=
  match d with
  | 0 => fun (clt : complete_leaf_tree A n 0) =>
    [clt : A]
  | S d' => fun (clt : complete_leaf_tree A n (S d')) =>
    List.flat_map complete_leaf_tree_to_list (sized_list_to_list clt)
  end clt.

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

Theorem complete_leaf_tree_to_list_length :
  forall {A n d} (clt : complete_leaf_tree A n d),
  length (complete_leaf_tree_to_list clt) = Nat.pow n d.
Proof.
  intros ? ? ?. induction d; intros clt.
  - auto.
  - simpl. rewrite flat_map_length_constant_length_for_type with (k := Nat.pow n d).
    + rewrite sized_list_to_list_length. auto.
    + auto.
Qed.

Inductive digital_list {A n} : nat -> Type :=
  | DigitalListNil : digital_list 0
  | DigitalListCons :
      forall {d} k,
      k < n ->
      sized_list (complete_leaf_tree A n d) k ->
      digital_list d ->
      digital_list (S d).

Arguments digital_list : clear implicits.

Inductive concrete_digital_list {A n} : Type :=
  | ConcreteDigitalList : forall d, digital_list A n d -> concrete_digital_list.

Arguments concrete_digital_list : clear implicits.

Fixpoint digital_list_to_list {A n d} (dl : digital_list A n d) :=
  match dl with
  | DigitalListNil => []
  | DigitalListCons k _ sl dl' =>
    List.flat_map complete_leaf_tree_to_list (sized_list_to_list sl) ++ digital_list_to_list dl'
  end.

Definition concrete_digital_list_to_list {A n} (cdl : concrete_digital_list A n) :=
  let '(ConcreteDigitalList _ dl) := cdl in digital_list_to_list dl.

Section Example.

Check
  DigitalListCons _ (le_n _)
  ([|[|[|[|0; 1|]; [|2; 3|]|]; [|[|4; 5|]; [|6; 7|]|]|]|] : sized_list (complete_leaf_tree _ _ 3) _)
  (
    DigitalListCons _ (le_S _ _ (le_n _))
    [||]
    (
      DigitalListCons _ (le_n _)
      ([|[|8; 9|]|] : sized_list (complete_leaf_tree _ _ 1) _)
      (
        DigitalListCons _ (le_S _ _ (le_n _))
        [||]
        DigitalListNil
      )
    )
  ).

End Example.

Fixpoint digital_list_length {A n d} (dl : digital_list A n d) :=
  match dl with
  | DigitalListNil => 0
  | DigitalListCons k _ _ dl' => (Nat.pow n (pred d)) * k + digital_list_length dl'
  end.

Definition concrete_digital_list_length {A n} (cdl : concrete_digital_list A n) :=
  let '(ConcreteDigitalList _ dl) := cdl in digital_list_length dl.

Theorem digital_list_length_correct :
  forall {A n d} (dl : digital_list A n d),
  digital_list_length dl = length (digital_list_to_list dl).
Proof.
  intros ? ? ? ?. induction dl.
  - auto.
  - simpl. rewrite IHdl; clear IHdl. rewrite List.app_length. apply PeanoNat.Nat.add_cancel_r.
    clear - s. induction s.
    + auto.
    + rewrite <- mult_n_Sm. rewrite IHs; clear IHs. simpl. rewrite List.app_length.
      rewrite complete_leaf_tree_to_list_length. lia.
Qed.

Theorem concrete_digital_list_length_correct :
  forall {A n} (cdl : concrete_digital_list A n),
  concrete_digital_list_length cdl = length (concrete_digital_list_to_list cdl).
Proof.
  intros ? ? ?. destruct cdl as (d & dl). apply digital_list_length_correct.
Qed.

Theorem digital_list_length_upper_bound :
  forall {A n d} (dl : digital_list A n d),
  digital_list_length dl < Nat.pow n d.
Proof.
  intros ? ? ? ?. induction dl.
  - auto.
  - simpl. nia.
Qed.

#[program] Fixpoint to_digits n m {measure m} :=
  match n, m with
  | _, 0 => []
  | 0, _ => []
  | 1, _ => [m]
  | _, _ => Nat.modulo m n :: to_digits n (Nat.div m n)
  end.
Next Obligation.
  specialize (H m). specialize (H0 m). specialize (H1 n). apply PeanoNat.Nat.div_lt; lia.
Qed.
Next Obligation.
  intuition lia.
Qed.

Definition indexes_sized_list_of_index {k} n m : sized_list nat k :=
  sized_list_rev (sized_list_of_list 0 (to_digits n m)).

Fixpoint indexes_sized_list_to_index {k} n (isl : sized_list nat k) :=
  match isl with
  | [||] => 0
  | i :||: isl' => Nat.pow n (pred k) * i + indexes_sized_list_to_index n isl'
  end.

Section Example.

Compute to_digits 2 10.
Compute indexes_sized_list_of_index 2 10 : sized_list _ 8.
Compute indexes_sized_list_to_index 2 [|0; 0; 0; 0; 1; 0; 1; 0|].

End Example.

Lemma to_digits_red_any_zero : forall n, to_digits n 0 = [].
Proof.
  intros ?. unfold to_digits, to_digits_func.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext. simpl.
  destruct n.
  - auto.
  - destruct n; auto.
Qed.

Lemma to_digits_red_any_nonzero :
  forall n m,
  n > 1 ->
  m <> 0 ->
  to_digits n m = Nat.modulo m n :: to_digits n (Nat.div m n).
Proof.
  intros ? ? ? ?. unfold to_digits, to_digits_func at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext. fold to_digits_func. simpl.
  do 2 (destruct n; try lia). destruct m; try lia. auto.
Qed.

Lemma indexes_sized_list_to_index_sized_list_rev_cons :
  forall {k} n i (isl : sized_list nat k),
  indexes_sized_list_to_index n (sized_list_rev (i :||: isl)) =
  indexes_sized_list_to_index n (sized_list_rev isl) * n + i.
Proof.
  intros ? ? ? ?. rewrite ? (sized_list_rev_correct_eq 0).
  remember (sized_list_to_list (i :||: isl)) as l0. simpl in Heql0. subst l0.
  assert (forall l, List.rev (i :: l) = List.rev l ++ [i]) by auto. rewrite H. clear H.
  remember (List.rev (sized_list_to_list isl)) as l0.
  generalize dependent k. generalize dependent i. induction l0; intros ? ? ? ?.
  - simpl. destruct isl.
    + simpl. lia.
    + simpl in Heql0. symmetry in Heql0. apply List.app_eq_nil in Heql0. intuition discriminate.
  - simpl. destruct k.
    + simpl. remember 0. destruct isl; discriminate.
    + rewrite (IHl0 _ _ (sized_list_pop isl)); clear IHl0.
      * simpl. lia.
      * apply (f_equal (@List.rev _)) in Heql0. rewrite List.rev_involutive in Heql0. simpl in Heql0.
        rewrite <- List.rev_involutive at 1. f_equal. rewrite sized_list_pop_correct.
        rewrite <- Heql0; clear Heql0. symmetry. apply List.removelast_last.
Qed.

Lemma indexes_sized_list_to_index_sized_list_rev_sized_list_repeat_0 :
  forall {k} n,
  indexes_sized_list_to_index (k := k) n (sized_list_rev (sized_list_repeat 0)) = 0.
Proof.
  intros ? ?. induction k.
  - auto.
  - simpl. rewrite indexes_sized_list_to_index_sized_list_rev_cons. lia.
Qed.

Theorem indexes_sized_list_to_of_correct :
  forall {k} n m,
  n > 1 ->
  m < Nat.pow n k ->
  indexes_sized_list_to_index (k := k) n (indexes_sized_list_of_index n m) = m.
Proof.
  intros ? ? ? ?. generalize dependent m. unfold indexes_sized_list_of_index. induction k; intros ? ?.
  - simpl. simpl in H0. lia.
  - simpl. destruct (PeanoNat.Nat.eqb_spec m 0).
    + clear IHk. subst m. rewrite to_digits_red_any_zero.
      rewrite indexes_sized_list_to_index_sized_list_rev_cons.
      rewrite indexes_sized_list_to_index_sized_list_rev_sized_list_repeat_0. auto.
    + assert (Nat.div m n < Nat.pow n k). {
        simpl in H0. destruct (PeanoNat.Nat.eqb_spec (Nat.div m n) (Nat.pow n k)).
        - apply PeanoNat.Nat.div_lt_upper_bound; lia.
        - unfold lt in H0. apply Le.le_Sn_le in H0. apply PeanoNat.Nat.div_le_mono with (c := n) in H0; try lia.
          rewrite PeanoNat.Nat.mul_comm in H0. rewrite PeanoNat.Nat.div_mul in H0; try lia.
      }
      specialize (IHk (Nat.div m n) H1); clear H1. rewrite to_digits_red_any_nonzero; try lia.
      rewrite indexes_sized_list_to_index_sized_list_rev_cons. rewrite IHk; clear IHk.
      symmetry. rewrite PeanoNat.Nat.mul_comm. apply PeanoNat.Nat.div_mod_eq.
Qed.

Theorem indexes_sized_list_of_index_upper_bound :
  forall {k} n m,
  n > 1 ->
  sized_list_forall (fun i => i < n) (indexes_sized_list_of_index (k := k) n m).
Proof.
  intros ? ? ? ?. unfold indexes_sized_list_of_index. apply sized_list_forall_sized_list_rev.
  generalize dependent m. induction k; intros ?.
  - simpl. auto.
  - simpl. destruct (PeanoNat.Nat.eqb_spec m 0).
    + clear IHk. subst m. rewrite to_digits_red_any_zero. simpl. split; try lia. induction k.
      * simpl. auto.
      * simpl. intuition lia.
    + rewrite to_digits_red_any_nonzero; try lia. simpl. split.
      * apply PeanoNat.Nat.mod_upper_bound. lia.
      * auto.
Qed.

Theorem indexes_sized_list_to_index_upper_bound :
  forall {n d} (isl : sized_list nat d),
  sized_list_forall (fun i => i < n) isl ->
  indexes_sized_list_to_index n isl < Nat.pow n d.
Proof.
  intros ? ? ?. induction isl; intros ?.
  - simpl. lia.
  - simpl. destruct H as (? & ?). specialize (IHisl H0); clear H0. nia.
Qed.

Fixpoint complete_leaf_tree_nth {A n d} (isl : sized_list nat d) (clt : complete_leaf_tree A n d) : option A :=
  match d with
  | 0 => fun (isl : sized_list nat 0) (clt : complete_leaf_tree A n 0) =>
    Some (clt : A)
  | S d' => fun (isl : sized_list nat (S d')) (clt : complete_leaf_tree A n (S d')) =>
    match isl with
    | @SizedListCons _ d'0 i isl'0 => fun (Heqd : S d'0 = S d') =>
      let isl' := rew (eq_add_S _ _ Heqd) in isl'0 in
      option_flat_map (complete_leaf_tree_nth isl') (sized_list_nth i clt)
    end eq_refl
  end isl clt.

Section Example.

Compute complete_leaf_tree_nth [|1; 1; 0|] [|[|[|0; 1|]; [|2; 3|]|]; [|[|4; 5|]; [|6; 7|]|]|].

End Example.

Theorem complete_leaf_tree_nth_correct :
  forall {A n d} (isl : sized_list nat d) (clt : complete_leaf_tree A n d),
  sized_list_forall (fun i => i < n) isl ->
  complete_leaf_tree_nth isl clt =
    List.nth_error (complete_leaf_tree_to_list clt) (indexes_sized_list_to_index n isl).
Proof.
  intros ? ? ?. induction d; intros ? ? ?.
  - remember 0. destruct isl.
    + auto.
    + discriminate.
  - remember (S d) as d0. destruct isl.
    + discriminate.
    + injection Heqd0 as ->. destruct H as (? & ?). simpl.
      rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_nth_error_constant_length_for_type.
      * rewrite sized_list_nth_correct. apply option_flat_map_ext. intros clt'. apply IHd. auto.
      * apply complete_leaf_tree_to_list_length.
      * apply indexes_sized_list_to_index_upper_bound. auto.
Qed.

Fixpoint complete_leaf_tree_update {A n d} (isl : sized_list nat d)
  (x : A) (clt : complete_leaf_tree A n d) : option (complete_leaf_tree A n d) :=
  match d with
  | 0 => fun (isl : sized_list nat 0) (clt : complete_leaf_tree A n 0) =>
    Some (x : complete_leaf_tree A n 0)
  | S d' => fun (isl : sized_list nat (S d')) (clt : complete_leaf_tree A n (S d')) =>
    match isl with
    | @SizedListCons _ d'0 i isl'0 => fun (Heqd : S d'0 = S d') =>
      let isl' := rew (eq_add_S _ _ Heqd) in isl'0 in
      option_flat_map
        (fun clt' => sized_list_update i clt' clt)
        (option_flat_map (complete_leaf_tree_update isl' x) (sized_list_nth i clt))
    end eq_refl : option (complete_leaf_tree A n (S d'))
  end isl clt.

Theorem complete_leaf_tree_update_correct :
  forall {A n d} x (isl : sized_list nat d) (clt : complete_leaf_tree A n d),
  sized_list_forall (fun i => i < n) isl ->
  option_map complete_leaf_tree_to_list (complete_leaf_tree_update isl x clt) =
    list_update (indexes_sized_list_to_index n isl) x (complete_leaf_tree_to_list clt).
Proof.
  intros ? ? ? ?. induction d; intros ? ? ?.
  - simpl. remember (@indexes_sized_list_to_index 0 n isl) as i. destruct i.
    + auto.
    + exfalso. remember 0. destruct isl; discriminate.
  - remember (S d) as d0. destruct isl.
    + discriminate.
    + injection Heqd0 as ->. destruct H as (? & ?). simpl. fold complete_leaf_tree.
      rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_update_constant_length_for_type.
      * rewrite sized_list_nth_correct. remember (List.nth_error (sized_list_to_list clt) n1) as o0.
        fold complete_leaf_tree in o0. setoid_rewrite <- Heqo0. destruct o0; try auto.
        simpl. rewrite <- IHd; auto; clear IHd. remember (complete_leaf_tree_update isl x c) as o1.
        destruct o1; auto. simpl.
        replace (
          fun clt0 =>
            @List.flat_map (complete_leaf_tree A n d) A (@complete_leaf_tree_to_list A n d)
              (@sized_list_to_list (complete_leaf_tree A n d) n clt0)
        ) with (
          Basics.compose
          (@List.flat_map (complete_leaf_tree A n d) A (@complete_leaf_tree_to_list A n d))
          (fun clt0 => @sized_list_to_list (complete_leaf_tree A n d) n clt0)
        ) by auto.
        rewrite <- option_map_option_map. rewrite sized_list_update_correct.
        rewrite (option_map_ext _ _ _ (List.flat_map_concat_map _)).
        replace (
          fun (l : list (complete_leaf_tree A n d)) => List.concat (List.map complete_leaf_tree_to_list l)
        ) with (
          Basics.compose
          (@List.concat _)
          (List.map (@complete_leaf_tree_to_list A n d))
        ) by auto.
        rewrite <- option_map_option_map. f_equal.
        symmetry. apply list_update_list_map.
      * apply complete_leaf_tree_to_list_length.
      * apply indexes_sized_list_to_index_upper_bound. auto.
Qed.

Fixpoint digital_list_nth_inner {A n d} (isl : sized_list nat d) (dl : digital_list A n d)
  {struct dl} : option A :=
  match dl with
  | DigitalListNil => fun (isl : sized_list nat 0) =>
    None
  | @DigitalListCons _ _ d' k _ sl dl' => fun (isl : sized_list nat (S d')) =>
    match isl with
    | @SizedListCons _ d'0 i isl'0 => fun (Heqd : S d'0 = S d') =>
      let isl' := rew (eq_add_S _ _ Heqd) in isl'0 in
      if Nat.eqb i k
      then digital_list_nth_inner isl' dl'
      else option_flat_map (complete_leaf_tree_nth isl') (sized_list_nth i sl)
    end eq_refl
  end isl.

Definition digital_list_nth {A n d} i (dl : digital_list A n d) : option A :=
  if Nat.ltb i (digital_list_length dl)
  then digital_list_nth_inner (indexes_sized_list_of_index n i) dl
  else None.

Definition concrete_digital_list_nth {A n} i (cdl : concrete_digital_list A n) : option A :=
  let '(ConcreteDigitalList _ dl) := cdl in digital_list_nth i dl.

Theorem digital_list_nth_inner_correct :
  forall {A n d} (isl : sized_list nat d) (dl : digital_list A n d),
  sized_list_forall (fun i => i < n) isl ->
  indexes_sized_list_to_index n isl < digital_list_length dl ->
  digital_list_nth_inner isl dl =
    List.nth_error (digital_list_to_list dl) (indexes_sized_list_to_index n isl).
Proof.
  intros ? ? ? ? ? ? ?. induction dl.
  - simpl. symmetry. apply list_nth_error_nil.
  - rename s into sl. simpl. dependent destruction isl. rename n1 into i.
    unrew. destruct H as (? & ?). simpl in H0.
    assert (length (List.flat_map complete_leaf_tree_to_list (sized_list_to_list sl)) = Nat.pow n d * k). {
      rewrite (flat_map_length_constant_length_for_type _ _ (Nat.pow n d)).
      - rewrite sized_list_to_list_length. lia.
      - apply complete_leaf_tree_to_list_length.
    }
    destruct (PeanoNat.Nat.eqb_spec i k).
    + subst i. rewrite IHdl; auto; try nia; clear IHdl. simpl. rewrite List.nth_error_app2.
      * f_equal. rewrite H2. lia.
      * rewrite H2. lia.
    + clear IHdl. simpl. rewrite List.nth_error_app1.
      * rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_nth_error_constant_length_for_type.
        -- rewrite <- sized_list_nth_correct. apply option_flat_map_ext. intros clt.
           apply complete_leaf_tree_nth_correct. auto.
        -- apply complete_leaf_tree_to_list_length.
        -- apply indexes_sized_list_to_index_upper_bound. auto.
      * specialize (indexes_sized_list_to_index_upper_bound isl H1) as ?.
        specialize (digital_list_length_upper_bound dl) as ?.
        rewrite H2. nia.
Qed.

Theorem digital_list_nth_correct :
  forall {A n d} i (dl : digital_list A n d),
  n > 1 ->
  digital_list_nth i dl = List.nth_error (digital_list_to_list dl) i.
Proof.
  intros ? ? ? ? ? ?. unfold digital_list_nth.
  destruct (PeanoNat.Nat.ltb_spec0 i (digital_list_length dl)).
  - assert (indexes_sized_list_to_index (k := d) n (indexes_sized_list_of_index n i) = i). {
      apply indexes_sized_list_to_of_correct.
      - auto.
      - apply (PeanoNat.Nat.le_trans _ _ _ l). apply PeanoNat.Nat.lt_le_incl.
        apply digital_list_length_upper_bound.
    }
    rewrite digital_list_nth_inner_correct.
    + rewrite H0. auto.
    + apply indexes_sized_list_of_index_upper_bound. auto.
    + rewrite H0. auto.
  - rewrite digital_list_length_correct in n0. symmetry. apply List.nth_error_None. lia.
Qed.

Theorem concrete_digital_list_nth_correct :
  forall {A n} i (cdl : concrete_digital_list A n),
  n > 1 ->
  concrete_digital_list_nth i cdl = List.nth_error (concrete_digital_list_to_list cdl) i.
Proof.
  intros ? ? ? ? ?. destruct cdl as (d & dl). apply digital_list_nth_correct. auto.
Qed.

Section Example.

Compute
  let cdl :=
    ConcreteDigitalList
    _
    (
      DigitalListCons _ (le_n _)
      ([|[|[|[|0; 1|]; [|2; 3|]|]; [|[|4; 5|]; [|6; 7|]|]|]|] : sized_list (complete_leaf_tree _ _ 3) _)
      (
        DigitalListCons _ (le_S _ _ (le_n _))
        [||]
        (
          DigitalListCons _ (le_n _)
          ([|[|8; 9|]|] : sized_list (complete_leaf_tree _ _ 1) _)
          (
            DigitalListCons _ (le_S _ _ (le_n _))
            [||]
            DigitalListNil
          )
        )
      )
    ) in
  let f :=
    fix f i :=
      match i with
      | 0 => []
      | S i' => f i' ++ [concrete_digital_list_nth i' cdl]
      end in
  (
    concrete_digital_list_to_list cdl,
    f (concrete_digital_list_length cdl),
    concrete_digital_list_nth 100 cdl
  ).

End Example.

Fixpoint digital_list_update_inner {A n d} (isl : sized_list nat d) (x : A) (dl : digital_list A n d)
  {struct dl} : option (digital_list A n d) :=
  match dl with
  | DigitalListNil => fun (isl : sized_list nat 0) =>
    None
  | @DigitalListCons _ _ d' k Hlt sl dl' => fun (isl : sized_list nat (S d')) =>
    match isl with
    | @SizedListCons _ d'0 i isl'0 => fun (Heqd : S d'0 = S d') =>
      let isl' := rew (eq_add_S _ _ Heqd) in isl'0 in
      if Nat.eqb i k
      then
        option_map
          (fun dl'0 => DigitalListCons k Hlt sl dl'0)
          (digital_list_update_inner isl' x dl')
      else
        option_map
          (fun sl0 => DigitalListCons k Hlt sl0 dl')
          (
            option_flat_map
              (fun clt' => sized_list_update i clt' sl)
              (option_flat_map (complete_leaf_tree_update isl' x) (sized_list_nth i sl))
          )
    end eq_refl : option (digital_list A n (S d'))
  end isl.

Definition digital_list_update {A n d} i x (dl : digital_list A n d) : option (digital_list A n d) :=
  if Nat.ltb i (digital_list_length dl)
  then digital_list_update_inner (indexes_sized_list_of_index n i) x dl
  else None.

Definition concrete_digital_list_update {A n} i x (cdl : concrete_digital_list A n) :
  option (concrete_digital_list A n) :=
  let '(ConcreteDigitalList _ dl) := cdl in
    option_map (fun dl0 => ConcreteDigitalList _ dl0) (digital_list_update i x dl).

Theorem digital_list_update_inner_correct :
  forall {A n d} (isl : sized_list nat d) x (dl : digital_list A n d),
  sized_list_forall (fun i => i < n) isl ->
  indexes_sized_list_to_index n isl < digital_list_length dl ->
  option_map digital_list_to_list (digital_list_update_inner isl x dl) =
    list_update (indexes_sized_list_to_index n isl) x (digital_list_to_list dl).
Proof.
  intros ? ? ? ? ? ? ? ?. induction dl.
  - simpl. symmetry. apply list_update_nil.
  - rename s into sl. simpl. dependent destruction isl. rename n1 into i.
    unrew. destruct H as (? & ?). simpl in H0.
    assert (length (List.flat_map complete_leaf_tree_to_list (sized_list_to_list sl)) = Nat.pow n d * k). {
      rewrite (flat_map_length_constant_length_for_type _ _ (Nat.pow n d)).
      - rewrite sized_list_to_list_length. lia.
      - apply complete_leaf_tree_to_list_length.
    }
    destruct (PeanoNat.Nat.eqb_spec i k).
    + subst i. simpl. rewrite list_update_app_2.
      * rewrite H2.
        replace (Nat.pow n d * k + indexes_sized_list_to_index n isl - Nat.pow n d * k)
          with (indexes_sized_list_to_index n isl) by lia.
        rewrite <- IHdl; auto; try nia; clear IHdl.
        remember (digital_list_update_inner isl x dl) as o0. destruct o0; auto.
      * rewrite H2. lia.
    + clear IHdl. simpl. rewrite list_update_app_1.
      * rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_update_constant_length_for_type.
        -- rewrite <- sized_list_nth_correct. remember (sized_list_nth i sl) as o0. destruct o0; auto. simpl.
           rewrite option_map_option_map. unfold Basics.compose. simpl.
           replace (
             fun (sl0 : sized_list (complete_leaf_tree A n d) k) =>
               List.flat_map complete_leaf_tree_to_list (sized_list_to_list sl0) ++ digital_list_to_list dl
           ) with (
             Basics.compose
             (fun l0 => l0 ++ digital_list_to_list dl)
             (
               Basics.compose
               (List.flat_map complete_leaf_tree_to_list)
               (@sized_list_to_list (complete_leaf_tree A n d) k)
             )
           ) by auto.
           rewrite <- option_map_option_map. f_equal.
           rewrite <- option_map_option_map. rewrite option_map_option_flat_map.
           rewrite (option_flat_map_ext _ _ _ (fun _ => sized_list_update_correct _ _ _)).
           rewrite ? option_map_option_flat_map. rewrite <- complete_leaf_tree_update_correct.
           rewrite option_map_flat_option_map. unfold Basics.compose.
           apply option_flat_map_ext. intros clt0. rewrite list_update_list_map.
           ++ remember (list_update i clt0 (sized_list_to_list sl)) as o1. destruct o1; auto. simpl.
              f_equal. apply List.flat_map_concat_map.
           ++ auto.
        -- apply complete_leaf_tree_to_list_length.
        -- apply indexes_sized_list_to_index_upper_bound. auto.
      * specialize (indexes_sized_list_to_index_upper_bound isl H1) as ?.
        specialize (digital_list_length_upper_bound dl) as ?.
        rewrite H2. nia.
Qed.

Theorem digital_list_update_correct :
  forall {A n d} i x (dl : digital_list A n d),
  n > 1 ->
  option_map digital_list_to_list (digital_list_update i x dl) = list_update i x (digital_list_to_list dl).
Proof.
  intros ? ? ? ? ? ? ?. unfold digital_list_update.
  destruct (PeanoNat.Nat.ltb_spec0 i (digital_list_length dl)).
  - assert (indexes_sized_list_to_index (k := d) n (indexes_sized_list_of_index n i) = i). {
      apply indexes_sized_list_to_of_correct.
      - auto.
      - apply (PeanoNat.Nat.le_trans _ _ _ l). apply PeanoNat.Nat.lt_le_incl.
        apply digital_list_length_upper_bound.
    }
    rewrite digital_list_update_inner_correct.
    + rewrite H0. auto.
    + apply indexes_sized_list_of_index_upper_bound. auto.
    + rewrite H0. auto.
  - rewrite digital_list_length_correct in n0. symmetry. apply list_update_None. lia.
Qed.

Theorem concrete_digital_list_update_correct :
  forall {A n} i x (cdl : concrete_digital_list A n),
  n > 1 ->
  option_map concrete_digital_list_to_list (concrete_digital_list_update i x cdl) =
    list_update i x (concrete_digital_list_to_list cdl).
Proof.
  intros ? ? ? ? ? ?. destruct cdl as (d & dl). unfold concrete_digital_list_to_list. simpl.
  rewrite option_map_option_map. apply digital_list_update_correct. auto.
Qed.
