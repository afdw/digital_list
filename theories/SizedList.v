Load Utils.

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

Fixpoint sized_list_push {A n} x (sl : sized_list A n) : sized_list A (S n) :=
  match sl with
  | [||] => [|x|]
  | y :||: sl' => y :||: sized_list_push x sl'
  end.

Theorem sized_list_push_correct :
  forall {A n} x (sl : sized_list A n),
  sized_list_to_list (sized_list_push x sl) = sized_list_to_list sl ++ [x].
Proof.
  intros ? ? ? ?. induction sl.
  - auto.
  - simpl. f_equal. auto.
Qed.

Fixpoint sized_list_pop {A n} (sl : sized_list A (S n)) : sized_list A n * A :=
  match sl with
  | @SizedListCons _ n0 x sl'0 => fun (H : S n0 = S n) =>
    let sl' := rew dependent (eq_add_S _ _ H) in sl'0 in
    match sl' with
    | [||] => fun _ =>
      ([||], x)
    | @SizedListCons _ n' y sl'' => fun (H0 : n = S n') =>
      let (sl'0, y) := sized_list_pop (rew H0 in sl') in
      (x :||: sl'0, y)
    end eq_refl
  end eq_refl.

Theorem sized_list_pop_correct :
  forall {A n} (sl : sized_list A (S n)),
  (let (sl0, x) := sized_list_pop sl in sized_list_to_list sl0 ++ [x]) = sized_list_to_list sl.
Proof.
  intros ? ?.
  cut (
    (fun n0 (H : n0 > 0) =>
      forall (sl : sized_list A n0),
        (let (sl0, x) := @sized_list_pop A (pred n0) (rew (Lt.S_pred_pos _ H) in sl) in
          @sized_list_to_list A (pred n0) sl0 ++ [x]) = @sized_list_to_list A n0 sl
    ) (S n) (Gt.gt_Sn_O _)
  ).
  - intros ? ?. simpl in H. rewrite <- H; clear H. unrew. destruct (@sized_list_pop A n sl). auto.
  - remember (Gt.gt_Sn_O n) as H. clear HeqH. remember (S n) as n0. clear Heqn0. intros ?.
    induction sl.
    + lia.
    + simpl. remember (sized_list_to_list sl) as l0. destruct l0.
      * clear IHsl. unrew. destruct sl; intuition discriminate.
      * assert (n0 > 0) by (destruct sl; [discriminate | lia]). rewrite <- (IHsl H0); clear IHsl Heql0.
        unrew. simpl. destruct sl.
        -- lia.
        -- do 2 unrew.
           replace (@sized_list_pop A (Nat.pred (S n0))) with (@sized_list_pop A n0) by auto.
           replace (@sized_list_to_list A (Nat.pred (S n0))) with (@sized_list_to_list A n0) by auto.
           destruct (sized_list_pop (a1 :||: sl)). rewrite sized_list_to_list_cons. auto.
Qed.
