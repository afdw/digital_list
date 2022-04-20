Load "NonDep/Array".

Inductive leaf_tree {A} :=
  | LeafTreeLeaf : A -> leaf_tree
  | LeafTreeInternalNode : array leaf_tree -> leaf_tree.

Arguments leaf_tree : clear implicits.

Inductive leaf_tree_complete {A} r : nat -> leaf_tree A -> Prop :=
  | LeafTreeCompleteLeaf : forall x, leaf_tree_complete r 0 (LeafTreeLeaf x)
  | LeafTreeCompleteInternalNode :
      forall {d} a,
      array_length a = r ->
      List.Forall (leaf_tree_complete r d) (array_to_list a) ->
      leaf_tree_complete r (S d) (LeafTreeInternalNode a).

Section Example.

Goal
  leaf_tree_complete 2 3 (
    LeafTreeInternalNode (Array [
      LeafTreeInternalNode (Array [
        LeafTreeInternalNode (Array [
          LeafTreeLeaf 0;
          LeafTreeLeaf 1
        ]);
        LeafTreeInternalNode (Array [
          LeafTreeLeaf 2;
          LeafTreeLeaf 3
        ])
      ]);
      LeafTreeInternalNode (Array [
        LeafTreeInternalNode (Array [
          LeafTreeLeaf 4;
          LeafTreeLeaf 5
        ]);
        LeafTreeInternalNode (Array [
          LeafTreeLeaf 6;
          LeafTreeLeaf 7
        ])
      ])
    ])
  ).
Proof.
  do 4 (constructor; auto; rewrite <- list_forall_equiv; simpl; repeat split).
Qed.

End Example.

Fixpoint leaf_tree_to_list {A} (lt : leaf_tree A) :=
  match lt with
  | LeafTreeLeaf x => [x]
  | LeafTreeInternalNode a => List.flat_map leaf_tree_to_list (array_to_list a)
  end.

Theorem complete_leaf_tree_to_list_length :
  forall {A} r d (lt : leaf_tree A),
  leaf_tree_complete r d lt ->
  length (leaf_tree_to_list lt) = Nat.pow r d.
Proof.
  intros ? ? ?. induction d; intros lt ?.
  - inversion H. auto.
  - inversion H. simpl. rewrite flat_map_length_constant_length with (k := Nat.pow r d).
    + rewrite array_to_list_length. auto.
    + rewrite list_forall_equiv. rewrite List.Forall_forall. rewrite List.Forall_forall in H2. auto.
Qed.

Inductive digital_list {A} :=
  | DigitalListNil : digital_list
  | DigitalListCons : array (leaf_tree A) -> digital_list -> digital_list.

Arguments digital_list : clear implicits.

Inductive concrete_digital_list {A} : Type :=
  | ConcreteDigitalList : forall (d : nat), digital_list A -> concrete_digital_list.

Arguments concrete_digital_list : clear implicits.

Inductive digital_list_good {A} r : nat -> digital_list A -> Prop :=
  | DigitalListGoodNil : digital_list_good r 0 DigitalListNil
  | DigitalListGoodCons :
      forall {d} (a : array (leaf_tree A)) (dl : digital_list A),
      array_length a < r ->
      list_forall (leaf_tree_complete r d) (array_to_list a) ->
      digital_list_good r d dl ->
      digital_list_good r (S d) (DigitalListCons a dl).

Fixpoint digital_list_to_list {A} (r d : nat) (dl : digital_list A) :=
  match dl with
  | DigitalListNil => []
  | DigitalListCons a dl' =>
    List.flat_map leaf_tree_to_list (array_to_list a) ++ digital_list_to_list r (pred d) dl'
  end.

Definition concrete_digital_list_to_list {A} r (cdl : concrete_digital_list A) :=
  let '(ConcreteDigitalList d dl) := cdl in digital_list_to_list r d dl.

Definition concrete_digital_list_good {A} r (cdl : concrete_digital_list A) :=
  let '(ConcreteDigitalList d dl) := cdl in digital_list_good r d dl.

Fixpoint digital_list_length {A} r d (dl : digital_list A) :=
  match dl with
  | DigitalListNil => 0
  | DigitalListCons a dl' => (Nat.pow r (pred d)) * (array_length a) + digital_list_length r (pred d) dl'
  end.

Definition concrete_digital_list_length {A} r (cdl : concrete_digital_list A) :=
  let '(ConcreteDigitalList d dl) := cdl in digital_list_length r d dl.

Theorem digital_list_length_correct :
  forall {A} r d (dl : digital_list A),
  digital_list_good r d dl ->
  digital_list_length r d dl = length (digital_list_to_list r d dl).
Proof.
  intros ? ? ? ? ?. induction H.
  - auto.
  - simpl. rewrite List.app_length. rewrite <- IHdigital_list_good.
    clear - a H0. destruct a as [l]. simpl. simpl in H0. induction l.
    + simpl. lia.
    + simpl. destruct H0 as (? & ?). rewrite <- mult_n_Sm. rewrite (PeanoNat.Nat.add_comm (Nat.pow _ _ * _)).
      rewrite <- PeanoNat.Nat.add_assoc. rewrite (IHl H0); clear IHl H0. rewrite List.app_length.
      rewrite (complete_leaf_tree_to_list_length r d _ H); clear H. lia.
Qed.

Theorem concrete_digital_list_length_correct :
  forall {A} r (cdl : concrete_digital_list A),
  concrete_digital_list_good r cdl ->
  concrete_digital_list_length r cdl = length (concrete_digital_list_to_list r cdl).
Proof.
  intros ? ? ? ?. destruct cdl as (d & dl). apply digital_list_length_correct. auto.
Qed.

Theorem digital_list_length_upper_bound :
  forall {A} r d (dl : digital_list A),
  digital_list_good r d dl ->
  digital_list_length r d dl < Nat.pow r d.
Proof.
  intros ? ? ? ? ?. induction H.
  - auto.
  - simpl. nia.
Qed.

Fixpoint complete_leaf_tree_nth {A} d il (lt : leaf_tree A) : option A :=
  match d with
  | 0 =>
    match lt with
    | LeafTreeLeaf x => Some x
    | LeafTreeInternalNode _ => None
    end
  | S d' =>
    match il with
    | [] => None
    | i :: il' =>
      match lt with
      | LeafTreeLeaf _ => None
      | LeafTreeInternalNode a => option_flat_map (complete_leaf_tree_nth d' il') (array_nth i a)
      end
    end
  end.

Section Example.

Compute
  complete_leaf_tree_nth
    3
    [1; 1; 0]
    (
      LeafTreeInternalNode (Array [
        LeafTreeInternalNode (Array [
          LeafTreeInternalNode (Array [
            LeafTreeLeaf 0;
            LeafTreeLeaf 1
          ]);
          LeafTreeInternalNode (Array [
            LeafTreeLeaf 2;
            LeafTreeLeaf 3
          ])
        ]);
        LeafTreeInternalNode (Array [
          LeafTreeInternalNode (Array [
            LeafTreeLeaf 4;
            LeafTreeLeaf 5
          ]);
          LeafTreeInternalNode (Array [
            LeafTreeLeaf 6;
            LeafTreeLeaf 7
          ])
        ])
      ])
    ).

End Example.

Theorem complete_leaf_tree_nth_correct :
  forall {A} r d il (lt : leaf_tree A),
  leaf_tree_complete r d lt ->
  length il = d ->
  list_forall (fun i => i < r) il ->
  complete_leaf_tree_nth d il lt = List.nth_error (leaf_tree_to_list lt) (indexes_list_to_index r d il).
Proof.
  intros ? ? ?. induction d; intros ? ? ? ? ?.
  - inversion H. subst lt. destruct il.
    + auto.
    + discriminate.
  - inversion H. subst d0 lt. destruct il.
    + discriminate.
    + rename n into i. destruct H1 as (? & ?). simpl.
      rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_nth_error_constant_length.
      * destruct a. simpl. remember (List.nth_error l i) as o. destruct o as [lt | ].
        -- symmetry in Heqo. apply List.nth_error_In in Heqo. apply (proj1 (List.Forall_forall _ _) H4) in Heqo.
           simpl. apply IHd; auto.
        -- auto.
      * rewrite list_forall_equiv. apply (@List.Forall_impl _ _ _ (complete_leaf_tree_to_list_length _ _) _ H4).
      * simpl in H0. injection H0 as ?. apply indexes_list_to_index_upper_bound; auto.
Qed.

Fixpoint complete_leaf_tree_update {A} d il x (lt : leaf_tree A) : option (leaf_tree A) :=
  match d with
  | 0 =>
    Some (LeafTreeLeaf x)
  | S d' =>
    match il with
    | [] => None
    | i :: il' =>
      match lt with
      | LeafTreeLeaf _ => None
      | LeafTreeInternalNode a =>
        option_map
          LeafTreeInternalNode
          (
            option_flat_map
              (fun lt' => array_update i lt' a)
              (option_flat_map (complete_leaf_tree_update d' il' x) (array_nth i a))
          )
      end
    end
  end.

Theorem complete_leaf_tree_update_correct :
  forall {A} r d x il (lt : leaf_tree A),
  leaf_tree_complete r d lt ->
  length il = d ->
  list_forall (fun i => i < r) il ->
  option_map leaf_tree_to_list (complete_leaf_tree_update d il x lt) =
    list_update (indexes_list_to_index r d il) x (leaf_tree_to_list lt).
Proof.
  intros ? ? ? ?. induction d; intros ? ? ? ? ?.
  - inversion H. subst lt. destruct il.
    + auto.
    + discriminate.
  - inversion H. subst d0 lt. destruct il.
    + discriminate.
    + rename n into i. destruct H1 as (? & ?). simpl.
      rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_update_constant_length.
      * destruct a. simpl. remember (List.nth_error l i) as o0. destruct o0 as [lt0 | ]; auto.
        simpl. rewrite <- IHd; auto; clear IHd.
        -- remember (complete_leaf_tree_update d il x lt0) as o1. destruct o1; auto. simpl.
           rewrite list_update_list_map. do 3 rewrite option_map_option_map. apply option_map_ext.
           intros l1. unfold Basics.compose. rewrite <- List.flat_map_concat_map. auto.
        -- symmetry in Heqo0. apply List.nth_error_In in Heqo0.
           apply (proj1 (List.Forall_forall _ _) H4) in Heqo0. auto.
      * rewrite list_forall_equiv. apply (@List.Forall_impl _ _ _ (complete_leaf_tree_to_list_length _ _) _ H4).
      * apply indexes_list_to_index_upper_bound; auto.
Qed.

Theorem complete_leaf_tree_update_complete :
  forall {A} r d x il (lt : leaf_tree A),
  leaf_tree_complete r d lt ->
  length il = d ->
  list_forall (fun i => i < r) il ->
  option_prop_to_prop (option_map (leaf_tree_complete r d) (complete_leaf_tree_update d il x lt)).
Proof.
  intros ? ? ? ?. induction d; intros ? ? ? ? ?.
  - simpl. apply LeafTreeCompleteLeaf.
  - inversion H. subst d0 lt. destruct il.
    + auto.
    + rename n into i. destruct H1 as (? & ?). destruct a. simpl.
      remember (List.nth_error l i) as o0. destruct o0 as [lt0 | ].
      * symmetry in Heqo0. apply List.nth_error_In in Heqo0. apply (proj1 (List.Forall_forall _ _) H4) in Heqo0.
        injection H0 as ?. specialize (IHd il lt0 Heqo0 H0 H2). simpl.
        remember (complete_leaf_tree_update d il x lt0) as o1. destruct o1 as [lt1 | ].
        -- simpl. remember (list_update i lt1 l) as o2. destruct o2 as [l0 | ].
           ++ simpl. apply LeafTreeCompleteInternalNode.
              ** symmetry in Heqo2. apply list_update_length in Heqo2. simpl. rewrite Heqo2. auto.
              ** symmetry in Heqo2. apply (list_forall_list_update_coarse _ _ (leaf_tree_complete r d)) in Heqo2.
                 --- rewrite <- list_forall_equiv. auto.
                 --- auto.
                 --- rewrite list_forall_equiv. auto.
           ++ simpl. auto.
        -- simpl. auto.
      * simpl. auto.
Qed.

Fixpoint complete_leaf_tree_pop {A} d (lt : leaf_tree A) : option (digital_list A * A) :=
  match d with
  | 0 =>
    match lt with
    | LeafTreeLeaf x => Some (DigitalListNil, x)
    | LeafTreeInternalNode _ => None
    end
  | S d' =>
    match lt with
    | LeafTreeLeaf _ => None
    | LeafTreeInternalNode a =>
      option_flat_map
        (fun '(sl0, x) =>
          option_map
            (fun '(dl', y) => (DigitalListCons sl0 dl', y))
            (complete_leaf_tree_pop d' x)
        )
        (array_pop a)
    end
  end.

Theorem complete_leaf_tree_pop_correct :
  forall {A} r d (lt : leaf_tree A),
  r > 1 ->
  leaf_tree_complete r d lt ->
  option_map
    (fun '(dl, x) => digital_list_to_list r d dl ++ [x])
    (complete_leaf_tree_pop d lt) = Some (leaf_tree_to_list lt).
Proof.
  intros ? ? ?. induction d; intros ? ? ?.
  - inversion H0. subst lt. auto.
  - inversion H0. subst d0 lt. destruct a. simpl. remember (list_pop l) as o0. symmetry in Heqo0.
    destruct o0 as [(l0, lt0) | ].
    + rewrite <- list_forall_equiv in H3. simpl in H3. apply (list_pop_list_forall _ _ l0 lt0 Heqo0) in H3.
      destruct H3 as (? & ?). specialize (IHd lt0 H H3).
      simpl. rewrite option_map_option_map. unfold Basics.compose.
      remember (complete_leaf_tree_pop d lt0) as o1. destruct o1 as [(dl0, x) | ].
      * simpl. f_equal. injection IHd as ?. rewrite <- List.app_assoc. rewrite H4.
        apply list_pop_Some in Heqo0. subst l. rewrite List.flat_map_app. simpl. rewrite List.app_nil_r. auto.
      * discriminate.
    + apply list_pop_None in Heqo0. subst l. simpl in H2. lia.
Qed.

Theorem complete_leaf_tree_pop_good :
  forall {A} r d (lt : leaf_tree A),
  r > 1 ->
  leaf_tree_complete r d lt ->
  option_prop_to_prop (
    option_map
      (fun '(dl, _) => digital_list_good r d dl)
      (complete_leaf_tree_pop d lt)
  ).
Proof.
  intros ? ? ?. induction d; intros ? ? ?.
  - inversion H0. subst lt. simpl. apply DigitalListGoodNil.
  - inversion H0. subst d lt. destruct a. simpl. remember (list_pop l) as o0. symmetry in Heqo0.
    destruct o0 as [(l0, lt0) | ].
    + rewrite <- list_forall_equiv in H3. simpl in H3. apply (list_pop_list_forall _ _ l0 lt0 Heqo0) in H3.
      destruct H3 as (? & ?). specialize (IHd lt0 H H3).
      simpl. remember (complete_leaf_tree_pop d0 lt0) as o1. destruct o1 as [(dl0, x) | ].
      * simpl. apply DigitalListGoodCons.
        -- apply list_pop_Some in Heqo0. subst l. simpl in H2. rewrite List.app_length in H2. simpl in H2.
           simpl. lia.
        -- auto.
        -- auto.
      * simpl. auto.
    + simpl. auto.
Qed.

Definition digital_list_empty {A} (r : nat) : digital_list A := DigitalListNil.

Definition concrete_digital_list_empty {A} r : concrete_digital_list A :=
  ConcreteDigitalList 0 (digital_list_empty r).

Theorem digital_list_empty_correct :
  forall {A} r,
  digital_list_to_list r 0 (digital_list_empty r : digital_list A) = [].
Proof.
  auto.
Qed.

Theorem digital_list_empty_good :
  forall {A} r,
  digital_list_good r 0 (digital_list_empty r : digital_list A).
Proof.
  intros ? ?. apply DigitalListGoodNil.
Qed.

Theorem concrete_digital_list_empty_correct :
  forall {A} r,
  concrete_digital_list_to_list r (concrete_digital_list_empty r : concrete_digital_list A) = [].
Proof.
  auto.
Qed.

Theorem concrete_digital_list_empty_good :
  forall {A} r,
  concrete_digital_list_good r (concrete_digital_list_empty r : concrete_digital_list A).
Proof.
  intros ? ?. apply digital_list_empty_good.
Qed.

Fixpoint digital_list_nth_inner {A} d il (dl : digital_list A) {struct dl} : option A :=
  match dl with
  | DigitalListNil =>
    None
  | DigitalListCons a dl' =>
    match il with
    | [] => None
    | i :: il' =>
      if Nat.eqb i (array_length a)
      then digital_list_nth_inner (pred d) il' dl'
      else option_flat_map (complete_leaf_tree_nth (pred d) il') (array_nth i a)
    end
  end.

Definition digital_list_nth {A} r d i (dl : digital_list A) : option A :=
  if Nat.ltb i (digital_list_length r d dl)
  then digital_list_nth_inner d (indexes_list_of_index r d i) dl
  else None.

Definition concrete_digital_list_nth {A} r i (cdl : concrete_digital_list A) : option A :=
  let '(ConcreteDigitalList d dl) := cdl in digital_list_nth r d i dl.

Theorem digital_list_nth_inner_correct :
  forall {A} r d il (dl : digital_list A),
  digital_list_good r d dl ->
  length il = d ->
  list_forall (fun i => i < r) il ->
  indexes_list_to_index r d il < digital_list_length r d dl ->
  digital_list_nth_inner d il dl =
    List.nth_error (digital_list_to_list r d dl) (indexes_list_to_index r d il).
Proof.
  intros ? ? ? ? ?. generalize dependent il. generalize dependent d. induction dl; intros ? ? ? ? ? ?.
  - simpl. symmetry. apply list_nth_error_nil.
  - destruct il.
    + simpl in H0. subst d. inversion H.
    + rename n into i. destruct H1 as (? & ?). inversion H. subst d a0 dl0.
      simpl in H7. injection H7 as ?.
      assert (length (List.flat_map leaf_tree_to_list (array_to_list a)) = Nat.pow r d0 * (array_length a)). {
        rewrite (flat_map_length_constant_length _ _ (Nat.pow r d0)).
        - rewrite array_to_list_length. lia.
        - rewrite list_forall_equiv. apply (@List.Forall_impl _ _ _ (complete_leaf_tree_to_list_length _ _) _).
          rewrite <- list_forall_equiv. auto.
      }
      simpl. destruct (PeanoNat.Nat.eqb_spec i (array_length a)).
      * subst i. rewrite IHdl; clear IHdl.
        -- rewrite List.nth_error_app2.
           ++ f_equal. rewrite H4. lia.
           ++ rewrite H4. lia.
        -- auto.
        -- auto.
        -- auto.
        -- simpl in H2. subst d0. lia.
      * clear IHdl. rewrite List.nth_error_app1.
        -- rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_nth_error_constant_length.
           ++ destruct a. simpl. remember (List.nth_error l i) as o. destruct o as [lt0 | ].
              ** symmetry in Heqo. apply List.nth_error_In in Heqo. rewrite list_forall_equiv in H8.
                 apply (proj1 (List.Forall_forall _ _) H8) in Heqo. simpl.
                 apply complete_leaf_tree_nth_correct; auto.
              ** auto.
           ++ rewrite list_forall_equiv.
              apply (@List.Forall_impl _ _ _ (complete_leaf_tree_to_list_length _ _) _).
              rewrite <- list_forall_equiv. auto.
           ++ apply indexes_list_to_index_upper_bound; auto.
        -- specialize (indexes_list_to_index_upper_bound r d0 il (eq_sym H0) H3) as ?.
           specialize (digital_list_length_upper_bound r d0 dl H9) as ?.
           rewrite H4. simpl in H2. subst d0. nia.
Qed.

Theorem digital_list_nth_correct :
  forall {A} r d i (dl : digital_list A),
  digital_list_good r d dl ->
  r > 1 ->
  digital_list_nth r d i dl = List.nth_error (digital_list_to_list r d dl) i.
Proof.
  intros ? ? ? ? ? ? ?. unfold digital_list_nth.
  destruct (PeanoNat.Nat.ltb_spec0 i (digital_list_length r d dl)).
  - assert (indexes_list_to_index r d (indexes_list_of_index r d i) = i). {
      apply indexes_list_to_of_correct.
      - auto.
      - apply (PeanoNat.Nat.le_trans _ _ _ l). apply PeanoNat.Nat.lt_le_incl.
        apply digital_list_length_upper_bound. auto.
    }
    rewrite (digital_list_nth_inner_correct r).
    + rewrite H1. auto.
    + auto.
    + apply indexes_list_of_index_length.
    + apply indexes_list_of_index_upper_bound. auto.
    + rewrite H1. auto.
  - rewrite digital_list_length_correct in n.
    + symmetry. apply List.nth_error_None. lia.
    + auto.
Qed.

Theorem concrete_digital_list_nth_correct :
  forall {A} r i (cdl : concrete_digital_list A),
  concrete_digital_list_good r cdl ->
  r > 1 ->
  concrete_digital_list_nth r i cdl = List.nth_error (concrete_digital_list_to_list r cdl) i.
Proof.
  intros ? ? ? ? ? ?. destruct cdl as (d & dl). apply digital_list_nth_correct; auto.
Qed.

Fixpoint digital_list_update_inner {A} d il x (dl : digital_list A) {struct dl} : option (digital_list A) :=
  match dl with
  | DigitalListNil =>
    None
  | DigitalListCons a dl' =>
    match il with
    | [] => None
    | i :: il' =>
      if Nat.eqb i (array_length a)
      then
        option_map
          (DigitalListCons a)
          (digital_list_update_inner (pred d) il' x dl')
      else
        option_map
          (fun a0 => DigitalListCons a0 dl')
          (
            option_flat_map
              (fun lt' => array_update i lt' a)
              (option_flat_map (complete_leaf_tree_update (pred d) il' x) (array_nth i a))
          )
    end
  end.

Definition digital_list_update {A} r d i x (dl : digital_list A) : option (digital_list A) :=
  if Nat.ltb i (digital_list_length r d dl)
  then digital_list_update_inner d (indexes_list_of_index r d i) x dl
  else None.

Definition concrete_digital_list_update {A} r i x (cdl : concrete_digital_list A) :
  option (concrete_digital_list A) :=
  let '(ConcreteDigitalList d dl) := cdl in
    option_map (ConcreteDigitalList d) (digital_list_update r d i x dl).

Theorem digital_list_update_inner_correct :
  forall {A} r d il x (dl : digital_list A),
  digital_list_good r d dl ->
  length il = d ->
  list_forall (fun i => i < r) il ->
  indexes_list_to_index r d il < digital_list_length r d dl ->
  option_map (digital_list_to_list r d) (digital_list_update_inner d il x dl) =
    list_update (indexes_list_to_index r d il) x (digital_list_to_list r d dl).
Proof.
  intros ? ? ? ? ? ?. generalize dependent il. generalize dependent d. induction dl; intros ? ? ? ? ? ?.
  - simpl. symmetry. apply list_update_nil.
  - destruct il.
    + simpl in H0. subst d. inversion H.
    + rename n into i. destruct H1 as (? & ?). inversion H. subst d a0 dl0.
      simpl in H7. injection H7 as ?.
      assert (length (List.flat_map leaf_tree_to_list (array_to_list a)) = Nat.pow r d0 * (array_length a)). {
        rewrite (flat_map_length_constant_length _ _ (Nat.pow r d0)).
        - rewrite array_to_list_length. lia.
        - rewrite list_forall_equiv. apply (@List.Forall_impl _ _ _ (complete_leaf_tree_to_list_length _ _) _).
          rewrite <- list_forall_equiv. auto.
      }
      simpl. destruct (PeanoNat.Nat.eqb_spec i (array_length a)).
      * subst i. rewrite list_update_app_2.
        -- rewrite H4.
           replace (Nat.pow r d0 * (array_length a) + indexes_list_to_index r d0 il -
             Nat.pow r d0 * (array_length a)) with (indexes_list_to_index r d0 il) by lia.
           rewrite <- IHdl; auto; try nia; clear IHdl.
           ++ remember (digital_list_update_inner d0 il x dl) as o0. destruct o0; auto.
           ++ simpl in H2. subst d0. lia.
        -- rewrite H4. lia.
      * clear IHdl. simpl. rewrite list_update_app_1.
        -- rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_update_constant_length.
           ++ destruct a. simpl. remember (List.nth_error l i) as o0. destruct o0; auto. simpl.
              rewrite option_map_option_map. unfold Basics.compose. simpl.
              replace (
                fun a0 => List.flat_map leaf_tree_to_list (array_to_list a0) ++ digital_list_to_list r d0 dl
              ) with (
                Basics.compose
                (fun l0 => l0 ++ digital_list_to_list r d0 dl)
                (
                  Basics.compose
                  (List.flat_map leaf_tree_to_list)
                  array_to_list
                )
              ) by auto.
              rewrite <- option_map_option_map. f_equal.
              rewrite <- option_map_option_map. rewrite option_map_option_flat_map.
              rewrite ? option_map_option_flat_map. rewrite <- complete_leaf_tree_update_correct.
              ** rewrite option_map_flat_option_map. unfold Basics.compose.
                 apply option_flat_map_ext. intros lt0. rewrite list_update_list_map.
                 remember (list_update i lt0 l) as o1. destruct o1; auto. simpl.
                 f_equal. apply List.flat_map_concat_map.
              ** symmetry in Heqo0. apply List.nth_error_In in Heqo0. rewrite list_forall_equiv in H8.
                 apply (proj1 (List.Forall_forall _ _) H8) in Heqo0. auto.
              ** auto.
              ** auto.
           ++ rewrite list_forall_equiv.
              apply (@List.Forall_impl _ _ _ (complete_leaf_tree_to_list_length _ _) _).
              rewrite <- list_forall_equiv. auto.
           ++ apply indexes_list_to_index_upper_bound; auto.
        -- specialize (indexes_list_to_index_upper_bound r d0 il (eq_sym H0) H3) as ?.
           specialize (digital_list_length_upper_bound r d0 dl H9) as ?.
           rewrite H4. simpl in H2. subst d0. nia.
Qed.

Theorem digital_list_update_inner_good :
  forall {A} r d il x (dl : digital_list A),
  digital_list_good r d dl ->
  length il = d ->
  list_forall (fun i => i < r) il ->
  indexes_list_to_index r d il < digital_list_length r d dl ->
  option_prop_to_prop (option_map (digital_list_good r d) (digital_list_update_inner d il x dl)).
Proof.
  intros ? ? ? ? ? ? ? ? ? ?. clear H2. generalize dependent H1. generalize dependent H0.
  generalize dependent H. generalize dependent il. generalize dependent d. induction dl; intros ? ? ? ? ?.
  - simpl. auto.
  - destruct il.
    + simpl. auto.
    + rename n into i. destruct H1 as (? & ?). inversion H. subst d a0 dl0.
      simpl in H6. injection H6 as ?.
      simpl. destruct (PeanoNat.Nat.eqb_spec i (array_length a)).
      * specialize (IHdl d0 il H8 (eq_sym H0) H2).
        remember (digital_list_update_inner d0 il x dl) as o0. destruct o0 as [dl0 | ].
        -- simpl. simpl in IHdl. apply DigitalListGoodCons; auto.
        -- simpl. auto.
      * destruct a. simpl. remember (List.nth_error l i) as o0. destruct o0 as [lt0 | ].
        -- simpl. remember (complete_leaf_tree_update d0 il x lt0) as o1. destruct o1 as [lt1 | ].
           ++ simpl. remember (list_update i lt1 l) as o2. destruct o2.
              ** simpl. apply DigitalListGoodCons.
                 --- symmetry in Heqo2. apply list_update_length in Heqo2. simpl. rewrite Heqo2. auto.
                 --- symmetry in Heqo0. apply List.nth_error_In in Heqo0. rewrite list_forall_equiv in H7.
                     apply (proj1 (List.Forall_forall _ _) H7) in Heqo0. rewrite <- list_forall_equiv in H7.
                     specialize (complete_leaf_tree_update_complete r d0 x il lt0 Heqo0 (eq_sym H0) H2) as ?.
                     rewrite <- Heqo1 in H3. simpl in H3.
                     apply (list_forall_list_update_coarse i lt1 _ l); auto.
                 --- auto.
              ** simpl. auto.
          ++ simpl. auto.
        -- simpl. auto.
Qed.

Theorem digital_list_update_correct :
  forall {A} r d i x (dl : digital_list A),
  digital_list_good r d dl ->
  r > 1 ->
  option_map (digital_list_to_list r d) (digital_list_update r d i x dl) =
    list_update i x (digital_list_to_list r d dl).
Proof.
  intros ? ? ? ? ? ? ? ?. unfold digital_list_update.
  destruct (PeanoNat.Nat.ltb_spec0 i (digital_list_length r d dl)).
  - assert (indexes_list_to_index r d (indexes_list_of_index r d i) = i). {
      apply indexes_list_to_of_correct.
      - auto.
      - apply (PeanoNat.Nat.le_trans _ _ _ l). apply PeanoNat.Nat.lt_le_incl.
        apply digital_list_length_upper_bound. auto.
    }
    rewrite (digital_list_update_inner_correct r).
    + rewrite H1. auto.
    + auto.
    + apply indexes_list_of_index_length.
    + apply indexes_list_of_index_upper_bound. auto.
    + rewrite H1. auto.
  - rewrite digital_list_length_correct in n.
    + symmetry. apply list_update_None. lia.
    + auto.
Qed.

Theorem digital_list_update_good :
  forall {A} r d i x (dl : digital_list A),
  digital_list_good r d dl ->
  r > 1 ->
  option_prop_to_prop (option_map (digital_list_good r d) (digital_list_update r d i x dl)).
Proof.
  intros ? ? ? ? ? ? ? ?. unfold digital_list_update.
  destruct (PeanoNat.Nat.ltb_spec0 i (digital_list_length r d dl)).
  - apply digital_list_update_inner_good.
    + auto.
    + apply indexes_list_of_index_length.
    + apply indexes_list_of_index_upper_bound. auto.
    + rewrite indexes_list_to_of_correct.
      * auto.
      * auto.
      * apply (PeanoNat.Nat.lt_trans _ _ _ l). apply digital_list_length_upper_bound. auto.
  - simpl. auto.
Qed.

Theorem concrete_digital_list_update_correct :
  forall {A} r i x (cdl : concrete_digital_list A),
  concrete_digital_list_good r cdl ->
  r > 1 ->
  option_map (concrete_digital_list_to_list r) (concrete_digital_list_update r i x cdl) =
    list_update i x (concrete_digital_list_to_list r cdl).
Proof.
  intros ? ? ? ? ? ? ?. destruct cdl as (d & dl). unfold concrete_digital_list_to_list. simpl.
  rewrite option_map_option_map. apply digital_list_update_correct; auto.
Qed.

Theorem concrete_digital_list_update_good :
  forall {A} r i x (cdl : concrete_digital_list A),
  concrete_digital_list_good r cdl ->
  r > 1 ->
  option_prop_to_prop (option_map (concrete_digital_list_good r) (concrete_digital_list_update r i x cdl)).
Proof.
  intros ? ? ? ? ? ? ?. destruct cdl as (d & dl). simpl. rewrite option_map_option_map.
  apply digital_list_update_good; auto.
Qed.

Fixpoint digital_list_push {A} r d (x : A) (dl : digital_list A) : option (leaf_tree A) * (digital_list A) :=
  match dl with
  | DigitalListNil =>
    (Some (LeafTreeLeaf x), DigitalListNil)
  | DigitalListCons a dl' =>
    match digital_list_push r (pred d) x dl' with
    | (None, dl'0) => (None, DigitalListCons a dl'0)
    | (Some lt0, dl'0) =>
      if Compare_dec.lt_dec (S (array_length a)) r
      then (None, DigitalListCons (array_push lt0 a) dl'0)
      else (Some (LeafTreeInternalNode (array_push lt0 a)), DigitalListCons array_empty dl'0)
    end
  end.

Definition concrete_digital_list_push {A} r x (cdl : concrete_digital_list A) : concrete_digital_list A :=
  let '(ConcreteDigitalList d dl) := cdl in
    match digital_list_push r d x dl with
    | (None, dl0) => ConcreteDigitalList d dl0
    | (Some lt0, dl0) => ConcreteDigitalList (S d) (DigitalListCons (array_single lt0) dl0)
    end.

Theorem digital_list_push_correct :
  forall {A} r d x (dl : digital_list A),
  digital_list_good r d dl ->
  r > 1 ->
  (let (lt0_o, dl0) := digital_list_push r d x dl in
    match lt0_o with
    | None => []
    | Some lt0 => leaf_tree_to_list lt0
    end ++ digital_list_to_list r d dl0) = digital_list_to_list r d dl ++ [x].
Proof.
  intros ? ? ? ? ?. generalize dependent d. induction dl; intros ? ? ?.
  - auto.
  - simpl. inversion H. subst d a0 dl0. simpl. specialize (IHdl d0 H6 H0).
    remember (digital_list_push r d0 x dl) as lt0_o_dl0. destruct lt0_o_dl0 as (lt0_o, dl0).
    destruct lt0_o as [lt0 | ].
    + destruct (Compare_dec.lt_dec (S (array_length a)) r).
      * simpl. rewrite <- List.app_assoc. rewrite <- IHdl.
        destruct a. simpl. rewrite List.flat_map_app. simpl.
        do 2 rewrite <- List.app_assoc. auto.
      * simpl. rewrite <- List.app_assoc. rewrite <- IHdl.
        destruct a. simpl. rewrite List.flat_map_app. simpl.
        do 2 rewrite <- List.app_assoc. auto.
    + simpl. simpl in IHdl. rewrite IHdl. apply List.app_assoc.
Qed.

Theorem digital_list_push_complete_good :
  forall {A} r d x (dl : digital_list A),
  digital_list_good r d dl ->
  r > 1 ->
  let (lt0_o, dl0) := digital_list_push r d x dl in
  option_prop_to_prop (option_map (leaf_tree_complete r d) lt0_o) /\
  digital_list_good r d dl0.
Proof.
  intros ? ? ? ? ?. generalize dependent d. induction dl; intros ? ? ?.
  - inversion H. subst d. simpl. split.
    + apply LeafTreeCompleteLeaf.
    + auto.
  - inversion H. subst d a0 dl0. simpl. specialize (IHdl d0 H6 H0).
    remember (digital_list_push r d0 x dl) as lt0_o_dl0. destruct lt0_o_dl0 as (lt0_o, dl0).
    destruct lt0_o as [lt0 | ].
    + simpl in IHdl. destruct IHdl as (? & ?). destruct (Compare_dec.lt_dec (S (array_length a)) r).
      * simpl. split; auto. apply DigitalListGoodCons.
        -- destruct a. simpl. rewrite List.app_length. simpl. simpl in l. lia.
        -- destruct a. simpl. rewrite list_forall_equiv. apply List.Forall_app. split.
           ++ rewrite <- list_forall_equiv. auto.
           ++ auto.
        -- auto.
      * simpl. split.
        -- apply LeafTreeCompleteInternalNode.
           ++ destruct a. simpl. rewrite List.app_length. simpl. simpl in H3, n. lia.
           ++ destruct a. simpl. apply List.Forall_app. split.
              ** rewrite <- list_forall_equiv. auto.
              ** auto.
        -- assert (array_length a + 1 = r) by lia. apply DigitalListGoodCons; simpl; auto; lia.
    + simpl in IHdl. destruct IHdl as (_ & ?). simpl. split; auto. apply DigitalListGoodCons; auto.
Qed.

Theorem concrete_digital_list_push_correct :
  forall {A} r x (cdl : concrete_digital_list A),
  concrete_digital_list_good r cdl ->
  r > 1 ->
  concrete_digital_list_to_list r (concrete_digital_list_push r x cdl) =
    concrete_digital_list_to_list r cdl ++ [x].
Proof.
  intros ? ? ? ? ? ?. destruct cdl as (d & dl). unfold concrete_digital_list_to_list. simpl.
  simpl in H. specialize (digital_list_push_complete_good r d x dl H H0) as ?.
  remember (digital_list_push r d x dl) as lt0_o_dl0. destruct lt0_o_dl0 as (lt0_o, dl0).
  destruct lt0_o as [lt0 | ].
  - simpl in H1. destruct H1 as (? & ?). rewrite <- digital_list_push_correct; auto.
    rewrite <- Heqlt0_o_dl0. simpl. rewrite <- List.app_assoc. auto.
  - simpl in H1. destruct H1 as (_ & ?). rewrite <- digital_list_push_correct; auto.
    rewrite <- Heqlt0_o_dl0. auto.
Qed.

Theorem concrete_digital_list_push_good :
  forall {A} r x (cdl : concrete_digital_list A),
  concrete_digital_list_good r cdl ->
  r > 1 ->
  concrete_digital_list_good r (concrete_digital_list_push r x cdl).
Proof.
  intros ? ? ? ? ? ?. destruct cdl as (d & dl). unfold concrete_digital_list_to_list. simpl.
  simpl in H. specialize (digital_list_push_complete_good r d x dl H H0) as ?.
  remember (digital_list_push r d x dl) as lt0_o_dl0. destruct lt0_o_dl0 as (lt0_o, dl0).
  destruct lt0_o as [lt0 | ].
  - simpl in H1. destruct H1 as (? & ?). simpl. apply DigitalListGoodCons; simpl; auto.
  - simpl in H1. destruct H1 as (? & ?). simpl. auto.
Qed.

Fixpoint digital_list_pop {A} (r : nat) d (dl : digital_list A) : option (digital_list A * A) :=
  match dl with
  | DigitalListNil => None
  | DigitalListCons a dl' =>
    match digital_list_pop r (pred d) dl' with
    | None =>
      option_flat_map
        (fun '(a0, blt) =>
          option_map
            (fun '(dl'0, x) => (DigitalListCons a0 dl'0, x))
            (complete_leaf_tree_pop (pred d) blt)
        )
        (array_pop a)
    | Some (dl'0, x) => Some (DigitalListCons a dl'0, x)
    end
  end.

Definition concrete_digital_list_pop {A} r (cdl : concrete_digital_list A) :
  option (concrete_digital_list A * A) :=
  let '(ConcreteDigitalList d dl) := cdl in
    option_map
      (fun '(dl0, x) => (ConcreteDigitalList d dl0, x))
      (digital_list_pop r d dl).

Lemma digital_list_pop_None :
  forall {A} r d (dl : digital_list A),
  digital_list_good r d dl ->
  r > 1 ->
  digital_list_pop r d dl = None ->
  digital_list_to_list r d dl = [].
Proof.
  intros ? ? ? ?. generalize dependent d. induction dl; intros ? ? ? ?.
  - auto.
  - inversion H. subst d a0 dl0.
    simpl in H1. remember (digital_list_pop r d0 dl) as o0. destruct o0 as [(dl'0, x) | ].
    + discriminate.
    + destruct a. simpl in H1. remember (list_pop l) as o1. destruct o1 as [(l0, lt0) | ].
      * symmetry in Heqo1. apply list_pop_Some in Heqo1. subst l. simpl in H6.
        rewrite list_forall_equiv in H6. rewrite List.Forall_app in H6. rewrite <- ? list_forall_equiv in H6.
        simpl in H6. destruct H6 as (? & ? & _).
        simpl in H1. specialize (complete_leaf_tree_pop_correct r d0 lt0 H0 H3) as ?.
        destruct (complete_leaf_tree_pop d0 lt0); discriminate.
      * symmetry in Heqo1. apply list_pop_None in Heqo1. subst l. simpl. apply IHdl; auto.
Qed.

Theorem digital_list_pop_correct :
  forall {A} r d (dl : digital_list A),
  digital_list_good r d dl ->
  r > 1 ->
  option_map
    (fun '(dl0, x) => (digital_list_to_list r d dl0, x))
    (digital_list_pop r d dl) = list_pop (digital_list_to_list r d dl).
Proof.
  intros ? ? ? ?. generalize dependent d. induction dl; intros ? ? ?.
  - auto.
  - inversion H. subst d a0 dl0. simpl. specialize (IHdl d0 H6 H0).
    remember (digital_list_pop r d0 dl) as o0. destruct o0 as [(dl'0, x) | ].
    + simpl. simpl in IHdl. symmetry in IHdl. eapply list_pop_app_Some in IHdl. rewrite IHdl. auto.
    + destruct a. simpl. remember (list_pop l) as l0_lt0. destruct l0_lt0 as [(l0, lt0) | ].
      * symmetry in Heql0_lt0. apply list_pop_Some in Heql0_lt0. subst l. simpl in H5.
        rewrite list_forall_equiv in H5. rewrite List.Forall_app in H5. rewrite <- ? list_forall_equiv in H5.
        simpl in H5. destruct H5 as (? & ? & _).
        simpl. rewrite option_map_option_map. unfold Basics.compose.
        specialize (complete_leaf_tree_pop_correct r d0 lt0 H0 H2) as ?.
        remember (complete_leaf_tree_pop d0 lt0) as o1. destruct o1 as [(dl0, x) | ]; try discriminate.
        simpl. simpl in H4. injection H4 as ?.
        rewrite List.flat_map_app. simpl. rewrite <- H4. rewrite List.app_nil_r. rewrite <- List.app_assoc.
        rewrite <- List.app_assoc. simpl.
        symmetry in Heqo0. apply digital_list_pop_None in Heqo0; auto. rewrite Heqo0.
        symmetry. apply list_pop_cons. apply List.app_assoc.
      * symmetry in Heql0_lt0. apply list_pop_None in Heql0_lt0. subst l. auto.
Qed.

Theorem digital_list_pop_good :
  forall {A} r d (dl : digital_list A),
  digital_list_good r d dl ->
  r > 1 ->
  option_prop_to_prop (option_map (fun '(dl0, _) => digital_list_good r d dl0) (digital_list_pop r d dl)).
Proof.
  intros ? ? ? ?. generalize dependent d. induction dl; intros ? ? ?.
  - simpl. auto.
  - inversion H. subst d a0 dl0. simpl. specialize (IHdl d0 H6 H0).
    remember (digital_list_pop r d0 dl) as o0. destruct o0 as [(dl'0, x) | ].
    + simpl. simpl in IHdl. apply DigitalListGoodCons; auto.
    + destruct a. simpl. remember (list_pop l) as l0_lt0. destruct l0_lt0 as [(l0, lt0) | ].
      * symmetry in Heql0_lt0. apply list_pop_Some in Heql0_lt0. subst l. simpl in H5.
        rewrite list_forall_equiv in H5. rewrite List.Forall_app in H5. rewrite <- ? list_forall_equiv in H5.
        simpl in H5. destruct H5 as (? & ? & _).
        simpl. rewrite option_map_option_map. unfold Basics.compose.
        specialize (complete_leaf_tree_pop_correct r d0 lt0 H0 H2) as ?.
        specialize (complete_leaf_tree_pop_good r d0 lt0 H0 H2) as ?.
        remember (complete_leaf_tree_pop d0 lt0) as o1. destruct o1 as [(dl0, x) | ]; try discriminate.
        simpl. simpl in H4. injection H4 as ?.
        apply DigitalListGoodCons.
        -- simpl in H3. rewrite List.app_length in H3. simpl in H3. simpl. lia.
        -- auto.
        -- auto.
      * simpl. auto.
Qed.

Theorem concrete_digital_list_pop_correct :
  forall {A} r (cdl : concrete_digital_list A),
  concrete_digital_list_good r cdl ->
  r > 1 ->
  option_map
    (fun '(cdl0, x) => (concrete_digital_list_to_list r cdl0, x))
    (concrete_digital_list_pop r cdl) = list_pop (concrete_digital_list_to_list r cdl).
Proof.
  intros ? ? ? ? ?. destruct cdl as (d & dl). unfold concrete_digital_list_to_list. simpl.
  rewrite option_map_option_map. unfold Basics.compose. rewrite <- digital_list_pop_correct; auto.
  apply option_map_ext. intros (dl0, x). auto.
Qed.

Theorem concrete_digital_list_pop_good :
  forall {A} r (cdl : concrete_digital_list A),
  concrete_digital_list_good r cdl ->
  r > 1 ->
  option_prop_to_prop (
    option_map (fun '(cdl0, _) => (concrete_digital_list_good r cdl0)) (concrete_digital_list_pop r cdl)
  ).
Proof.
  intros ? ? ? ? ?. destruct cdl as (d & dl). simpl.
  remember (digital_list_pop r d dl) as o. destruct o as [(dl', x) | ].
  - specialize (digital_list_pop_good r d dl H H0) as ?. rewrite <- Heqo in H1. auto.
  - simpl. auto.
Qed.

Section Example.

About concrete_digital_list_empty.
Check @concrete_digital_list_empty_correct.
Check @concrete_digital_list_empty_good.

About concrete_digital_list_nth.
Check @concrete_digital_list_nth_correct.

About concrete_digital_list_update.
Check @concrete_digital_list_update_correct.
Check @concrete_digital_list_update_good.

About concrete_digital_list_push.
Check @concrete_digital_list_push_correct.
Check @concrete_digital_list_push_good.

About concrete_digital_list_pop.
Check @concrete_digital_list_pop_correct.
Check @concrete_digital_list_pop_good.

End Example.
