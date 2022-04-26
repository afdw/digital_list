Load "Dep/Array".

Fixpoint complete_leaf_tree A r d :=
  match d with
  | 0 => A
  | S d' => array (complete_leaf_tree A r d') r
  end.

Section Example.

Compute complete_leaf_tree nat 2 3.

Check Array [|Array [|Array [|0; 1|]; Array [|2; 3|]|]; Array [|Array [|4; 5|]; Array [|6; 7|]|]|] :
  complete_leaf_tree nat 2 3.

End Example.

Fixpoint complete_leaf_tree_to_list {A r d} (clt : complete_leaf_tree A r d) :=
  match d with
  | 0 => fun (clt : complete_leaf_tree A r 0) =>
    [clt : A]
  | S d' => fun (clt : complete_leaf_tree A r (S d')) =>
    List.flat_map complete_leaf_tree_to_list (array_to_list clt)
  end clt.

Theorem complete_leaf_tree_to_list_length :
  forall {A r d} (clt : complete_leaf_tree A r d),
  length (complete_leaf_tree_to_list clt) = Nat.pow r d.
Proof.
  intros ? ? ?. induction d; intros clt.
  - auto.
  - simpl. rewrite flat_map_length_constant_length_for_type with (k := Nat.pow r d).
    + rewrite array_to_list_length. auto.
    + auto.
Qed.

Inductive digital_list {A r} : nat -> Type :=
  | DigitalListNil : digital_list 0
  | DigitalListCons :
      forall {d} k,
      k < r ->
      array (complete_leaf_tree A r d) k ->
      digital_list d ->
      digital_list (S d).

Arguments digital_list : clear implicits.

Inductive concrete_digital_list {A r} :=
  | ConcreteDigitalList : forall d, digital_list A r d -> concrete_digital_list.

Arguments concrete_digital_list : clear implicits.

Fixpoint digital_list_to_list {A r d} (dl : digital_list A r d) :=
  match dl with
  | DigitalListNil => []
  | DigitalListCons k _ a dl' =>
    List.flat_map complete_leaf_tree_to_list (array_to_list a) ++ digital_list_to_list dl'
  end.

Definition concrete_digital_list_to_list {A r} (cdl : concrete_digital_list A r) :=
  let '(ConcreteDigitalList _ dl) := cdl in digital_list_to_list dl.

Section Example.

Compute array (complete_leaf_tree nat 2 3) 2.

Check
  DigitalListCons _ (le_n _)
  (Array [|Array [|Array [|Array [|0; 1|]; Array [|2; 3|]|]; Array [|Array [|4; 5|]; Array [|6; 7|]|]|]|] :
    array (complete_leaf_tree _ _ 3) _)
  (
    DigitalListCons _ (le_S _ _ (le_n _))
    (Array [||])
    (
      DigitalListCons _ (le_n _)
      (Array [| Array [|8; 9|]|] : array (complete_leaf_tree _ _ 1) _)
      (
        DigitalListCons _ (le_S _ _ (le_n _))
        (Array [||])
        DigitalListNil
      )
    )
  ).

End Example.

Fixpoint digital_list_length {A r d} (dl : digital_list A r d) :=
  match dl with
  | DigitalListNil => 0
  | DigitalListCons k _ _ dl' => (Nat.pow r (pred d)) * k + digital_list_length dl'
  end.

Definition concrete_digital_list_length {A r} (cdl : concrete_digital_list A r) :=
  let '(ConcreteDigitalList _ dl) := cdl in digital_list_length dl.

Theorem digital_list_length_correct :
  forall {A r d} (dl : digital_list A r d),
  digital_list_length dl = length (digital_list_to_list dl).
Proof.
  intros ? ? ? ?. induction dl.
  - auto.
  - simpl. rewrite IHdl; clear IHdl. rewrite List.app_length. apply PeanoNat.Nat.add_cancel_r.
    clear - a. destruct a as [sl]. unfold array_to_list. induction sl.
    + auto.
    + rewrite <- mult_n_Sm. rewrite IHsl; clear IHsl. simpl. rewrite List.app_length.
      rewrite complete_leaf_tree_to_list_length. lia.
Qed.

Theorem concrete_digital_list_length_correct :
  forall {A r} (cdl : concrete_digital_list A r),
  concrete_digital_list_length cdl = length (concrete_digital_list_to_list cdl).
Proof.
  intros ? ? ?. destruct cdl as (d & dl). apply digital_list_length_correct.
Qed.

Theorem digital_list_length_upper_bound :
  forall {A r d} (dl : digital_list A r d),
  digital_list_length dl < Nat.pow r d.
Proof.
  intros ? ? ? ?. induction dl.
  - auto.
  - simpl. nia.
Qed.

Fixpoint complete_leaf_tree_nth {A r d} (isl : sized_list nat d) (clt : complete_leaf_tree A r d) : option A :=
  match d with
  | 0 => fun (isl : sized_list nat 0) (clt : complete_leaf_tree A r 0) =>
    Some (clt : A)
  | S d' => fun (isl : sized_list nat (S d')) (clt : complete_leaf_tree A r (S d')) =>
    match isl with
    | @SizedListCons _ d'0 i isl'0 => fun (Heqd : S d'0 = S d') =>
      let isl' := rew (eq_add_S _ _ Heqd) in isl'0 in
      option_flat_map (complete_leaf_tree_nth isl') (array_nth i clt)
    end eq_refl
  end isl clt.

Section Example.

Compute
  complete_leaf_tree_nth
    [|1; 1; 0|]
    (Array [|Array [|Array [|0; 1|]; Array [|2; 3|]|]; Array [|Array [|4; 5|]; Array [|6; 7|]|]|]).

End Example.

Theorem complete_leaf_tree_nth_correct :
  forall {A r d} (isl : sized_list nat d) (clt : complete_leaf_tree A r d),
  sized_list_forall (fun i => i < r) isl ->
  complete_leaf_tree_nth isl clt =
    List.nth_error (complete_leaf_tree_to_list clt) (indexes_sized_list_to_index r isl).
Proof.
  intros ? ? ?. induction d; intros ? ? ?.
  - remember 0. destruct isl.
    + auto.
    + discriminate.
  - remember (S d) as d0. destruct isl.
    + discriminate.
    + injection Heqd0 as ->. destruct H as (? & ?). simpl.
      rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_nth_error_constant_length_for_type.
      * rewrite array_nth_correct. apply option_flat_map_ext. intros clt'. apply IHd. auto.
      * apply complete_leaf_tree_to_list_length.
      * apply indexes_sized_list_to_index_upper_bound. auto.
Qed.

Fixpoint complete_leaf_tree_update {A r d} (isl : sized_list nat d)
  (x : A) (clt : complete_leaf_tree A r d) : option (complete_leaf_tree A r d) :=
  match d with
  | 0 => fun (isl : sized_list nat 0) (clt : complete_leaf_tree A r 0) =>
    Some (x : complete_leaf_tree A r 0)
  | S d' => fun (isl : sized_list nat (S d')) (clt : complete_leaf_tree A r (S d')) =>
    match isl with
    | @SizedListCons _ d'0 i isl'0 => fun (Heqd : S d'0 = S d') =>
      let isl' := rew (eq_add_S _ _ Heqd) in isl'0 in
      option_flat_map
        (fun clt' => array_update i clt' clt)
        (option_flat_map (complete_leaf_tree_update isl' x) (array_nth i clt))
    end eq_refl : option (complete_leaf_tree A r (S d'))
  end isl clt.

Theorem complete_leaf_tree_update_correct :
  forall {A r d} x (isl : sized_list nat d) (clt : complete_leaf_tree A r d),
  sized_list_forall (fun i => i < r) isl ->
  option_map complete_leaf_tree_to_list (complete_leaf_tree_update isl x clt) =
    list_update (indexes_sized_list_to_index r isl) x (complete_leaf_tree_to_list clt).
Proof.
  intros ? ? ? ?. induction d; intros ? ? ?.
  - simpl. remember (indexes_sized_list_to_index r (d := 0) isl) as i. destruct i.
    + auto.
    + exfalso. remember 0. destruct isl; discriminate.
  - remember (S d) as d0. destruct isl.
    + discriminate.
    + rename n0 into i. injection Heqd0 as ->. destruct H as (? & ?). simpl. fold complete_leaf_tree.
      rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_update_constant_length_for_type.
      * rewrite array_nth_correct. remember (List.nth_error (array_to_list clt) i) as o0.
        fold complete_leaf_tree in o0. setoid_rewrite <- Heqo0. destruct o0 as [clt0 | ]; auto.
        simpl. rewrite <- IHd; auto; clear IHd. remember (complete_leaf_tree_update isl x clt0) as o1.
        destruct o1; auto. simpl.
        replace (
          fun clt0 =>
            @List.flat_map (complete_leaf_tree A r d) A (@complete_leaf_tree_to_list A r d)
              (@array_to_list (complete_leaf_tree A r d) r clt0)
        ) with (
          Basics.compose
          (@List.flat_map (complete_leaf_tree A r d) A (@complete_leaf_tree_to_list A r d))
          (fun clt0 => @array_to_list (complete_leaf_tree A r d) r clt0)
        ) by auto.
        rewrite <- option_map_option_map. rewrite array_update_correct.
        rewrite (option_map_ext _ _ _ (List.flat_map_concat_map _)).
        replace (
          fun (l : list (complete_leaf_tree A r d)) => List.concat (List.map complete_leaf_tree_to_list l)
        ) with (
          Basics.compose
          (@List.concat _)
          (List.map (@complete_leaf_tree_to_list A r d))
        ) by auto.
        rewrite <- option_map_option_map. f_equal.
        symmetry. apply list_update_list_map.
      * apply complete_leaf_tree_to_list_length.
      * apply indexes_sized_list_to_index_upper_bound. auto.
Qed.

Fixpoint complete_leaf_tree_pop {A r d} (clt : complete_leaf_tree A r d) : option (digital_list A r d * A) :=
  match d with
  | 0 => fun (Heqd : d = 0) (clt : complete_leaf_tree A r 0) =>
    Some (DigitalListNil, clt : A)
  | S d' => fun (Heqd : d = S d') =>
    match r with
    | 0 => fun _ _ => None
    | S r' => fun (Heqn : r = S r') (clt : complete_leaf_tree A (S r') (S d')) =>
      let (sl0, x) := array_pop clt in
      option_map
        (fun '(dl', y) => (DigitalListCons r' (le_n _) sl0 dl', y))
        (complete_leaf_tree_pop x)
    end eq_refl
  end eq_refl clt.

Theorem complete_leaf_tree_pop_correct :
  forall {A r d} (clt : complete_leaf_tree A r d),
  r > 1 ->
  option_map
    (fun '(dl, x) => digital_list_to_list dl ++ [x])
    (complete_leaf_tree_pop clt) = Some (complete_leaf_tree_to_list clt).
Proof.
  intros ? ? ? ? ?. induction d.
  - auto.
  - simpl. destruct r; try lia. remember (array_pop clt) as a0_clt0. fold complete_leaf_tree in a0_clt0.
    destruct a0_clt0 as (a0, clt0). rewrite option_map_option_map. unfold Basics.compose.
    specialize (IHd clt0). remember (complete_leaf_tree_pop clt0) as o0.
    destruct o0  as [(dl0, x) | ]; try discriminate. simpl. f_equal. simpl in IHd. injection IHd as ?.
    rewrite <- List.app_assoc. rewrite H0. specialize (array_pop_correct clt) as ?. rewrite <- Heqa0_clt0 in H1.
    rewrite <- H1. rewrite List.flat_map_app. simpl. rewrite List.app_nil_r. auto.
Qed.

Definition digital_list_empty {A r} : digital_list A r 0 := DigitalListNil.

Definition concrete_digital_list_empty {A r} : concrete_digital_list A r :=
  ConcreteDigitalList 0 digital_list_empty.

Theorem digital_list_empty_correct :
  forall {A r},
  digital_list_to_list (digital_list_empty : digital_list A r 0) = [].
Proof.
  auto.
Qed.

Theorem concrete_digital_list_empty_correct :
  forall {A r},
  concrete_digital_list_to_list (concrete_digital_list_empty : concrete_digital_list A r) = [].
Proof.
  auto.
Qed.

Fixpoint digital_list_nth_inner {A r d} (isl : sized_list nat d) (dl : digital_list A r d)
  {struct dl} : option A :=
  match dl with
  | DigitalListNil => fun (isl : sized_list nat 0) =>
    None
  | @DigitalListCons _ _ d' k _ a dl' => fun (isl : sized_list nat (S d')) =>
    match isl with
    | @SizedListCons _ d'0 i isl'0 => fun (Heqd : S d'0 = S d') =>
      let isl' := rew (eq_add_S _ _ Heqd) in isl'0 in
      if Nat.eqb i k
      then digital_list_nth_inner isl' dl'
      else option_flat_map (complete_leaf_tree_nth isl') (array_nth i a)
    end eq_refl
  end isl.

Definition digital_list_nth {A r d} i (dl : digital_list A r d) : option A :=
  if Nat.ltb i (digital_list_length dl)
  then digital_list_nth_inner (indexes_sized_list_of_index r i) dl
  else None.

Definition concrete_digital_list_nth {A r} i (cdl : concrete_digital_list A r) : option A :=
  let '(ConcreteDigitalList _ dl) := cdl in digital_list_nth i dl.

Theorem digital_list_nth_inner_correct :
  forall {A r d} (isl : sized_list nat d) (dl : digital_list A r d),
  sized_list_forall (fun i => i < r) isl ->
  indexes_sized_list_to_index r isl < digital_list_length dl ->
  digital_list_nth_inner isl dl =
    List.nth_error (digital_list_to_list dl) (indexes_sized_list_to_index r isl).
Proof.
  intros ? ? ? ? ? ? ?. induction dl.
  - simpl. symmetry. apply list_nth_error_nil.
  - simpl. dependent destruction isl. rename n0 into i.
    unrew. destruct H as (? & ?). simpl in H0.
    assert (length (List.flat_map complete_leaf_tree_to_list (array_to_list a)) = Nat.pow r d * k). {
      rewrite (flat_map_length_constant_length_for_type _ _ (Nat.pow r d)).
      - rewrite array_to_list_length. lia.
      - apply complete_leaf_tree_to_list_length.
    }
    destruct (PeanoNat.Nat.eqb_spec i k).
    + subst i. rewrite IHdl; auto; try nia; clear IHdl. simpl. rewrite List.nth_error_app2.
      * f_equal. rewrite H2. lia.
      * rewrite H2. lia.
    + clear IHdl. simpl. rewrite List.nth_error_app1.
      * rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_nth_error_constant_length_for_type.
        -- rewrite <- array_nth_correct. apply option_flat_map_ext. intros clt.
           apply complete_leaf_tree_nth_correct. auto.
        -- apply complete_leaf_tree_to_list_length.
        -- apply indexes_sized_list_to_index_upper_bound. auto.
      * specialize (indexes_sized_list_to_index_upper_bound isl H1) as ?.
        specialize (digital_list_length_upper_bound dl) as ?.
        rewrite H2. nia.
Qed.

Theorem digital_list_nth_correct :
  forall {A r d} i (dl : digital_list A r d),
  r > 1 ->
  digital_list_nth i dl = List.nth_error (digital_list_to_list dl) i.
Proof.
  intros ? ? ? ? ? ?. unfold digital_list_nth.
  destruct (PeanoNat.Nat.ltb_spec0 i (digital_list_length dl)).
  - assert (indexes_sized_list_to_index r (d := d) (indexes_sized_list_of_index r i) = i). {
      apply indexes_sized_list_to_of_correct.
      - auto.
      - apply (PeanoNat.Nat.le_trans _ _ _ l). apply PeanoNat.Nat.lt_le_incl.
        apply digital_list_length_upper_bound.
    }
    rewrite digital_list_nth_inner_correct.
    + rewrite H0. auto.
    + apply indexes_sized_list_of_index_upper_bound. auto.
    + rewrite H0. auto.
  - rewrite digital_list_length_correct in n. symmetry. apply List.nth_error_None. lia.
Qed.

Theorem concrete_digital_list_nth_correct :
  forall {A r} i (cdl : concrete_digital_list A r),
  r > 1 ->
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
      (Array [|Array [|Array [|Array [|0; 1|]; Array [|2; 3|]|]; Array [|Array [|4; 5|]; Array [|6; 7|]|]|]|] :
        array (complete_leaf_tree _ _ 3) _)
      (
        DigitalListCons _ (le_S _ _ (le_n _))
        (Array [||])
        (
          DigitalListCons _ (le_n _)
          (Array [| Array [|8; 9|]|] : array (complete_leaf_tree _ _ 1) _)
          (
            DigitalListCons _ (le_S _ _ (le_n _))
            (Array [||])
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

Fixpoint digital_list_update_inner {A r d} (isl : sized_list nat d) (x : A) (dl : digital_list A r d)
  {struct dl} : option (digital_list A r d) :=
  match dl with
  | DigitalListNil => fun (isl : sized_list nat 0) =>
    None
  | @DigitalListCons _ _ d' k Hlt a dl' => fun (isl : sized_list nat (S d')) =>
    match isl with
    | @SizedListCons _ d'0 i isl'0 => fun (Heqd : S d'0 = S d') =>
      let isl' := rew (eq_add_S _ _ Heqd) in isl'0 in
      if Nat.eqb i k
      then
        option_map
          (DigitalListCons k Hlt a)
          (digital_list_update_inner isl' x dl')
      else
        option_map
          (fun a0 => DigitalListCons k Hlt a0 dl')
          (
            option_flat_map
              (fun clt' => array_update i clt' a)
              (option_flat_map (complete_leaf_tree_update isl' x) (array_nth i a))
          )
    end eq_refl : option (digital_list A r (S d'))
  end isl.

Definition digital_list_update {A r d} i x (dl : digital_list A r d) : option (digital_list A r d) :=
  if Nat.ltb i (digital_list_length dl)
  then digital_list_update_inner (indexes_sized_list_of_index r i) x dl
  else None.

Definition concrete_digital_list_update {A r} i x (cdl : concrete_digital_list A r) :
  option (concrete_digital_list A r) :=
  let '(ConcreteDigitalList _ dl) := cdl in
    option_map (ConcreteDigitalList _) (digital_list_update i x dl).

Theorem digital_list_update_inner_correct :
  forall {A r d} (isl : sized_list nat d) x (dl : digital_list A r d),
  sized_list_forall (fun i => i < r) isl ->
  indexes_sized_list_to_index r isl < digital_list_length dl ->
  option_map digital_list_to_list (digital_list_update_inner isl x dl) =
    list_update (indexes_sized_list_to_index r isl) x (digital_list_to_list dl).
Proof.
  intros ? ? ? ? ? ? ? ?. induction dl.
  - simpl. symmetry. apply list_update_nil.
  - simpl. dependent destruction isl. rename n0 into i.
    unrew. destruct H as (? & ?). simpl in H0.
    assert (length (List.flat_map complete_leaf_tree_to_list (array_to_list a)) = Nat.pow r d * k). {
      rewrite (flat_map_length_constant_length_for_type _ _ (Nat.pow r d)).
      - rewrite array_to_list_length. lia.
      - apply complete_leaf_tree_to_list_length.
    }
    destruct (PeanoNat.Nat.eqb_spec i k).
    + subst i. simpl. rewrite list_update_app_2.
      * rewrite H2.
        replace (Nat.pow r d * k + indexes_sized_list_to_index r isl - Nat.pow r d * k)
          with (indexes_sized_list_to_index r isl) by lia.
        rewrite <- IHdl; auto; try nia; clear IHdl.
        remember (digital_list_update_inner isl x dl) as o0. destruct o0; auto.
      * rewrite H2. lia.
    + clear IHdl. simpl. rewrite list_update_app_1.
      * rewrite PeanoNat.Nat.mul_comm. rewrite flat_map_list_update_constant_length_for_type.
        -- rewrite <- array_nth_correct. remember (array_nth i a) as o0. destruct o0; auto. simpl.
           rewrite option_map_option_map. unfold Basics.compose. simpl.
           replace (
             fun (a0 : array (complete_leaf_tree A r d) k) =>
               List.flat_map complete_leaf_tree_to_list (array_to_list a0) ++ digital_list_to_list dl
           ) with (
             Basics.compose
             (fun l0 => l0 ++ digital_list_to_list dl)
             (
               Basics.compose
               (List.flat_map complete_leaf_tree_to_list)
               (@array_to_list (complete_leaf_tree A r d) k)
             )
           ) by auto.
           rewrite <- option_map_option_map. f_equal.
           rewrite <- option_map_option_map. rewrite option_map_option_flat_map.
           rewrite (option_flat_map_ext _ _ _ (fun _ => array_update_correct _ _ _)).
           rewrite ? option_map_option_flat_map. rewrite <- complete_leaf_tree_update_correct.
           rewrite option_map_flat_option_map. unfold Basics.compose.
           apply option_flat_map_ext. intros clt0. rewrite list_update_list_map.
           ++ remember (list_update i clt0 (array_to_list a)) as o1. destruct o1; auto. simpl.
              f_equal. apply List.flat_map_concat_map.
           ++ auto.
        -- apply complete_leaf_tree_to_list_length.
        -- apply indexes_sized_list_to_index_upper_bound. auto.
      * specialize (indexes_sized_list_to_index_upper_bound isl H1) as ?.
        specialize (digital_list_length_upper_bound dl) as ?.
        rewrite H2. nia.
Qed.

Theorem digital_list_update_correct :
  forall {A r d} i x (dl : digital_list A r d),
  r > 1 ->
  option_map digital_list_to_list (digital_list_update i x dl) = list_update i x (digital_list_to_list dl).
Proof.
  intros ? ? ? ? ? ? ?. unfold digital_list_update.
  destruct (PeanoNat.Nat.ltb_spec0 i (digital_list_length dl)).
  - assert (indexes_sized_list_to_index r (d := d) (indexes_sized_list_of_index r i) = i). {
      apply indexes_sized_list_to_of_correct.
      - auto.
      - apply (PeanoNat.Nat.le_trans _ _ _ l). apply PeanoNat.Nat.lt_le_incl.
        apply digital_list_length_upper_bound.
    }
    rewrite digital_list_update_inner_correct.
    + rewrite H0. auto.
    + apply indexes_sized_list_of_index_upper_bound. auto.
    + rewrite H0. auto.
  - rewrite digital_list_length_correct in n. symmetry. apply list_update_None. lia.
Qed.

Theorem concrete_digital_list_update_correct :
  forall {A r} i x (cdl : concrete_digital_list A r),
  r > 1 ->
  option_map concrete_digital_list_to_list (concrete_digital_list_update i x cdl) =
    list_update i x (concrete_digital_list_to_list cdl).
Proof.
  intros ? ? ? ? ? ?. destruct cdl as (d & dl). unfold concrete_digital_list_to_list. simpl.
  rewrite option_map_option_map. apply digital_list_update_correct. auto.
Qed.

Fixpoint digital_list_push {A r d} (x : A) (dl : digital_list A r d) :
  option (complete_leaf_tree A r d) * (digital_list A r d) :=
  match dl with
  | DigitalListNil => fun _ =>
    (Some (x : complete_leaf_tree A r 0), DigitalListNil)
  | @DigitalListCons _ _ d' k Hlt a dl' => fun (Heqd : d = S d') =>
    match digital_list_push x dl' with
    | (None, dl'0) => (None, @DigitalListCons _ _ d' k Hlt a dl'0)
    | (Some clt0, dl'0) =>
      match Compare_dec.le_lt_eq_dec (S k) r Hlt with
      | left Hlt0 => (None, @DigitalListCons _ _ d' (S k) Hlt0 (array_push clt0 a) dl'0)
      | right Heq =>
        match Compare_dec.zerop r with
        | left _ => (None, @DigitalListCons _ _ d' k Hlt a dl'0)
        | right Hlt0 => (Some (rew Heq in (array_push clt0 a)), @DigitalListCons _ _ d' 0 Hlt0 array_empty dl'0)
        end
      end
    end
  end eq_refl.

Definition concrete_digital_list_push {A r} (x : A) (cdl : concrete_digital_list A r) :
  concrete_digital_list A r :=
  let '(ConcreteDigitalList d dl) := cdl in
    match digital_list_push x dl with
    | (None, dl0) => ConcreteDigitalList d dl0
    | (Some clt0, dl0) =>
      match Compare_dec.lt_dec 1 r with
      | left Hlt => ConcreteDigitalList (S d) (@DigitalListCons _ _ d 1 Hlt (array_single clt0) dl0)
      | right _ => ConcreteDigitalList d dl
      end
    end.

Theorem digital_list_push_correct :
  forall {A r d} x (dl : digital_list A r d),
  r > 1 ->
  (let (clt0_o, dl0) := digital_list_push x dl in
    match clt0_o with
    | None => []
    | Some clt0 => complete_leaf_tree_to_list clt0
    end ++ digital_list_to_list dl0) = digital_list_to_list dl ++ [x].
Proof.
  intros ? ? ? ? ? ?. induction dl.
  - auto.
  - simpl. fold complete_leaf_tree.
    remember (digital_list_push x dl) as clt0_o_dl0. destruct clt0_o_dl0 as (clt0_o, dl0).
    destruct clt0_o as [clt0 | ].
    + destruct (Compare_dec.le_lt_eq_dec (S k) r l).
      * simpl. rewrite <- List.app_assoc. rewrite <- IHdl.
        rewrite array_push_correct. rewrite List.flat_map_app. simpl.
        do 2 rewrite <- List.app_assoc. auto.
      * destruct (Compare_dec.zerop r); try lia. simpl. rewrite <- List.app_assoc. rewrite <- IHdl.
        unrew. rewrite array_push_correct. rewrite List.flat_map_app. simpl.
        do 2 rewrite <- List.app_assoc. auto.
    + simpl. simpl in IHdl. rewrite IHdl. apply List.app_assoc.
Qed.

Theorem concrete_digital_list_push_correct :
  forall {A r} x (cdl : concrete_digital_list A r),
  r > 1 ->
  concrete_digital_list_to_list (concrete_digital_list_push x cdl) =
    concrete_digital_list_to_list cdl ++ [x].
Proof.
  intros ? ? ? ? ?. destruct cdl as (d & dl). unfold concrete_digital_list_to_list. simpl.
  rewrite <- digital_list_push_correct; auto.
  remember (digital_list_push x dl) as clt0_o_dl0. destruct clt0_o_dl0 as (clt0_o, dl0).
  destruct clt0_o as [clt0 | ].
  - destruct (Compare_dec.lt_dec 1 r); try lia. simpl. rewrite <- List.app_assoc. auto.
  - auto.
Qed.

Fixpoint digital_list_pop {A r d} (dl : digital_list A r d) : option (digital_list A r d * A) :=
  match dl with
  | DigitalListNil => None
  | @DigitalListCons _ _ d' k Hlt a dl' =>
    match digital_list_pop dl' with
    | None =>
      match k with
      | 0 => fun _ _ =>
        None
      | S k' => fun (a : array (complete_leaf_tree A r d') (S k')) (Hlt : S k' < r) =>
        let (a0, blt) := array_pop a in
        option_map
          (fun '(dl'0, x) => (@DigitalListCons _ _ d' k' (PeanoNat.Nat.lt_succ_l _ _ Hlt) a0 dl'0, x))
          (complete_leaf_tree_pop blt)
      end a Hlt
    | Some (dl'0, x) => Some (@DigitalListCons _ _ d' k Hlt a dl'0, x)
    end
  end.

Definition concrete_digital_list_pop {A r} (cdl : concrete_digital_list A r) :
  option (concrete_digital_list A r * A) :=
  let '(ConcreteDigitalList d dl) := cdl in
    option_map
      (fun '(dl0, x) => (ConcreteDigitalList d dl0, x))
      (digital_list_pop dl).

Lemma digital_list_pop_None :
  forall {A r d} (dl : digital_list A r d),
  r > 1 ->
  digital_list_pop dl = None ->
  digital_list_to_list dl = [].
Proof.
  intros ? ? ? ? ? ?. induction dl.
  - auto.
  - simpl. simpl in H0. remember (digital_list_pop dl) as o0. destruct o0 as [(dl'0, x) | ].
    + discriminate.
    + destruct k.
      * remember 0. destruct a as [sl]. destruct sl; try discriminate. rewrite IHdl; auto.
      * remember (array_pop a) as a0_clt0. destruct a0_clt0 as (a0, clt0).
        specialize (complete_leaf_tree_pop_correct clt0 H) as ?.
        remember (complete_leaf_tree_pop clt0) as o1. destruct o1; discriminate.
Qed.

Theorem digital_list_pop_correct :
  forall {A r d} (dl : digital_list A r d),
  r > 1 ->
  option_map
    (fun '(dl0, x) => (digital_list_to_list dl0, x))
    (digital_list_pop dl) = list_pop (digital_list_to_list dl).
Proof.
  intros ? ? ? ? ?. induction dl.
  - auto.
  - simpl. remember (digital_list_pop dl) as o0. destruct o0 as [(dl'0, x) | ].
    + simpl. simpl in IHdl. symmetry in IHdl. eapply list_pop_app_Some in IHdl. rewrite IHdl. auto.
    + destruct k.
      * simpl. remember 0. destruct a as [sl]. destruct sl; try discriminate. auto.
      * remember (array_pop a) as a0_clt0. destruct a0_clt0 as (a0, clt0).
        rewrite option_map_option_map. unfold Basics.compose.
        specialize (complete_leaf_tree_pop_correct clt0 H) as ?.
        remember (complete_leaf_tree_pop clt0) as o1. destruct o1 as [(dl0, x) | ]; try discriminate.
        simpl. simpl in H0. injection H0 as ?.
        specialize (array_pop_correct a) as ?. rewrite <- Heqa0_clt0 in H1.
        rewrite <- H1. rewrite List.flat_map_app. simpl. rewrite List.app_nil_r. rewrite <- List.app_assoc.
        rewrite <- H0. rewrite <- List.app_assoc. simpl.
        symmetry in Heqo0. apply digital_list_pop_None in Heqo0; auto. rewrite Heqo0.
        symmetry. apply list_pop_cons. apply List.app_assoc.
Qed.

Theorem concrete_digital_list_pop_correct :
  forall {A r} (cdl : concrete_digital_list A r),
  r > 1 ->
  option_map
    (fun '(cdl0, x) => (concrete_digital_list_to_list cdl0, x))
    (concrete_digital_list_pop cdl) = list_pop (concrete_digital_list_to_list cdl).
Proof.
  intros ? ? ? ?. destruct cdl as (d & dl). unfold concrete_digital_list_to_list. simpl.
  rewrite option_map_option_map. unfold Basics.compose. rewrite <- digital_list_pop_correct; auto.
  apply option_map_ext. intros (dl0, x). auto.
Qed.

Section Example.

About concrete_digital_list_empty.
Check @concrete_digital_list_empty_correct.

About concrete_digital_list_nth.
Check @concrete_digital_list_nth_correct.

About concrete_digital_list_update.
Check @concrete_digital_list_update_correct.

About concrete_digital_list_push.
Check @concrete_digital_list_push_correct.

About concrete_digital_list_pop.
Check @concrete_digital_list_pop_correct.

End Example.
