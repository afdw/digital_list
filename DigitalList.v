(*
Abbreviations used:
- red - a reduction lemma
- sl - a sized_list
- isl - a sized_list of indexes (digits)
- clt - a complete_leaf_tree
- dl - a digital_list
- cdl - a concrete_digital_list
*)

Require Coq.Program.Wf.
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

Definition option_flat_map {A B} (f : A -> option B) (o : option A) : option B :=
  match o with
  | None => None
  | Some a =>
    match f a with
    | None => None
    | Some b => Some b
    end
  end.

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
  forall {A n1 n2} default (sl1 : sized_list A n1) (sl2 : sized_list A n2),
  sized_list_rev_inner sl1 sl2 =
  sized_list_of_list default (List.rev (sized_list_to_list sl1) ++ sized_list_to_list sl2).
Proof.
  intros ? ? ? ? ?. generalize dependent n2. induction sl1; intros ? ?.
  - simpl. symmetry. apply sized_list_of_to_list_correct.
  - simpl. rewrite IHsl1. remember (List.rev (sized_list_to_list sl1)) as l0. destruct l0.
    + simpl. rewrite <- sized_list_of_list_cons. unrew. auto.
    + simpl. rewrite <- sized_list_of_list_cons. rewrite <- List.app_assoc. unrew. auto.
Qed.

Theorem sized_list_rev_correct :
  forall {A n} default (sl : sized_list A n),
  sized_list_rev sl = sized_list_of_list default (List.rev (sized_list_to_list sl)).
Proof.
  intros ? ? ? ?. unfold sized_list_rev. unrew. rewrite (sized_list_rev_inner_correct default).
  simpl. rewrite List.app_nil_r. auto.
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

Fixpoint sized_list_nth {A n} i (sl : sized_list A n) :=
  match sl, i with
  | [||], _ => None
  | x :||: _, 0 => Some x
  | _ :||: sl', S i' => sized_list_nth i' sl'
  end.

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

Fixpoint complete_leaf_tree_nth {A n d} (isl : sized_list nat d) (clt : complete_leaf_tree A n d) : option A :=
  match d with
  | 0 => fun (isl : sized_list nat 0) (clt : complete_leaf_tree A n 0) =>
    Some (clt : A)
  | S d' => fun (isl : sized_list nat (S d')) (clt : complete_leaf_tree A n (S d')) =>
    let d := S d' in let Heqd : d = S d' := eq_refl in
    match isl with
    | @SizedListCons _ d'0 i isl'0 => fun (Heqd : S d'0 = S d') =>
      let isl' := rew dependent (eq_add_S _ _ Heqd) in isl'0 in
      option_flat_map (complete_leaf_tree_nth isl') (sized_list_nth i clt)
    end Heqd
  end isl clt.

Section Example.

Compute complete_leaf_tree_nth [|1; 1; 0|] [|[|[|0; 1|]; [|2; 3|]|]; [|[|4; 5|]; [|6; 7|]|]|].

End Example.

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
  intros ? ? ? ?. rewrite ? (sized_list_rev_correct 0).
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

Fixpoint digital_list_nth_inner {A n d} (isl : sized_list nat d) (dl : digital_list A n d) : option A :=
  match dl with
  | DigitalListNil => fun (isl : sized_list nat 0) =>
    None
  | @DigitalListCons _ _ d' k _ sl dl' => fun (isl : sized_list nat (S d')) =>
    let d := S d' in let Heqd : d = S d' := eq_refl in
    match isl with
    | @SizedListCons _ d'0 i isl'0 => fun (Heqd : S d'0 = S d') =>
      let isl' := rew dependent (eq_add_S _ _ Heqd) in isl'0 in
      if Nat.eqb i k
      then digital_list_nth_inner isl' dl'
      else option_flat_map (complete_leaf_tree_nth isl') (sized_list_nth i sl)
    end Heqd
  end isl.

Definition digital_list_nth {A n d} (i : nat) (dl : digital_list A n d) : option A :=
  if Nat.ltb i (digital_list_length dl)
  then digital_list_nth_inner (indexes_sized_list_of_index n i) dl
  else None.

Definition concrete_digital_list_nth {A n} (i : nat) (cdl : concrete_digital_list A n) : option A :=
  let '(ConcreteDigitalList _ dl) := cdl in digital_list_nth i dl.

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
      end
  in (
    concrete_digital_list_to_list cdl,
    f (concrete_digital_list_length cdl),
    concrete_digital_list_nth 100 cdl
  ).

End Example.
