Require Coq.Program.Wf.
Require Import Lia.
Require Coq.Lists.List.
Import List.ListNotations.

Open Scope list_scope.

#[program] Fixpoint to_digits n m {measure m} :=
  match n, m with
  | 0, _ => []
  | 1, _ => [m]
  | _, 0 => []
  | _, _ => Nat.modulo m n :: to_digits n (Nat.div m n)
  end.
Next Obligation.
  specialize (H m). specialize (H0 n). specialize (H1 m). apply PeanoNat.Nat.div_lt; lia.
Qed.
Next Obligation.
  intuition lia.
Qed.
Next Obligation.
  intuition lia.
Qed.

Section Example.

Compute to_digits 2 10.

End Example.

Inductive sized_list {A} : nat -> Type :=
  | SizedListNil : sized_list 0
  | SizedListCons : forall {n}, A -> sized_list n -> sized_list (S n).

Arguments sized_list : clear implicits.

Notation "x :||: l" := (SizedListCons x l) (at level 10).

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
  | x :||: sl  => x :: sized_list_to_list sl
  end.

Theorem sized_list_to_list_length :
  forall {A n} (sl : sized_list A n),
  length (sized_list_to_list sl) = n.
Proof.
  intros ? ? ?. induction sl.
  - auto.
  - simpl. f_equal. auto.
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

Fixpoint complete_leaf_tree_to_list {A n d} (clt : complete_leaf_tree A n d) : list A :=
  match d with
  | 0 => fun (clt : complete_leaf_tree A n 0) =>
    [clt : A]
  | S d' => fun (clt : complete_leaf_tree A n (S d')) =>
    List.flat_map complete_leaf_tree_to_list (sized_list_to_list clt)
  end clt.

Lemma flat_map_length_same_length_for_type :
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
  - simpl. rewrite flat_map_length_same_length_for_type with (k := Nat.pow n d).
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
