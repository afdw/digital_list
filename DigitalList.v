(*
Abbreviations used:
- sl - a sized_list
- sl - a sized_list of indexes (digits)
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

Definition nat_computational_eq {m n} (opaque_eq: m = n) : m = n :=
  match PeanoNat.Nat.eq_dec m n with
  | left transparent_eq => transparent_eq
  | right neq => False_rect _ (neq opaque_eq)
  end.

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

Notation "x :||: l" := (SizedListCons x l) (at level 50).

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

Theorem sized_list_to_list_length :
  forall {A n} (sl : sized_list A n),
  length (sized_list_to_list sl) = n.
Proof.
  intros ? ? ?. induction sl.
  - auto.
  - simpl. f_equal. auto.
Qed.

Definition sized_list_rev {A n} (sl : sized_list A n) : sized_list A n :=
  let f := (fix f n1 (sl1 : sized_list A n1) : forall n2 (sl2 : sized_list A n2), sized_list A (n1 + n2) :=
    match sl1 in (sized_list _ n1) return forall n2 (sl2 : sized_list A n2), sized_list A (n1 + n2) with
    | [||] => fun n2 sl2 =>
      sl2
    | @SizedListCons _ n1' x sl1' => fun n2 sl2 =>
      rew <- (nat_computational_eq (Plus.plus_Snm_nSm _ _)) in (f n1' sl1' (S n2) (x :||: sl2))
    end) in
  rew (nat_computational_eq (PeanoNat.Nat.add_0_r _)) in (f n sl 0 [||]).

Section Example.

Compute sized_list_rev [|1; 2; 3; 4; 5|].

End Example.

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

Definition to_digits_sized {k} n m : sized_list nat k := sized_list_of_list 0 (to_digits n m).

Definition to_digits_sized_rev {k} n m : sized_list nat k := sized_list_rev (to_digits_sized n m).

Section Example.

Compute to_digits 2 10.
Compute to_digits_sized 2 10 : sized_list _ 8.
Compute to_digits_sized_rev 2 10 : sized_list _ 8.

End Example.

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
  then digital_list_nth_inner (to_digits_sized_rev n i) dl
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
