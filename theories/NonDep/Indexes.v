Load "Utils".

Fixpoint pad_list {A} n default (l : list A) :=
  match n, l with
  | 0, _ => []
  | _, [] => List.repeat default n
  | _, x :: l'  => x :: pad_list (pred n) default l'
  end.

Lemma pad_list_length :
  forall {A} n default (l : list A),
  length (pad_list n default l) = n.
Proof.
  intros ? ? ? ?. generalize dependent n. induction l; intros ?.
  - destruct n.
    + auto.
    + simpl. f_equal. apply List.repeat_length.
  - destruct n.
    + auto.
    + simpl. f_equal. apply IHl.
Qed.

Definition indexes_list_of_index n d i :=
  List.rev (pad_list d 0 (to_digits n i)).

Fixpoint indexes_list_to_index n d il :=
  match il with
  | [] => 0
  | i :: il' => Nat.pow n (pred d) * i + indexes_list_to_index n (pred d) il'
  end.

Section Example.

Compute indexes_list_of_index 2 8 10.
Compute indexes_list_to_index 2 8 [0; 0; 0; 0; 1; 0; 1; 0].

End Example.

Lemma indexes_list_of_index_length :
  forall n d i,
  length (indexes_list_of_index n d i) = d.
Proof.
  intros ? ? ?. unfold indexes_list_of_index. rewrite List.rev_length. apply pad_list_length.
Qed.

Lemma indexes_list_to_index_list_rev_cons :
  forall n d i il,
  length il = d ->
  indexes_list_to_index n (S d) (List.rev (i :: il)) =
  indexes_list_to_index n d (List.rev il) * n + i.
Proof.
  intros ? ? ? ?. remember (List.rev il) as l0. generalize dependent il.
  generalize dependent d. generalize dependent i. induction l0; intros ? ? ? ? ?.
  - simpl. destruct il.
    + simpl in H. subst d. simpl. lia.
    + simpl in Heql0. symmetry in Heql0. apply List.app_eq_nil in Heql0. intuition discriminate.
  - simpl. destruct d.
    + simpl. destruct il; discriminate.
    + rewrite <- List.rev_involutive in Heql0 at 1. simpl in Heql0.
      apply list_rev_injective in Heql0. subst il. simpl.
      rewrite PeanoNat.Nat.mul_add_distr_r. rewrite <- PeanoNat.Nat.add_assoc.
      simpl in IHl0. rewrite <- (IHl0 _ _ (List.rev l0)); clear IHl0.
      * replace [i] with (List.rev [i]) at 1 by auto. rewrite List.rev_app_distr. simpl. lia.
      * symmetry. apply List.rev_involutive.
      * rewrite List.app_length in H. simpl in H. lia.
Qed.

Lemma indexes_list_to_index_list_rev_list_repeat_0 :
  forall n d,
  indexes_list_to_index n d (List.rev (List.repeat 0 d)) = 0.
Proof.
  intros ? ?. induction d.
  - auto.
  - simpl List.repeat. rewrite indexes_list_to_index_list_rev_cons.
    + lia.
    + apply List.repeat_length.
Qed.

Theorem indexes_list_to_of_correct :
  forall n d i,
  n > 1 ->
  i < Nat.pow n d ->
  indexes_list_to_index n d (indexes_list_of_index n d i) = i.
Proof.
  intros ? ? ? ?. generalize dependent i. unfold indexes_list_of_index. induction d; intros ? ?.
  - simpl in H0. destruct i; try lia. rewrite to_digits_red_any_zero. simpl. auto.
  - destruct (PeanoNat.Nat.eqb_spec i 0).
    + clear IHd. subst i. rewrite to_digits_red_any_zero. simpl pad_list.
      rewrite indexes_list_to_index_list_rev_cons.
      * rewrite indexes_list_to_index_list_rev_list_repeat_0. auto.
      * apply List.repeat_length.
    + assert (Nat.div i n < Nat.pow n d). {
        simpl in H0. destruct (PeanoNat.Nat.eqb_spec (Nat.div i n) (Nat.pow n d)).
        - apply PeanoNat.Nat.div_lt_upper_bound; lia.
        - unfold lt in H0. apply Le.le_Sn_le in H0. apply PeanoNat.Nat.div_le_mono with (c := n) in H0; try lia.
          rewrite PeanoNat.Nat.mul_comm in H0. rewrite PeanoNat.Nat.div_mul in H0; try lia.
      }
      specialize (IHd (Nat.div i n) H1); clear H1. rewrite to_digits_red_any_nonzero; try lia.
      simpl pad_list. rewrite indexes_list_to_index_list_rev_cons.
      * rewrite IHd; clear IHd. symmetry. rewrite PeanoNat.Nat.mul_comm. apply PeanoNat.Nat.div_mod_eq.
      * apply pad_list_length.
Qed.

Theorem indexes_list_of_index_upper_bound :
  forall n d i,
  n > 1 ->
  list_forall (fun i => i < n) (indexes_list_of_index n d i).
Proof.
  intros ? ? ? ?. unfold indexes_list_of_index.
  rewrite list_forall_equiv. apply List.Forall_rev. rewrite <- list_forall_equiv.
  generalize dependent i. induction d; intros ?.
  - remember (pad_list 0 0 (to_digits n i)) as l. rewrite (proj1 (List.length_zero_iff_nil l)).
    + simpl. auto.
    + subst l. apply pad_list_length.
  - destruct (PeanoNat.Nat.eqb_spec i 0).
    + clear IHd. subst i. rewrite to_digits_red_any_zero. simpl. split; try lia. induction d.
      * simpl. auto.
      * simpl. intuition lia.
    + rewrite to_digits_red_any_nonzero; try lia. simpl. split.
      * apply PeanoNat.Nat.mod_upper_bound. lia.
      * auto.
Qed.

Theorem indexes_list_to_index_upper_bound :
  forall n d il,
  length il = d ->
  list_forall (fun i => i < n) il ->
  indexes_list_to_index n d il < Nat.pow n d.
Proof.
  intros ? ? ?. generalize dependent d. induction il; intros ? ? ?.
  - simpl. simpl in H. subst d. simpl. auto.
  - simpl. simpl in H. destruct H0 as (? & ?). specialize (IHil (pred d) ltac:(lia) H1); clear H1. destruct d.
    + lia.
    + simpl. simpl in IHil. nia.
Qed.
