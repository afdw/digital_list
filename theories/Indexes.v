Load SizedList.

Definition indexes_sized_list_of_index n {d} i : sized_list nat d :=
  sized_list_rev (sized_list_of_list 0 (to_digits n i)).

Fixpoint indexes_sized_list_to_index n {d} (isl : sized_list nat d) :=
  match isl with
  | [||] => 0
  | i :||: isl' => Nat.pow n (pred d) * i + indexes_sized_list_to_index n isl'
  end.

Section Example.

Compute indexes_sized_list_of_index 2 10 : sized_list _ 8.
Compute indexes_sized_list_to_index 2 [|0; 0; 0; 0; 1; 0; 1; 0|].

End Example.

Lemma indexes_sized_list_to_index_sized_list_rev_cons :
  forall n {d} i (isl : sized_list nat d),
  indexes_sized_list_to_index n (sized_list_rev (i :||: isl)) =
  indexes_sized_list_to_index n (sized_list_rev isl) * n + i.
Proof.
  intros ? ? ? ?. rewrite ? (sized_list_rev_correct_eq 0).
  remember (sized_list_to_list (i :||: isl)) as l0. simpl in Heql0. subst l0.
  assert (forall l, List.rev (i :: l) = List.rev l ++ [i]) by auto. rewrite H. clear H.
  remember (List.rev (sized_list_to_list isl)) as l0.
  generalize dependent d. generalize dependent i. induction l0; intros ? ? ? ?.
  - simpl. destruct isl.
    + simpl. lia.
    + simpl in Heql0. symmetry in Heql0. apply List.app_eq_nil in Heql0. intuition discriminate.
  - simpl. destruct d.
    + simpl. remember 0. destruct isl; discriminate.
    + rewrite (IHl0 _ _ (fst (sized_list_pop isl))); clear IHl0.
      * simpl. lia.
      * apply (f_equal (@List.rev _)) in Heql0. rewrite List.rev_involutive in Heql0. simpl in Heql0.
        rewrite <- List.rev_involutive at 1. f_equal. rewrite <- sized_list_pop_correct in Heql0.
        remember (sized_list_pop isl) as isl0. destruct isl0. simpl. apply List.app_inj_tail in Heql0.
        intuition auto.
Qed.

Lemma indexes_sized_list_to_index_sized_list_rev_sized_list_repeat_0 :
  forall n {d},
  indexes_sized_list_to_index n (d := d) (sized_list_rev (sized_list_repeat 0)) = 0.
Proof.
  intros ? ?. induction d.
  - auto.
  - simpl. rewrite indexes_sized_list_to_index_sized_list_rev_cons. lia.
Qed.

Theorem indexes_sized_list_to_of_correct :
  forall n {d} i,
  n > 1 ->
  i < Nat.pow n d ->
  indexes_sized_list_to_index n (d := d) (indexes_sized_list_of_index n i) = i.
Proof.
  intros ? ? ? ?. generalize dependent i. unfold indexes_sized_list_of_index. induction d; intros ? ?.
  - simpl. simpl in H0. lia.
  - simpl. destruct (PeanoNat.Nat.eqb_spec i 0).
    + clear IHd. subst i. rewrite to_digits_red_any_zero.
      rewrite indexes_sized_list_to_index_sized_list_rev_cons.
      rewrite indexes_sized_list_to_index_sized_list_rev_sized_list_repeat_0. auto.
    + assert (Nat.div i n < Nat.pow n d). {
        simpl in H0. destruct (PeanoNat.Nat.eqb_spec (Nat.div i n) (Nat.pow n d)).
        - apply PeanoNat.Nat.div_lt_upper_bound; lia.
        - unfold lt in H0. apply Le.le_Sn_le in H0. apply PeanoNat.Nat.div_le_mono with (c := n) in H0; try lia.
          rewrite PeanoNat.Nat.mul_comm in H0. rewrite PeanoNat.Nat.div_mul in H0; try lia.
      }
      specialize (IHd (Nat.div i n) H1); clear H1. rewrite to_digits_red_any_nonzero; try lia.
      rewrite indexes_sized_list_to_index_sized_list_rev_cons. rewrite IHd; clear IHd.
      symmetry. rewrite PeanoNat.Nat.mul_comm. apply PeanoNat.Nat.div_mod_eq.
Qed.

Theorem indexes_sized_list_of_index_upper_bound :
  forall n {d} i,
  n > 1 ->
  sized_list_forall (fun i => i < n) (indexes_sized_list_of_index n (d := d) i).
Proof.
  intros ? ? ? ?. unfold indexes_sized_list_of_index. apply sized_list_forall_sized_list_rev.
  generalize dependent i. induction d; intros ?.
  - simpl. auto.
  - simpl. destruct (PeanoNat.Nat.eqb_spec i 0).
    + clear IHd. subst i. rewrite to_digits_red_any_zero. simpl. split; try lia. induction d.
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
