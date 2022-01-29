Load SizedList.

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
    + rewrite (IHl0 _ _ (fst (sized_list_pop isl))); clear IHl0.
      * simpl. lia.
      * apply (f_equal (@List.rev _)) in Heql0. rewrite List.rev_involutive in Heql0. simpl in Heql0.
        rewrite <- List.rev_involutive at 1. f_equal. rewrite <- sized_list_pop_correct in Heql0.
        remember (sized_list_pop isl) as isl0. destruct isl0. simpl. apply List.app_inj_tail in Heql0.
        intuition auto.
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
