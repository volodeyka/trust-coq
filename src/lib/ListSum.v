Require Import List.
From hahn Require Import Hahn.
Require Import Lia.
Require Import Arith.

Definition list_sum l := fold_right plus 0 l.

Lemma list_sum_app l1 l2: list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof. 
  induction l1; [done| ]. 
  ins. rewrite IHl1. lia.
Qed.

Lemma list_sum_inc_inside a l1 l2:
  list_sum (l1 ++ S a :: l2) = S (list_sum (l1 ++ a :: l2)).
Proof. 
  ins. rewrite !list_sum_app. simpl. lia.
Qed. 

Lemma list_sum_bound l k (BOUND: forall x (INx: In x l), x <= k):
  list_sum l <= k * length l.
Proof. 
  ins. induction l. 
  { simpl. lia. }
  simpl. specialize_full IHl.
  { ins. apply BOUND. intuition. }
  specialize_full BOUND.
  { simpl. by left. }
  rewrite Nat.mul_succ_r. lia.
Qed. 

Lemma emiT {A: Type} {P: Prop} (b1 b2: A) (p: P):
  (ifP P then b1 else b2) = b1.
Proof. by destruct (excluded_middle_informative P). Qed. 

Lemma emiF {A: Type} {P: Prop} (b1 b2: A) (np: ~ P):
  (ifP P then b1 else b2) = b2.
Proof. by destruct (excluded_middle_informative P). Qed.

Lemma list_sum_separation {A B: Type} (tid_: A -> B) (l: list A) (domB: list B)
      (ND : NoDup l)
      (NDB: NoDup domB)
      (INCL: forall x, In x l -> In (tid_ x) domB):
  length l = list_sum (map (fun tn => length (filterP (fun e => nth_error domB tn = Some (tid_ e)) l)) (List.seq 0 (length domB))).
Proof.
  remember (length domB) as n.
  generalize dependent l. induction l.
  { ins. (* clear BOUNDED_THREADS0. *) clear Heqn. 
    induction n; [by rewrite seq0| ].
    rewrite seqS, map_app, list_sum_app, <- IHn; auto. }
  ins.
  rewrite IHl.
  2: { eapply nodup_consD; eauto. }
  2: { ins. apply INCL. intuition. }
  specialize (INCL a). specialize_full INCL; [intuition| ]. apply In_nth_error in INCL as [ia Ia]. 
  rewrite seq_split0 with (a := ia).
  2: { rewrite Heqn. apply nth_error_Some. by rewrite Ia. }
  rewrite !map_app, !list_sum_app. rewrite plus_n_Sm. f_equal.
  { f_equal. apply map_ext_in. 
    intros b INb. rewrite emiF; [apply eq_refl| ].
    apply in_seq0_iff in INb.
    red. ins. 
    apply (proj1 (@NoDup_nth_error _ domB)) with (i := ia) (j := b) in NDB; [lia | |congruence].
    apply nth_error_Some. by rewrite Ia. }
  simpl. rewrite emiT; [| done]. simpl. do 2 f_equal.
  { f_equal. apply map_ext_in. 
    intros b INb. rewrite emiF; [apply eq_refl| ].
    apply in_seq_iff in INb.
    red. ins. 
    apply (proj1 (@NoDup_nth_error _ domB)) with (i := ia) (j := b) in NDB; [lia | |congruence].
    apply nth_error_Some. by rewrite Ia. }
Qed. 
