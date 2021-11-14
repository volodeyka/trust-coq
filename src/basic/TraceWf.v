Require Import Lia.
Require Import Arith.
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import lib.SetSize.
Require Import IndefiniteDescription.
Require Import lib.ListSum.

Set Implicit Arguments.

Definition trace_wf (t: trace Event) :=
  forall i j (LTij: i < j) (LTj : NOmega.lt_nat_l j (trace_length t)) d
         (EQtid : tid (trace_nth i t d) = tid (trace_nth j t d)),
    index (trace_nth i t d) < index (trace_nth j t d).

Lemma trace_wf_nodup t (WF: trace_wf t) :
  trace_nodup t.
Proof using.
  unfold trace_wf; repeat red; ins.
  forward eapply WF with (d := d); eauto;
  rewrite H; ins; lia.
Qed.

Definition trace_no_init_tid t :=
  forall d (IN: trace_elems t d), tid d <> 0.

Ltac liaW no := (destruct no; [done|simpl in *; lia]).

Lemma trace_nodup_list {A: Type} (l: list A):
  NoDup l <-> trace_nodup (trace_fin l).
Proof.
  destruct (classic (inhabited A)).
  2: { destruct l; [| by destruct H]. 
       split; ins. red. ins. lia. }
  destruct H as [a]. 
  split. 
  { intros ND. red. ins. red. ins. apply NoDup_nth in H; auto; lia. }
  { ins. apply NoDup_nth with (d := a). ins.
    red in H. simpl in H.
    pose proof (Nat.lt_trichotomy i j). des; auto.
    all: specialize H with (d := a); specialize_full H; eauto; congruence. }
Qed.

Lemma trace_nodup_size {A: Type} (tr: trace A) (ND: trace_nodup tr):
  trace_length tr = set_size (trace_elems tr).
Proof.
  destruct tr.
  { simpl. apply trace_nodup_list in ND.
    unfold set_size. destruct (excluded_middle_informative _).
    2: { destruct n. vauto. }
    f_equal. destruct (constructive_indefinite_description _ _). simpl in *.
    apply Permutation_length. apply NoDup_Permutation; auto.
    ins.
    symmetry. etransitivity.
    { rewrite in_undup_iff, in_filterP_iff. reflexivity. }
    intuition. }
  { simpl.
    unfold set_size. destruct (excluded_middle_informative _); auto.    
    exfalso.
    apply set_finiteE in s. desc.
    red in ND. simpl in ND.
        
    forward eapply (@list_sum_separation _ _ fl (List.seq 0 (S (length findom)))) as EQ. 
    { apply seq_NoDup. }
    { eauto. }
    { ins. apply s0. eauto. }
    forward eapply list_sum_bound with (l := (map
            (fun tn : nat =>
             length
               (filterP
                  (fun e : nat => nth_error findom tn = Some (fl e))
                  (List.seq 0 (S (length findom)))))
            (List.seq 0 (length findom)))) (k := 1).
    2: { rewrite <- EQ, map_length, !seq_length. lia. }
    intros len' H. apply in_map_iff in H as [ind [LEN IND]]. desc.
    remember (filterP (fun e : nat => nth_error findom ind = Some (fl e))
                      (List.seq 0 (S (length findom)))) as poss.
    rewrite <- LEN. do 2 (destruct poss; [vauto| ]).
    assert (In n (n :: n0 :: poss)) as IN1 by done. assert (In n0 (n :: n0 :: poss)) as IN2 by vauto.
    rewrite Heqposs in IN1, IN2. apply in_filterP_iff in IN1. apply in_filterP_iff in IN2. desc.
    pose proof (NPeano.Nat.lt_trichotomy n n0). des. 
    2: { subst n0.
         assert (NoDup (n :: n :: poss)).
         { rewrite Heqposs. apply nodup_filterP, seq_NoDup. }
         inversion H. subst. by destruct H2. }
    all: edestruct ND; eauto; congruence. }  
Qed.

Lemma trace_wf_helper (nu: nat -> Event) (tr: trace Event) (G: execution)
      (ENUM : enumerates nu (acts G \₁ is_init))
      (ORD_SB: forall i, lt_size i (acts G \₁ is_init) -> forall j, lt_size j (acts G \₁ is_init) -> sb G (nu i) (nu j) -> i < j)
      (EVENTS: trace_elems tr ≡₁ (acts G \₁ is_init))
      (ND: trace_nodup tr)
      (TRACE_NU: forall i d, NOmega.lt_nat_l i (trace_length tr) -> trace_nth i tr d = nu i)
      (WF: Wf G):
  trace_wf tr.
Proof. 
  red. ins.
  rewrite !TRACE_NU. 2, 3: liaW (trace_length tr).
  rewrite !TRACE_NU in EQtid. 2, 3: liaW (trace_length tr).
  apply enumeratesE' in ENUM. desc.
  rewrite trace_nodup_size in LTj; auto. rewrite (set_size_equiv _ _ EVENTS) in LTj.
  assert (NOmega.lt_nat_l i (set_size (acts G \₁ is_init))) as LTi.
  { liaW (set_size (acts G \₁ is_init)). }

  pose proof (NPeano.Nat.lt_trichotomy (index (nu i)) (index (nu j))). des; auto.
  { exfalso. specialize INJ with (i := i) (j := j). specialize_full INJ; auto; [| lia].
    eapply wf_index; eauto.
    apply INSET in LTj. apply INSET in LTi. red in LTj, LTi. desc. 
    splits; vauto. }
  exfalso.
  specialize ORD_SB with (i := j) (j := i). specialize_full ORD_SB; [| | | lia]. 
  1,2: by apply set_lt_size.
  apply INSET in LTj. apply INSET in LTi. red in LTj, LTi. desc.
  red. apply seq_eqv_lr. splits; auto. 
  destruct (nu i), (nu j); vauto; by simpl in LTi0.
Qed. 
