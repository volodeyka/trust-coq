From hahn Require Import Hahn.
Require Import Lia.
Require Import IndefiniteDescription.


Section Subtrace.

Context {A: Type}.

Ltac by_subst := by (subst; simpl in *; (lia || des; (vauto || lia))).

Lemma split_exists (tr: trace A) (pos: nat)
      (BOUND: NOmega.le (NOnum pos) (trace_length tr)):
  exists tr1 tr2, tr = trace_app tr1 tr2 /\
             trace_length tr1 = NOnum pos /\
             trace_length tr2 = NOmega.sub (trace_length tr) (NOnum pos).
Proof.
  destruct tr; simpl in *.
  { exists (trace_fin (firstn pos l)). exists (trace_fin (skipn pos l)). simpl.
    splits; f_equal; auto using firstn_skipn, firstn_length_le, skipn_length. }
  exists (trace_fin (mk_list pos fl)). exists (trace_inf (fun n => fl (pos + n))). 
  simpl. unfold trace_prepend. rewrite length_mk_list. 
  splits; try done. 
  f_equal. extensionality x. 
  destruct (PeanoNat.Nat.ltb x pos) eqn:X.
  2: { apply NPeano.Nat.ltb_ge in X. f_equal. lia. }
  apply PeanoNat.Nat.ltb_lt in X.
  rewrite nth_mk_list. destruct (Compare_dec.le_lt_dec pos x); by_subst.
Qed.


Lemma subtrace_exists (tr: trace A) (start: nat) (len: nat_omega)
      (BOUND: ~ NOmega.lt (trace_length tr) (NOmega.add (NOnum start) len)):
  exists tr1 tr2 tr3, tr = trace_app tr1 (trace_app tr2 tr3) /\
                 trace_length tr1 = NOnum start /\
                 trace_length tr2 = len /\
                 trace_length tr3 = NOmega.sub (trace_length tr) (NOmega.add (NOnum start) len).
Proof.
  forward eapply (split_exists tr start).
  { destruct tr, len; by_subst. }
  ins. desc.
  destruct len as [| len]. 
  { exists tr1. exists tr2. exists tr.
    destruct tr; try by_subst. simpl in *. splits; try by_subst.
    by rewrite trace_app_assoc, <- H. }
  
  forward eapply (split_exists tr2 len).
  { destruct tr1, tr2, tr; try by_subst. simpl in *.
    inversion H0. inversion H1. lia. }
  ins. desc.
  exists tr1. exists tr0. exists tr3. splits; try by vauto.
  destruct tr, tr0, tr1, tr2, tr3; try by_subst. simpl in *.
  inversion H0. inversion H1. inversion H3. inversion H4. subst.
  f_equal. lia. 
Qed.

Definition subtrace (tr: trace A) (start: nat) (len: nat_omega) : trace A.
  destruct (excluded_middle_informative (NOmega.lt (trace_length tr) (NOmega.add (NOnum start) len))).
  { exact (trace_fin nil). }
  pose proof (subtrace_exists tr start len n).
  apply constructive_indefinite_description in H as [tr1 H].
  apply constructive_indefinite_description in H as [tr2 H].
  exact tr2.
Defined.

Lemma subtrace_incl (tr: trace A) start len:
  trace_elems (subtrace tr start len) ⊆₁ trace_elems tr.
Proof.
  unfold subtrace. destruct (excluded_middle_informative _); [by_subst| ].
  do 2 (destruct (constructive_indefinite_description _ _)). desc.
  destruct x; [| by_subst].
  rewrite e0, trace_app_assoc. do 2 rewrite trace_elems_app.
  destruct (excluded_middle_informative _); [by_subst| ].
  edestruct n0; by_subst. 
Qed.

Lemma subtrace_trace_corr (tr: trace A) (start: nat) (len: nat_omega)
      (BOUND: ~ NOmega.lt (trace_length tr) (NOmega.add (NOnum start) len)):
  forall i d (DOMi: NOmega.lt_nat_l i len),
    trace_nth i (subtrace tr start len) d = trace_nth (start + i) tr d.
Proof.
  intros.
  unfold subtrace. destruct (excluded_middle_informative _); [done| ].
  do 2 (destruct (constructive_indefinite_description _ _)). desc.
  rewrite e0. rewrite trace_nth_app, e1.
  destruct (excluded_middle_informative _); [by_subst| ].
  simpl. rewrite Minus.minus_plus. rewrite trace_nth_app, e2.
  destruct (excluded_middle_informative _); by_subst.
Qed. 
  
Lemma subtrace_length (tr: trace A) (start: nat) (len: nat_omega)
      (BOUND: ~ NOmega.lt (trace_length tr) (NOmega.add (NOnum start) len)):
  trace_length (subtrace tr start len) = len.
Proof.
  unfold subtrace. destruct (excluded_middle_informative _); [done| ].
  do 2 (destruct (constructive_indefinite_description _ _)). desc. done.
Qed.

End Subtrace.
