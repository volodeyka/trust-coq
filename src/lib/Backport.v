Require Import List.
Import ListNotations. 
From hahn Require Import Hahn.
Require Import Arith.

Lemma seq_app : forall len1 len2 start,
    List.seq start (len1 + len2) = List.seq start len1 ++ List.seq (start + len1) len2.
Proof. ins. by rewrite <- seq_add. Qed.

Lemma nth_error_nth' {A: Type} : forall (l : list A) (n : nat) (d : A),
    n < length l -> nth_error l n = Some (nth n l d).
Proof.
  intros l n d H.
  apply (nth_split _ d) in H. destruct H as [l1 [l2 [H H']]].
  subst. rewrite H. rewrite nth_error_app2; [|auto].
  rewrite app_nth2; [| auto]. repeat (rewrite Nat.sub_diag). reflexivity.
Qed.

Lemma nth_error_nth {A: Type} : forall (l : list A) (n : nat) (x d : A),
    nth_error l n = Some x -> nth n l d = x.
Proof.
  intros l n x d H.
  apply nth_error_split in H. destruct H as [l1 [l2 [H H']]].
  subst. rewrite app_nth2; [|auto].
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma map_ext_in_iff {A B: Type} (f g : A -> B) (l : list A):
  (forall a, In a l -> f a = g a) <-> map f l = map g l.
Proof.
  split; [apply map_ext_in| ].
  ins. apply In_nth_error in H0 as [n NTH].
  pose proof (map_nth_error f n l NTH) as F. pose proof (map_nth_error g n l NTH) as G.
  congruence. 
Qed. 
