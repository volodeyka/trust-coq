Require Import Lia.
Require Import Arith.
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Labels.

Set Implicit Arguments.

Definition Timestamp := nat.

Definition View := Loc -> Timestamp.

Definition view_le (v v' : View) := forall x, v x <= v' x.

Definition view_lt v v' := view_le v v' /\ v <> v'.

Definition view_join (v1 v2 : View) x := Nat.max (v1 x) (v2 x).

Lemma view_ltE v v' :
  view_lt v v' <-> view_le v v' /\ exists x, v x < v' x.
Proof using.
  unfold view_lt, view_le; intuition; desf; try lia.
  apply NNPP; intro X; apply H1; extensionality x.
  specialize (H0 x); rewrite Nat.le_lteq in *; desf; exfalso; eauto.
Qed.

Lemma view_le_refl v :
  view_le v v.
Proof using.
  unfold view_le; ins.
Qed.

Lemma view_le_trans v v' v'' :
  view_le v v' ->
  view_le v' v'' ->
  view_le v v''.
Proof using.
  unfold view_le; ins; eauto with arith.
Qed.

Lemma view_lt_irrefl v : ~ view_lt v v.
Proof using.
  unfold view_lt; intro; desf.
Qed.

Lemma view_lt_trans v v' v'' :
  view_lt v v' ->
  view_lt v' v'' ->
  view_lt v v''.
Proof using.
  rewrite !view_ltE; ins; desf; split; eauto using view_le_trans.
  exists x; eauto with arith.
Qed.

Lemma view_lt_weaken v v' :
  view_lt v v' ->
  view_le v v'.
Proof using.
  unfold view_lt; tauto.
Qed.

Lemma view_lt_le_trans v v' v'' :
  view_lt v v' ->
  view_le v' v'' ->
  view_lt v v''.
Proof using.
  rewrite !view_ltE; ins; desf; split; eauto using view_le_trans.
  exists x; eauto with arith.
Qed.

Lemma view_le_lt_trans v v' v'' :
  view_le v v' ->
  view_lt v' v'' ->
  view_lt v v''.
Proof using.
  rewrite !view_ltE; ins; desf; split; eauto using view_le_trans.
  exists x; eauto with arith.
Qed.

Fixpoint view_joinl (l : list View) : View :=
  match l with
  | nil => fun _ => 0
  | x :: l => view_join x (view_joinl l)
  end.

Lemma view_join_comm v v' :
  view_join v v' = view_join v' v.
Proof using.
  extensionality x; apply Nat.max_comm.
Qed.

Lemma view_join_assoc v v' v'' :
  view_join v (view_join v' v'') = view_join (view_join v v') v''.
Proof using.
  extensionality x; apply Nat.max_assoc.
Qed.

Lemma view_joinl_app l l' :
  view_joinl (l ++ l') = view_join (view_joinl l) (view_joinl l').
Proof using.
  induction l; ins; rewrite IHl, view_join_assoc; done.
Qed.

Lemma view_join_lub v v' v'' :
  view_le v v'' ->
  view_le v' v'' ->
  view_le (view_join v v') v''.
Proof using.
  unfold view_le, view_join; ins.
  apply Nat.max_lub; eauto.
Qed.

Lemma view_join_0_l v :
  view_join (fun _ => 0) v = v.
Proof using.
  extensionality x; apply Nat.max_0_l.
Qed.

Lemma view_join_0_r v :
  view_join v (fun _ => 0) = v.
Proof using.
  extensionality x; apply Nat.max_0_r.
Qed.

Lemma view_le_join_l v v' v'' :
  view_le v v' ->
  view_le v (view_join v' v'').
Proof using.
  unfold view_le, view_join; ins.
  eauto with arith.
Qed.

Lemma view_le_join_r v v' v'' :
  view_le v v'' ->
  view_le v (view_join v' v'').
Proof using.
  unfold view_le, view_join; ins.
  eauto with arith.
Qed.

Lemma view_le_join v v' v'' v'''
      (LE1: view_le v  v'')
      (LE2: view_le v' v''') :
  view_le (view_join v v') (view_join v'' v''').
Proof using.
  unfold view_le, view_join in *; ins.
  specialize (LE1 x). specialize (LE2 x).
  apply Nat.max_lub; eauto with arith.
Qed.

Lemma view_le_joinl_l l v :
  (forall x, In x l -> view_le x v) -> view_le (view_joinl l) v.
Proof using.
  unfold view_le; induction l; ins; try lia.
  apply Nat.max_lub; eauto.
Qed.

Lemma view_joinlE vl x :
  view_joinl vl x = max_of_list (map (fun y => y x) vl).
Proof using.
  induction vl; ins; unfold view_join; f_equal; ins.
Qed.
