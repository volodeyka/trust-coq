From hahn Require Import Hahn.
From Coq Require Import Lia.

Set Implicit Arguments.

Arguments last : simpl nomatch.

Section Path.

Context {T : Type}.

Variables (e : relation T).

Lemma last_cons T' (a x : T') (p1: list T') : 
 last (a :: p1) x = last p1 a.
Proof.
  induction p1; ins; by destruct p1.
Qed.


Fixpoint path x (p : list T) :=
  match p with 
  | y :: p' => e x y /\ path y p'
  | _       => True
  end.

Definition Path x p y := path x (p ++ y :: nil).

Lemma cat_path x p1 p2 : path x (p1 ++ p2) <-> path x p1 /\ path (last p1 x) p2.
Proof.
  generalize x.
  induction p1; [|ins; rewrite IHp1, last_cons]; firstorder.
Qed.

Lemma path_cont p x (P : T -> Prop)
  (PT : path x p) 
  (Px : ~ P x) (Plp : P (last p x)) : 
  exists p1 x1 x2 p2, 
    << pE  : x :: p = p1 ++ x1 :: x2 :: p2 >> /\
    << P1  : Forall P (x2 :: p2)      >> /\
    << P12 : e x1 x2                  >> /\
    << NP2 : ~ P x1                   >>.
Proof.
  generalize dependent x.
  induction p using rev_ind; ins; desf.
  rewrite last_last in Plp.
  apply cat_path in PT; desf; ins; desf.
  tertium_non_datur (P (last p x0)) as [Pl|NPl].
  { specialize (IHp x0 PT Px Pl); desf.
    exists p1, x1, x2, (p2 ++ x :: nil); splits; eauto.
    { by rewrite ?app_comm_cons, pE, appA. }
    rewrite app_comm_cons, Forall_app; vauto. }
  tertium_non_datur (p = nil) as [|N]; desf; ins.
  { exists nil, x0, x, nil; splits; eauto. }
  apply (app_removelast_last x0) in N.
  exists (x0 :: removelast p), (last p x0), x, nil; splits; eauto.
  rewrite N at 1. rewrite ?app_comm_cons, ?appA.
  by apply f_equal; rewrite <-app_comm_cons.
Qed.

Lemma sub_path x y (p p1 p2 : list T)
  (PT : path x p)
  (pE : x :: p = p1 ++ y :: p2) : 
  path y p2.
Proof.
  destruct p1; injection pE; ins; desf.
  rewrite app_comm_cons' in PT.
  apply cat_path in PT; desf; by rewrite last_last in PT0.
Qed.

Arguments nth : simpl nomatch.

Lemma nith_n_Sn d n (p : list T) x y
  (L : S n < length p)
  (N1 : nth n p d = x)
  (N2 : nth (S n) p d = y) : 
  exists p1 p2, p = p1 ++ x :: y :: p2.
Proof.
  generalize dependent n.
  induction p; ins; [lia|].
  destruct p; ins; [lia|].
  destruct n; ins; desf; [by exists nil, p|].
  destruct (IHp n) as [p1 E]; eauto; try lia; desf.
  by exists (a :: p1), p2; rewrite E at 1.
Qed.

Lemma nth_def d1 d2 n (p : list T)
  (L : n < length p) :
  nth n p d1 = nth n p d2.
Proof.
  generalize dependent n.
  induction p; ins; [lia|].
  destruct n; ins; apply IHp; lia.
Qed.

Lemma in_list_ind d (p : list T) (P : T -> Prop) : 
  P d ->
  (forall x, 
    (exists (p1 p2 : list T) y, (d :: p = p1 ++ y :: x :: p2) /\ P y) ->
    P x) ->
  (forall x, In x (d :: p) -> P x).
Proof.
  intros Pd Pst.
  intros x IN.
  assert (IN' := IN).
  apply In_nth with (d := x) in IN'; desf.
  generalize dependent x.
  induction n; [ins; desf| intros].
  apply Pst.
  eapply (nith_n_Sn _ _ IN') in IN'0; eauto; desf.
  do 3 eexists; splits; eauto.
  apply IHn; eauto; try lia.
  { apply nth_In; lia. } 
  apply nth_def; lia.
Qed.

Lemma path_neigb_rel (p1 p2 : list T) p x y z
  (PT : path x p)
  (pE : x :: p = p1 ++ y :: z :: p2) :
  e y z.
Proof.
  generalize dependent x.
  generalize dependent p.
  induction p1; ins; injection pE; ins; desf.
  { basic_solver. }
  destruct p1; [basic_solver|ins; desf].
  eapply IHp1; eauto.
Qed.

Lemma pathE (p : list T) x y 
  (L : last p x = y) 
  (P : path x p) : 
  e^^(length p) x y.
Proof.
  generalize dependent x.
  induction p; [ins|intros].
  change (length (a :: p)) with (S (length p)).
  rewrite last_cons in L.
  apply pow_S_begin; ins; desc; exists a; splits; auto.
Qed.


Lemma path_r_str (p : list T) x y 
  (IN : In y p)
  (PT : path x p) : e^* x y.
Proof.
  apply clos_rt1n_rt.
  generalize dependent x; induction p; ins; desf; vauto.
  econstructor; eauto.
Qed.

Lemma last_map S (f : T -> S) p x: 
  f (last p x) = last (map f p) (f x).
Proof.
  generalize dependent x.
  by elim p; ins; rewrite ?last_cons.
Qed.

Lemma last_app_cons (p1 p2 : list T) x y : 
  last (p1 ++ x :: p2) y = last p2 x.
Proof.
  generalize dependent y.
  induction p1; ins; try by rewrite last_cons.
Qed.

Lemma last_in (p : list T) x: 
  In (last p x) (x :: p).
Proof.
  generalize dependent x; induction p; ins; [basic_solver|].
  rewrite last_cons; destruct (IHp a); vauto.
Qed.

End Path.

Lemma Path_transp T (e : relation T) x y p
  (P : Path e x p y) : Path e⁻¹ y (rev p) x.
Proof.
  generalize dependent x; induction p; unfold Path; ins; desf.
  apply cat_path; rewrite last_last; splits; ins.
  apply IHp; ins.
Qed.
