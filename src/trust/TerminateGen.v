From hahn Require Import Hahn.
From Coq Require Import Lia.

Set Implicit Arguments.

Section Terminate.

Variables (A : Type) (r : relation A).
Variable a : A.

Variable measure : A -> nat -> Prop.
Variable ma : nat.
Hypothesis measure_a : measure a ma.
Hypothesis measure_ex : forall x, r^* a x -> exists m, measure x m.

Hypothesis dec : 
  forall x y, 
    r^* a x -> r x y -> 
    forall n1 n2, measure x n1 -> measure y n2 -> n1 < n2.

Variable B : nat.
Hypothesis bounded :
  forall x m, r^* a x -> measure x m -> m < B.

Theorem r_terminate : 
  exists B, forall k x, r^^k a x -> k < B.
Proof.
  exists (S B); intros k x R.
  enough (forall n, measure x n -> k < S n) as M.
  { apply pow_rt in R; assert (R' := R).
    apply measure_ex in R; desf.
    eapply bounded in R'; [|eauto]; apply M in R; lia. }
  generalize dependent x.
  induction k; [lia|]; intros ??? M; ins.
  unfolder in R; desf.
  assert (r^* a z) as rt by eby eapply pow_rt.
  assert (Mz := rt); apply measure_ex in Mz; desf.
  eapply IHk in R; eauto.
  eapply dec in rt; [|eauto| |]; [|eauto|eauto]. lia.
Qed.

Theorem r_min_ex : 
  exists x, r^* a x /\ forall y, ~ r x y.
Proof.
  apply NNPP; intro F; clarify_not.
  assert (forall x, ~ (r＊ a x /\ (forall y : A, ~ r x y))) as F'.
  { apply not_ex_all_not; eauto. }
  enough (forall B, ~ (forall k x, r^^k a x -> k < B)) as F''.
  { apply all_not_not_ex in F''; destruct F''; apply r_terminate. }
  intro B'; induction B'.
  { intro F''; specialize (F'' 0 a (conj eq_refl I)); ins; lia. }
  clarify_not.
  specialize (F' n0); clarify_not.
  { apply pow_rt in IHB'; contradiction. }
  assert (r ^^ (S n) a n1) as R by (ins; vauto).
  intro F''; specialize (F'' (S n) n1 R); lia.
Qed.

End Terminate.
