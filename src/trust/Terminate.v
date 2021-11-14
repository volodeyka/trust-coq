From hahn Require Import Hahn.
Require Import Execution Execution_Aux Events Labels.
From Coq Require Import Lia.
Require Import Util Sem Alg.

Set Implicit Arguments.

Section Termination.

Variable thread_sem : tsemType.
Variable LR         : LRType thread_sem.
Variable cons       : consType.

Notation "e1 '<_next' e2" := (LR_of LR e1 e2) (at level 20).
Notation avail := (avail thread_sem).
Notation p_sem := (p_sem thread_sem).
Notation next := (next LR).
Notation TruSt_step := (TruSt_step LR cons).
Notation TruSt := (TruSt LR cons).
Notation TruSt_rel := (TruSt_rel LR cons).



Add Parametric Morphism : thread_sem with signature
  eq ==> eq ==> (fun f1 f2 => forall x y, f1 x y <-> f2 x y) ==> iff as tsem_more.
Proof using All.
  ins. by apply tsem_more.
Qed.

Add Parametric Morphism : thread_sem with signature
  eq ==> set_equiv ==> eq ==> iff as tsem_tid_more.
Proof using All.
  by ins; apply tsem_tid.
Qed.

Inductive TruSt_step_RW G l RW : execution -> list Event -> list Event -> Prop :=
  | NREVISIT_RW G' l' e (nr : TruSt_step G l NR e G' l') :
    TruSt_step_RW G l RW G' l' RW
  | REVISIT_RW G' l' e a (rv : TruSt_step G l (RV a) e G' l') :
    TruSt_step_RW G l RW G' l' (e :: RW).

Inductive TruSt_RW  G l RW : execution -> list Event -> list Event -> Prop :=
  | Base_RW : TruSt_RW G l RW G l RW
  | Step_RW G1 l1 RW1 G2 l2 RW2
    (TS1 : TruSt_RW      G  l  RW  G1 l1 RW1)
    (TS2 : TruSt_step_RW G1 l1 RW1 G2 l2 RW2) :
    TruSt_RW G l RW G2 l2 RW2.

Definition Revisitable G l RW :=
  filterP (fun w => ~ ⦗ eq w ⦘ ⨾ rf G ∩ total_order_from_list l ≡ ∅₂) RW.

Definition NRevisitable G l RW :=
  filterP (fun w => ~ In w (Revisitable G l RW)) RW.

Lemma Revisitable_NRevisitable G l {RW w} (InRW : In w RW) :
  In w (Revisitable G l RW) \/ In w (NRevisitable G l RW).
Proof using.
  unfold NRevisitable; in_simp.
  tertium_non_datur (In w (Revisitable G l RW)); vauto.
Qed.

Arguments D /.

Lemma TruSt_RW_TruSt {G l RW}
  (TS_RW : TruSt_RW G0 nil nil G l RW) :
  TruSt G0 nil G l.
Proof using.
  induction TS_RW; vauto.
  destruct TS2; vauto.
Qed.

Lemma TruSt_step_RW_RW {G l G' l' RW}
  (TS0 : TruSt G0 nil G l)
  (TS : TruSt_step_RW G l RW G' l' RW) :
  ⟪ R_R   : Revisitable  G l RW = Revisitable  G' l' RW ⟫ /\
  ⟪ NR_NR : NRevisitable G l RW = NRevisitable G' l' RW ⟫.
Proof using .
  cut (Revisitable G l RW = Revisitable G' l' RW);
    [unfold NRevisitable; intros ->; eauto|].
  inv TS; [|eapply (f_equal (@length Event)) in H1; simpls; lia].
  inv nr; unfold Revisitable; simpls; apply filterP_set_equiv.
  { cdes Next; cdes Next0; split; unfolder; intros x F F1.
    { clarify_not.
      apply (F1 z n0); exists z; splits; eauto.
      { left; splits; eauto.
        apply (wf_rfE (TruSt_Wf TS0)) in F3; unfolder in F3.
        exists n0; desf; splits; ins; intro; desf. }
      apply total_order_from_list_cons; eauto. }
    clarify_not. desf.
    { apply total_order_from_list_cons in F4.
      apply (wf_rfE (TruSt_Wf TS0)) in F3; unfolder in F3; desf.
      apply (F1 z n0); exists z; eauto. }
    apply total_order_from_list_cons in F4; desf.
    apply total_order_from_list_in2 in F4;
    apply (TruSt_G_corr_ord TS0) in F4; unfolder in F4; desf. }
  cdes Next; cdes Next0; split; unfolder; intros x F F1.
  { clarify_not.
    apply (F1 z n0); exists z; splits; eauto.
    apply total_order_from_list_cons; vauto. }
  clarify_not; apply total_order_from_list_cons in F4.
  apply (wf_rfE (TruSt_Wf TS0)) in F3; unfolder in F3; desf.
  apply (F1 z n0); exists z; eauto.
Qed.

Lemma revisit_wirte_NR {G l a e G' l' w RW}
  (TS0 : TruSt G0 nil G l)
  (TS : TruSt_step G l (RV a) e G' l')
  (InNR : In w (NRevisitable G' l' (e :: RW))) :
  In w RW.
Proof using .
  unfold NRevisitable in InNR. in_simp; simpls; desf.
  destruct InNR0; unfold Revisitable; in_simp; split; [basic_solver|].
  unfolder; intros F; desf; apply (F w a).
  inv TS; splits; ins; eauto; unfolder; eauto.
  destruct (excluded_middle_informative _); [| tauto].
  apply total_order_from_list_cons; left; splits; eauto.
  in_simp; splits; [|left]; splits; eauto.
  { eapply TruSt_G_corr_ord; eauto; split; eauto.
    by destruct a as [|?? [|]]. }
  apply r_not_in_Del; [eby eapply TruSt_NoDup | intros IN].
  apply (TruSt_G_corr_ord TS0) in IN; unfolder in IN.
  cdes Next; cdes Next0; desf.
Qed.

Lemma e_hb e G1 l1 RW1 G2 l2 w a
  (Gw : acts G2 w)
  (TS : TruSt_RW G0 nil nil G1 l1 RW1)
  (TS2  : TruSt_step_RW G1 l1 RW1 G2 l2 (e :: RW1))
  (IN : In w (NRevisitable G2 l2 (e :: RW1)))
  (Rw : In w (Revisitable G1 l1 RW1))
  (rv: TruSt_step G1 l1 (RV a) e G2 l2) :
  hb G2 w e.
Proof using  .
  unfold NRevisitable in IN; in_simp; unfold Revisitable in IN0, Rw; in_simp.
  clarify_not; unfolder in Rw0; desf.
  apply TruSt_RW_TruSt in TS.
  assert (IsMaximal (Add G1 e) l1 n0 e) as M.
  eapply Max_Da; eauto.
  tertium_non_datur (n0 = a) as [|NEQ]; desf; vauto; left.
  { eapply InDel; [eauto|eapply TruSt_Wf in Rw1; eauto|].
    { unfolder in Rw1; desf. }
    unfolder in IN0; desf; intros ACT.
    apply (IN0 n n0); splits; eauto.
    { apply (rf_G' rv); eauto. left; splits; eauto.
      rewrite (set_equiv_exp (acts_G' rv)) in ACT.
      unfolder in ACT; desf.
      { rewrite (set_equiv_exp (acts_G' rv)) in Gw.
        unfolder in Gw; desf; [basic_solver|].
        apply e_not_in_G in rv; eapply (TruSt_Wf TS) in Rw1.
        by unfolder in Rw1; desf. }
      apply e_not_in_G in rv; eapply (TruSt_Wf TS) in Rw1.
      by unfolder in Rw1; desf. }
    inv rv; ins; destruct (excluded_middle_informative _); [|firstorder].
    apply total_order_from_list_cons; right.
    apply total_order_from_list_filterP; unfolder; eauto. }
  pose proof Rw1 as Rw'.
  apply (wf_rfD (TruSt_Wf TS)) in Rw1; unfolder in Rw1; desf.
  destruct (M n) as [M' _]; [basic_solver|]; clear M.
  desf; [by destruct n0 as [|??[]]| |].
  { edestruct (total_order_from_list_irreflexive (TruSt_NoDup TS)).
    eapply (total_order_from_list_trans (TruSt_NoDup TS)); eauto. }
  eapply hb_Add_in_G'; eauto; unfolder; splits; eauto.
  { eby eapply G'_e. }
  intro; desf; inv rv; by destruct a as [|??[]].
Qed.

Lemma e_in_R e G1 l1 RW1 G2 l2 a
  (TS : TruSt_RW G0 nil nil G1 l1 RW1)
  (TS2  : TruSt_step_RW G1 l1 RW1 G2 l2 (e :: RW1))
  (rv : TruSt_step G1 l1 (RV a) e G2 l2):
   In e (Revisitable G2 l2 (e :: RW1)).
Proof using .
  unfold Revisitable; in_simp; splits; [vauto|unfolder; intro F].
  desf; clarify_not; apply (F e a); splits; eauto.
  { apply (rf_G' rv); apply TruSt_RW_TruSt in TS; vauto. }
  inv rv; simpls.
  destruct (excluded_middle_informative _); [|firstorder].
  apply total_order_from_list_cons; left; splits; eauto.
  in_simp. apply TruSt_RW_TruSt in TS; splits.
  { apply (TruSt_G_corr_ord TS).
    split; eauto; by destruct a as [|??[]]. }
  left; split; eauto.
  apply r_not_in_Del; [eby eapply TruSt_NoDup|intros F'].
  cdes Next; cdes Next0.
  eapply (TruSt_G_corr_ord TS) in F'; unfolder in F'; desf.
Qed.

Lemma is_w_RW {G l RW w}
  (TS: TruSt_RW G0 nil nil G l RW)
  (RWw : In w RW) : is_w w.
Proof using.
  induction TS; [basic_solver|].
  destruct TS2; simpls; desf; eauto.
  by inv rv.
Qed.

Lemma TruSt_RW_prop G l RW (TS : TruSt_RW G0 nil nil G l RW) :
  ⟪ RW_G : forall e, In e RW -> acts G e ⟫ /\
  ⟪ NR_R : forall w, In w (NRevisitable G l RW) ->
     exists w', In w' (Revisitable G l RW) /\ hb G w w' ⟫.
Proof using  .
  induction TS; [basic_solver|]; desf.
  assert (forall e, In e RW2 -> acts G2 e) as RW2_G2.
  { inv TS2.
    { intros ??. rewrite (set_equiv_exp (TruSt_Step_NRV nr)); left.
      eauto. }
    intros w IN; simpls; desf; [eby eapply G'_e|].
    tertium_non_datur (acts G2 w) as [|NACT]; auto; exfalso.
    eapply InDel in NACT; eauto.
    destruct (Revisitable_NRevisitable G1 l1 IN) as [InR|InNR].
    { unfold Revisitable in InR; in_simp; clarify_not.
      eapply Del_rf_l; eauto; [eby eapply TruSt_RW_TruSt|].
      unfolder in InR0; desf; unfolder; eauto. }
    apply NR_R in InNR; desf. unfold Revisitable in InNR; in_simp; clarify_not.
    unfolder in InNR1; desf.
    eapply Da_hb_rf_l; eauto; [eby eapply TruSt_RW_TruSt|].
    unfolder; split; [left; eauto|]; eauto 11. }
  split; auto; intros w IN.
  assert (acts G2 w) as Gw.
  { apply RW2_G2; unfold NRevisitable in IN; in_simp. }
  inv TS2.
  { pose proof (TruSt_step_RW_RW (TruSt_RW_TruSt TS) TS2); desf.
    rewrite <- NR_NR, <- R_R in *.
    destruct (NR_R w IN); eexists; split; desf; eauto.
    eapply hb_TruSt_step_nr; eauto; eby eapply TruSt_RW_TruSt. }
  destruct (Revisitable_NRevisitable G1 l1 (revisit_wirte_NR (TruSt_RW_TruSt TS) rv IN)) as [Rw|NRw].
  { exists e; split; [eapply e_in_R|eapply e_hb]; edone. }
  apply NR_R in NRw; desf.
  assert (acts G2 w').
  { apply RW2_G2; unfold Revisitable in NRw; in_simp; vauto. }
  pose proof (TruSt_RW_TruSt TS).
  pose proof NRw as Ww.
  unfold Revisitable in Ww; in_simp; apply (is_w_RW TS) in Ww.
  destruct (Revisitable_NRevisitable G2 l2 (w := w') (RW := e :: RW1)).
  { unfold Revisitable in NRw; in_simp; basic_solver. }
  { exists w'; split; eauto; eapply hb_in_G'; eauto.
    unfolder; splits; eauto; intro; desf.
    pose proof (is_r_a rv).
    by destruct a as [|??[]]. }
  exists e; split; [eapply e_in_R|]; eauto.
  apply ct_ct; exists w'; split; [eapply hb_in_G'|]; eauto.
  { unfolder; splits; eauto; intro; desf.
    pose proof (is_r_a rv); by destruct a as [|??[]]. }
  eby eapply e_hb.
Qed.

Lemma TruSt_NoDup_RW G l RW (TS : TruSt_RW G0 nil nil G l RW) :
  NoDup RW.
Proof using  .
  induction TS; auto.
  destruct TS2; auto.
  apply TruSt_RW_prop in TS; desf.
  apply e_not_in_G in rv.
  apply nodup_cons; auto.
Qed.

Lemma TruSt_not_init_RW G l RW e
  (TS  : TruSt_RW G0 nil nil G l RW)
  (Inl : In e RW) :
  ~ is_init e.
Proof using.
  induction TS; auto.
  destruct TS2; auto; simpls; desf; eauto.
  inv rv; by apply not_init_next in Next.
Qed.

Lemma TruSt_RW_l G l RW
  (TS  : TruSt_RW G0 nil nil G l RW) : 
  length RW <= length l.
Proof using  .
  apply (NoDup_incl_length (TruSt_NoDup_RW TS)).
  intros ? IN; assert (IN' := IN); apply (TruSt_RW_prop TS) in IN.
  eapply TruSt_G_corr_ord; [eby eapply TruSt_RW_TruSt|].
  split; auto; eby eapply TruSt_not_init_RW.
Qed.

Variable K : nat.

Definition B := (K + 1) * (K + 1) + K + 2.

Hypothesis p_sem_finite :
  forall G, p_sem G -> 
    exists l, 
      << OC : G_ord_corr G l >> /\
      << ND : NoDup l        >> /\
      << LK : length l < K   >>.

Record state_rw : Type := mkst_rw {
  Gl_of :> state;
  RW_of : list Event
}.

Definition TruSt_RW_rel (st1 st2 : state_rw) := 
  TruSt_step_RW (G_of st1) (l_of st1) (RW_of st1) (G_of st2) (l_of st2) (RW_of st2).

Definition strw0 := mkst_rw st0 nil.

Lemma TruSt_TruSt_RW st k
  (TS : TruSt_rel ^^ k st0 st) :
  exists rw, TruSt_RW_rel ^^ k strw0 (mkst_rw st rw).
Proof using. 
  generalize dependent st.
  induction k; simpls; unfolder.
  { eexists; basic_solver. }
  intros; desf.
  assert (TS' := TS); apply IHk in TS; desf.
  inv TS0; desf; inv H.
  all: do 2 eexists; vauto.
Qed.

Lemma TruSt_k strw k 
  (TS : TruSt_RW_rel ^^ k strw0 strw) : 
  TruSt_RW G0 nil nil (G_of strw) (l_of strw) (RW_of strw).
Proof using.
  generalize dependent strw.
  induction k; intros strw; simpls; unfolder.
  { intros [<-]; vauto. }
  intros TS; desf; apply IHk in TS.
  destruct z, strw; inv TS0; ins; subst; vauto.
Qed.

Lemma l_RW_K (strw : state_rw) k
  (TS : TruSt_RW_rel ^^ k strw0 strw) : 
  << L  : length (l_of  strw) < K + 1 >> /\
  << RW : length (RW_of strw) < K + 1 >>.
Proof using p_sem_finite.
  apply TruSt_k in TS.
  cut (length (l_of strw) < K + 1).
  { intros l_K; split; eauto. apply TruSt_RW_l in TS; red; lia. }
  destruct strw as [[G l] RW]; ins.
  assert (G2_l2 := TS).
  apply TruSt_RW_TruSt, TruSt_G_corr_ord in G2_l2.
  destruct TS; [ins; lia|].
  assert (ND_l1 := TS).
  apply TruSt_RW_TruSt, TruSt_NoDup in ND_l1.
  assert (G1_l1 := TS).
  apply TruSt_RW_TruSt, TruSt_G_corr_ord in G1_l1.
  assert (length l1 < K) as l1_K.
  { assert (exists e, next G1 e) as AVAIL.
    { destruct TS2; [inv nr| inv rv]; eauto. }
    desf; cdes AVAIL; cdes AVAIL0.
    apply p_sem_finite in Sem; desf.
    assert (length l1 <= length l); [|lia].
    apply NoDup_incl_length; eauto.
    intros e' IN.
    apply G1_l1 in IN; apply OC.
    cdes GG'; generalize IN; basic_solver. }
  destruct TS2; [inv nr; ins; lia|inv rv; ins].
  destruct (excluded_middle_informative _); [ins|firstorder].
  assert  
  (length (filterP (acts G1 ∩₁ (set_compl D) ∪₁ eq e) l1) <=
   length l1); [apply length_filterP|lia].
Qed.

Theorem TruSt_wf k st
  (TS : TruSt_rel ^^ k st0 st) :
  k < B.
Proof using p_sem_finite.
  unfold B.
  apply TruSt_TruSt_RW in TS; desf.
  transitivity (length rw * (K + 1) + length (l_of st) + 1).
  { generalize st rw TS.
    clear st rw TS.
    induction k; [lia|intros st rw [[st' rw'] [TSk TS]]].
    assert (TSk' := TSk).
    apply IHk in TSk.
    destruct st' as [G' l']; destruct st as [G l]; ins.
    inv TS; ins; subst.
    { inv nr; ins; lia. }
    enough (length l' < K + 1); [ins; lia|].
    apply l_RW_K in TSk'; basic_solver. }
  apply l_RW_K in TS; desf; simpls.
  assert (length rw * (K + 1) < (K + 1) * (K + 1)); try lia.
  apply Mult.mult_lt_compat_r; lia.
Qed.

Lemma TruSt0 k (TS : TruSt_rel^^k st0 st0) : k = 0.
Proof using p_sem_finite.
  apply NNPP; intro.
  assert (forall x, TruSt_rel ^^ (x * k) st0 st0) as F.
  { intro x; induction x; ins.
    apply pow_add; vauto. }
  specialize (F B); apply TruSt_wf in F.
  destruct k; lia.
Qed.

End Termination.
