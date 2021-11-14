From hahn Require Import Hahn.
Require Import Execution Execution_Aux Events Labels.
From Coq Require Import Lia.
Require Import Util.

Set Implicit Arguments.

(******************************************************************************)
(** **  Thread Semantics  *)
(******************************************************************************)

Implicit Type val_t : (Event -> Val -> Prop).

Record tsemType := {
  tsem :> Tid -> (Event -> Prop) -> (Event -> Val -> Prop) -> Prop;

  tsem_index_corr : forall t l val_t, tsem t l val_t -> index_corr l;
  tsem_tid_init  : forall t l val_t, tsem t l val_t -> tid_init l;
  tsem_in_thrd   : forall t l val_t, 
    tsem t l val_t -> l ⊆₁ (fun e => tid e = t);
  tsem_pref_clos : forall l t l' val_t,
    sub_thread l' l ->
    tsem t l val_t ->  tsem t l' val_t;
  tsem_det       : forall t l val_t e1 e2,
    sb_max l e1 -> sb_max l e2 -> 
    tsem t (l ∪₁ eq e1) val_t -> 
    tsem t (l ∪₁ eq e2) val_t -> e1 = e2;
  tsem_recept     : forall t l val_t r v,
    sb_max l r -> is_r r ->
    tsem t l val_t ->
    tsem t l (fun x => ifP x = r then eq v else val_t x);
  tsem_val       : forall t (l : Event -> Prop) val_t1 val_t2, 
    (forall e, l e -> val_t1 e ≡₁ val_t2 e) -> 
    tsem t l val_t1 <-> tsem t l val_t2;
  tsem_tid       : forall t l1 l2 val_t,
    l1 ≡₁ l2 -> 
    tsem t l1 val_t <-> tsem t l2 val_t;
  tsem_write     : forall t l val_t w,
    is_w w -> tsem t l val_t -> val_t w ≡₁ eq (valw w);
  tsem_read     : forall t l val_t r,
    is_r r -> tsem t l val_t -> 
    exists v, val_t r ≡₁ eq v;
}.

Section Sem.

Variable thread_sem : tsemType.

Add Parametric Morphism : thread_sem with signature
  eq ==> eq ==> (fun f1 f2 => forall x y, f1 x y <-> f2 x y) ==> iff as tsem_more.
Proof using All.
  intros t l val_t1 val_t2 vE.
  by split; apply tsem_val; ins; split; unfolder; ins; apply vE.
Qed.

Add Parametric Morphism : thread_sem with signature
  eq ==> set_equiv ==> eq ==> iff as tsem_tid_more.
Proof using All.
  by ins; apply tsem_tid.
Qed.

Lemma tsem_val_sb_max t e (l : Event -> Prop) val_t1 val_t2
  (VALEQ : forall e, l e -> val_t2 e ≡₁ val_t1 e)
  (SBM   : sb_max l e)
  (VAL2w : is_w e -> val_t2 e ≡₁ eq (valw e))
  (VAL2r : is_r e -> exists v, val_t2 e ≡₁ eq v) 
  (TS : thread_sem t (l ∪₁ eq e) val_t1) :
    thread_sem t (l ∪₁ eq e) val_t2.
Proof using All.
  tertium_non_datur (is_r e) as [R|NR].
  { specialize (VAL2r R); desf.
    eapply tsem_recept with (v := v) in TS; eauto.
    { eapply tsem_val; [|apply TS]; intros e0 [|]; desf; auto. }
    generalize (ext_sb_irr e) SBM.
    unfold sb_max; basic_solver. }
  apply n_is_r in NR.
  eapply tsem_val; [|apply TS]; intros e0 [|]; desf; auto.
  rewrite VAL2w; auto; symmetry; eby eapply tsem_write.
Qed.

Lemma index_corr_Add G e v1 v2
  (TSEM1 : forall t, thread_sem t (thread_of G t) v1)
  (TSEM2 : thread_sem (tid e) (thread_of G (tid e) ∪₁ eq e) v2):
  index_corr (acts (Add G e)).
Proof using All.
  apply index_corr_ex; ins.
  tertium_non_datur (t = tid e) as [|T]; subst.
  { apply tsem_index_corr in TSEM2; intros ?? F.
    apply TSEM2; generalize F; basic_solver. }
  intros ??.
  assert ((acts G ∪₁ eq e) ∩₁ (fun x : Event => tid x = t) ≡₁
          acts G ∩₁ (fun x : Event => tid x = t)) as R.
  { basic_solver. }
  specialize (TSEM1 t); rewrite <-R in TSEM1.
  eby eapply tsem_index_corr.
Qed.

(******************************************************************************)
(** **  Programm Semantics  *)
(******************************************************************************)

Definition p_sem G := 
  << Wf_G : Wf G >> /\
  << RFC  : rf_complete G >> /\
  << TSEM : forall t, thread_sem t (thread_of G t) (val G) >>.

Lemma p_sem_Wf : p_sem ⊆₁ Wf.
Proof using. firstorder. Qed.

Hint Immediate p_sem_Wf : core.

Lemma p_sem_RF : 
   forall G r w
    (Read : is_r r)
    (Write : is_w w)
    (SM : same_loc w r)
    (inG_r : acts G r)
    (inG_w : acts G w)
    (HBM   : hb_max G r)
    (PS : p_sem G), p_sem (SetRF G r w).
Proof using All.
  ins.
  unfold p_sem in PS; desf; split; splits.
  { split; try (by apply Wf_G); ins.
    1: rewrite (wf_rfE Wf_G) at 1.
    2: rewrite (wf_rfD Wf_G) at 1.
    1,2: rewrite ?seqA, seq_union_l, seqA, seq_union_r. 
    1,2: setoid_rewrite seq_eqvC at 2; apply union_more; eauto.
    1,2: basic_solver.
    { apply inclusion_union_l.
      { rewrite inclusion_seq_eqv_r; apply Wf_G. }
      unfolder; ins; desf. }
    unfolder; ins; desf; eby eapply (wf_rff Wf_G). }
  { unfold rf_complete; ins.
    etransitivity; [eauto|].
    rewrite codom_union, codom_singl_rel, codom_eqv1.
    rewrite set_union_inter_l.
    apply set_subset_inter_r; split; [basic_solver|].
    intros x ?; unfolder; destruct (classic (x = r)); vauto. }
  ins; specialize (TSEM t).
  eapply tsem_more; [| |apply val_SetRF|]; eauto; ins.
  apply tsem_recept; eauto; split; [|basic_solver].
  intros e1 e2 F; unfolder in F; desf.
  eapply HBM with (x := e2); unfolder; exists e1, e1; splits; eauto.
  apply ct_step; left; unfold sb. basic_solver.
Qed.

Add Parametric Morphism : p_sem with signature
  sub_execution ==> (Basics.flip Basics.impl) as p_sem_mori.
Proof using All.
  intros G G' SUB; cdes SUB.
  specialize (sub_execution_sb SUB); intro SUBsb.
  unfold p_sem; intros PS; desf; split; splits.
  { eby eapply sub_execution_wf. }
  { unfold rf_complete; rewrite SUBrf, codom_eqv1.
    apply set_subset_inter_r; split.
    { etransitivity; [|eauto]; by apply set_subset_inter. }
    basic_solver. }
  ins. specialize (TSEM t).
  cut (thread_sem t (acts G ∩₁ (fun x : Event => tid x = t)) (val G')).
  { apply tsem_val; intros ? []; apply sub_execution_val; eauto. }
  generalize TSEM; apply tsem_pref_clos.
  by apply sub_execution_thread.
Qed.

Lemma tid_init_Add G e v2
  (PSEM : p_sem G)
  (TSEM : thread_sem (tid e) (thread_of G (tid e) ∪₁ eq e) v2):
  tid_init (acts (Add G e)).
Proof using All.
  ins; apply tid_init_union.
  { apply p_sem_Wf in PSEM; by destruct PSEM. }
  apply tsem_tid_init in TSEM; intros ??; apply TSEM; basic_solver.
Qed.

(* ************************************************************************* *)
(*                              <_next definition                            *)
(* ************************************************************************* *)

Record LRType := {
  LR_of    :> relation Event;

  LR_irr   : irreflexive LR_of;
  LR_trans : transitive LR_of;
  sb_LR    : ext_sb ⊆ LR_of;
  LR_total : forall G, p_sem G -> is_total (acts G) LR_of;
}.

Variable LR : LRType.

Lemma LRcr_trans : transitive LR^?.
Proof.
  destruct LR; ins; basic_solver.
Qed.

Notation "e1 '<_next' e2" := (LR_of LR e1 e2) (at level 20).

Implicit Types (G : execution) (e r w : Event).

(******************************************************************************)
(** **  Avaliable events  *)
(******************************************************************************)

Definition avail G e :=
  exists G',
    ⟪ Sem  : p_sem G'     ⟫ /\
    ⟪ InG' : G'.(acts) e  ⟫ /\
    ⟪ NInG : ~ G.(acts) e ⟫ /\
    ⟪ GG'  : (G ⊆ G')%Ex  ⟫ /\
    ⟪ HB   : forall e', hb G' e' e -> G.(acts) e' ⟫.

Definition avail_sbrf G e :=
  exists G',
    ⟪ Sem  : p_sem G'     ⟫ /\
    ⟪ InG' : G'.(acts) e  ⟫ /\
    ⟪ NInG : ~ G.(acts) e ⟫ /\
    ⟪ GG'  : (G ⊆ G')%Ex  ⟫ /\
    ⟪ HB   : forall e', (sb G' ∪ rf G') e' e -> G.(acts) e' ⟫.

Definition avail_sb G e :=
  exists G',
    ⟪ Sem  : p_sem G'     ⟫ /\
    ⟪ InG' : G'.(acts) e  ⟫ /\
    ⟪ NInG : ~ G.(acts) e ⟫ /\
    ⟪ GG'  : (G ⊆ G')%Ex  ⟫ /\
    ⟪ HB   : forall e', sb G' e' e -> G.(acts) e' ⟫/\
    << HBee : ~ hb G' e e >>.

Lemma avail_avail_sbrf G
  (Wf_G : Wf G) :
  avail G ≡₁ avail_sbrf G.
Proof using.
  unfold avail, avail_sbrf.
  split; intros e AV; desf; exists G'; splits; eauto.
  { by intros ??; apply HB, ct_step. }
  intros e' HB'.
  apply clos_trans_tn1 in HB'.
  destruct HB' as [x SBRF|x y SBRF].
  { by apply HB. }
  apply clos_tn1_trans in HB'.
  apply HB in SBRF; eby eapply sub_execution_hb.
Qed.

Lemma avail_sb_max G e e' (AVAIL : avail G e) (ACT : acts G e'):
  ~ ext_sb e e'.
Proof using.
  intros F; cdes AVAIL.
  assert (sb G e e') as SB'.
  { hahn_rewrite (sub_execution_sb GG'); unfolder; split; eauto.
    by unfold sb; unfolder; splits; eauto; apply GG'. }
  unfold sb in SB'; unfolder in SB'; desf.
Qed.

Lemma avail_avail_sb G
  (Wf_G : Wf G) :
  avail G ≡₁ avail_sb G.
Proof using All.
  unfold avail_sb.
  split; [|rewrite (avail_avail_sbrf Wf_G)]; intros e AV; desf.
  { cdes AV; exists G'; splits; eauto; intros ??; apply HB; vauto. }
  destruct (classic (is_r e)) as [R|NR].
  { exists (SetRF (Restr G' (acts G ∪₁ (fun x => (hb G')^? x e))) e (InitEvent (loc e))).
    assert ((acts G' ∩₁ (acts G ∪₁ (fun x : Event => (hb G')^? x e))) e) as ACT.
    { split; eauto; vauto. }
    splits; eauto.
    { apply p_sem_RF; eauto; ins.
      { split; [by apply (p_sem_Wf Sem)|left; by apply Wf_G]. }
      { apply hb_maxE; split; eauto; split; [|basic_solver].
        unfolder; intros e' SBRF; desf.
        { apply sb_Restr in SBRF0; unfolder in SBRF0; desf.
          { eapply NInG, sub_execution_hb; eauto.
            apply ct_step; vauto. }
          { eby eapply sb_irr. }
          apply HBee, ct_ct; eexists; split; eauto.
          apply ct_step; vauto. }
        ins; unfolder in SBRF0; destruct SBRF0 as [_ [RF _]].
        apply (wf_rfD (p_sem_Wf Sem)) in RF; unfolder in RF; desf.
        by destruct x as [|??[]]. }
      eapply p_sem_mori; eauto.
      apply (Restr_clos_sub (p_sem_Wf Sem)).
      { destruct Wf_G; firstorder. }
      rewrite id_union, seq_union_r, dom_union; apply set_subset_union.
      { unfolder; intros ??; desf; eby eapply sub_execution_hb. }
      intros ? [? [? [? [? []]]]]; subst; eauto.
      right; eby eapply hb_trans. }
    { apply sub_sub_exec_SetRF; eauto; by apply Restr_union. }
    intros e' [SB|RF].
    { apply sb_SetRF, sb_Restr in SB.
      unfolder in SB. destruct SB as [_ [SB _]]; auto. }
    { simpl in RF; unfolder in RF; desf; by apply Wf_G. } }
  exists G'; splits; eauto; intros ? [SB|RF]; eauto.
  apply (wf_rfD (p_sem_Wf Sem)) in RF; unfolder in RF; desf.
Qed.

Lemma avail_SetRF G w r
  (Wf_G : Wf G) (InGw : acts G w)
  (R : is_r r) (W : is_w w) (SL : same_loc w r)
  (AV : avail G r) :
  avail (SetRF (Add G r) r w) ⊆₁
  avail G ∪₁ (fun x => ext_sb r x).
Proof using All.
  rewrite (avail_avail_sb Wf_G).
  unfold avail_sb; intros e AVAIL; desf; ins.
  apply avail_avail_sb in AVAIL.
  { cdes AVAIL; tertium_non_datur (ext_sb r e) as [|NSB]; vauto.
    left; exists G'; splits; eauto.
    { eapply sub_execution_trans; eauto.
      eapply sub_exec_SetRF; eauto; [by cdes AV|].
      ins; eapply avail_sb_max; eauto. }
    intros e' SB'.
    destruct (HB e'); vauto.
    unfold sb in SB'; unfolder in SB'; desf. }
  cdes AV; eapply Wf_SetRF with (G' := G'); eauto; by apply GG'.
Qed.

Lemma avail_SetCO G w w'
  (Wf_G : Wf G) 
  (SL : same_loc w w') (InGw : acts G w)
  (W : is_w w) (W' : is_w w') (WF : Wf G)
  (AV : avail G w') :
  avail (SetCO (Add G w') w w') ⊆₁
  avail G ∪₁ (fun x => ext_sb w' x).
Proof using All.
  rewrite (avail_avail_sb Wf_G).
  unfold avail_sb; intros e AVAIL; desf; ins.
  apply avail_avail_sb in AVAIL.
  { cdes AVAIL; tertium_non_datur (ext_sb w' e) as [|NSB]; vauto.
    left; exists G'; splits; eauto.
    { eapply sub_execution_trans; eauto.
      eapply sub_exec_SetCO; eauto; [by cdes AV|].
      ins; eapply avail_sb_max; eauto. }
    intros e' SB'.
    destruct (HB e'); vauto.
    unfold sb in SB'; unfolder in SB'; desf. }
  cdes AV; eapply Wf_SetCO with (G' := G'); eauto; by apply GG'.
Qed.

Lemma avail_thread G e : 
  avail G e <->
  << SBM   : sb_max (acts G) e >> /\
  << SEM   : p_sem G           >> /\
  << NinG  : ~ acts G e        >> /\
  exists t v, 
  << TS   : 
    thread_sem t (thread_of G t ∪₁ eq e) 
    (fun x => ifP x = e then eq v else val G x) >>.
Proof using thread_sem.
  split.
  { intros AV; cdes AV.
    split; splits; eauto.
    { split; [|basic_solver].
      intros e1 e2 F; unfolder in F; desf.
      cdes GG'; apply sub_execution_sb in GG'.
      apply NInG; specialize (SUBev _ F1).
      destruct GG' as [? [? SB]].
      { unfold sb; unfolder; splits; [|eauto| |]; auto. }
      unfolder in SB; desf. }
    { by rewrite GG'. }
    cdes Sem.
    assert (WF := Wf_G).
    apply (sub_execution_wf GG') in WF.
    destruct (classic (is_r e)) as [R|NR].
    { specialize (RFC e); unfolder in RFC; destruct RFC as [w RF]; eauto.
      desf; exists (tid e), (valw w); splits; eauto.
      apply tsem_val with (val_t1 := val G').
      { intros e' [T|EQ]; desf.
        { ins; unfolder in T; desf. }
        { symmetry; apply sub_execution_val; eauto; ins.
          generalize T; basic_solver. }
        apply wf_rff in Wf_G; unfold val; desf; split.
        { by intros ? RF'; apply RF'. }
        eby intros ? V; subst; ins; eapply f_equal, Wf_G. }
      eapply tsem_pref_clos; eauto; by apply sub_execution_thread_e. }
    exists (tid e), (valw e).
    eapply tsem_val with (val_t1 := val G'); eauto.
    { intros e0 T.
      tertium_non_datur (e0 = e) as [|N]; desf.
      { unfold val; desf. }
      rewrite <-sub_execution_val; eauto.
      ins; unfolder in T; desf. }
    eapply tsem_pref_clos; eauto. by apply sub_execution_thread_e. }
  ins; desf; cdes SEM.
  assert (T := tsem_in_thrd _ _ _ _ TS); unfolder in T; desf.
  specialize (T e). rewrite <-T in TS; vauto.
  destruct (classic (is_r e)) as [R|NR].
  { eapply tsem_recept with (r := e) (v := 0) in TS; eauto.
    { apply avail_avail_sbrf; eauto.
      exists (SetRF (Add G e) e (InitEvent (loc e))); splits; vauto.
      { unfold p_sem; splits.
        { eapply Wf_SetRF' with (G' := (Add G e)); vauto.
          { eby eapply tid_init_Add. }
          { eby eapply index_corr_Add. }
          by apply Wf_G. }
        { intro e'; intro ACT.
           destruct (classic (e' = e)); subst;
           ins; unfolder in ACT; desf; apply codom_union.
          { by right; apply codom_singl_rel. }
          left. apply codom_eqv1; split; eauto.
          apply RFC; basic_solver. }
        ins. 
        eapply tsem_more; [| |apply (val_SetRF _ _ _ R)|]; eauto.
        tertium_non_datur (tid e = t0) as [T0|T0]; subst.
        { assert (
          (acts G ∪₁ eq e) ∩₁ (fun x : Event => tid x = tid e) ≡₁
          (acts G ∩₁ (fun x : Event => tid x = tid e) ∪₁ eq e)
          ) as ACTE.
          { basic_solver. }
          rewrite ACTE; eapply tsem_more; eauto; basic_solver. }
        assert (
            (acts G ∪₁ eq e) ∩₁ (fun x : Event => tid x = t0) ≡₁
            acts G ∩₁ (fun x : Event => tid x = t0)
            ) as ACTE.
        { basic_solver. }
        rewrite ACTE; eapply tsem_val; eauto.
        intro e'; desf; basic_solver. }
      { apply sub_exec_SetRF; eauto; intros ???.
        eapply SBM; basic_solver. }
      intros e' [SB|RF]; ins.
      { apply sb_SetRF  in SB; unfold sb in SB; ins; unfolder in SB; desf.
        by apply ext_sb_irr in SB0. }
      by unfolder in RF; desf; apply Wf_G. }
    apply sb_max_in_tid in SBM.
    { ins; unfold sb_max; rewrite id_union, ?seq_union_r.
      unfold sb_max in SBM; rewrite SBM.
      generalize (ext_sb_irr e); basic_solver. }
    by destruct e as [|??[]]. }
  apply avail_avail_sbrf; eauto.
  exists (SetCO (Add G e) (InitEvent (loc e)) e); splits; vauto.
  { unfold p_sem; splits.
    { apply n_is_r in NR.
      eapply Wf_SetCO' with (G' := Add G e); vauto.
      { eby eapply tid_init_Add. }
      { eby eapply index_corr_Add. }
      by apply Wf_G. }
    { intros ? F; ins; apply RFC; unfolder in F; desf. }
    ins.
    tertium_non_datur (tid e = t0) as [T0|T0]; subst.
    { assert (
      (acts G ∪₁ eq e) ∩₁ (fun x : Event => tid x = tid e) ≡₁
      (acts G ∩₁ (fun x : Event => tid x = tid e) ∪₁ eq e)
      ) as ACTE.
      { basic_solver. }
      rewrite ACTE; eapply tsem_more; eauto.
      intros ??.
      assert (v = valw e); subst.
      { apply n_is_r in NR.
        apply tsem_write with (w := e) in TS; eauto.
        generalize TS; basic_solver. }
      desf; unfold val; desf. }
    assert (
        (acts G ∪₁ eq e) ∩₁ (fun x : Event => tid x = t0) ≡₁
        acts G ∩₁ (fun x : Event => tid x = t0)
        ) as ACTE.
    { basic_solver. }
    rewrite ACTE; eapply tsem_val; eauto. }
  { apply sub_exec_SetCO; eauto.
    intros ???; eapply SBM; basic_solver. }
  intros ? [SB|RF]; ins.
  { apply sb_SetCO in SB; unfold sb in SB; ins; unfolder in SB; desf.
    by apply ext_sb_irr in SB0.  }
  apply Wf_G in RF; unfolder in RF; desf.
Qed.

(* Arguments thread_of : simpl never. *)

Lemma not_init_avail G e (Next : avail G e) : ~ is_init e.
Proof using.
  intros F; cdes Next.
  apply p_sem_Wf, (sub_execution_wf GG') in Sem.
  by apply Sem in F.
Qed.


Lemma avail_Restr G e 
  (NINI : ~ is_init e)
  (PSEM : p_sem G) 
  (HBM  : hb_max G e) : 
  avail (Restr G (set_compl (eq e))) ⊆₁
  avail G ∪₁ eq e.
Proof using.
  intros e' AV.
  assert (NINI' := not_init_avail AV).
  apply avail_thread in AV; desf; ins.
  assert (Restr G (set_compl (eq e)) ⊆ G)%Ex.
  { rewrite Resrt_in_G; eauto.
    apply Restr_clos_sub; eauto.
    { apply p_sem_Wf in SEM; apply SEM. }
    unfolder; intros x HB; desf; split.
    { apply wf_hbE in HB; eauto; unfolder in HB; desf. }
    intro; desf; eapply HBM; exists x, x; splits; basic_solver. }
  assert (TID := TS).
  apply tsem_in_thrd in TID.
  specialize (TID e'); ins; rewrite <- TID in TS; vauto.
  clear TID.
  destruct (classic (tid e' = tid e)) as [T|T].
  { right; clarify_not.
    assert (
      sb_max 
        (acts G ∩₁ set_compl (eq e) ∩₁ (fun x : Event => tid x = tid e')) e
    ).
    { rewrite T; rewrite <- sb_max_in_tid; eauto.
      apply hb_max_sb_max in HBM.
      eapply sb_max_subset; [|eauto]; firstorder. }
    eapply tsem_det; [| | |eauto]; eauto.
    { rewrite <- sb_max_in_tid; eauto. }
    apply tsem_val_sb_max with (val_t1 := val G); eauto.
    { intros ? F; unfolder in F; desf.
      apply sub_execution_val; basic_solver. } 
    { ins; eapply tsem_write in TS; eauto. }
    { ins; eapply tsem_read in TS; eauto. }
    rewrite T; cdes PSEM; specialize (TSEM (tid e)).
    eapply tsem_tid; [|eauto]. cdes HBM; ins.
    rewrite set_union_inter_l. apply set_equiv_inter; [|basic_solver].
    rewrite <- set_minusE. 
    unfolder; split; ins; desf. destruct (classic (e = x)); desf; vauto. }
  assert (
    set_compl (eq e) ∩₁ (fun x : Event => tid x = tid e') ≡₁
    fun x : Event => tid x = tid e') as E.
  { split; [basic_solver|].
    unfolder; ins; split; eauto; intro; basic_solver. }
  left; apply avail_thread; splits; eauto.
  { apply sb_max_in_tid in SBM; eauto.
    apply sb_max_in_tid; eauto.
    unfold sb_max in SBM; rewrite set_interA in SBM. 
    rewrite E in SBM; eauto. }
  { clarify_not. }
  exists (tid e'), v.
  apply (@tsem_tid _ _ (thread_of (Restr G (set_compl (eq e))) (tid e') ∪₁ eq e')).
  { ins. by rewrite set_interA, E. }
  eapply tsem_val; eauto; intros e'' TR.
  unfolder in TR; desf; symmetry.
  apply sub_execution_val; auto.
  ins; unfolder in TR; desf.
Qed.

Lemma Restr_sub_hb_max G e 
  (INI : ~ is_init e)
  (Wf_G : Wf G)
  (HBM : hb_max G e) : 
  ((Restr G (set_compl (eq e))) ⊆ G)%Ex.
Proof.
  apply Restr_clos_sub; eauto.
  { unfolder; intros ???; destruct x; desf. }
  cdes HBM; unfolder; intros ? HB ?; desf.
  eapply N_HB; vauto.
Qed.

Lemma RestrRestrE G e1 e2: Restr G (set_compl (eq e1 ∪₁ eq e2)) =
  Restr (Restr G (set_compl (eq e1))) (set_compl (eq e2)).
Proof.
  rewrite <-eq_executionE; split; splits; ins.
  all: rewrite ?set_compl_union; basic_solver.
Qed.

Lemma avail_Restr2 G e1 e2
  (NINI1 : ~ is_init e1)
  (NINI2 : ~ is_init e2)
  (PSEM  : p_sem G) 
  (HBM   : hb_max G e1)
  (CD    : codom_rel (<|eq e2|> ;; hb G) ≡₁ eq e1) : 
  avail (Restr G (set_compl (eq e1 ∪₁ eq e2))) ⊆₁
  avail G ∪₁ eq e1 ∪₁ eq e2.
Proof using.
  destruct (classic (e1 = e2)); desf.
  { assert (Restr G (set_compl (eq e2 ∪₁ eq e2)) =
            Restr G (set_compl (eq e2))) as EQ.
    { rewrite <-eq_executionE; split; splits; ins.
      all: rewrite ?set_compl_union; basic_solver. }
    rewrite EQ, avail_Restr; basic_solver. }
  assert (EQ := RestrRestrE G e1 e2).
  assert (WF := p_sem_Wf PSEM).
  assert (Restr G (set_compl (eq e1)) ⊆ G)%Ex as SUB.
  { apply Restr_sub_hb_max; eauto. }
  rewrite EQ, ?avail_Restr; auto.
  { eapply p_sem_mori; eauto. }
  split; red; ins.
  { unfolder in CD; destruct CD as [? CD].
    clear EQ.
    specialize (CD _ eq_refl); desf. 
    apply (wf_hbE WF) in CD0; unfolder in CD0; desf. }
  split; [|basic_solver].
  apply sub_execution_hbE in SUB; auto.
  rewrite SUB, <-seqA, codom_eqv1, CD; ins; basic_solver.
Qed.

Lemma p_sem_Add_avail_r G w r
  (AV : avail G r) 
  (WF : Wf (SetRF (Add G r) r w)) : 
  p_sem (SetRF (Add G r) r w).
Proof.
  assert (is_r r).
  { assert (rf (SetRF (Add G r) r w) w r) as RF.
    { ins; basic_solver. }
    apply (wf_rfD WF) in RF; unfolder in RF; desf. }
  apply avail_thread in AV; desf.
  cdes SEM; unfold p_sem; splits; eauto.
  { by apply SetRF_rf_complete. }
  assert (tid r = t); desf.
  { apply tsem_in_thrd in TS; apply TS; basic_solver. }
  ins.
  tertium_non_datur (t = tid r) as [|NEQ]; desf.
  { arewrite 
    ((acts G ∪₁ eq r) ∩₁ (fun x : Event => tid x = tid r) ≡₁
    (acts G ∩₁ (fun x : Event => tid x = tid r) ∪₁ eq r)).
    { basic_solver. }
    eapply tsem_val_sb_max in TS; eauto.
    { intros ? ACT. rewrite set_equivE. 
      apply functional_extensionality; ins; apply prop_eq.
      rewrite val_SetRF; eauto; unfolder in ACT; desf. }
    { rewrite <- sb_max_in_tid; eauto; by destruct r. }
    { intro W; apply n_is_r in W; basic_solver. }
    ins; exists (valw w); split; unfolder; intro.
    all: rewrite val_SetRF; desf. }
  arewrite 
    ((acts G ∪₁ eq r) ∩₁ (fun x : Event => tid x = t) ≡₁
    acts G ∩₁ (fun x : Event => tid x = t)).
  { basic_solver. }
  eapply tsem_val; [|apply TSEM].
  intros ? ACT. rewrite set_equivE. 
  apply functional_extensionality; ins; apply prop_eq.
  rewrite val_SetRF; eauto; unfolder in ACT; desf.
Qed.

Lemma p_sem_Add_avail_w G w w'
  (AV : avail G w') 
  (WF : Wf (SetCO (Add G w') w w')) : 
  p_sem (SetCO (Add G w') w w').
Proof.
  assert (is_w w').
  { assert (co (SetCO (Add G w') w w') w w') as CO.
    { ins; unfold into_rel. right; vauto. }
    apply (wf_coD WF) in CO; unfolder in CO; desf. }
  assert (~ is_init w').
  { by apply not_init_avail in AV. }
  apply avail_thread in AV; desf.
  cdes SEM; unfold p_sem; splits; eauto.
  { by apply SetCO_rf_complete. }
  assert (tid w' = t); desf.
  { apply tsem_in_thrd in TS; apply TS; basic_solver. }
  ins.
  tertium_non_datur (t = tid w') as [|NEQ]; desf.
  { arewrite 
    ((acts G ∪₁ eq w') ∩₁ (fun x : Event => tid x = tid w') ≡₁
    (acts G ∩₁ (fun x : Event => tid x = tid w') ∪₁ eq w')).
    { basic_solver. }
    eapply tsem_val_sb_max in TS; eauto.
    { intros ? ACT. rewrite set_equivE. 
      apply functional_extensionality; ins; apply prop_eq.
      unfolder in ACT; desf. }
    { rewrite <- sb_max_in_tid; eauto. }
    { intro W. apply n_is_r in W. unfold val; ins; desf. }
    intro R; apply n_is_w in R; basic_solver. }
  arewrite 
    ((acts G ∪₁ eq w') ∩₁ (fun x : Event => tid x = t) ≡₁
    acts G ∩₁ (fun x : Event => tid x = t)).
  { basic_solver. }
  eapply tsem_val; [|apply TSEM].
  intros ? ACT. ins.
Qed.

Lemma tsem_write_val G t (P : Event -> Prop) e v
  (W : is_w e)
  (TS : thread_sem t P (fun x => ifP x = e then eq v else val G x)) : 
  thread_sem t P (val G).
Proof.
  assert ((fun x : Event => ifP x = e then eq v else val G x) = val G) as V.
  { apply (tsem_write _ _ _ _ _ W) in TS.
    apply functional_extensionality; ins.
    rewrite <-set_equivE; desf; apply n_is_r in W.
    unfold val; desf. }
  by rewrite V in TS.
Qed.

Lemma tsem_read_val G t (P : Event -> Prop) e v v'
  (SBM : sb_max P e) (W : is_r e)
  (TS : thread_sem t P (fun x => ifP x = e then eq v else val G x)) : 
  thread_sem t P (fun x => ifP x = e then eq v' else val G x).
Proof.
  eapply tsem_recept with (v := v') in TS; eauto.
  assert ((fun x => ifP x = e then eq v' else val G x) = 
          fun x => ifP x = e then eq v' else (ifP x = e then eq v else val G x))
          as V.
  { apply functional_extensionality; ins.
    rewrite <-set_equivE; desf. }
  by rewrite V.
Qed.

Lemma avail_same_tid G e1 e2 
  (AV1 : avail G e1)
  (AV2 : avail G e2) 
  (TID : same_tid e1 e2) : e1 = e2.
Proof.
  assert (~ is_init e1).
  { eby eapply not_init_avail. }
  assert (~ is_init e2).
  { eby eapply not_init_avail. }
  apply avail_thread in AV1, AV2; desf.
  apply sb_max_in_tid in SBM0; eauto.
  apply sb_max_in_tid in SBM; eauto.
  rewrite TID in SBM0;
  rewrite <-(tsem_in_thrd _ _ _ _ TS _ (or_intror eq_refl)) in TS.
  rewrite <-(tsem_in_thrd _ _ _ _ TS0 _ (or_intror eq_refl)) in TS0.
  rewrite TID in TS0.
  tertium_non_datur (e1 = e2); desf.
  eapply tsem_val with 
    (val_t1 := fun x =>
    ifP x = e1 then eq v0 else (ifP x = e2 then eq v else val G x))
      in TS0.
  { eapply tsem_val with 
    (val_t1 := fun x =>
    ifP x = e1 then eq v0 else (ifP x = e2 then eq v else val G x))
      in TS.
    { eapply tsem_det; eauto. }
    intros ? [[]|]; desf. }
  intros ? [[]|]; desf.
Qed.

Lemma sub_execution_avail G G' 
  (SEM : p_sem G')
  (SUB : (G ⊆ G')%Ex): 
  avail G ⊆₁ avail G' ∪₁ acts G'.
Proof.
  intros e AV.
  tertium_non_datur (acts G' e) as [|NACT]; vauto; left.
  assert (~ is_init e) by by intro; destruct NACT; apply SEM.
  assert (thread_of G (tid e) = thread_of G' (tid e)) as TIDE.
  { assert (SUB' := SUB).
    apply sub_execution_thread with (t := tid e) in SUB.
    rewrite <-set_equivE.
    apply sub_threadE in SUB; desf.
    assert (TSEM' := TSEM).
    destruct TSEM as [SUBev _]; specialize (SUBev _ (or_intror eq_refl)).
    ins; unfolder in SUBev; desf.
    cdes SEM; specialize (TSEM (tid e)).
    apply (tsem_pref_clos _ _ _ TSEM') in TSEM.
    apply avail_thread in AV; desc.
    assert (TID := TS); apply tsem_in_thrd in TID.
    specialize (TID e (or_intror eq_refl)); ins; subst.
    apply sb_max_in_tid in SBM0; eauto.
    tertium_non_datur (e' = e); desf.
    apply tsem_val with (val_t1 := 
      fun x => ifP x = e then eq v else val G' x) in TSEM.
    { apply tsem_val_sb_max with 
      (val_t2 := fun x => ifP x = e then eq v else val G' x) in TS; eauto.
      { apply tsem_det with (e1 := e) in TSEM; subst; eauto.
        contradiction. }
      { intros ? [ACT]; desf; symmetry; apply sub_execution_val; eauto. }
      { intros W; apply n_is_r in W; unfold val; desf.
        apply tsem_write with (w := e) in TS; desf.
        by apply n_is_r. }
      exists v; desf. }
    intros ? [T|]; desf; unfolder in T; desf. }
  apply avail_thread in AV; desc.
  assert (TID := TS); apply tsem_in_thrd in TID.
  specialize (TID e (or_intror eq_refl)); ins; subst.
  apply avail_thread; splits; auto.
  { apply sb_max_in_tid; auto.
    rewrite <-TIDE; apply sb_max_in_tid in SBM; auto. }
  exists (tid e), v; ins; rewrite <-TIDE.
  eapply tsem_val; eauto; intros ? [T|]; desf; symmetry.
  apply sub_execution_val; eauto; unfolder in T; desf.
Qed.


(******************************************************************************)
(** **  Next event  *)
(******************************************************************************)

Definition next G e :=
  avail G e /\
  forall e', avail G e' -> e = e' \/ e <_next e'.


Lemma not_init_next G e (Next : next G e) : ~ is_init e.
Proof using.
  intros F; cdes Next; cdes Next0.
  apply p_sem_Wf, (sub_execution_wf GG') in Sem.
  by apply Sem in F.
Qed.

Lemma next_avail G e (N : next G e) : avail G e.
Proof using. by destruct N. Qed.

Hint Immediate next_avail : hahn.

Lemma next_uniq G e e'
  (N1 : next G e)
  (N2 : next G e') :
  e = e' .
Proof.
  cdes N1; cdes N2.
  specialize (N3 _ N4); specialize (N5 _ N0); desf.
  eby edestruct LR_irr; eapply LR_trans.
Qed.

Lemma next_Wf e G (N : next G e) : Wf G.
Proof.
  cdes N; cdes N0; cdes Sem; eby eapply sub_execution_wf.
Qed.

Variable K : nat.

Hypothesis p_sem_finite :
  forall G, p_sem G -> 
    exists l, 
      << OC : G_ord_corr G l >> /\
      << ND : NoDup l        >> /\
      << LK : length l < K   >>.

Lemma Restr_SetRF G r w 
  (NACT : ~ acts G r)
  (WF : Wf G): 
  G = (Restr (SetRF (Add G r) r w) (set_compl (eq r))).
Proof.
  rewrite <-eq_executionE.
  unfold eq_execution; ins.
  splits.
  { rewrite set_inter_union_l.
    arewrite (acts G ∩₁ set_compl (eq r) ≡₁ acts G).
    { split; unfolder; ins; desf; split; eauto.
      intro; desf. }
    basic_solver. }
  { split; unfolder; intros ?? RF; desf.
    apply WF in RF; unfolder in RF; desf; splits.
    all : try by intro; desf.
    left; exists y; splits; eauto; intro; desf. }
  split; unfolder; intros ?? CO; desf.
  apply WF in CO; unfolder in CO; desf; splits; eauto.
  all: by intro; desf.
Qed.

Lemma Restr_SetCO G w' w 
  (NACT : ~ acts G w')
  (WF : Wf G): 
  G = (Restr (SetCO (Add G w') w w') (set_compl (eq w'))).
Proof.
  rewrite <-eq_executionE.
  unfold eq_execution; ins.
  splits.
  { rewrite set_inter_union_l.
    arewrite (acts G ∩₁ set_compl (eq w') ≡₁ acts G).
    { split; unfolder; ins; desf; split; eauto; intro; desf. }
    basic_solver. }
  { split; unfolder; intros ?? CO; desf.
    apply WF in CO; unfolder in CO; desf; splits; eauto.
    all: by intro; desf. }
  split; unfolder; unfold into_rel; intros ?? CO; desf.
  apply WF in CO; unfolder in CO; desf; splits; vauto.
  all : by intro; desf.
Qed.

Fixpoint add_events G (add : list Event) := 
  match add with 
  | nil => G
  | e :: add => 
    let ie := (InitEvent (loc e)) in
    ifP is_r e then
      add_events (SetRF (Add G e) e ie) add
    else add_events (SetCO (Add G e) ie e) add
  end.

Lemma add_events_p_sem G add 
  (PSEM : p_sem G)
  (AV : Forall (avail G) add) 
  (ND : NoDup add) : 
  p_sem (add_events G add).
Proof.
  generalize dependent G.
  induction add; ins; apply nodup_cons in ND; apply Forall_cons in AV; desf.
  { assert (p_sem (SetRF (Add G a) a (InitEvent (loc a)))).
    { apply p_sem_Add_avail_r; ins.
      cdes AV; apply Wf_SetRF with (G' := G'); ins; eauto.
      { by apply GG'. }
      by apply (p_sem_Wf PSEM). }
    apply IHadd; eauto.
    apply ForallE; intros e IN.
    eapply ForallE in AV0; eauto.
    cdes AV; cdes PSEM.
    erewrite (Restr_SetRF _ _ NInG Wf_G) in AV0.
    apply avail_Restr in AV0; eauto.
    { unfolder in AV0; desf. }
    { by destruct a. }
    apply hb_maxE.
    split; [vauto|]; clear HB.
    split; [|basic_solver]; intros ? HB.
    destruct HB as [y [z [[] SBRF]]]; desf.
    eapply sub_execution_sbrf with (G := G) in SBRF; eauto.
    { cdes AV; basic_solver. }
    { unfolder in SBRF; desf.
      { unfold sb in SBRF; ins; unfolder in SBRF; desf.
        by apply ext_sb_irr in SBRF0. }
      ins; unfolder in SBRF; desf.
      { apply (wf_rfE (p_sem_Wf PSEM)) in SBRF; unfolder in SBRF; desf. }
      apply not_init_avail in AV; by destruct z. }
    apply sub_exec_SetRF; eauto.
    ins; eby eapply avail_sb_max. }
  assert (p_sem (SetCO (Add G a) (InitEvent (loc a)) a)).
  { apply p_sem_Add_avail_w; ins.
    cdes AV; apply Wf_SetCO with (G' := G'); ins; eauto.
    { by apply GG'. }
    { by apply n_is_r. }
    by apply (p_sem_Wf PSEM). }
  apply IHadd; eauto.
  apply ForallE; intros e IN.
  eapply ForallE in AV0; eauto.
  cdes AV; cdes PSEM.
  erewrite (Restr_SetCO _ _ NInG Wf_G) in AV0.
  apply avail_Restr in AV0; eauto.
  { unfolder in AV0; desf. }
  { by apply not_init_avail in AV. }
  apply hb_maxE.
  split; [vauto|]; clear HB.
  split; [|basic_solver]; intros ? HB.
  destruct HB as [y [z [[] SBRF]]]; desf.
  eapply sub_execution_sbrf with (G := G) in SBRF; eauto.
  { cdes AV; basic_solver. }
  { unfolder in SBRF; desf.
    { unfold sb in SBRF; ins; unfolder in SBRF; desf.
      by apply ext_sb_irr in SBRF0. }
    ins; unfolder in SBRF; desf.
    apply (wf_rfE (p_sem_Wf PSEM)) in SBRF; unfolder in SBRF; desf. }
  apply sub_exec_SetCO; eauto.
  ins; eby eapply avail_sb_max.
Qed.

Lemma add_sub_add_events G add :
  (fun x => In x add) ∪₁ acts G ⊆₁ acts (add_events G add).
Proof.
  generalize dependent G.
  induction add; [basic_solver|ins]; desf.
  all: intros e ACT; apply IHadd; ins.
  all: generalize ACT; basic_solver.
Qed.

Lemma avail_finite G
  (PSEM : p_sem G) : exists s, avail G ⊆₁ (fun x => In x s).
Proof.
  apply NNPP; intro F.
  apply not_finite with (k := K) in F; desf.
  set (G' := add_events G s).
  assert (p_sem G') as SEM.
  { apply add_events_p_sem; eauto.
    by apply ForallE. }
  apply p_sem_finite in SEM; desf.
  apply NoDup_incl_length with (l' := l) in NDs; [lia|].
  intros ? IN; apply OC; split.
  { apply add_sub_add_events; vauto. }
  by apply SUBs, not_init_avail in IN.
Qed.

Lemma next_avail_emp G s
  (FIN : acts G \₁ is_init ⊆₁ (fun x : Event => In x s)) :
  avail G ≡₁ ∅ <-> next G ≡₁ ∅ .
Proof. 
  split.
  { intro AV; split; [|basic_solver]; intros ? [A].
    by apply AV in A. }
  intros N; split; [|basic_solver]; intros e AV.
  assert (p_sem G) as PSEM by by (cdes AV; rewrite GG').
  assert (PSEM' := PSEM).
  apply avail_finite in PSEM; desf.
  assert (acyclic (restr_rel (avail G) LR)⁻¹) as AC.
  { intros ? F. apply transp_ct, restr_ct in F; destruct F as [F].
    by apply (ct_of_trans (LR_trans LR)), LR_irr in F. }
  destruct (last_exists s0 AC) with (a := e) as [m [R M]].
  { intros ? R; apply clos_rt_rtn1 in R.
    destruct R as [|?? R]; eauto.
    unfolder in R; desf; eauto. }
  assert (avail G m) as AVm.
  { apply clos_rt_rtn1 in R; destruct R as [|?? R]; eauto.
    unfolder in R; desf; eauto. }
  unfolder; apply N with (x := m); split; eauto.
  intros e' AV'; tertium_non_datur (m = e') as [|NEQ]; vauto.
  set (G' := add_events G (e' :: m :: nil)).
  edestruct LR_total with (G := G') (a := m) (b := e'); eauto.
  { apply add_events_p_sem; eauto.
    constructor; vauto; intro; ins; desf. }
  1,2: apply add_sub_add_events; basic_solver.
  specialize (M e'); destruct M; basic_solver.
Qed.

(******************************************************************************)
(** **  Maximal Event  *)
(******************************************************************************)


Definition me G e := 
  << HBM_e : hb_max G e >> /\
  << NM_e  : forall e', hb_max G e' -> e' = e \/ e' <_next e >>.

Lemma meE G e : 
  me G ≡₁ eq e <-> me G e.
Proof using.
  split; intros ME.
  { apply set_equiv_exp with (x := e) in ME; desf.
    by apply ME0. }
  unfold me in ME.
  desf; split; intros x; [intros [? M]|by intros<-].
  destruct (NM_e x) as [|N1]; eauto.
  destruct (M e) as [|N2]; eauto.
  edestruct (LR_irr); eby eapply LR_trans.
Qed.

Lemma me_Restr G e x
  (Wf_G : Wf G)
  (MEe : me G e)
  (MEx : me (Restr G (set_compl (eq e))) x) :
  hb_max G x \/
  (sb G ∪ rf G) x e /\ 
  << CDOM : (codom_rel (<|eq x|> ;; hb G) ≡₁ eq e) >>.
Proof using.
  tertium_non_datur (hb_max G x) as [HB|HB]; vauto.
  { cdes MEx; cdes HBM_e; ins; generalize ACT HB; basic_solver. }
  right; unfolder in HB; desf.
  assert (codom_rel (<|eq z|> ;; (sb G ∪ rf G)) ≡₁ eq e) as SBRF.
  { assert (codom_rel (⦗eq z⦘ ⨾ (sb G ∪ rf G)) ⊆₁ eq e) as S.
    { intros e' [x [y [E SBRF]]].
      unfolder in E; desf.
      tertium_non_datur (e = e') as [|NEQ]; desf.
      cdes MEx; cdes HBM_e.
      exfalso; eapply N_HB; unfolder; exists y,y; splits; eauto.
      apply ct_step; destruct SBRF as [SB|RF]; [left|right].
      { unfold sb in *; unfolder; unfolder in SB; basic_solver. }
      ins; unfolder; unfolder in ACT; basic_solver. }
    split; eauto.
    intros ??; desf. exists z, z; split; [basic_solver|].
    assert (exists e', (sb G ∪ rf G) z e') as SBRF; desf.
    { destruct (clos_trans_t1n _ _ _ _ HB1); vauto. }
    unfolder in S; specialize (S e'); rewrite S; eauto. }
  split.
  { destruct SBRF as [? SBRF].
    specialize (SBRF _ eq_refl). unfolder in SBRF. desf; vauto. }
  cdes MEe; cdes HBM_e.
  unfold hb in *; red.
  rewrite ct_step_ct, seq_union_r, codom_union.
  rewrite <- seqA, codom_seq, SBRF, N_HB; basic_solver. 
Qed.

Lemma ninit_me_ex G e s
  (PSEM : p_sem G)
  (WF : Wf G) (FIN : acts G \₁ is_init ⊆₁ (fun x : Event => In x s))
  (HBIRR : irreflexive (hb G))
  (ACT : acts G e) (NINI : ~ is_init e) : 
  exists m, 
    << MEm  : me G m      >> /\
    << INIm : ~ is_init m >>.
Proof.
  apply hb_max_ex with (s := s) in ACT; desf.
  set (LR' := restr_rel (hb_max G \₁ is_init) LR).
  assert (LR'^* ≡ LR'^?) as LRE.
  { split; [intros ?? L|by apply inclusion_r_rt].
    apply cr_of_ct in L; destruct L as [|L]; vauto.
    apply restr_ct in L; destruct L as [L]; right; split; eauto.
    by apply (ct_of_trans (LR_trans LR)). }
  assert (acyclic LR') as AC.
  { intros ? LRx. apply restr_ct in LRx; destruct LRx as [LRx].
    by apply (ct_of_trans (LR_trans LR)), LR_irr in LRx. }
  assert (~ is_init m).
  { destruct HBxm as [|HBxm]; desf.
    eby unfold not; eapply hb_init_r. }
  assert (forall c, LR'^* m c -> In c s) as DOM.
  { intros ? LR'mc; apply FIN; apply LRE in LR'mc.
    destruct LR'mc as [|LR'mc]; desf. 
    { cdes HBMm; split; eauto. }
    destruct LR'mc as [LRx HBM]; desf.
    unfolder in HBM0; desf; cdes HBM0; basic_solver. }
  destruct (last_exists s AC DOM) as [m' L]; desf.
  assert (~ is_init m') as INI'.
  { apply LRE in L; destruct L as [|L]; desf.
    destruct L as [L]; intro INI.
    eapply LR_irr, LR_trans; eauto; eapply sb_LR.
    by destruct m, m'. }
  assert (hb_max G m') as HBM'.
  { apply LRE in L; destruct L as [|[?[? []]]]; desf. }
  exists m'; splits; eauto.
  split; eauto.
  intros e' HBM; tertium_non_datur (is_init e') as [INI|INI].
  { right; apply sb_LR. by destruct e', m'. }
  tertium_non_datur (e' = m'); vauto; right.
  edestruct (LR_total LR); eauto; [by cdes HBM|by cdes HBM'|].
  specialize (L0 e'); destruct L0.
  split; eauto; basic_solver.
Qed.

Lemma next_sb_clos G G' r 
  (PS : p_sem G')
  (IRR : irreflexive (hb G'))
  (AV : next G r)
  (SUB : (G ⊆ G')%Ex) : 
  dom_rel (sb G' ⨾ ⦗acts G ∪₁ eq r⦘) ⊆₁ acts G ∪₁ eq r.
Proof.
  cdes SUB; cdes PS.
  rewrite id_union, seq_union_r, dom_union, DOMsb.
  apply set_subset_union_l; split; [basic_solver|].
  intros x SB; unfolder in SB; desf; left.
  tertium_non_datur (acts G x); eauto.
  assert (well_founded (sb G')) as wfs.
  { unfold sb; rewrite <-restr_relE; apply wf_restr, wf_ext_sb. }
  destruct (wf_impl_min_elt wfs) 
    with (set_compl (acts G) ∩₁ fun x => sb G' x y) as [a [ACT M]].
  { intros [F]; apply (F x); basic_solver. }
  unfolder in ACT; desc.
  assert (avail G a) as AVa.
  { apply avail_avail_sb.
    { by apply sub_execution_wf in SUB. }
    exists G'; splits; eauto.
    { unfold sb in ACT0; unfolder in ACT0; desf. }
    intros e' SB'.
    tertium_non_datur (acts G e'); eauto.
    destruct (M e'); eauto; split; eauto.
    eby eapply sb_trans. }
  apply AV in AVa; desf.
  { by apply sb_irr in ACT0. }
  destruct (LR_irr LR a); eapply LR_trans; eauto.
  apply sb_LR. generalize ACT0. unfold sb. basic_solver.
Qed.


Lemma SetRF_sub G G' w r
  (PS : p_sem G')
  (IRR : irreflexive (hb G'))
  (AV : next G r)
  (ACTw : acts G w)
  (SUB : (G ⊆ G')%Ex) 
  (RF : rf G' w r) : 
  (SetRF (Add G r) r w ⊆ G')%Ex.
Proof.
  cdes PS.
  apply Wf_G in RF; unfolder in RF; desc.
  cdes SUB.
  unfold sub_execution; splits; ins; try basic_solver.
  { assert (forall y, rf G' y r -> y = w) as RFF.
    { intros ? RF'. eby eapply wf_rff. }
    rewrite SUBrf; split; unfolder; ins; desf; eauto.
    tertium_non_datur (y = r); subst; eauto. }
  { rewrite SUBco, (wf_coD Wf_G), n_is_r.
    apply (wf_rfD Wf_G) in RF0; unfolder in RF0; desf.
    unfolder; splits; ins; desf; splits; vauto. }
  { by apply next_sb_clos. }
  rewrite dom_union, dom_singl_rel, dom_seq, DOMrf.
  basic_solver.
Qed.

Lemma SetCO_sub G G' w w'
  (PS : p_sem G')
  (IRR : irreflexive (hb G'))
  (AV : next G w')
  (ACTw : acts G w)
  (SUB : (G ⊆ G')%Ex)
  (COMw : forall x, ~ co G w x)
  (CO : co G' w w') : 
  (SetCO (Add G w') w w' ⊆ G')%Ex.
Proof.
  cdes PS.
  apply Wf_G in CO; unfolder in CO; desc.
  cdes SUB.
  unfold sub_execution; splits; ins; try basic_solver.
  { rewrite id_union, seq_union_r, <-SUBrf.
    arewrite (rf G' ⨾ ⦗eq w'⦘ ≡ ∅₂); [|basic_solver].
    split; [|basic_solver]; unfolder; intros ?? [RF]; desf.
    apply wf_coD in CO0; eauto; unfolder in CO0; desf.
    apply wf_rfD in RF; eauto; unfolder in RF; desf.
    by apply n_is_w in RF1. }
  { rewrite SUBco; unfolder; unfold into_rel;
    splits; intros ?? CO'; ins; desf; splits; vauto.
    { eby eapply (co_trans Wf_G). }
    { destruct (COMw y); apply SUBco; basic_solver. }
    { destruct (COMw y); apply SUBco; unfolder; splits; eauto.
      eby eapply co_trans. }
    { tertium_non_datur (x = w); subst; eauto.
      right; left; splits; eauto.
      edestruct (wf_co_total Wf_G) with (x := loc y); eauto.
      { unfolder; splits; eauto.
        { apply wf_coD in CO'0; unfolder in CO'0; desf. }
        eapply wf_col; eauto. }
      { unfolder; splits; eauto.
        { apply wf_coD in CO0; unfolder in CO0; desf. }
        eapply wf_col; eauto. }
      destruct (COMw x); apply SUBco; basic_solver. }
    edestruct (co_irr Wf_G); eauto. }
  { by apply next_sb_clos. }
  rewrite DOMrf; basic_solver.
Qed.

End Sem.


