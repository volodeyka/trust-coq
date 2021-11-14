From hahn Require Import Hahn.
Require Import Execution Execution_Aux Events Labels.
From Coq Require Import Lia.
Require Import Path Util Sem Alg Prev Terminate.

Set Implicit Arguments.

Section Optimality.

Variable thread_sem : tsemType.
Variable LR         : LRType thread_sem.
Variable cons       : consType.

Notation "e1 '<_next' e2" := (LR_of LR e1 e2) (at level 20).
Notation avail := (avail thread_sem).
Notation p_sem := (p_sem thread_sem).
Notation full  := (full thread_sem).
Notation next  := (next LR).
Notation me    := (me LR).
Notation TruSt_step := (TruSt_step LR cons).
Notation TruSt := (TruSt LR cons).
Notation TruSt_rel := (TruSt_rel LR cons).
Notation "G '~~>*' G'" := (Prev LR G G') (at level 20).
Notation "G '~(' e ')~(' rv ')~>' G'" := (Prev_step LR G e rv G') (at level 20).

Variable K : nat.

Hypothesis p_sem_finite :
  forall G, p_sem G -> 
    exists l, 
      << OC : G_ord_corr G l >> /\
      << ND : NoDup l        >> /\
      << LK : length l < K   >>.

Section PrevTruSt.

Context {G G' : execution}.
Context {e : Event} {sf l l' : list Event}.

Hypothesis TS  : TruSt G0 nil G l.

Lemma Wf_G : Wf G.
Proof using TS.
  eby eapply TruSt_Wf.
Qed.

Hint Resolve Wf_G : core.

Lemma me_avail_LR_G : hb_max G × avail G ⊆ LR.
Proof using TS.
  inv TS.
  { intros ?? [HBM_e AV]; apply not_init_avail in AV.
    cdes HBM_e; ins.
    by apply sb_LR; destruct x, y. }
  apply B23 in TS2; eauto; desc.
  set (m := match rv with RV a => a| NR => e0 end).
  assert (me G m) as ME by by apply TruSt_me; desf.
  intros e1 e2 [HBM AV].
  tertium_non_datur (m = e1); subst; [by apply avail_LR_l|].
  apply LR_trans with (y := m); [|by apply avail_LR_l].
  cdes ME; specialize (NM_e _ HBM); desf.
Qed.

Section Revisit.

Context {a : Event}.
Hypothesis PR : TruSt_step G l (RV a) e G' l'.

Lemma p_sem_G : p_sem G.
Proof using PR. 
  inv PR. 
  cdes Next; cdes Next0.
  eby eapply p_sem_mori.
Qed.

Notation Da := (set_compl (Del (Add G e) l a e ∪₁ eq a)).

Lemma Wf_Restr_Da : Wf (Restr G Da).
Proof using TS PR.
  apply Wf_Restr; eauto; intros ???.
  eby eapply not_init_Del.
Qed.

Hint Resolve p_sem_G Wf_Restr_Da : core.

Lemma Da_hb_clos : dom_rel (hb G ⨾ ⦗Da⦘) ⊆₁ Da.
Proof using TS PR.
  intros x xHB; unfolder in xHB; desc; subst.
  unfolder; intro. eapply Da_hb_cD with (x := x) (y := y); eauto.
  unfolder; splits; eauto.
Qed.


Lemma avail_Restr_Da : avail (Restr G Da) e.
Proof using TS PR.
  assert (HBDA := Da_hb_clos).
  assert (WF := Wf_Restr_Da).
  inv PR; cdes Next; cdes Next0.
  apply avail_avail_sb; eauto.
  exists G'; splits; eauto.
  { ins; unfolder; intro; desf. }
  { eapply sub_execution_trans; eauto.
    apply Restr_clos_sub; ins. 
    intros ?? D'; eapply not_init_Del in D'; eauto. }
  intros ? SB; assert (acts G e') by by apply HB; vauto.
  split; eauto.
  intros [[T NHB]|]; subst.
  { destruct NHB; apply ct_step; left.
    unfold sb; unfolder; unfold sb in SB; unfolder in SB; desf.
    splits; vauto. }
  destruct Nporf; apply ct_step; left.
  unfold sb; unfolder; unfold sb in SB; unfolder in SB; desf.
  splits; vauto.
Qed.

Lemma next_Restr_Da : next (Restr G Da) a.
Proof using TS PR.
  assert (N : next G e) by inv PR.
  split.
  { apply avail_avail_sb; eauto. 
    exists G; splits; eauto.
    { inv PR. }
    { ins; unfolder; intro F; desf; clarify_not. }
    { apply Restr_clos_sub; eauto.
      { intros ?? Dx; eby eapply not_init_Del in Dx. }
      by apply Da_hb_clos. }
    { intros e' SB.
      tertium_non_datur (is_init e').
      { apply wf_initE; eauto. }
      split.
      { unfold sb in SB; unfolder in SB; desf. }
      unfolder; intros [[T]|]; desf.
      { assert ((<|set_compl is_init|> ;; sb G) e' a) as ISB.
        { basic_solver. }
        eapply TruSt_sb_l in ISB; eauto.
        assert (ND := TruSt_NoDup TS).
        eapply total_order_from_list_irreflexive; eauto.
        eby eapply total_order_from_list_trans. }
      by apply sb_irr in SB. }
    apply TruSt_correct, cons_hb_irr in TS; eauto. }
  intros e' AV; assert (AV' := AV).
  apply sub_execution_avail with (G' := G) in AV; eauto.
  { destruct AV as [AV|AV].
    { assert (a <_next e).
      { edestruct LR_tot with (G := G) (e1 := a); eauto.
        { inv PR; vauto. }
        { desf; inv PR; by apply n_is_r in Write. }
        desf. assert (TS' := PR).
        apply rf_l_e_a in TS'; eauto.
        apply B23 in PR; cdes PR; eauto; exfalso.
        eapply rf_l_next; vauto. }
      apply N in AV; desf; vauto; right.
      eby eapply LR_trans. }
    assert (~ Da e') as Dae'; clarify_not.
    { cdes AV'; clarify_not. }
    unfold Del in Dae'; unfolder in Dae'; desf; vauto.
    right.
    apply B23 in PR; eauto; cdes PR.
    apply t_rv; unfolder; splits; vauto. }
  apply Restr_clos_sub; eauto.
  { intros ???; eby eapply not_init_Del. }
  apply Da_hb_clos.
Qed.

Lemma Completions_Restr_Da G1 
  (COMPL : (Completion LR)^* (Restr G Da) G1) 
  (NEMP : exists x, next G1 x)
  (N : next G1 × eq e ⊆ LR^?): 
  (G1 ⊆ G)%Ex.
Proof using TS PR.
  apply clos_rt_rtn1 in COMPL.
  induction COMPL as [|G1 G2 C].
  { apply Restr_clos_sub; eauto.
    { intros ???; eby eapply not_init_Del. }
    apply Da_hb_clos. }
  apply clos_rtn1_rt in COMPL.
  assert (Wf G1) by eby eapply Completions_Wf.
  assert (NE : next G1 × eq e ⊆ LR^?).
  { intros e1 ? []; desf.
    eapply LRcr_trans with x; [|apply N; basic_solver].
    eapply next_Completion in C; eauto. }
  assert (exists x : Event, next G1 x) as NEX.
  { apply Completion_hb_max in C; desf; vauto. }
  specialize (IHCOMPL NEX NE).
  assert (cons G) as CON by eby eapply TruSt_correct.
  apply cons_hb_irr in CON.
  assert (next G1 ⊆₁ acts G) as NG.
  { intros x N'; cdes N'.
    eapply sub_execution_avail in N'0; eauto.
    unfolder in N'0; desf.
    assert (Next : next G e) by inv PR.
    apply Next in N'0.
    specialize (NE _ _ (conj N' eq_refl)).
    tertium_non_datur (e = x); subst.
    { eapply next_Completion in C; eauto.
      tertium_non_datur (x = x1); subst.
      { by apply LR_irr in C. }
      edestruct (LR_irr LR x); eapply LR_trans; eauto.
      specialize (N _ _ (conj NEMP eq_refl)); destruct N; desf. }
    unfolder in NE; desf.
    eby edestruct LR_irr; eapply LR_trans. }
  assert (next G1 ⊆₁ Del (Add G e) l a e ∪₁ eq a) as NDa.
  { intros x N'; assert (N'' := N'); apply NG in N''.
    assert (~ acts (Restr G Da) x).
    { intros ACT; apply sub_Completions in COMPL; eauto.
      by apply COMPL in ACT; cdes N'; cdes N'0. }
    clarify_not. }
  assert (RFC : rf_complete G).
  { by apply TruSt_correct, cons_complete in TS. }
  assert (forall a0, next G1 a0 ->
    eq a ∪₁ acts G1 ≡₁ 
    fun x => 
      a = x \/ acts G x /\ 
      (total_order_from_list l a0 x \/
      hb (Add G e) x e)) as G1E.
  { intros ? Na0.
    assert (In a l) by by eapply a_in_l; eauto.
    assert (In a0 l) by by eapply NDa, Da_in_l in Na0; eauto.
    assert ((total_order_from_list l)^? a0 a) as ala0.
    { tertium_non_datur (a0 = a); vauto; right.
      assert (WF := conj Wf_Restr_Da next_Restr_Da); desc.
      apply B23 in PR; eauto; cdes PR; apply t_rv.
      unfolder; splits; eauto; [|by apply NDa].
      eapply next_Completions with (G := Restr G Da) (G' := G1); eauto. }
    split.
    { intros x [|ACT]; vauto.
      assert (acts G x) by by apply IHCOMPL.
      tertium_non_datur (a = x); vauto.
      right; split; eauto.
      tertium_non_datur (is_init x).
      { right; apply ct_step; left; unfold sb; unfolder; splits; vauto.
        assert (next G e) as Ne by by inv PR.
        apply not_init_next in Ne; by destruct e, x. }
      assert (In x l).
      { eapply TruSt_G_corr_ord; vauto. }
      tertium_non_datur (Da x) as [Dax|NDax].
      { unfolder in Dax; clarify_not; vauto.
        destruct total_order_from_list_total with (l := l) (a := a) (b := x); vauto.
        left; destruct ala0; desf.
        eapply total_order_from_list_trans; eauto.
        eby eapply TruSt_NoDup. }
      assert (WF := Wf_Restr_Da).
      left; apply B23 in PR; eauto; cdes PR.
      apply t_rv; unfolder; splits; vauto.
      { eapply next_max_Completion with (G' := G1) (G := (Restr G Da)); eauto.
        split; eauto; intros []; eauto. }
      by apply NDa. }
    intros x [|[ACT THB]]; vauto.
    tertium_non_datur (a = x); vauto.
    tertium_non_datur (Da x) as [Dax|NDax]; right.
    { apply sub_Completions in COMPL; eauto.
      apply COMPL; vauto. }
    unfolder in NDax; desf; [|by destruct NDax].
    eapply in_Comletions with (G := Restr G Da) (G'' := G); eauto.
    apply B23 in PR; eauto; cdes PR.
    apply t_rv; unfolder; splits; eauto.
    by apply NDa. }
  inv C; cdes MW; assert (InDa := Next).
  { eapply SetRF_sub; eauto.
    eapply NDa, Max_Da in InDa; eauto; 
    unfold IsMaximal in InDa; des_if; ins.
    specialize (RFC _ (conj (NG _ Next) R)).
    unfolder in RFC; desc; specialize (InDa _ RFC); desc.
    tertium_non_datur (w = x1); subst; eauto.
    destruct (classic (max_elt (co G1) x1)) as [M|NM].
    { edestruct wf_co_total with (x := loc a0) as [CO|CO]; eauto.
      { unfolder; splits; eauto. }
      { apply wf_rfD in RFC; eauto; unfolder in RFC; desc.
        apply wf_rfE in RFC0; eauto; unfolder in RFC0; desc.
        apply wf_rfl in RFC2; unfolder; splits; eauto.
        unfold Del in NDa.
        assert (a = x1 \/ acts G1 x1) as [|]; vauto.
        { eapply G1E; eauto; right. 
          splits; eauto.
          destruct InDa1; desf; by apply n_is_w in RFC1. }
        inv PR; by apply n_is_w in Read. }
      { by destruct MCO with (b := x1). }
      by destruct M with (b := w). }
      clarify_not. apply IHCOMPL in NM; unfolder in NM; desc.
      destruct InDa0; exists n; splits; vauto.
      { by left; eapply IHCOMPL. }
      assert (NM2 : a = n \/ acts G1 n); vauto.
      eapply G1E in NM2; eauto.
      destruct NM2; desc; vauto.
      apply wf_coD in NM0; unfolder in NM0; desc; eauto.
      apply n_is_r in NM3; inv PR. }
  eapply SetCO_sub; eauto.
  eapply NDa, Max_Da in InDa; eauto.
  apply n_is_r in W.
  unfold IsMaximal in InDa; des_if; ins.
  specialize (InDa _ eq_refl); desc.
  assert (a0 <> w) by by intro; subst; cdes Next; cdes Next0.
  edestruct wf_co_total with (G := G) (x := loc a0) as [CO|CO]; eauto.
  { unfolder; splits; eauto. by apply n_is_r. }
  { unfolder; splits; eauto. by apply IHCOMPL. }
  destruct InDa0; exists w; splits; eauto.
  { by left; apply IHCOMPL. }
  assert (A : a = w \/ acts G1 w); vauto.
  eapply G1E in A; destruct A; desc; vauto.
  apply wf_coD in CO; unfolder in CO; desc; eauto.
  apply n_is_r in CO1; inv PR.
Qed.

Lemma e_LRmax_in_Dela : 
  <|eq e|> ;; LR ;; <|(Del (Add G e) l a e ∪₁ eq a)|> ≡ ∅₂.
Proof using TS PR.
  inv TS; [|clear TS].
  { apply TruSt_first_step in PR; cdes PR; desf. }
  split; [|basic_solver]; intros e1 y eLRD.
  unfolder in eLRD; desc; subst.
  assert (N : avail G e1) by by inv PR; cdes Next.
  destruct rv as [a'|].
  { assert (a' <_next y) as a'LRy.
    { eapply LR_trans; eauto.
      apply B23 in TS2; eauto; desc; apply avail_LR_l.
      split; eauto; by apply TruSt_me. }
    destruct total_order_from_list_total with (l := l) (a := y) (b := a')
      as [T|T].
    { eapply Da_in_l; vauto. }
    { eapply a_in_l'; vauto. }
    { intro; subst; by apply LR_irr in a'LRy. }
    { eapply Da_hb_rf_l with (y := a') (x := y) (G := G); vauto.
      assert (acts G y) as Gy.
      { eapply Da_in_l in eLRD1; vauto.
        eapply TruSt_G_corr_ord in eLRD1; vauto.
        by destruct eLRD1. }
      apply seqA; exists e0; split.
      {  exists y; splits; [basic_solver|].
        tertium_non_datur (y = e0); subst; vauto; right.
        eapply hb_Add_in_G'; vauto; unfolder; splits; eauto.
        { eapply acts_G' in Gy; vauto; unfolder in Gy.
          destruct Gy as [Gy|Gy]; subst; [|desf]; desc.
          clear eLRD1; clarify_not.
          destruct Gy0. eapply l'_order in T; vauto.
          unfolder in T; desf. }
        { eapply G'_e; vauto. }
        inv TS2; intro; subst; by apply n_is_w in Read. }
      eapply rf_l_e_a; vauto. }
    assert (TS := TS2); apply B23 in TS2; vauto; cdes PR.
    rewrite <-seqA in LR_l; destruct (LR_l y a') as [? []]; vauto.
    eapply Da_hb_rf_l; vauto. }
  assert (TS := TS2).
  apply B23 in TS; cdes TS; vauto; clear TS.
  rewrite <-seqA in LR_l; destruct (LR_l y e0) as [? HB].
  { assert (e0 <_next y) as e0LRy.
    { tertium_non_datur (e1 = e0); subst; eauto.
      eapply LR_trans; eauto.
      tertium_non_datur (ext_sb e0 e1); [by apply sb_LR|].
      assert (N' : next G1 e0) by inv TS2.
      apply avail_nr in TS2; eauto.
      apply TS2 in N; unfolder in N.
      enough (AV : avail G1 e1) by (by apply N' in AV; desf); desf. }
    split; eauto.
    assert (y <> e0) by by intro; subst; apply LR_irr in e0LRy.
    eapply Da_in_l in eLRD1; vauto.
    inv TS2; apply total_order_from_list_cons; destruct eLRD1; vauto. } 
  eapply Da_hb_rf_l; vauto; desc; exists y. basic_solver.
Qed.


Lemma MaxComletion_Restr_Da Gm
  (COMPL : MaxCompletion LR (Restr G Da) e Gm) : 
  Gm = G.
Proof using TS PR.
  assert (WF := Wf_Restr_Da).
  rewrite <-eq_executionE; cdes COMPL.
  assert ((Gm ⊆ G)%Ex) as SUB.
  { apply Completions_Restr_Da; eauto.
    intros ?? [N]; desf; apply (next_uniq N) in MAX; vauto. }
  apply sub_execution_eq_acts; eauto.
  tertium_non_datur (acts Gm ≡₁ acts G) as [|F]; ins.
  { by apply SUB in F. }
  assert (well_founded (sb G)) as wfs.
  { unfold sb; rewrite <-restr_relE; apply wf_restr, wf_ext_sb. }
  destruct (wf_impl_min_elt wfs) with (B := acts G \₁ acts Gm) 
    as [e' [[ACTe' NACTe'] Min]].
  { unfolder; intros []. eauto. }
  assert (avail Gm e') as AV.
  { apply next_Wf in MAX; apply avail_avail_sb; eauto.
    exists G; splits; eauto.
    { intros x SB.
      tertium_non_datur (acts Gm x) as [|NACT]; eauto.
      destruct (Min x); eauto.
      unfold sb in SB; unfolder in SB; desf. }
    apply TruSt_correct, cons_hb_irr in TS; eauto. }
  apply MAX in AV; desf.
  { by inv PR; cdes Next; cdes Next0. }
  assert ((Del (Add G e) l a e ∪₁ eq a) e').
  { tertium_non_datur (Da e'); eauto.
    destruct NACTe'; apply sub_Completions in COMPL1; auto.
    apply COMPL1; vauto. }
  exfalso; eapply e_LRmax_in_Dela. unfolder; vauto.
  Unshelve. eauto.
Qed.

Lemma MaxCompletionG : 
  MaxCompletion LR (Restr G Da) e G.
Proof using p_sem_finite TS PR.
  destruct (MaxCompletion_ex LR p_sem_finite avail_Restr_Da l) as [Gm MC].
  { generalize (TruSt_G_corr_ord TS); firstorder. }
  by rewrite <-(MaxComletion_Restr_Da MC) at 3.
Qed.

End Revisit.

Context {rv : Revisit}.
Hypothesis PR : TruSt_step G l rv e G' l'.

Lemma PrevTruSt : G ~(e)~(rv)~> G'.
Proof using p_sem_finite TS PR.
  assert (Wf G') by by eapply TruSt_Wf; vauto.
  destruct rv as [a|].
  { assert (MC := MaxCompletionG PR); inv PR.
    apply Prev_rv; vauto.
    { apply B23 in PR; cdes PR; eauto; by apply TruSt_me. }
    { edestruct LR_tot with (e1 := a) (e2 := e); eauto; subst.
      { by apply n_is_w in Write. }
      desf; assert (TSr := PR); apply rf_l_e_a in TSr; eauto.
      apply B23 in PR; eauto; cdes PR; exfalso.
      eby eapply rf_l_next; split. }
    { eby eapply codom_hbGe. }
    assert (~ D a).
    { eapply r_not_in_Del; [eapply TruSt_NoDup|eapply e_not_in_l]; vauto. }
    rewrite RestrRestrE, acts_revisitE; ins.
    assert (Wf (Restr G (set_compl (D ∪₁ eq a)))).
    { apply Wf_Restr; ins; intros ? INI Dx.
      eby eapply not_init_Del in Dx. }
    rewrite <-Restr_SetRF.
    { rewrite <-Restr_SetCO; eauto.
      by ins; unfolder; intro; desc; cdes Next; cdes Next0. }
    { ins; unfolder; intro; desf; clarify_not.
      by cdes Next; cdes Next0. }
    cdes Next; cdes Next0; cdes Sem.
    eapply Wf_SetCO with (G' := G'); ins; eauto.
    { unfolder; intro; desf. }
    { cdes GG'. rewrite SUBev. basic_solver. }
    unfolder in InG0; desc; unfolder; splits; eauto.
    intro; desf; by apply n_is_w in Read. }
  inv PR.
  { cdes Next; apply not_init_next in Next.
    cdes Next0.
    erewrite Restr_SetRF with (G := G) (r := e) (w := w) at 1; eauto.
    apply Prev_nr_not_max with (e := w); vauto.
    { by apply B23 in PR; auto; cdes PR; apply TruSt_me. }
    destruct (classic (hb_max G w)) as [ME|NME].
    { by left; apply me_avail_LR_G. }
    clarify_not. right; intro F.
    cdes Next0; apply NInG; unfolder in NME; desc; subst.
    apply wf_hbE in NME1; eauto; unfolder in NME1; desc.
    assert (e = n); subst; auto.
    eapply F; unfolder; exists z,z; splits; eauto.
    eapply sub_execution_hbE with (G' := SetRF (Add G e) e z) in NME2; eauto.
    { unfolder in NME2; desf. }
    apply sub_exec_SetRF; auto; ins; eby eapply avail_sb_max. }
  { cdes Next; apply not_init_next in Next; cdes Next0.
    erewrite Restr_SetCO with (G := G) (w' := e) (w := wp) at 1; eauto.
    apply Prev_nr_w; eauto.
    apply B23 in PR; cdes PR; eauto; by apply TruSt_me. }
Qed.

End PrevTruSt.

Lemma TruSt_Optimal_exec (Gs1 Gs2 : list state) st1 st2
  (P1 : path TruSt_rel⁻¹ st1 Gs1)
  (P2 : path TruSt_rel⁻¹ st2 Gs2)
  (L1 : last Gs1 st1 = st0)
  (L2 : last Gs2 st2 = st0) 
  (EQ : G_of st1 = G_of st2) :
  map G_of Gs1 = map G_of Gs2.
Proof using p_sem_finite.
  generalize dependent st1.
  generalize dependent st2.
  generalize dependent Gs2.
  induction Gs1; ins; desf.
  { eapply pathE in L2; eauto.
    apply (proj1 (pow_transp _ _)) in L2.
    assert (st2 = st0); subst.
    { apply pow_rt, TruSt_rel_str in L2.
      unfold st0 in L2, EQ; ins; destruct st2 as [G l]; ins; desf.
      apply f_equal; apply TruSt_G_corr_ord in L2.
      apply incl_l_nil; intros ? IN.
      by apply L2 in IN; ins; destruct IN. }
    eapply TruSt0 in L2; eauto.
    by destruct Gs2. }
  destruct Gs2 as [|st Gs2]; ins; desf.
  { rewrite last_cons in L1;
    eapply pathE in P0; eauto. 
    apply (proj1 (pow_transp _ _)) in P0.
    assert (st1 = st0); subst.
    { apply pow_rt, TruSt_rel_str in P0.
      destruct a as [G l]; destruct st1 as [G' l']; ins.
      unfolder in P1; unfold TruSt_rel in P1; ins; desf.
      apply f_equal, incl_l_nil; intros ? IN.
      assert (TruSt G0 nil G0 l') as TS; vauto.
      apply TruSt_G_corr_ord in TS; apply TS in IN; ins.
      by destruct IN. }
    assert (TruSt_rel^^(S (length Gs1)) st0 st0) as F; vauto.
    eapply TruSt0 in F; vauto. }
  rewrite last_cons in L2, L1.
  assert (G_of a = G_of st); eauto.
  { eapply pathE in P3, P0; eauto. 
    apply pow_transp, pow_rt, TruSt_rel_str in P3, P0; ins.
    destruct a as [G1 l1]; ins.
    destruct st as [G2 l2]; ins.
    destruct st2 as [G l]; ins.
    destruct st1 as [? l']; ins; desf.
    unfolder in P2; unfolder in P1.
    cdes P2; cdes P1; ins.
    assert (Wf G) by by eapply TruSt_Wf; vauto.
    eapply PrevTruSt in P4, P5; eauto.
    eapply Prev_det with (G2 := G2) in P5; desf; eauto. }
  apply f_equal2; eauto.
Qed.

Lemma TruSt_step_Optimapl st st1 st2
  (TS0 : TruSt_rel^* st0 st)
  (TS1 : TruSt_rel st st1)
  (TS2 : TruSt_rel st st2) 
  (EQG : G_of st1 = G_of st2) : 
  st1 = st2.
Proof using p_sem_finite.
  destruct st as [G l].
  destruct st1 as [G1 l1].
  destruct st2 as [G2 l2].
  apply TruSt_rel_str in TS0; ins.
  cdes TS1; cdes TS2; ins; desf.
  apply f_equal; clear TS1 TS2.
  assert (TS1 := TS3); assert (TS2 := TS4).
  apply PrevTruSt in TS4, TS3; eauto.
  assert (WF : Wf G2) by by eapply TruSt_Wf; vauto.
  apply (Prev_det WF TS3) in TS4; desf.
  inv TS1; inv TS2.
Qed.

(** TruSt is optimal. There are never two different paths of the algorithm
that lead to the same execution graph. *)

Theorem TruSt_Optimal (Gs1 Gs2 : list state) st1 st2
  (P1 : Path TruSt_rel st0 Gs1 st1)
  (P2 : Path TruSt_rel st0 Gs2 st2)
  (L1 : eq_execution (G_of st1) (G_of st2)) :
  Gs1 = Gs2 /\ st1 = st2.
Proof using p_sem_finite.
  apply Path_transp in P1, P2.
  rewrite <-rev_eq.
  remember (rev Gs1) as s1; clear Heqs1.
  remember (rev Gs2) as s2; clear Heqs2.
  rewrite eq_executionE in L1.
  assert (EXEQ := P2).
  apply (TruSt_Optimal_exec _ _ _ _ P1) in EXEQ; eauto.
  all: try by rewrite last_last.
  rewrite ?map_app in EXEQ; apply app_inj_tail in EXEQ; desc.
  unfold Path in P1, P2.
  generalize dependent s2.
  generalize dependent st1.
  generalize dependent st2.
  induction s1; ins.
  { assert (nil = s2) by by destruct s2.
    desf; split; ins; desc.
    eapply TruSt_step_Optimapl; vauto. }
  desf; destruct s2; ins.
  injection EXEQ as EG Es; desc.
  eapply IHs1 in Es; eauto; desf; splits; eauto.
  eapply TruSt_step_Optimapl; eauto.
  eapply pathE in P3; [|eby rewrite last_last].
  by apply pow_rt, transp_rt in P3.
Qed.

End Optimality.
