From hahn Require Import Hahn.
Require Import Execution Execution_Aux Events Labels.
From Coq Require Import Lia.
Require Import Util Sem Alg Prev.

Set Implicit Arguments.

Section Completeness.

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
Notation "G '~~>*' G'" := (Prev LR G G') (at level 20).
Notation "G '~(' e ')~(' rv ')~>' G'" := (Prev_step LR G e rv G') (at level 20).

Variable K : nat.

Hypothesis p_sem_finite :
  forall G, p_sem G -> 
    exists l, 
      << OC : G_ord_corr G l >> /\
      << ND : NoDup l        >> /\
      << LK : length l < K   >>.

Section TruStPrev.

Context {Gf G G' : execution}.
Context {e : Event} {sf l : list Event}.

Hypothesis Gf_full  : full Gf.
Hypothesis Gf_cons  : cons Gf.
Hypothesis Gf_Wf    : Wf Gf.
Hypothesis Gf_p_sem : p_sem Gf.
Hypothesis Gf_finite : (acts Gf \₁ is_init) ⊆₁ fun x => In x sf.

Hypothesis PRf : G' ~~>* Gf.
Hypothesis TS  : TruSt G0 nil G l.

Section Revisit.

Context {a : Event}.
Hypothesis PR : G ~(e)~(RV a)~> G'.

Lemma Wf_G' : Wf G'.
Proof using Gf_Wf PRf.
  eby eapply Prev_Wf.
Qed.

Lemma Wf_G : Wf G.
Proof using Gf_Wf PRf PR.
  eapply Prev_Wf; vauto.
Qed.

Lemma set_finit_G' : set_finite (acts G' \₁ is_init).
Proof using Gf_finite PRf.
  eapply Prev_finite in PRf; eauto.
Qed.

Lemma cons_G' : cons G'.
Proof using Gf_cons Gf_Wf Gf_p_sem PRf.
  eby eapply Prev_cons.
Qed.

Hint Resolve Wf_G Wf_G' set_finit_G' cons_G' : core.

Lemma DelE : 
  Del (Add G e) l a e = acts G \₁ acts G'.
Proof using TS PRf PR LR Gf_p_sem Gf_full Gf_finite Gf_cons Gf_Wf.
  rewrite <-set_equivE; assert (Wf__G := Wf_G).
  subst.
  assert (Wf (Restr G' (set_compl (eq a ∪₁ eq e)))).
  { eapply sub_execution_wf; [|apply Wf_G'].
    eapply sub_execution_RV; [apply Gf_Wf| |]; eauto. }
  inv TS; ins.
  { unfold Del; split; unfolder; intros ? F; desf.
    { by apply total_order_from_list_in2 in F. }
    by apply Wf_G' in F. }
  symmetry; desf; inv PR; split.
  { intros y [ACT' ACT]; split.
    assert (y <> a).
    { by intro; desf; cdes ME; cdes HBM_e. }
    { edestruct total_order_from_list_total with
        (a := y) (b := a) (l := l) as [|T]; eauto.
      1,2: apply (TruSt_G_corr_ord TS); split; eauto.
      { intro; destruct ACT; by apply Wf_G'. }
      { eby eapply In_RV_a. }
      { by destruct a. }
      apply B23 in TS2; eauto; desc.
      rewrite <-seqA in LR_l.
      assert (a <_next y).
      { edestruct me_Add_evs; eauto; desf. }
      destruct (LR_l y a) as [z [[w [HB [RF']]] [L]]].
      { split; eauto. }
      destruct LR_irr with (x := z) (l := LR).
      eapply LR_trans; eauto.
      apply (rewrite_trans_seq_cr_r (LR_trans LR)); exists y; split; eauto.
      eapply RV_hb_LR with (Gf := Gf) (G := G'); try left; eauto.
      exists y; split; [basic_solver|].
      apply (rewrite_trans_seq_cr_l (@hb_trans G)).
      exists w; split; vauto. }
  apply (wf_rfD Wf_G') in RF; unfolder in RF; desf.
  assert (Wf G) by (eapply TruSt_Wf; vauto).
  assert (forall e' : Event, acts G e' -> ~ ext_sb e e').
  { ins. eapply avail_sb_max; eauto.
    eapply next_Prev in PR; eauto; cdes PR; eauto. }
  assert (Wf (Restr G' (set_compl (eq a ∪₁ eq e)))) as Wf_R; eauto.
  intro HB; apply hb_add_max in HB; eauto; desf; cdes MC.
  destruct (classic (acts (Restr G' (set_compl (eq a ∪₁ eq e))) e2)) as [A|A].
  { destruct ACT.
    unfolder in HB; desf; [ins; generalize A; basic_solver|].
    apply sub_Completions in COMPL; eauto.
    eapply sub_execution_hb in A; eauto.
    ins; generalize A; basic_solver. }
  apply ext_sb_tid_init' in SB; unfolder in SB; desf.
  { set (P := fun x =>  ~ acts x e2).
    assert (~ is_init e) by eby eapply not_init_next.
    apply MaxCompletion_Compl in MC; [|eapply avail_Restr_e_RV; eauto].
    eapply (r_str_cont P A) in MC; ins; desf.
    clear A; unfold P in *; clarify_not; cdes MC0.
    assert (next z e2) as N by (eapply Completion_nextE; basic_solver).
    assert (avail z e) as N'.
    { by apply avail_Compl in MC; [|eapply avail_Restr_e_RV; eauto]. }
    cdes N.
    eapply avail_same_tid in SB0; eauto; desf. }
  by apply Wf_R in SB. }
  intros x [T NHB]; split.
  { eapply total_order_from_list_in1, TruSt_G_corr_ord in T; vauto.
    unfolder in T ; desf. }
  intros ACT.
  assert (forall z, hb G a z -> a <_next z) as aHB.
  { intros ? HB.
    eapply RV_hb_LR in PR; eauto.
    { specialize (PR a z); destruct PR; desf; [basic_solver|].
      eapply (cons_hb_irr cons) in HB; ins; eapply Prev_cons; vauto. }
    eby eapply In_RV_a. }
  assert (acts G x) as ACTx.
  { eapply total_order_from_list_in1, TruSt_G_corr_ord in T; eauto.
    unfolder in T; desf. }
  assert (TS2' := TS2).
  apply B23 in TS2; eauto; desc.
  destruct LR_total with (a := x) (b := a) (G := G) (l := LR) as [xLRa|aLRx].
  { eapply Prev_p_sem; vauto. }
  { eauto. }
  { eapply total_order_from_list_in2, TruSt_G_corr_ord in T; eauto.
    unfolder in T; desf. }
  { intro; subst; apply total_order_from_list_irreflexive in T; eauto.
    eby eapply TruSt_NoDup. }
  { rewrite <- seqA in LR_l.
    specialize (LR_l _ _ (conj xLRa T)).
    destruct LR_l as [z [[y [? []]] [zLRx]]].
    eapply LR_irr, LR_trans; eauto; eapply LR_trans with (y := z); eauto.
    apply aHB, (rewrite_trans_seq_cr_l (@hb_trans _)); do 2 esplit; vauto. }
  assert (set_finite (acts G' \₁ is_init)) as [s].
  { eapply Prev_finite; vauto. }
  assert (irreflexive (hb G')). 
  { eapply (cons_hb_irr cons), Prev_cons; vauto. }
  eapply hb_max_ex with (s := s) in ACT; eauto.
  destruct ACT as [y]; desc.
  assert (LR^? y a) as yLRa by by apply ME in HBMm.
  assert (x <> y).
  { intro; destruct yLRa; subst.
    all: eby eapply LR_irr, LR_trans. }
  destruct HBxm as [|HBxa]; eauto.
  assert (exists y', 
    << y'NEe : y' <> e     >> /\ 
    << xHB'y' : hb G' x y'  >> /\
    << y'LRa : y' <_next a >>).
  { tertium_non_datur (y <> a); subst.
    { destruct yLRa as [|yLRa]; subst; [contradiction|].
      exists y; splits; eauto; intro; subst.
      eapply HBMm with (x := a); exists e, e; splits; vauto. }
    apply ct_end in HBxa; destruct HBxa as [z [HB SBRF]].
    apply cr_of_ct in HB.
    tertium_non_datur (z = e); subst.
    { destruct HB as [|HB]; subst.
      { by cdes MC; cdes MAX; cdes MAX0. }
      destruct NHB.
      apply ct_end in HB; destruct HB as [x' [HB [SB|RF']]].
      { apply cr_of_ct in HB; destruct HB as [|HB]; subst.
        { unfold sb in SB; unfolder in SB; desc.
          apply ct_step; left; unfold sb; unfolder; splits; vauto. }
        assert (x' <> a).
        { intro; subst.
          apply (cons_hb_irr cons cons_G') with (x := e). 
          apply hb_trans with (y := a); vauto. }
        assert (x' <> e).
        { intro; subst; by apply sb_irr in SB. }
        assert (acts G' x').
        { unfold sb in SB; unfolder in SB; desf. }
        cdes MC; apply sub_Completions in COMPL; eauto.
        apply hb_trans with (y := x').
        { apply Add_hb.
          assert (hb (Restr G' (set_compl (eq a ∪₁ eq e))) x x') as HBR.
          { eapply sub_execution_hbE with (G' := G').
            { apply Wf_G'. }
            { eapply sub_execution_RV; [apply Gf_Wf| |]; eauto. }
            ins; unfolder; splits; eauto; intro; desf. }
          eapply sub_execution_hbE in HBR; [| |apply COMPL]; eauto.
          unfolder in HBR; desf. }
        apply ct_step; left.
        unfold sb in *; unfolder in SB; desc.
        unfolder; splits; vauto; left; apply COMPL; split; eauto.
        unfolder; intro; desf. }
      apply (wf_rfD Wf_G') in RF', RF.
      unfolder in RF; unfolder in RF'; desf;
      by apply n_is_w in RF'1. }
    destruct SBRF as [SB|RF'].
    { unfold sb in SB; unfolder in SB; desc; apply (sb_LR LR) in SB0.
      exists z; splits; eauto.
      destruct HB as [|HB]; subst; eauto.
      edestruct LR_irr; eapply LR_trans; eauto. }
    apply (wf_rff Wf_G' _ _ _ RF) in RF'; desf. }
  desc.
  assert (hb G x y') as xHBy'.
  { assert (hb (Restr G' (set_compl (eq a ∪₁ eq e))) x y') as HBR.
    { eapply sub_execution_hbE; [apply Wf_G'| |].
      { eapply sub_execution_RV; [apply Gf_Wf| |]; eauto. }
      apply (wf_hbE Wf_G') in xHB'y'; unfolder in xHB'y'; desc.
      ins; unfolder; splits; eauto; intros []; subst; eauto.
      by apply LR_irr in y'LRa. }
    cdes MC; apply sub_Completions in COMPL; eauto.
    eapply sub_execution_hbE in HBR; [| |eauto]; eauto.
    unfolder in HBR; desf. }
  apply (wf_hbE Wf__G) in xHBy'; unfolder in xHBy'; desc.
  specialize (hb_init_r Wf_G' xHB'y') as NINI.
  assert (T'' := T).
  apply total_order_from_list_in2 in T.
  edestruct total_order_from_list_total 
    with (a := y') (b := a) (l := l) as [aLy'|y'La]; eauto.
  { eapply TruSt_G_corr_ord; vauto. }
  { intro; subst; by apply LR_irr in y'LRa. }
  { rewrite <-seqA in LR_l.
    specialize (LR_l _ _ (conj y'LRa aLy')).
    destruct LR_l as [p [[z [? []]] [pLRy' _]]].
    eapply (LR_irr LR p), LR_trans; eauto; eapply LR_trans; eauto.
    apply aHB, (rewrite_trans_seq_cr_l (@hb_trans _)); do 2 esplit; vauto. }
  assert ((<|set_compl is_init|> ;; hb G) x y') as HBA.
  { unfolder; split; eauto; intro.
    eapply (LR_irr LR a), LR_trans; eauto.
    by apply sb_LR; destruct x, a. }
  eapply TruSt_ninit_hbE in HBA; eauto.
  assert (NoDup l) as ND.
  { eapply TruSt_NoDup; vauto. }
  destruct HBA as [w [T' [|RFL]]]; subst; apply transp_cr in T'.
  { eapply (total_order_from_list_irreflexive ND) with (x := x).
    eapply (total_order_from_list_trans ND); eauto.
    destruct T'; subst; eauto.
    eby eapply total_order_from_list_trans. }
  eapply B23_P6 with (w := w) (r := y') (x := a) in TS2'; auto.
  { destruct TS2' as [|[|HB]].
    { eapply (total_order_from_list_irreflexive ND).
      eapply (total_order_from_list_trans ND); eauto. }
    { destruct T' as [|T']; subst.
      1,2: eapply (total_order_from_list_irreflexive ND) with (x := x).
      1,2:  eapply (total_order_from_list_trans ND); eauto.
      eapply total_order_from_list_trans with (y := w); eauto. }
    eapply (LR_irr LR a), LR_trans with (y := y'); auto.
    apply aHB, ct_ct; exists w; split; auto; destruct RFL; vauto. }
  { intro; subst.
    destruct T'; subst.
    { by apply total_order_from_list_irreflexive in T''. }
    eapply (total_order_from_list_irreflexive ND).
    eapply (total_order_from_list_trans ND); eauto. }
  { intro; subst.
    by apply total_order_from_list_irreflexive in y'La. }
  unfolder; split; auto.
  eby eapply In_RV_a.
Qed.

Lemma Da_in_l :
  (Del (Add G e) l a e ∪₁ eq a) ⊆₁ (fun x => In x l).
Proof.
  intros ? [[T]|]; subst.
  { by apply total_order_from_list_in1 in T. }
  eapply TruSt_G_corr_ord; vauto.
  split; [eby eapply In_RV_a|inv PR; by destruct x]. 
Qed.

Lemma l_in_G : (fun x : Event => In x l) ⊆₁ acts G.
Proof.
  intros ? IN; eapply TruSt_G_corr_ord in IN; vauto.
  by destruct IN.
Qed.


Lemma LR_L_in_Del :
        restr_rel (Del (Add G e) l a e ∪₁ eq a) LR
        ≡ 
        restr_rel (Del (Add G e) l a e ∪₁ eq a) (total_order_from_list l)⁻¹.
Proof.
  assert (NoDup l) as ND.
  { eapply TruSt_NoDup; vauto. }
  inv TS.
  { arewrite (Del (Add G0 e) nil a e ≡₁ ∅).
    { split; [|basic_solver]; intros ? [T].
      by apply total_order_from_list_in1 in T. }
    rewrite set_union_empty_l.
    split; intros ???T; unfolder in T; desf.
    { by apply LR_irr in T. }
    by apply total_order_from_list_irreflexive in T. }
  apply total_eqv.
  { rewrite Da_in_l, l_in_G; eapply LR_total, Prev_p_sem; vauto. }
  { rewrite Da_in_l, <- total_transp; apply total_order_from_list_total. }
  { by apply LR_irr. }
  { by apply total_order_from_list_irreflexive. }
  rewrite transp_inv; split; [|basic_solver].
  rewrite DelE; intros ?? LRL. 
  unfolder in LRL; desc.
  apply B23 in TS2; eauto; desc.
  rewrite <-seqA in LR_l; specialize (LR_l _ _ (conj LRL0 LRL2)).
  destruct LR_l as [w [[? [? []]] [wLRx]]].
  eapply LR_irr, LR_trans; eauto.
  tertium_non_datur (y = w) as [|NEQ]; subst; eauto.
  eapply LR_trans; eauto.
  assert (LR^? y w) as LRr; [|by destruct LRr].
  eapply RV_hb_LR with (e := y) (a := a); eauto.
  { desf; vauto. }
  { destruct LRL1; subst; desc; eauto; eby eapply In_RV_a. }
  exists y; split; [basic_solver|].
  apply (rewrite_trans_seq_cr_l (@hb_trans _)). do 2 esplit; vauto.
Qed.

Lemma G'E : exists wp, 
  G' =
  SetCO (SetRF (Add (Restr G (set_compl (Del (Add G e) l a e))) e) a e) wp e /\
  << HBM0: is_w wp >> /\
  << HBM1: same_loc wp e >> /\
  << HBM2: acts (Restr G' (set_compl (eq a))) wp >> /\
  << NWP : wp <> e >>.
Proof.
  assert (forall wp, 
    SetCO (SetRF (Add (Restr G (set_compl (Del (Add G e) l a e))) e) a e) wp e = 
    SetRF (
      Add (SetCO (
           Add (Restr G' (set_compl (eq a ∪₁ eq e))) 
           e) 
           wp e) 
      a) 
      a e) as E.
  { assert ((Restr G (set_compl (Del (Add G e) l a e ∪₁ eq a))) = 
    Restr G' (set_compl (eq a ∪₁ eq e))) as E.
    { assert (Wf (Restr G' (set_compl (eq a ∪₁ eq e)))).
      { subst. eby eapply next_Wf, next_Restr_RV. }
      rewrite DelE; apply sub_exec_same_acts with (G := G).
      { rewrite Resrt_in_G; eauto.
        arewrite (acts G ∩₁ set_compl (acts G \₁ acts G' ∪₁ eq a) = 
                  acts G ∩₁ (acts G' \₁ eq a)).
        { rewrite <-set_equivE, set_compl_union, set_compl_minus.
          basic_solver. }
        arewrite (acts G ∩₁ (acts G' \₁ eq a) =
          acts G ∩₁ (acts G' ∩₁ set_compl (eq a ∪₁ eq e))).
        { assert (~ acts G e).
          { by inv PR; cdes MC; cdes MAX; cdes MAX0. }
          rewrite <-set_equivE; split; try basic_solver.
          unfolder; ins; desf; splits; eauto; intro; desf. }
        rewrite <-Resrt_in_G; eauto.
        assert (WF := Wf_G).
        inv PR; cdes MC; apply sub_Completions in COMPL; eauto.
        erewrite <-Restr_eq_sub; eauto. }
      { inv PR; cdes MC. by apply sub_Completions in COMPL. }
      ins. rewrite set_compl_union, set_compl_minus.
      assert (~ acts G e).
      { by inv PR; cdes MC; cdes MAX; cdes MAX0. }
      split; unfolder; ins; desf; splits; eauto.
      { intro; desf. }
      inv PR; cdes MC; apply sub_Completions in COMPL; eauto.
      apply COMPL; ins; splits. }
    rewrite <-E; clear E.
    intros. rewrite <-eq_executionE; unfold eq_execution; splits; ins.
    { rewrite DelE; assert (acts G a).
      { eapply In_RV_a; vauto. }
      assert (acts G' a).
      { by inv PR; cdes ME; cdes HBM_e. }
      rewrite set_compl_union. unfolder; split; ins; desf; vauto.
      { destruct (classic (a = x)); vauto. }
      left; split; vauto; intro; desf. }
    { rewrite <-?restr_relE, set_compl_union.
      rewrite set_interC, <-restr_restr.
      arewrite ((restr_rel (set_compl (eq a)) (rf G)) ≡ rf G ;; ⦗fun e' : Event => e' <> a⦘).
      { split; [basic_solver|]; intros ???RF; unfolder; unfolder in RF; desc.
        splits; eauto; intro; subst; inv PR; apply n_is_w in R.
        apply wf_rfD in RF; unfolder in RF; desf.
        eapply Prev_Wf; vauto. }
      rewrite ?restr_relE, ?seqA, seq_eqvC, <-3?seqA.
      setoid_rewrite <-seqA at 2. by rewrite seq_eqvK, ?seqA. }
    rewrite <-?restr_relE, set_compl_union, set_interC, <-restr_restr.
    arewrite (restr_rel (set_compl (eq a)) (co G) ≡ co G); ins.
    assert (Wf G) as WF by (eapply Prev_Wf; vauto).
    inv PR; apply n_is_w in R; rewrite (wf_coD WF).
    split; try basic_solver; unfolder; ins; desf; splits; eauto; intro; desf. }
  assert (hb_max (Restr G' (set_compl (eq a))) e) as HBM.
  { inv PR; split; ins.
    { apply Wf_G' in RF; unfolder in RF; desf.
      split; eauto; intro; subst; by apply LR_irr in Next. }
    split; [|basic_solver].
    intros ? HB; unfolder in HB; desf.
    eapply sub_execution_hbE with (G' := G') in HB0; eauto.
    { ins; unfolder in HB0; desf; destruct HB2.
      apply HBe; unfolder; vauto. }
    apply Restr_clos_sub; eauto.
    { unfolder; intros ???; desf; by destruct x0. }
    unfolder; ins; intro; desf.
    eapply ME; unfolder; vauto. }
  apply SetCO_Restr in HBM; eauto.
  { desf; exists w. rewrite E.
    inv PR; specialize (@SetRF_Restr _ e a Wf_G' RF).
    intros E1; setoid_rewrite <-E1 at 1; splits; eauto.
    by rewrite <-HBM0, RestrRestrE. }
  { apply Wf_Restr; eauto. inv PR.
    intros ???; subst; destruct x; ins. }
  { inv PR; apply (wf_rfD Wf_G') in RF.
    unfolder in RF; desf. }
  { by inv PR; cdes MC; apply not_init_next in MAX. }
  eapply Prev_finite in PRf; eauto; destruct PRf as [s ACT].
  exists s; ins; generalize ACT, IN; basic_solver.
Qed.

Lemma IsMaximalDel x : 
  Del (Add G e) l a e x \/ a = x -> IsMaximal (Add G e) l x e.
Proof.
  inv TS.
  { inv PR; assert (acts G0 a) as ACT by eby eapply In_RV_a.
    ins; by destruct a. }
  assert (Wf__G := Wf_G).
  assert (cons G) as consG by by eapply Prev_cons; vauto.
  inv PR; intros Da.
  apply (wf_rfD Wf_G') in RF; unfolder in RF; desc.
  assert (Da' := Da); unfold Del in Da.
  rewrite DelE in Da'.
  assert (forall y x,  (acts G \₁ acts G') x \/ a = x -> hb G x y -> x <_next y) as HBx.
  { intros y x0 Da'' HB.
    unfolder in Da''; desc; eapply RV_hb_LR with (e := x0) in PR; eauto; try (by desf).
    { enough (LR^? x0 y) as xLRy.
      { destruct xLRy; subst; eauto; by apply (cons_hb_irr _ consG) in HB. }
      apply PR; basic_solver. }
    { desf; vauto. }
    desf; eby eapply In_RV_a. }
  intros x' RF'. des_if; split.
  { ins; apply Wf__G in RF'; unfolder in RF'; desc.
    splits; vauto.
    destruct (classic (Del (Add G e) l a e x')) as [D|ND].
    { rewrite DelE in D; right; left.
      apply LR_L_in_Del; rewrite DelE; unfolder; splits.
      { apply HBx; vauto. }
      all: unfolder in D; vauto. }
    destruct (classic (is_init x')) as [INI|INI].
    { do 2 right; apply ct_step; left; 
      cdes MC; apply not_init_next in MAX.
      unfold sb; unfolder; splits; vauto; by destruct x', e. }
    unfold Del in ND; apply not_and_or in ND.
    destruct ND as [ND|ND].
    { right; left.
      enough (total_order_from_list l a x') as T.
      { clear Da'; desf; eapply total_order_from_list_trans; eauto.
        eapply TruSt_NoDup; vauto. }
      apply (wf_rfD Wf__G) in RF'0; unfolder in RF'0; desc.
      destruct total_order_from_list_total with (l := l) (a := a) (b := x'); eauto.
      1,2: eapply TruSt_G_corr_ord; vauto; split.
      { eby eapply In_RV_a. }
      { by destruct a. }
      { intro; subst; by apply n_is_r in RF'0. }
      contradiction. }
    clarify_not; vauto. }
  2: desf; split; vauto; ins; generalize Da'; basic_solver.
  all: intros F; desc; ins.
  all: unfolder in F; destruct F as [F|F]; subst.
  2,4: apply Wf__G in F0; unfolder in F0; desc.
  2,3: cdes MC; cdes MAX; cdes MAX0; contradiction.
  { apply Wf__G in F0; unfolder in F0; desc.
    eapply hb_Add_Prev with (x := x) (y := w') in PR; eauto.
    { cdes PR. inv COMP; apply (next_uniq Next1) in Next0; subst.
      { eapply MW with (b := w').
        assert (rf (SetRF (Add G'1 x) x w) w x) as wRFx by vauto.
        apply SUB2 in wRFx; unfolder in wRFx; desc.
        apply (wf_rff Wf__G _ _ _ RF') in wRFx; subst.
        apply SUB2; unfolder; splits; vauto; cdes MW; vauto. }
      apply n_is_r in W; contradiction. }
    { apply wf_coD in F2; unfolder in F2; desf. }
    destruct F1 as [F1|[F1|F1]]; subst; vauto.
    { apply (wf_coD Wf__G) in F2; unfolder in F2; desc.
      by apply n_is_r in F4. }
    tertium_non_datur (acts G' w') as [|NACT]; vauto.
    left; apply LR_L_in_Del; rewrite DelE; unfolder; splits; eauto. }
  apply Wf__G in F0; unfolder in F0; desc.
  eapply hb_Add_Prev with (x := x) (y := w') in PR; eauto.
  { assert (w' <> x).
    { by intro; subst; apply co_irr in F2. }
    cdes PR. inv COMP; apply (next_uniq Next1) in Next0; subst.
    { desf. }
    eapply MW with (b := w').
    apply SUB1; unfolder; splits; cdes MW; eauto; ins.
    { eapply co_trans; eauto.
      assert (co (SetCO (Add G'1 x) w x) w x) as CO.
      { ins; unfold into_rel; right; vauto. }
      by apply SUB2 in CO; unfolder in CO; desc. }
    unfolder in ACT1; desf. }
  { apply (wf_coD Wf__G) in F2; unfolder in F2; desf. }
  destruct F1 as [F1|[F1|F1]]; subst; vauto.
  { apply (wf_coD Wf__G) in F2; unfolder in F2; desc.
    by apply co_irr in F1. }
  tertium_non_datur (acts G' w') as [|NACT]; vauto.
  left; apply LR_L_in_Del; rewrite DelE; unfolder; splits; eauto.
Qed.


End Revisit.

Context {rv : Revisit}.
Hypothesis PR  : G ~(e)~(rv)~> G'.

Lemma TruStPrev : 
  exists l', TruSt_step G l rv e G' l'.
Proof.
  assert (cons G') by by eapply Prev_cons; vauto.
  assert (Wf G') by by eapply Prev_Wf; vauto.
  assert (Wf G) by by eapply Prev_Wf; vauto.
  assert (set_finite (acts G' \₁ is_init)) by by eapply Prev_finite; vauto.
  assert (next G e) as N.
  { eby eapply next_Prev. }
  inv PR.
  { assert (Wf (Restr G' (set_compl (eq a ∪₁ eq e)))) as Wf_R.
    { eapply sub_execution_wf; [|apply Wf_G'].
      eapply sub_execution_RV; [apply Gf_Wf| |]; eauto. }
    assert (coirr := Wf_G').
    apply co_irr in coirr.
    assert (GE := PR); apply G'E in GE; desc.
    eexists; eapply REVISIT; eauto.
    { apply (wf_rfl Wf_G') in RF; basic_solver. }
    { apply (wf_rfD Wf_G') in RF; unfolder in RF; desf. }
    { eby eapply In_RV_a. }
    { ins. rewrite DelE; eauto; unfolder.
      unfolder in HBM2; desc; splits; eauto; desf; ins.
      { unfolder in HBM2; desf. }
      intro; desf. }
    { clear GE.
      apply wf_rfD in RF; eauto; unfolder in RF; desc.
      assert (acts G a) by eby eapply In_RV_a.
      assert (forall e' : Event, acts G e' -> ~ ext_sb e e').
      { ins; eapply avail_sb_max; eauto; eby cdes MC; cdes MAX. }
      intro HB; apply hb_add_max in HB; eauto; desf; cdes MC.
      destruct (classic (acts (Restr G' (set_compl (eq a ∪₁ eq e))) e2)) as [A|A].
      { unfolder in HB; desf; [ins; generalize A; basic_solver|].
        apply sub_Completions in COMPL; eauto.
        eapply sub_execution_hb in A; eauto.
        ins; generalize A; basic_solver. }
      apply ext_sb_tid_init' in SB; unfolder in SB; desf.
      { set (P := fun x =>  ~ acts x e2).
        assert (~ is_init e) by eby eapply not_init_next.
        apply MaxCompletion_Compl in MC;
          [|eapply avail_Restr_e_RV with (Gf := Gf); eauto].
        eapply (r_str_cont P A) in MC; eauto. ins; desf.
        clear A; unfold P in *; clarify_not; cdes MC0.
        clear N.
        assert (next z e2) as N by (eapply Completion_nextE; basic_solver).
        assert (avail z e) as N'.
        { by apply avail_Compl in MC;
            [|eapply avail_Restr_e_RV with (Gf := Gf); eauto]. }
        cdes N.
        eapply avail_same_tid in SB0; eauto; desf. }
      by apply Wf_R in SB. }
    by apply IsMaximalDel. }
  { exists (e :: l).
    cdes ME; apply SetCO_Restr in HBM_e; eauto.
    desf; eapply WRITE with (wp := w); eauto.
    split; eauto; intro; desf. }
  exists (e :: l).
  apply (wf_rfD Wf_G') in RF; unfolder in RF; desc.
  apply READ with (w := e0); eauto.
  { symmetry. by eapply (wf_rfl Wf_G'). }
  { apply Wf_G' in RF0; unfolder in RF0; desc.
    split; eauto; intro; desf; by apply n_is_w in RF. }
  rewrite SetRF_Restr; eauto.
Qed.

End TruStPrev.

Lemma TruSt_n1 G1 l1 G2 l2 G3 l3 e rv
  (TS1 : TruSt_step G1 l1 rv e G2 l2)
  (TS  : TruSt G2 l2 G3 l3) : 
  TruSt G1 l1 G3 l3.
Proof using.
  induction TS; vauto.
Qed.

Lemma TruSt_trans G1 l1 G2 l2 G3 l3
  (TS1 : TruSt G1 l1 G2 l2)
  (TS2 : TruSt G2 l2 G3 l3) : 
  TruSt G1 l1 G3 l3.
Proof using.
  induction TS2; vauto.
Qed.

(** TruSt is complete: Every consistent full execution graph 
of the given program is visited by the algorithm. *)

Theorem TruSt_Complete G 
  (G_full : full  G)
  (G_cons : cons  G)
  (G_psem : p_sem G) : 
  exists l, TruSt G0 nil G l.
Proof using p_sem_finite.
  assert (G_fin : set_finite (acts G \₁ is_init)).
  { specialize (p_sem_finite G_psem) as F; desc; exists l; intros ? IN.
    by apply OC. }
  assert (G0 ~~>* G) as R.
  { cdes G_psem. cdes G_fin.
    eapply G0_prev_Gf; eauto.
    unfolder. apply G_fin0. }
  assert (exists G' l', G' ~~>* G /\ TruSt G0 nil G' l') as I.
  { exists G0, nil; vauto. }
  clear R; desf.
  enough (exists l, TruSt G' l' G l); desf.
  { exists l; eby eapply TruSt_trans. }
  generalize dependent l'.
  induction I; vauto.
  cdes G_psem; cdes G_fin; ins.
  eapply TruStPrev in PR2; eauto; desf.
  { destruct IHI with (l' := l'0) as [l'' TS]; vauto.
    exists l''; eapply TruSt_n1; eauto. }
  unfolder; by apply G_fin0.
Qed.

End Completeness.
