From hahn Require Import Hahn.
Require Import Execution Execution_Aux Events Labels.
From Coq Require Import Lia.
Require Import Util Sem.

Set Implicit Arguments.

Section AlgDef.

Variable thread_sem : tsemType.
Variable LR         : LRType thread_sem.
Variable cons       : consType.

Notation "e1 '<_next' e2" := (LR_of LR e1 e2) (at level 20).
Notation avail := (avail thread_sem).
Notation p_sem := (p_sem thread_sem).
Notation me    := (me LR).

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

(* ************************************************************************* *)
(*                                TruSt                                      *)
(* ************************************************************************* *)

Definition IsMaximal G l e w : Prop :=
  let B      := fun w' =>
                  G.(acts) w' /\
                  (w' = e \/ total_order_from_list l e w' \/ hb G w' w) in
    forall e',
      (if is_r e then
        G.(rf) e' e
      else e' = e) -> B e' /\ ~ exists w', B w' /\ G.(co) e' w'.

(* ************************************************************************* *)
(*                             Algorithm definition                          *)
(* ************************************************************************* *)

Hint Resolve cons0 : core. 

Notation next := (next LR).

Inductive TruSt_step G l : Revisit -> Event -> execution -> list Event -> Prop :=
  | READ G' r w
    (SL : same_loc r w)
    (Next : next G r) (Write : is_w w) (Read : is_r r) (InG : G.(acts) w)
    (RF : G' = SetRF (Add G r) r w) (Cons : cons G') :
      TruSt_step G l NR r G' (r :: l)
  | WRITE G' wp w
    (SL : same_loc wp w)
    (Next : next G w) (Write : is_w w) (Writep : is_w wp) (InG : G.(acts) wp)
    (CO : G' = SetCO (Add G w) wp w) (Cons : cons G') :
      TruSt_step G l NR w G' (w :: l)
  | REVISIT G' w wp r
    (D := Del (Add G w) l r w)
    (wp_w : wp <> w)
    (SL : same_loc wp w) (SL : same_loc r w)
    (Next : next G w)
    (Write : is_w w) (Read : is_r r) (Writep : is_w wp)
    (InG : G.(acts) r) (InG : acts (SetRF (Restr G (set_compl D)) r w) wp)
    (Nporf : ~ hb (Add G w) r w)
    (Max : forall e, D e \/ r = e -> IsMaximal (Add G w) l e w)
    (Corr : G' = SetCO (SetRF (Add (Restr G (set_compl D)) w) r w) wp w)
    (Cons : cons G') :
      TruSt_step G l (RV r) w G' (filterP (acts G') (w :: l)).


Inductive TruSt G l : execution -> list Event -> Prop :=
  | Base : TruSt G l G l
  | Step : forall G1 l1 G2 l2 rv e
    (TS1 : TruSt G l G1 l1) (TS2 : TruSt_step G1 l1 rv e G2 l2),
    TruSt G l G2 l2.

Record state : Type := mkst {
  G_of  : execution;
  l_of  : list Event
}.

Definition TruSt_rel st1 st2 := 
  exists e rv, TruSt_step (G_of st1) (l_of st1) rv e (G_of st2) (l_of st2).

Lemma TruSt_rel_str st1 st2: 
  TruSt_rel^* st1 st2 <-> TruSt (G_of st1) (l_of st1) (G_of st2) (l_of st2).
Proof.
  split; intro TS.
  { apply clos_rt_rtn1 in TS; induction TS as [|st ? T]; vauto.
    cdes T; vauto. }
  destruct st1, st2; ins; apply clos_rtn1_rt; induction TS; vauto; ins.
  econstructor; vauto.
Qed.


Definition st0 := mkst G0 nil.

(* ************************************************************************* *)
(*                           First TruSt properties                          *)
(* ************************************************************************* *)

Lemma TruSt_G_corr_ord  {G l} (Tr : TruSt G0 nil G l) :
  G_ord_corr G l.
Proof using.
  remember G0 as G'; induction Tr; subst.
  { unfold G_ord_corr; unfolder; ins; tauto. }
  inv TS2; unfold G_ord_corr in *; simpls; intros e';
  generalize (IHTr e'); unfolder; intros H.
  1,2: apply not_init_next in Next; split; ins; desf; tauto.
  desf; [|tauto]; rewrite in_cons_iff, in_filterP_iff; split.
  all: apply not_init_next in Next; ins; desf; tauto.
Qed.

Lemma TruSt_NoDup G l (Tr : TruSt G0 nil G l) :
  NoDup l.
Proof using.
  remember G0 as G'; induction Tr; eauto.
  destruct TS2; desf.
  3: apply nodup_filterP.
  all: apply nodup_cons; split; eauto;
    destruct Next as [[]]; desf; intro IN; apply (TruSt_G_corr_ord Tr) in IN;
    unfolder in IN; desf.
Qed.

Theorem TruSt_correct G l (Tr : TruSt G0 nil G l) : cons G.
Proof using cons.
  destruct Tr; eauto. destruct Tr; by do 2 (destruct TS2; desf).
Qed.

(* ************************************************************************* *)
(*                           TruSt Well-formedness                           *)
(* ************************************************************************* *)

Lemma TruSt_step_Wf G1 l1 rv e G2 l2
      (T : TruSt_step G1 l1 rv e G2 l2)
      (ND: NoDup l1) (GOC: G_ord_corr G1 l1)
      (WF : Wf G1) : Wf G2.
Proof using.
  destruct T; desf; unfold next in Next; desf;
    unfold avail in Next; desf; ins; red in GG'; desc.
  { apply Wf_SetRF with (G' := G'); eauto; try basic_solver.
    eby eapply p_sem_Wf. }
  { apply Wf_SetCO with (G' := G'); eauto; try basic_solver.
    eby eapply p_sem_Wf. }
  rewrite SetCORF.
  assert (eq_execution
  (SetRF (Add (SetCO (Add (Restr G1 (set_compl D)) w) wp w) r) r w)
  (SetRF (SetCO (Add (Restr G1 (set_compl D)) w) wp w) r w))
  as EQ.
  { apply SetRF_more; ins; apply Add_eq.
    ins; unfolder; ins; left; splits; ins.
    eapply r_not_in_Del; ins.
    red; intro X; apply GOC in X; unfolder in X; desf. }
  apply (Wf_eq EQ), Wf_SetRF with (G' := G').
  all: try (ins; basic_solver).
  { eby eapply p_sem_Wf. }
  eapply Wf_SetCO with (G' := G'); eauto.
  1: unfold SetCO, SetRF, Restr; ins; unfolder;
    desf; firstorder.
  { unfold Restr; basic_solver. }
  { eby eapply p_sem_Wf. }
  apply Wf_Restr; eauto.
  intros e INI; unfolder.
  unfold D, Del; intro F; desf.
  eapply total_order_from_list_in1 in F.
  apply GOC in F ; unfolder in F; desf.
Qed.


Theorem TruSt_Wf G l (Tr : TruSt G0 nil G l) : Wf G.
Proof using.
  remember G0 as G'; induction Tr; desf; eauto using Wf_G0.
  eapply TruSt_step_Wf; eauto using TruSt_G_corr_ord, TruSt_NoDup.
Qed.

Hint Immediate TruSt_Wf : hahn.

Lemma sb_l G e l
  (Gl: G_ord_corr G l)
  (SB: ⦗fun x : Event => ~ is_init x⦘ ⨾ sb G ⊆ (total_order_from_list l)⁻¹)
  (Next : next G e) : ⦗fun x : Event => ~ is_init x⦘ ⨾ sb (Add G e)
  ⊆ (total_order_from_list (e :: l))⁻¹.
Proof using.
  intros e1 e2.
  unfolder; ins; desf; apply total_order_from_list_cons.
  rewrite @sb_add_max in *; auto; desf.
  { right; apply SB; basic_solver. }
  { left; splits; eauto. apply Gl; basic_solver. }
  intros ??; eapply avail_sb_max; eauto with hahn.
  eby eapply next_avail.
Qed.

Lemma TruSt_sb_l G l (Tr : TruSt G0 nil G l) :
  ⦗fun x => ~ is_init x⦘ ⨾ sb G ⊆ (total_order_from_list l)⁻¹.
Proof using.
  induction Tr.
  { unfold sb; unfolder; ins; desf. }
  pose proof (TruSt_G_corr_ord Tr) as Gl.
  inv TS2; [hahn_rewrite sb_SetRF|hahn_rewrite sb_SetCO|]; try by apply sb_l.
  rewrite sb_SetCO, sb_SetRF.
  hahn_rewrite total_order_from_list_filterP.
  intros x y SB; unfolder in SB; desf.
  rewrite sb_add_max in SB0.
  { desf; unfold SetCO, SetRF; simpls; unfolder.
    { unfold SetCO, SetRF; simpls.
      hahn_rewrite sb_Restr in SB0; unfolder in SB0; desc.
      assert (SB' := SB1); unfold sb in SB1; unfolder in SB1.
      clear TS2; desf; splits; eauto 11.
      apply total_order_from_list_cons; right; apply IHTr. basic_solver. }
    unfolder in SB0.
    splits; eauto 11; apply total_order_from_list_cons; left.
    splits; auto; apply Gl; basic_solver. }
  intros ? ACT.
  eapply avail_sb_max with (G := G1); eauto with hahn.
  { eby eapply next_avail. }
  unfold Restr in ACT; simpls; unfolder in ACT; desf.
Qed.

(* Section with common properties for revisit and non-revisit step *)
Section General_Properties.

Context {G G' : execution}.
Context {l l' : list Event}.
Context {e a  : Event}.
Context {t : Revisit}.
Hypothesis TS  : TruSt_step G l t e G' l'.
Hypothesis TS1 : TruSt G0 nil G l.

Lemma e_not_in_l  : ~ In e l.
Proof using TS1 TS.
  intros IN.
  inv TS. 
  all: apply (TruSt_G_corr_ord TS1) in IN; unfold next, avail in Next; desf.
  all: unfolder in IN; basic_solver.
Qed.

Lemma e_not_in_G : ~ acts G e.
Proof using TS. by inv TS; cdes Next; cdes Next0. Qed.

Lemma G'_e : acts G' e.
Proof using TS. inv TS; vauto. Qed.

Lemma hb_rf_l_LR_LR :
  ((hb G')^? ;; rf G' ∩ total_order_from_list l' ;; LR ∩ (total_order_from_list l')⁻¹) ;;
  LR ∩ (total_order_from_list l')⁻¹
    ⊆
  (hb G')^? ;; rf G' ∩ total_order_from_list l' ;; LR ∩ (total_order_from_list l')⁻¹.
Proof using TS1 TS.
  rewrite ?seqA.
  do 2 (apply seq_mori; [basic_solver|]).
  intros ?? [? [[LR1 L1] [LR2 L2]]].
  split; [eby eapply LR_trans|].
  eapply total_order_from_list_trans; eauto.
  eapply TruSt_NoDup; eby econstructor.
Qed.

Lemma NoDup_el : NoDup (e :: l).
Proof using TS1 TS.
  apply nodup_cons. split; [eby eapply e_not_in_l | eby eapply TruSt_NoDup].
Qed.

Lemma LR_tot e1 e2 
  (ACT1 : acts G e1 \/ e1 = e)
  (ACT2 : acts G e2 \/ e2 = e) : 
  e1 = e2      \/
  e1 <_next e2 \/
  e2 <_next e1.
Proof using TS.
  assert (exists G', 
      << PS    : p_sem G'     >> /\
      << ACT1  : acts  G' e1  >> /\
      << ACT2  : acts  G' e2  >>) as [E]; [|cdes E].
  { inv TS; cdes Next; cdes Next0;
    exists G'; splits; eauto; desf;
    apply GG'; eauto. }
  tertium_non_datur (e1 = e2); vauto; right.
  edestruct LR_total with (a := e1) (b := e2) as [ee0|e0e]; eauto.
Qed.

End General_Properties.

Hint Immediate NoDup_el : hahn.

(* Section with properties of the non-revisit step *)
Section NRevisit_Properties.

Context {G G' : execution}.
Context {l l' : list Event}.
Context {e a  : Event}.
Hypothesis TS  : TruSt_step G l NR e G' l'.
Hypothesis TS1 : TruSt G0 nil G l.

Lemma TruSt_Step_NRV :
  acts G' ≡₁ acts G ∪₁ eq e.
Proof using TS. inv TS. Qed.

Lemma hb_TruSt_step_nr :
  hb G ⊆ hb G'.
Proof using TS TS1.
  apply inclusion_t_t, inclusion_union_mon; unfold sb.
  { inv TS; simpls; apply inclusion_seq_mon; try apply inclusion_seq_mon.
    all: basic_solver. }
  inv TS; simpls; intros x y RF; left; unfolder; splits; eauto.
  intros ?; subst; apply (wf_rfE (TruSt_Wf TS1)) in RF.
  unfolder in RF; desf.
  by cdes Next; cdes Next0.
Qed.

Lemma rf_l_nr : 
  rf G' ∩ total_order_from_list l' ≡ rf G ∩ total_order_from_list l.
Proof using TS TS1.
  inv TS; ins; unfolder; split; intros e1 e2 RFL; desf.
  1,4: split; eauto; apply total_order_from_list_cons in RFL0; desf.
  1,2: eapply wf_rfE in RFL; eauto with hahn; unfolder in RFL; desf.
  1,2: cdes Next; cdes Next0; basic_solver.
  { eby (eapply total_order_from_list_cons_max in RFL0; [|eapply NoDup_el]). }
  { split; [|apply total_order_from_list_cons; eauto].
    apply total_order_from_list_in2 in RFL0.
    assert (F := e_not_in_l TS TS1); left; splits; eauto; intros EQ; desf. }
  split; [|apply total_order_from_list_cons]; vauto.
Qed.

Lemma avail_nr : 
  avail G' ⊆₁ avail G ∪₁ (fun x => ext_sb e x).
Proof using TS1 TS.
  inv TS; [apply avail_SetRF|apply avail_SetCO]; eauto with hahn.
  by symmetry.
  all: eby eapply next_avail.
Qed.

Lemma split_rf : 
  <|set_compl is_init |> ;; rf G ⊆
  rf G ∩ (total_order_from_list l)⁻¹ ∪ rf G ∩ total_order_from_list l.
Proof.
  intros ?? RF; unfolder in RF; desf.
  apply no_rf_to_init in RF0; eauto with hahn.
  unfolder in RF0; desf.
  apply wf_rfE in RF0; unfolder in RF0; desf; eauto with hahn.
  assert (NoDup l) as ND by (eapply TruSt_NoDup; vauto).
  edestruct (total_order_from_list_total) with (a := x) (b := y) (l := l).
  1,2: eapply TruSt_G_corr_ord; vauto.
  { intro; desf; apply wf_rfD in RF2; eauto with hahn.
    unfolder in RF2; desf; by apply n_is_w in RF5. }
  all: basic_solver.
Qed.

Lemma union_seq_emp A (r1 r2 : relation A)
  (R22 : r2 ;; r2 ≡ ∅₂): 
  (r1 ∪ r2)^* ⊆ (r1 ∪ r2 ;; r1)^* ;; r2^?.
Proof.
  assert ((r1 ∪ r2)^* ;; r1 ⊆  (r1 ∪ r2 ;; r1)^*) as AUX.
  { intros ?? [? [R12 R1]].
    apply inclusion_t_rt.
    apply clos_rt_rt1n in R12.
    induction R12 as [|??? [R1'|R2]]; vauto; specialize (IHR12 R1).
    { eapply inclusion_r_t_t with (r := r1); [|reflexivity|]; vauto. }
    apply clos_trans_t1n in IHR12.
    assert (forall z, (r1 ∪ r2 ;; r1) y0 z -> (r1 ∪ r2 ;; r1) x z) as AU.
    { intros ? [|[? []]]; vauto.
      exfalso; eapply R22; exists y0; vauto. }
    destruct IHR12 as [??IHR12|].
    { apply AU in IHR12; vauto. }
    eapply clos_t1n_trans, Relation_Operators.t1n_trans; eauto. }
  intros ?? R12.
  apply clos_rt_rtn1 in R12; destruct R12 as [|?? [R1|R2]].
  { exists x; vauto. }
  { exists z; split; vauto. apply AUX; exists y; split; eauto.
    by apply clos_rtn1_rt. }
  destruct R12 as [|?? [R1|R2']].
  { exists x; vauto. }
  { exists z0; split; vauto; apply AUX; exists y; split; vauto.
    by apply clos_rtn1_rt. }
  exfalso; eapply R22; exists z0; vauto.
Qed.

Lemma union_seq_emp3 A (r1 r2 r3 : relation A)
  (R32 : r3 ;; r2 ≡ ∅₂)
  (R33 : r3 ;; r3 ≡ ∅₂) : 
  (r1 ∪ r2 ∪ r3)^* ⊆ (r1 ∪ r2 ∪ r3 ;; r1)^* ;; r3^?.
Proof.
  by rewrite (union_seq_emp R33), seq_union_r, R32, union_false_r.
Qed.

Lemma ninit_hbE_aux : 
  <|set_compl is_init|> ;; hb G ⊆ 
  (<|set_compl is_init |> ;; sb G     ∪ 
  (rf G ∩ (total_order_from_list l)⁻¹)    ∪
  (rf G ∩ total_order_from_list l) ;; sb G)^* ;; 
  (rf G ∩ total_order_from_list l)^?.
Proof.
  assert (<|set_compl is_init|> ;; hb G ⊆ 
         (<|set_compl is_init|> ;; sb G ∪
          <|set_compl is_init|> ;; rf G)⁺) as HB.
  { intros ?? HB.
    unfolder in HB; desf.
    apply clos_trans_t1n in HB0.
    apply clos_t1n_trans.
    induction HB0 as [??[SB|RF]|????SBRF].
    1,2: apply clos_trans_t1n, ct_step; basic_solver.
    eapply Relation_Operators.t1n_trans with (y := y).
    { destruct SBRF; basic_solver. }
    apply IHHB0; destruct SBRF as [SB|RF].
    { apply no_sb_to_init in SB; unfolder in SB; desf. }
    apply no_rf_to_init in RF; eauto with hahn; unfolder in RF; desf. }
  assert (
    <|set_compl is_init|> ;; hb G ⊆ 
    (<|set_compl is_init |> ;; sb G     ∪ 
    (rf G ∩ (total_order_from_list l)⁻¹)    ∪
    (rf G ∩ total_order_from_list l))⁺
  ) as HB'.
  { by rewrite HB, split_rf, unionA. }
  rewrite HB'; clear HB HB'.
  assert ((⦗set_compl is_init⦘ ⨾ sb G ∪ rf G ∩ (total_order_from_list l)⁻¹
      ∪ rf G ∩ total_order_from_list l)
    ⊆ (⦗set_compl is_init⦘ ⨾ sb G ∪ rf G ∩ (total_order_from_list l)⁻¹
        ∪ rf G ∩ total_order_from_list l ⨾ sb G)＊
      ⨾ (rf G ∩ total_order_from_list l)^?) as AUX.
  { intros ?? HB.
    destruct HB as [[SB|RF]|].
    1,2: eapply trailing_refl; eauto; intros ???.
    1,2: apply inclusion_t_rt, ct_step; vauto.
    exists x; splits; vauto. }
  assert (Wf G); eauto with hahn.
  rewrite inclusion_t_rt, union_seq_emp3.
  { apply inclusion_seq_mon; [|reflexivity].
    apply inclusion_rt_rt, inclusion_union_mon; [reflexivity|].
    basic_solver. }
  all: split; try basic_solver; intros ?? F.
  all: unfolder in F; desf.
  all: apply wf_rfD in F, F0; eauto.
  all: unfolder in F; unfolder in F0; desf.
  all: by apply n_is_w in F6.
Qed.

End NRevisit_Properties.

Section  Revisit_Properties.

Context {G G' : execution}.
Context {l l' : list Event}.
Context {e a  : Event}.
Hypothesis TS  : TruSt_step G l (RV a) e G' l'.
Hypothesis TS1 : TruSt G0 nil G l.

Definition D := Del (Add G e) l a e.
Definition Da := D ∪₁ eq a.

Lemma is_r_a : is_r a.
Proof using TS. inv  TS. Qed.

Lemma G'_rf_complete : rf_complete G'.
Proof using TS TS1.
  eapply cons_complete, TruSt_correct with (l := l'); vauto.
Qed.

Lemma InDel w (ACT : acts G w) (NACT : ~ acts G' w) :
  D w.
Proof using  TS.
  unfold D; inv  TS; simpls.
  unfolder in NACT. clarify_not.
Qed.

Lemma acts_G' : acts G' ≡₁ acts G \₁ D ∪₁ eq e.
Proof using  TS .
  unfold D in *; inv  TS; desf; ins; basic_solver.
Qed.

Lemma acts_G'G_cD : acts G' ∩₁ acts G ⊆₁ set_compl D.
Proof using  TS.
  hahn_rewrite acts_G'; intros x [[[]|]]; desf.
  unfold set_compl, D, Del. intros F; desf.
  eby eapply e_not_in_G.
Qed.

Lemma rf_G' :
  rf G' ≡ ⦗acts G \₁ D⦘ ⨾ rf G ⨾ ⦗acts G \₁ D⦘ ⨾ ⦗fun e2 => e2 <> a⦘
          ∪ singl_rel e a.
Proof using TS1 TS.
  assert (Wf G) as WF by (eapply TruSt_Wf; vauto).
  unfold D in *; inv  TS; ins;
  unfolder; split; ins; desf; vauto.
  all: try (apply WF in H0; unfolder in H0; desf; vauto).
Qed.

Lemma Wf_G : Wf G.
Proof using TS1. eby eapply TruSt_Wf. Qed.

Lemma Wf_G' : Wf G'.
Proof using TS TS1. by eapply TruSt_Wf; vauto. Qed.

Lemma hb_e_G' e'
  (ACT : acts G e')
  (HB : hb (Add G e) e' e ) :
  acts G' e'.
Proof using  TS.
  inv  TS; ins; left; clear  TS.
  unfolder; splits; eauto; unfold D0, Del; intros F; desf.
Qed.

Lemma hb_e_na e' (HB : hb (Add G e) e' e ) :
  e' <> a.
Proof using  TS. inv  TS; intro; apply Nporf; desf. Qed.

Lemma Add_hb_l e1 e2
  (HB : hb (Add G e) e1 e2) : acts G e1.
Proof using TS TS1.
  apply clos_trans_tn1 in HB.
  induction HB as [y [SB|RF]|]; eauto.
  { unfold sb in SB; ins; unfolder in SB; desf; [|eby edestruct ext_sb_irr].
    inv  TS.
    eapply next_avail, avail_sb_max in Next; [by apply Next in SB0|]; eauto. }
  simpls; apply Wf_G in RF; generalize RF; basic_solver.
Qed.

Lemma Max_Da x (Dax : Da x) : IsMaximal (Add G e) l x e.
Proof using  TS.
  unfold Da, D in *; cdes Dax.
  inv  TS. by apply Max.
Qed.

Lemma D_rf_cDa :
  ⦗D⦘ ⨾ rf G ⨾ ⦗set_compl Da⦘ ≡ ∅₂.
Proof using TS TS1.
  split; [unfolder; intros x y [Dx [RF T]]|basic_solver].
  apply (wf_rfD Wf_G) in RF; unfolder in RF; desf.
  apply (eq_in_l (wf_rfE Wf_G)) in RF0; unfolder in RF0; desf.
  destruct (G'_rf_complete) with (x := y) as [z RF'].
  { unfolder; rewrite (set_equiv_exp acts_G'); unfolder; splits; eauto.
    left; split; eauto. clarify_not. }
  hahn_rewrite rf_G' in RF'; unfolder in RF'; desf.
  { generalize (wf_rff Wf_G _ _ _ RF'0 RF2); basic_solver. }
  clarify_not.
Qed.

Local Notation NoDup_l := (TruSt_NoDup TS1).

Lemma Da_rf_cD :
  ⦗Da⦘ ⨾ rf G ⨾ ⦗set_compl D⦘ ≡ ∅₂.
Proof using TS TS1.
  split; [intros x y; unfolder; intros Daz *; desf|basic_solver].
  unfold Da in Daz3; unfolder in Daz3; desf.
  { eapply D_rf_cDa; unfold Da; unfolder.
    splits; eauto; intros F; desf.
    assert (Da a) as M2 by vauto; apply Max_Da in M2.
    generalize (M2 z); rewrite is_r_a; intros M2'.
    destruct M2' as [M _]; eauto.
    cdes Daz3; cdes Daz1; desf.
    eapply (total_order_from_list_irreflexive NoDup_l).
    eby eapply (total_order_from_list_trans NoDup_l). }
  apply (wf_rfD Wf_G) in Daz0; unfolder in Daz0; desf.
  generalize is_r_a; by destruct a as [|?? []].
Qed.

Lemma not_init_Del x (InD : Da x) : ~ is_init x.
Proof using TS TS1.
  unfold Da in InD; unfolder in InD. pose proof is_r_a. desf.
  { unfold D, Del in InD; desf.
    apply total_order_from_list_in1 in InD.
    simpls; inv  TS; cdes Next; cdes Next0.
    apply (TruSt_G_corr_ord TS1) in InD; unfolder in InD; desf. }
  by destruct x.
Qed.

Hint Immediate TruSt_NoDup : core.

Lemma Da_sb_cD :
  ⦗Da⦘ ⨾ sb G ⨾ ⦗set_compl D⦘ ≡ ∅₂.
Proof using TS TS1.
  split; [intros x y; unfolder; intro SB; desf |basic_solver].
  unfold D, Del in SB2.
  generalize SB3; unfold Da, D, Del; unfolder; intros F.
  clarify_not; desf.
  { apply SB2; eapply (total_order_from_list_trans); eauto.
    eapply TruSt_sb_l; eauto; unfolder; splits; eauto.
    by apply not_init_Del. }
  { apply F0, ct_ct; exists y; split; [apply ct_step; left|eauto].
    rewrite sb_add_max; eauto.
    ins; eapply avail_sb_max; inv  TS; eauto with hahn.
    eby eapply next_avail. }
  { apply SB2, (TruSt_sb_l TS1); unfolder; splits; eauto.
    pose proof is_r_a; by destruct a. }
    inv  TS; apply Nporf; apply ct_ct; exists y; split; eauto.
  apply ct_step; left. rewrite sb_add_max; eauto.
  ins; eapply avail_sb_max; eauto with hahn.
  eby eapply next_avail.
Qed.

Lemma Da_hb_cD:
  ⦗Da⦘ ⨾ hb G ⨾ ⦗set_compl D⦘ ≡ ∅₂.
Proof using TS TS1.
  split; [|basic_solver]; unfolder; intros x y HB.
  desf.
  apply clos_trans_tn1 in HB0.
  induction HB0 as [x' [SB|RF]|].
  { eapply Da_sb_cD; basic_solver. }
  { unfold Da in HB; unfolder in HB; desf.
    { eapply D_rf_cDa; unfold Da; unfolder.
      splits; eauto; intros F; desf.
      assert (M2 : Da a); vauto; apply Max_Da in M2.
      generalize (M2 x); rewrite is_r_a; intros M2'.
      destruct M2' as [M _]; eauto.
      cdes HB; cdes HB0; desf.
      eapply (total_order_from_list_irreflexive NoDup_l).
      eapply (total_order_from_list_trans NoDup_l); eauto. }
    apply (wf_rfD Wf_G) in RF; unfolder in RF; desf.
    generalize is_r_a; by destruct a as [|?? []]. }
  apply IHHB0; eauto.
  intro F; destruct H as [SB|RF].
  { eapply Da_sb_cD; unfolder; splits; [|edone|]; vauto. }
  eapply Da_rf_cD; unfolder; splits; [|edone|]; vauto.
Qed.


Lemma Del_rf_l: ⦗ D ⦘ ⨾ (rf G ∩ (total_order_from_list l)) ≡ ∅₂.
Proof using TS TS1.
  assert (ND := NoDup_l).
  split; [|basic_solver]; unfolder; intros x y [Dx [RF T]].
  destruct (classic (Da y)) as [Day|NDay]; desf.
  { unfold D in *; cdes Dx.
    apply (wf_rfD Wf_G) in RF; unfolder in RF; desf.
    apply Max_Da in Day; unfold IsMaximal in Day; desf.
    edestruct Day as [F H2]; simpls; eauto.
    generalize (e_not_in_l TS TS1); intros ?.
    unfolder in F; desf.
    { by destruct y as [|z w []]. }
    { apply total_order_from_list_irreflexive in T; eauto. }
    { eapply total_order_from_list_irreflexive with (x := x) (l := l).
      { eapply TruSt_NoDup. eauto. }
      eapply total_order_from_list_trans with (y := y); eauto. }
    by apply total_order_from_list_in2 in F0. }
  eby eapply (D_rf_cDa); unfolder.
Qed.


Lemma Da_hb_rf_l :
  ⦗Da⦘ ⨾ (hb G)^? ⨾ (rf G ∩  (total_order_from_list l)) ≡ ∅₂.
Proof using TS TS1.
  split; [unfolder; intros x y F; desf|basic_solver].
  1,2:  unfold Da in F; unfolder in F; pose proof is_r_a.
  desf.
  { eapply Del_rf_l; unfolder; eauto. }
  { apply (wf_rfD Wf_G) in F1; unfolder in F1; desf; by destruct z as [|??[]]. }
  { eapply Del_rf_l; unfolder; splits; [|edone|edone].
    destruct (classic (D z)); eauto; exfalso.
    eapply Da_hb_cD; unfolder; splits; vauto. }
Qed.

Lemma hb_in_G' :
  ⦗acts G'⦘ ⨾ hb G ⨾ ⦗acts G' ∩₁ fun x => x <> a⦘ ⊆ hb G'.
Proof using TS TS1.
  unfolder; intros x y HB; desf.
  assert
  (⦗acts G'⦘ ⨾ (sb G ∪ rf G) ⨾ ⦗acts G' ∩₁ fun x => x <> a ⦘ ⊆
   sb G' ∪ rf G') as ST.
  { unfolder; intros e1 e2 SBRF; desf; [left|right].
    { unfold sb in *; unfolder in *; basic_solver. }
    simpls. apply (TruSt_Wf TS1) in SBRF0; unfolder in SBRF0; desf.
    apply rf_G'; left; unfolder; splits; eauto; apply acts_G'G_cD; ins. }
  apply clos_trans_tn1 in HB0.
  induction HB0 as [x'|].
  { apply ct_step, ST; unfolder; basic_solver. }
  pose proof H.
  apply ct_step, (wf_hbE (TruSt_Wf TS1)) in H0; unfolder in H0; desf.
  assert (acts G' y).
  { tertium_non_datur (y = e) as [|NEQ]; desf; [eby eapply G'_e|].
    eapply acts_G'; left; split; eauto; intros Del.
    eapply Da_hb_cD; unfolder; splits; vauto.
    by apply acts_G'G_cD. }
  apply ct_unit; exists y; split.
  { apply IHHB0; eauto; intros ?; subst.
    eapply Da_hb_cD; unfolder; splits; vauto.
    by apply acts_G'G_cD. }
  apply ST; unfolder; basic_solver.
Qed.

Lemma hb_Add_in_G' :
  ⦗acts G'⦘ ⨾ hb (Add G e) ⨾ ⦗acts G' ∩₁ fun x => x <> a⦘ ⊆ hb G'.
Proof using TS TS1.
  unfolder; intros x y HB.
  tertium_non_datur (y = e) as [|Nye]; desf.
  { apply hb_add_max in HB0; eauto; desf.
    { destruct HB0 as [EQ|HB0]; desf.
      { apply ct_step; left; unfold sb; basic_solver. }
      assert (hb (Add G e) e2 e) as HBe2e.
      { apply ct_step; left; unfold sb; unfolder; splits; vauto. }
      assert (NEQ := hb_e_na HBe2e).
      apply hb_e_G' in HBe2e; eauto.
      eapply hb_trans with (y := e2).
      { apply hb_in_G'; unfolder; splits; eauto. }
      apply ct_step; left; unfold sb; unfolder; splits; vauto. }
    { ins. eapply avail_sb_max; inv  TS; eauto with hahn.
      eby eapply next_avail. }
    { inv  TS. }
    { eby eapply TruSt_Wf. }
    by apply Add_hb_l in HB0. }
  eapply hb_Add_e_ne in HB0; eauto.
  { apply hb_in_G'; basic_solver. }
  { ins. eapply avail_sb_max; inv  TS; eauto with hahn.
    eby eapply next_avail. }
  { eby eapply e_not_in_G. }
  eby eapply TruSt_Wf.
Qed.

Lemma l'_order : 
  total_order_from_list l' ≡ 
  ⦗acts G \₁ D⦘ ;; total_order_from_list l ;; ⦗acts G \₁ D⦘ ∪
  (eq e) × ((fun x => In x l) ∩₁ acts G \₁ D).
Proof using TS TS1.
  assert (EL := e_not_in_l TS TS1).
  inv  TS; rewrite total_order_from_list_filterP; ins.
  unfolder; split; intros ??; rewrite total_order_from_list_cons; ins; desf.
  all: try solve [basic_solver| vauto].
  2,4,6: firstorder.
  1,3: apply total_order_from_list_in2 in H0; vauto.
  by apply total_order_from_list_in2, EL in H0.
Qed.

Lemma rf_l_hb_e y y'
  (rf_l :  (rf G ∩ total_order_from_list l) y y')
  (Day' : Da y') : 
  hb (Add G e) y e.
Proof using   TS1 TS.
  destruct rf_l as [RF L]; apply wf_rfD in RF; eauto with hahn.
  unfolder in RF; desf.
  apply Max_Da in Day'; unfold IsMaximal in Day'; desf; ins.
  specialize (Day' _ RF0); desf; [by destruct y' as [|??[]]|].
  edestruct total_order_from_list_irreflexive; [eby eapply NoDup_l|].
  eapply total_order_from_list_trans; eauto with hahn.
Qed.

Lemma rf_l_e_a : (rf G' ∩ total_order_from_list l') e a.
Proof using   TS1 TS.
  split; [inv  TS; ins; basic_solver|hahn_rewrite l'_order; right; unfolder].
  assert (H := e_not_in_l  TS).
  splits; eauto; inv  TS.
  { eapply TruSt_G_corr_ord; eauto; split; eauto.
    by destruct a as [|??[]]. }
  eby apply r_not_in_Del; eauto; eapply TruSt_NoDup.
Qed.


Lemma hb_rf_l_LR 
  (LR_l : (LR ∩ total_order_from_list l)⁻¹ ⊆ 
  (hb G )^? ;; rf G  ∩ total_order_from_list l ;; LR ∩ (total_order_from_list l )⁻¹) :
  <|acts G \₁ D|> ;; ((hb G )^? ;; rf G  ∩ total_order_from_list l  ;;
   LR ∩ (total_order_from_list l )⁻¹) ;; <|acts G \₁ D|>  ⊆
  (hb G')^? ;; rf G' ∩ total_order_from_list l' ;; LR ∩ (total_order_from_list l')⁻¹.
Proof using TS1 TS.
  intros x x' [z [[? ACT'] [w [[y [HB [y' [yRFLy' [yLRx' x'Ly']]]]][? [ACT NDx']]]]]].
  subst.
  assert (y' <> e) as y'Ne.
  { intro; desf. eby eapply total_order_from_list_in2, e_not_in_l in x'Ly'. }
  subst.
  destruct (classic (Da y')) as [Day'|NDay'].
  { assert (exists G', 
      << PS    : p_sem G'   >> /\
      << ACT1  : acts G' y' >> /\
      << ACT2  : acts G' a  >>).
    { eapply total_order_from_list_in2, TruSt_G_corr_ord in x'Ly'; eauto.
      destruct x'Ly' as [ACTy' _].
      inv  TS; cdes Next; cdes Next0.
      exists G'; splits; eauto; by apply GG'. }
    desf.
    destruct (AuxRel.total_case_split (LR_total LR PS) _ _ ACT2 ACT1) as [ya|ay].
    { exists e; split.
      right; apply hb_Add_in_G'; unfolder; splits.
      1,3: apply acts_G'; vauto.
      { destruct ACT' as [ACT' NDz].
        clear NDx'; clarify_not.
        eapply (rewrite_trans_seq_cr_l (@hb_trans (Add G e))); exists y.
        split; [generalize HB; apply inclusion_r_cr, Add_hb|].
        eapply rf_l_hb_e; eauto. }
      { intro EA; rewrite EA in  TS;
        inv  TS; by destruct a as [|??[]]. }
      exists a; split; [apply rf_l_e_a|split].
      { apply (rewrite_trans_seq_cr_l (LR_trans LR)); basic_solver. }
      hahn_rewrite l'_order; left; unfolder; splits; eauto.
      { eapply rewrite_trans_seq_cr_r.
        { intros ???; apply (total_order_from_list_trans (TruSt_NoDup TS1)). }
        exists y'; split; eauto.
        destruct Day' as [[T _]|]; vauto. }
      { inv  TS. }
      apply (r_not_in_Del (TruSt_NoDup TS1) (e_not_in_l TS TS1)). }
    destruct (LR_l a y') as [w [HB' [b []]]].
    { split; eauto; unfold Da, D, Del in Day'; unfolder in Day'; desf.
      by apply LR_irr in ay. }
    exfalso; eapply Da_hb_rf_l; esplit; split; [|esplit; eauto]; vauto. }
  apply not_or_and in NDay'; desf.
  cdes yRFLy'; eapply wf_rfE in yRFLy'0; eauto with hahn.
  unfolder in yRFLy'0; desf.
  assert (~ D y) as NDe'.
  { intro De'; eapply Del_rf_l; basic_solver. }
  exists y; split.
  { destruct HB as [|HB]; desf; vauto.
    right; apply hb_in_G'.
    unfolder; splits; eauto; try (apply acts_G'; left; split; eauto).
    { eapply wf_hbE in HB; eauto with hahn.
      unfolder in HB; desf. }
    { intros De1; eapply Da_hb_cD; unfolder; splits; vauto. }
    eapply wf_rfD in yRFLy'2; eauto with hahn; unfolder in yRFLy'2; desf.
    intro; subst; inv  TS; by destruct a as [|??[]]. }
  exists y'; unfolder; splits; eauto.
  { hahn_rewrite rf_G'; left; basic_solver. }
  { hahn_rewrite l'_order; left; basic_solver. }
  hahn_rewrite l'_order; left; basic_solver.
Qed.

Lemma rf_l_ea : 
  rf G' ∩ total_order_from_list l' ⊆ 
  singl_rel e a ∪ rf G ∩ total_order_from_list l.
Proof using   TS TS1.
  rewrite rf_G', l'_order, ?inter_union_l, ?inter_union_r.
  do 3 try apply inclusion_union_l.
  2: generalize (e_not_in_G  TS).
  all: basic_solver.
Qed.

Lemma a_in_l' : In a l'.
Proof using  TS1 TS.
  assert (H:= e_not_in_l  TS TS1).
  inv  TS; in_simp; ins; unfolder. split; [right|left]; splits; eauto.
  { apply (TruSt_G_corr_ord TS1); split; eauto.
    by destruct a as [|??[]]. }
  by apply r_not_in_Del; [eby eapply TruSt_NoDup|].
Qed.

Lemma a_in_l : In a l.
Proof using  TS1 TS.
  eapply TruSt_G_corr_ord; eauto.
  split; inv  TS; by destruct a as [|??[]].
Qed.

Lemma G'_D_a : (acts G \₁ D) a.
Proof using  TS1 TS.
  split; [inv  TS|].
  eby apply r_not_in_Del; [eapply TruSt_NoDup|eapply e_not_in_l].
Qed.

Lemma e_l'_a : 
  total_order_from_list l' e a.
Proof using  TS1 TS.
  hahn_rewrite l'_order; right; split; eauto.
  destruct G'_D_a; unfolder; splits; eauto.
  by apply a_in_l.
Qed.

Lemma Da_in_l : Da ⊆₁ (fun x => In x l).
Proof using  TS1 TS.
  assert (al := a_in_l); intros x Dax.
  unfold Da,D,Del in Dax; unfolder in Dax; desf.
  by apply total_order_from_list_in1 in Dax.
Qed.

Lemma thread_of_G' t
  (Nte : t <> tid e) : 
  sub_thread (thread_of G' t) (thread_of G t).
Proof using  TS1 TS.
  assert (acts G' ∩₁ (fun x : Event => tid x = t)
  ⊆₁ acts G ∩₁ (fun x : Event => tid x = t)) as ACT.
  { rewrite acts_G', set_inter_union_l.
    apply set_subset_union_l; basic_solver. }
  split; ins; eauto; split; [|firstorder].
  unfolder; intros e1 e2 SB; desf; splits; eauto.
  apply ext_sb_to_non_init in SB0; unfolder in SB0; desf.
  apply acts_G' in SB1; unfolder in SB1; desf; [|lia].
  apply acts_G'; left; split; eauto; intro De1.
  eapply Da_sb_cD with (x := e1) (y := e2).
  unfold sb. do 2 hahn_rewrite seqA. unfolder. splits; vauto.
Qed.

Lemma val_G' e' v
  (ACT : acts G' e'): 
  val G' e' v <-> 
    e' = a /\ valw e = v \/ val G e' v /\ e' <> a.
Proof using   TS1 TS.
  tertium_non_datur (is_r e') as [R|NR]; unfold val; desf.
  { tertium_non_datur (e' = a) as [|NA]; subst.
    { split; intro RF.
      { left; split; eauto; apply RF, rf_G'; vauto. }
      desf; intros ? RF; apply rf_G' in RF; unfolder in RF; desf. }
    split; intro RF; desf.
    { right; split; eauto; intros ? RF'.
      apply RF, rf_G'; left.
      assert (ACT' := ACT); apply acts_G' in ACT; unfolder in ACT; desf.
      { assert (acts G' w) as ACT1.
        { destruct (@G'_rf_complete e') as [x RF'']; [split; eauto|].
          apply Wf_G' in RF''; unfolder in RF''; desf.
          apply rf_G' in RF''0; unfolder in RF''0; desf.
          assert (w = x); desf; eapply (wf_rff Wf_G); eauto. }
        apply acts_G' in ACT1; unfolder in ACT1; desf.
        { basic_solver. }
        apply Wf_G in RF'; unfolder in RF'; desf.
        eby eapply e_not_in_G in RF'. }
      inv TS; by destruct e as [|??[]]. }
    intros ? RF'; apply RF; apply rf_G' in RF'; unfolder in RF'; desf. }
  assert (Ra := is_r_a); split; ins; desf.
  right; split; eauto; intro; desf.
Qed.

Lemma p_sem_G : p_sem G.
Proof using TS.
  inv TS; cdes Next; cdes Next0; eby eapply p_sem_mori.
Qed.

Lemma avail_G' e'
  (AV : avail G' e') : 
  D e'        \/
  avail G e'  \/
  ext_sb a e' \/
  ext_sb e e'.
Proof using TS1 TS.
  cdes AV.
  assert (~ is_init e') as NINI.
  { intro; apply NInG; apply wf_initE; eauto.
    apply Wf_G'. }
  assert (acts G'0 a).
  { apply GG'. apply acts_G'; left; by apply G'_D_a. }
  assert (acts G'0 e).
  { eby eapply GG', G'_e. }
  apply avail_thread in AV; desf.
  tertium_non_datur (t = tid a) as [|NT]; subst.
  { right; right; left; eapply (sb_max_same_tid SBM); eauto.
    { eby eapply p_sem_Wf. }
    { apply acts_G'; left; by apply G'_D_a. }
    apply tsem_in_thrd in TS0. apply eq_sym, TS0; vauto. }
  tertium_non_datur (t = tid e) as [|NT']; subst.
  { do 3 right; eapply sb_max_same_tid; eauto.
    { eby eapply p_sem_Wf. }
    { eby eapply G'_e. }
    apply tsem_in_thrd in TS0. apply eq_sym, TS0; vauto. }
  assert (t = tid e'); subst.
  { apply tsem_in_thrd in TS0; apply eq_sym, TS0; vauto. }
  apply thread_of_G', sub_threadE in NT'; desf.
  { right; left. apply avail_thread.
    rewrite NT' in TS0; splits.
    { apply sb_max_in_tid; eauto.
      apply sb_max_in_tid in SBM; eauto.
      by unfold sb_max; rewrite <- NT'. }
    { inv TS; cdes Next; cdes Next0.
      eby eapply p_sem_mori. }
    { intro F; apply NInG; apply NT'.
      basic_solver. }
    exists (tid e'), v; splits; eauto.
    eapply tsem_val; eauto. intros e0 T; ins.
    destruct T as [ACT|]; desf; apply NT' in ACT.
    unfolder in ACT; desf; split; intros v' V.
    { apply val_G'; eauto; right; split; eauto; intro; desf. eauto. }
    apply val_G' in V; eauto; desf; destruct NT; eauto. }
  cdes p_sem_G.
  eapply tsem_pref_clos with (val_t := val G) in TSEM; eauto.
  left; apply InDel; eauto.
  simpl in T21; unfolder in T21; desf.
  clarify_not.
  tertium_non_datur (acts G e') as [|NACT]; auto.
  apply tsem_val with 
    (val_t2 := fun x => ifP x = e' then eq (valw e') else val G x) in TSEM.
  { eapply tsem_det with (e1 := e') in TSEM; desf. eauto.
    { ins; rewrite <- sb_max_in_tid; eauto. }
    eapply tsem_val_sb_max; [| | | |apply TS0].
    { intros e0 T; ins; desf.
      { unfolder in T; desf. }
      unfolder in T; desf; split; intros v' V.
      { apply val_G'; eauto; right; split; eauto; intro; desf. eauto. }
      apply val_G' in V; eauto; desf; destruct NT; eauto. }
    { ins; rewrite <- sb_max_in_tid; eauto. }
    { rewrite (set_equiv_exp n_is_r); unfold val; basic_solver. }
    exists (valw e'); desf. }
  intros e0 T; desf; ins; unfolder in T; desf.
Qed.

End Revisit_Properties.

Section Alg_Properties.

Lemma hb_max_nr G l G' l' e
  (TS0 : TruSt G0 nil G l)
  (TS  : TruSt_step G l NR e G' l') : 
  hb_max G' e.
Proof using .
  assert (Wf G') as WF by (eapply TruSt_Wf; eby econstructor).
  split; [eby eapply G'_e|].
  split; [unfolder; intros x HB|basic_solver]; desf.
  enough (forall y, ~ (sb G' ∪ rf G') x0 y) as SBRF.
  { apply clos_trans_t1n in HB0; destruct HB0; eby eapply SBRF. }
  intros y [F|F]; [apply wf_sbE in F|apply wf_rfE in F]; unfolder in F; desf.
  { assert (acts G y) as ACT; inv TS.
    1,2: ins; unfolder in F1; desf; by apply sb_irr in F0.
    1,2: eapply (avail_sb_max _ (next_avail Next) ACT); generalize F0.
    1,2: unfold sb; basic_solver. }
  assert (acts G y) as ACT; inv TS.
  1,2: ins; unfolder in F1; desf; unfolder in F0; desf.
  { apply wf_rfD in F0; eauto with hahn; unfolder in F0; desf.
    by destruct y as [|??[]]. }
  { apply wf_rfD in F0; eauto; unfolder in F0; desf.
    by destruct x0 as [|??[]]. }
  ins; apply wf_rfE in F0; eauto with hahn; unfolder in F0; desf.
  by cdes Next; cdes Next0.
Qed.

Lemma hb_max_rv G l G' l' e a
  (TS0 : TruSt G0 nil G l)
  (TS  : TruSt_step G l (RV a) e G' l') : 
  hb_max G' a.
Proof using  .
  split; red.
  { eapply acts_G'; eauto; left.
    eapply G'_D_a; eauto. }
  split; [unfolder|basic_solver].
  intros e1 HB; desf.
  assert (exists y, (sb G' ∪ rf G') x y) as [y [SB|RF]].
  { apply clos_trans_t1n in HB0; destruct HB0; eexists; eauto. }
  { cdes SB;
    unfolder in SB0; desf.
    apply (acts_G' TS) in SB2; unfolder in SB2; desf.
    { eapply Da_hb_cD; eauto; unfolder; splits; vauto.
      apply ct_step; left; unfold sb; unfolder; splits; eauto.
      inv TS. }
    inv TS; apply Nporf, ct_step; left.
    unfold sb; ins; unfolder; splits; eauto. }
  apply wf_rfD in RF; [|eapply TruSt_Wf; eby econstructor].
  unfolder in RF; desf.
  inv TS; by destruct x as [|??[]].
Qed.


Lemma LR_init e1 e2 G (INI : is_init e1) (N : next G e2) : 
  e1 <_next e2.
Proof using.
  apply sb_LR; apply not_init_next in N; by destruct e1, e2.
Qed.

Hint Immediate LR_init : hahn.

Lemma TruSt_first_step G2 l2 e t
  (TS1 : TruSt_step G0 nil t e G2 l2) : 
  << ACT_1 : acts G2 ≡₁ is_init ∪₁ eq e    >> /\
  << t_1   : t = NR                      >> /\
  << l2_1  : l2 = e :: nil                 >> /\
  << l_1   : total_order_from_list l2 ≡ ∅₂ >> /\
  << me_1  : me G2 ≡₁ eq e                 >> /\
  << Next : next G0 e >>.
Proof using.
  assert (Wf G2) as Wf_G2.
  { eapply TruSt_Wf; vauto. }
  inv TS1; splits; ins.
  1,3: split; [|basic_solver]; intros x y F;
    apply total_order_from_list_cons in F;
    by desf; apply total_order_from_list_in1 in F.
  1,2: apply meE; split; unfold hb_max; splits.
  1,4: ins; basic_solver.
  { split; [|basic_solver]; unfolder; intros e1.
    assert 
      (forall y, acts (SetRF (Add G0 e) e w) y ->
                 ~ (sb (SetRF (Add G0 e) e w) ∪ rf (SetRF (Add G0 e) e w)) e y)
                as F_HB.
    { simpls; unfolder; intros y ACT F'; desf.
      { by apply sb_in_hb, hb_init_r in F'. }
      { by apply sb_irr in F'. }
      all: by destruct w as [|??[]]. }
    intros F; desf; apply clos_trans_t1n in F0.
    destruct F0 as [? SBRF|?? SBRF]; eapply F_HB; eauto.
    all: apply ct_step, (wf_hbE Wf_G2) in SBRF; generalize SBRF; basic_solver. }
  1,3: by simpls; unfolder; ins; desf; eauto with hahn.
  { assert 
    (forall y, acts (SetCO (Add G0 e) wp e) y ->
              ~ (sb (SetCO (Add G0 e) wp e) ∪ rf (SetCO (Add G0 e) wp e)) e y)
              as F_HB.
    { intros ? [INI|] [SB|SB]; desf; ins.
      { by apply sb_in_hb, hb_init_r in SB. }
        by apply sb_irr in SB. }
    split; [unfolder; intros ? F; desf|basic_solver].
    apply clos_trans_t1n in F0.
    destruct F0 as [? SBRF|?? SBRF]; eapply F_HB; eauto.
    all: apply ct_step, (wf_hbE Wf_G2) in SBRF; generalize SBRF; basic_solver. }
  { split; [basic_solver|unfolder; intros x [| ->]; vauto; left; splits; auto].
    clear TS1.
    unfold D0, Del; intros F; desf.
    by apply total_order_from_list_in1 in F. }
  all: by destruct r as [|??[]].
Qed.

Arguments LR_tot {_ _ _ _ _ _} _ _ _.

Lemma B23_P6 w r x G1 l1 G2 l2 e t
  (TS0 : TruSt G0 nil G1 l1)
  (TS  : TruSt_step G1 l1 t e G2 l2) :
  x <> w -> 
  x <> r ->
  (rf G2 ∩ total_order_from_list l2) w r ->
  (LR ;; <|acts G2|>) r x ->
  total_order_from_list l2 r x \/
  total_order_from_list l2 x w \/
  hb G2 x w.
Proof using.
  generalize G2 t e l2 TS; clear TS G2 t e l2.
  induction TS0.
  { intros ??????? F.
    apply TruSt_first_step in TS.
    cdes TS; desf; hahn_rewrite l_1 in F.
    generalize F. basic_solver. }
  assert (TruSt G0 nil G2 l2) as TS02 by eby econstructor.
  specialize (IHTS0 _ rv _ _ TS2).
  intros G3 ???? xNw xNr [RF L] [z [eLRx ACT]].
  assert (TruSt G0 nil G3 l0) as TS03 by eby econstructor.
  unfolder in ACT; desf.
  destruct t as [a'|].
  { tertium_non_datur (w = e0) as [|wNe0].
    { subst.
      eapply rf_G' in RF; eauto.
      unfolder in RF; desf.
      { eby eapply e_not_in_G in RF. }
      edestruct total_order_from_list_total with (a := x) (b := a') as [ax|xa]; eauto.
      { eapply TruSt_G_corr_ord; eauto.
        split; eauto; intro INI.
        eapply LR_irr, LR_trans, sb_LR; eauto.
        assert (R := is_r_a TS); destruct x; by destruct a'. }
      { eby eapply a_in_l'. }
      eapply acts_G' in ACT0; eauto.
      unfolder in ACT0; desf; clarify_not.
      { eapply l'_order in ax; eauto.
        unfolder in ax; desf. }
      eapply l'_order in ax; eauto.
      unfolder in ax; desf.
      do 2 right; eapply hb_Add_in_G'; eauto.
      unfolder; splits; eauto; try  eapply acts_G'; vauto.
      intro; subst; inv TS; by destruct a' as [|??[]]. }
    apply wf_rfD in RF; [|eapply TruSt_Wf; by do 2 (econstructor; [|eauto])].
    unfolder in RF; desf.
    tertium_non_datur (r = e0).
    { subst; inv TS; by destruct e0 as [|??[]]. }
    eapply acts_G' in ACT0; eauto; unfolder in ACT0; desf.
    { assert (L' := L).
      apply total_order_from_list_in in L; desf.
      eapply TruSt_G_corr_ord in L,L0; try by do 2 (econstructor; [|eauto]).
      unfolder in L; desf; eapply (acts_G' TS) in L; unfolder in L; desf.
      unfolder in L0; desf; eapply (acts_G' TS) in L0; unfolder in L0; desf.
      destruct IHTS0 as [T|[T|HB]]; eauto.
      { split.
        { eapply rf_G' in RF0; eauto; unfolder in RF0; desf. }
          eapply l'_order in L'; eauto.
          unfolder in L'; desf. }
      { basic_solver. }
      { left; eapply l'_order; eauto.
        unfolder; left; splits; eauto. }
      { right; left; eapply l'_order; eauto.
        unfolder; left; splits; eauto. }
      do 2 right; eapply hb_in_G'; eauto.
      unfolder; splits; eauto.
      { eapply acts_G'; vauto. }
      { eapply acts_G'; eauto; vauto. }
      apply is_r_a in TS; intro; subst; by destruct a' as [|??[]]. }
    right; left; eapply l'_order; eauto.
    right; split; eauto.
    eapply TruSt_Wf in RF0; try by do 2 (econstructor; [|eauto]).
    unfolder in RF0; desf; apply (acts_G' TS) in RF0.
    unfolder in RF0; desf.
    unfolder; splits; eauto; eapply TruSt_G_corr_ord; eauto.
    split; eauto; apply total_order_from_list_in1 in L.
    eapply TruSt_G_corr_ord in L; [by destruct L|].
    by do 2 (econstructor; [|eauto]). }
  tertium_non_datur (x = e0) as [|xNe0].
  { subst; right; left.
    inv TS; apply total_order_from_list_cons; left; split; auto.
    all: apply  total_order_from_list_cons in L; desf.
    all: by apply total_order_from_list_in1 in L. }
  tertium_non_datur (r = e0) as [|rNe0].
  { inv TS; apply total_order_from_list_cons_max in L; desf.
    all: eauto with hahn. }
  destruct IHTS0 as [T|[T|HB]]; eauto.
  { split.
    { inv TS; ins. unfolder in RF; desf. }
    edestruct hb_max_nr as [? NHB]; [|eauto|]; eauto.
    inv TS; apply total_order_from_list_cons in L; desf.
    all: exfalso; eapply NHB; unfolder; exists w, w; split; eauto.
    all: apply ct_step; vauto. }
  { exists x; split; eauto.
    split; eauto; inv TS; ins; unfolder in ACT0; desf. }
  { left; inv TS; apply total_order_from_list_cons; vauto. }
  { right; left; inv TS; apply total_order_from_list_cons; vauto. }
  by right; right; eapply hb_TruSt_step_nr; eauto.
Qed.

Arguments B23_P6 _ _ _ {G1 l1 G2 l2 e t} _ _.

Variable G1 G2 : execution.
Variable l1 l2 : list Event.
Variable e     : Event.
Variable t     : Revisit.

Hypothesis TS0 : TruSt G0 nil G1 l1.
Hypothesis TS  : TruSt_step G1 l1 t e G2 l2.

Lemma rfl_sb_sub_l : 
  (rf G2 ∩ total_order_from_list l2) ;; sb G2 ⊆ (total_order_from_list l2)⁻¹.
Proof.
  intros e1 e3 [e2 [RF SB]].
  assert (NoDup l2) as ND.
  { eapply TruSt_NoDup; vauto. }
  assert (G_ord_corr G2 l2) as GC.
  { eapply TruSt_G_corr_ord; vauto. }
  assert (cons G2) as C.
  { eapply TruSt_correct; vauto. }
  assert (TS' := TS).
  eapply B23_P6 with (x := e3) in TS; eauto.
  { destruct TS as [T|[T|HB]]; eauto.
    { destruct (@total_order_from_list_irreflexive _ _ ND e2).
      eapply total_order_from_list_trans; eauto.
      eapply TruSt_sb_l; vauto; unfolder; split; eauto.
      apply total_order_from_list_in1, GC in T.
      by destruct T. }
    destruct (cons_hb_irr _ C) with (x := e2).
    apply hb_trans with (y := e3); vauto.
    apply hb_trans with (y := e1); auto.
    destruct RF; vauto. }
  { intro; subst.
    destruct (cons_hb_irr _ C) with (x := e2).
    apply hb_trans with (y := e1); vauto.
    destruct RF; vauto. }
  { by intro; subst; apply sb_irr in SB. }
  unfold sb in SB; unfolder in SB; desf.
  apply (sb_LR LR) in SB0; basic_solver.
Qed.

Lemma TruSt_ninit_hbE : 
  <|set_compl is_init|> ;; hb G2 ⊆ 
  ((total_order_from_list l2)⁻¹)^? ;; 
  (rf G2 ∩ total_order_from_list l2)^?.
Proof.
  erewrite ninit_hbE_aux; vauto.
  rewrite rfl_sb_sub_l, TruSt_sb_l; vauto.
  rewrite unionC, <-unionA, unionK, union_absorb_r; ins.
  { rewrite <-transp_rt, rt_of_trans, ?transp_cr; ins.
    unfolder; eapply total_order_from_list_trans, TruSt_NoDup; vauto. }
  basic_solver.
Qed.

Lemma B23 : 
  << rf_l_next  : LR ∩ (rf G2 ∩ total_order_from_list l2) ≡ ∅₂ >> /\
  << TruSt_me   : me G2 ≡₁ match t with RV a => eq a | _ => eq e end >> /\
  << LR_l       : (LR ∩ total_order_from_list l2)⁻¹ ⊆ 
      (hb G2)^? ;; (rf G2 ∩ total_order_from_list l2) ;;
       LR ∩ (total_order_from_list l2)⁻¹ >> /\
  << avail_LR_l :  (me G2) × (avail G2) ⊆ LR >>  /\
  << t_rv       :
    match t with
    | RV a => 
      restr_rel ((Del (Add G1 e) l1 a e) ∪₁ eq a) (total_order_from_list l1)⁻¹
      ≡
      restr_rel ((Del (Add G1 e) l1 a e) ∪₁ eq a) LR
    | _     => True 
    end>>.
Proof using All.
  generalize G2 t e l2 TS. clear TS G2 t e l2.
  induction TS0; intro G3; ins.
  { assert (TS' := TS).
    apply TruSt_first_step in TS; cdes TS; desf; splits; eauto.
    1,2: rewrite l_1; basic_solver.
    apply avail_nr in TS'; eauto.
    unfolder; intros e1 e2 [M A]; assert (A' := A).
    apply me_1 in M; apply TS' in A. unfolder in A; desf.
    { cdes Next; specialize (Next1 _ A); desf.
      cdes A'; rewrite (set_equiv_exp ACT_1) in NInG; clarify_not. } 
    by apply sb_LR. }
  specialize (IHt t _ _ _ _ TS2 ); des.
  assert (LR ∩ (rf G3 ∩ total_order_from_list l0) ≡ ∅₂) as rf_l_next1.
  { assert (TruSt G0 nil G2 l2) as TS0'; [eby econstructor|].
    destruct t0 as [a'|]; [|by rewrite (rf_l_nr TS TS0')].
    split; [|basic_solver].
    rewrite (rf_l_ea TS TS0'), inter_union_r, rf_l_next.
    unfolder; intros eq e2 LR12.
    assert (In a' l2) as  a'l2.
    { eapply a_in_l; eauto. }
    destruct rv as [a|]; desf.
    assert (a <_next e0) as aLRe; [apply avail_LR_l|].
    { split; [by apply TruSt_me|by inv TS; cdes Next]. }
    { edestruct total_order_from_list_total with (a := a') (b := a) as [a'a|aa].
      { eauto. }
      { eapply (a_in_l' TS2 t). }
      { intro; subst; eby eapply LR_irr, LR_trans. }
      { inv TS. apply Nporf.
        assert (total_order_from_list l2 e a') as el2a'.
        { rewrite (set_equiv_exp (acts_G' TS2)) in InG.
          unfolder in InG; desf; [|inv TS2; by destruct a' as [|??[]]].
          hahn_rewrite (l'_order TS2 t); unfolder; right; splits; eauto. 
          eapply TruSt_G_corr_ord; eauto; split; eauto.
          by destruct a' as [|??[]]. }
        apply hb_trans with (y := e).
        { apply Add_hb. 
          destruct (B23_P6 e a a' t TS2) as [T| [T|HB]]; eauto.
          { inv TS2; intro; desf; by destruct e as [|??[]]. }
          { intro; desf; apply total_order_from_list_irreflexive in a'a; eauto.
            eby eapply TruSt_NoDup. }
          { by eapply (rf_l_e_a TS2 t). }
          { unfolder; split; eauto.
            eby eapply LR_trans. }
          { edestruct total_order_from_list_irreflexive with (l := l2); 
            [|eapply total_order_from_list_trans; eauto].
            all: eby eapply TruSt_NoDup. }
          edestruct total_order_from_list_irreflexive with (l := l2) (x := e).
          { eby eapply TruSt_NoDup. }
          eapply total_order_from_list_trans; eauto.
          eby eapply TruSt_NoDup. }
        assert (RFLea := rf_l_e_a TS2 t); unfolder in RFLea; desf.
        assert (~ @D G2 l2 e0 a' e) as ND.
        { intros De; eapply Del_rf_l; eauto; basic_solver. }
        unfold D, Del in ND; clarify_not. }
      destruct (LR_l a' a) as [y [HB [z []]]].
      { by split; [eby eapply LR_trans|]. }
      eapply Da_hb_rf_l; eauto; unfolder; splits; vauto. }
    edestruct (LR_tot TS e e0) as [EQ | [ee0|e0e]]; vauto.
    { left; eby eapply G'_e. }
    { apply e_not_in_G in TS; apply G'_e in TS2; auto. }
    { destruct (LR_l a' e) as [y [HB [z []]]].
      { split; [eby eapply LR_trans|].
        assert (In a' l1).
        { inv TS2; ins; desf; edestruct LR_irr;
          eby eapply LR_trans. }
        inv TS2; apply total_order_from_list_cons; vauto. }
      eapply Da_hb_rf_l; eauto; unfolder; splits; vauto. }
    eapply LR_irr, LR_trans with (x := e); eauto.
    apply avail_LR_l; split; eauto.
    { by rewrite (set_equiv_exp TruSt_me). }
    by inv TS; cdes Next; cdes Next0. }
  assert ((LR ∩ total_order_from_list l0)⁻¹
  ⊆ (hb G3)^? ⨾ rf G3 ∩ total_order_from_list l0 ⨾
     LR ∩ (total_order_from_list l0)⁻¹) as  LR_l1.
  { destruct t0 as [a'|].
    { assert (a' <_next e0).
      { edestruct (LR_tot TS a' e0) as [|[a'e0|e0a']]; vauto.
        { left; inv TS. }
        { inv TS; by destruct e0 as [|??[]]. }
        exfalso; eapply rf_l_next1; split; eauto.
        eby eapply (rf_l_e_a TS). }
      intros x x' [N T].
      hahn_rewrite (l'_order TS TS0) in T; unfolder in T.
      clear TruSt_me t_rv; desf.
      { eapply hb_rf_l_LR; eauto.
        exists x; splits; [basic_solver|].
        exists x'; splits; [|basic_solver].
        apply LR_l; basic_solver. }
      destruct (classic (x = a')) as [|xNa']; desf.
      { exfalso; eapply LR_irr, LR_trans; eauto. }
      assert (ACT' := (acts_G' TS)); generalize T1.
      clarify_not; intros T.
      { edestruct total_order_from_list_total with (a := x) (b := a') as [xa|ax];
        eauto.
        { eapply a_in_l; eauto. }
        { clarify_not. }
        eapply hb_rf_l_LR_LR; eauto.
        exists a'; split.
        { eapply hb_rf_l_LR; eauto.
          exists x; split; [|exists a'; split].
          { basic_solver. }
          { apply (LR_l); unfolder; split;
            try eapply LR_trans; eauto. }
          unfolder; split; eauto; eby eapply G'_D_a. }
        eby split; eauto; eapply e_l'_a. }
      exists x'; split.
      { right; eapply hb_Add_in_G'; eauto.
        unfolder; splits; eauto; try apply ACT'; vauto.
        intro; subst; inv TS; by destruct a' as [|??[]]. }
      exists a'; split; [eby eapply rf_l_e_a|].
      eby split; eauto; eapply e_l'_a. }
    assert (
      (hb G2)^? ⨾ rf G2 ∩ total_order_from_list l2 ⨾ LR ∩ (total_order_from_list l0)⁻¹ ⊆
      (hb G3)^? ⨾ rf G3 ∩ total_order_from_list l0 ⨾ LR ∩ (total_order_from_list l0)⁻¹
    ) as hb_hb.
    { eapply seq_mori; [eby eapply clos_refl_mori, hb_TruSt_step_nr|].
      eapply seq_mori; [by rewrite (rf_l_nr TS TS0)|].
      eapply inclusion_inter_mon; [basic_solver|].
      inv TS; unfolder; intros ???; apply total_order_from_list_cons; vauto. }
    assert (
      (hb G2)^? ⨾ rf G2 ∩ total_order_from_list l2 ⨾ LR ∩ (total_order_from_list l2)⁻¹ ⊆
      (hb G2)^? ⨾ rf G2 ∩ total_order_from_list l2 ⨾ LR ∩ (total_order_from_list l0)⁻¹
    ) as hb_hb'.
    { do 2 (eapply seq_mori; [basic_solver|]).
      eapply inclusion_inter_mon; [basic_solver|].
      inv TS; intros ???; apply total_order_from_list_cons; vauto. }
    assert (l0 = e0 :: l2); [by inv TS|subst].
    intros y e2 [N T]; apply total_order_from_list_cons in T.
    destruct T as [[EQ IN]|T].
    { apply eq_sym in EQ; subst. 
      destruct rv as [a|].
      { assert (a <_next e0) as ae0.
        { apply avail_LR_l; split; [by apply TruSt_me|].
          by inv TS; cdes Next. }
        edestruct total_order_from_list_total with (a := y) (b := a) as [ay|ya].
        { eauto. }
        { eby eapply a_in_l'. }
        { intro; subst; eapply LR_irr, LR_trans; eauto. }
        { apply (TruSt_G_corr_ord TS0) in IN; unfolder in IN; desf.
          eapply acts_G' in IN; eauto.
          apply hb_hb; exists e; split.
          { unfolder in IN; desf; vauto; eauto.
            cdes IN1.
            unfold D, Del in IN1; clarify_not.
            { hahn_rewrite (l'_order TS2 t) in ay; unfolder in ay.
              desf; vauto; destruct IN1. }
            right; eapply hb_Add_in_G'; eauto; unfolder; splits; eauto.
            { eapply acts_G'; eauto; basic_solver. }
            { eby eapply G'_e. }
            intro; subst; inv TS2; by destruct a as [|??[]]. }
          exists a; splits; eauto; [eby eapply rf_l_e_a|].
          split; eauto. apply total_order_from_list_cons; left.
          split; eauto; by apply total_order_from_list_in2 in ay. }
        eapply hb_rf_l_LR_LR; eauto.
        exists a; split.
        { apply hb_hb, hb_hb', LR_l; split; eauto.
          eby eapply LR_trans. }
        split; eauto; apply total_order_from_list_cons; left.
        by apply total_order_from_list_in1 in ya. }
      assert (e <_next e0) as e0e.
      { apply avail_LR_l; split; [by apply TruSt_me|].
        by inv TS; cdes Next. }
      eapply hb_rf_l_LR_LR; eauto.
      exists e; split.
      { apply hb_hb, hb_hb', LR_l; split; eauto.
        { eby eapply LR_trans. }
        inv TS2; apply total_order_from_list_cons; left; split; ins; desf.
        all: edestruct (LR_irr); eby eapply LR_trans. }
      split; eauto. apply total_order_from_list_cons; left.
      split; eauto. inv TS2. }
    apply hb_hb, hb_hb', LR_l; basic_solver. }
  assert (me G3 ≡₁ match t0 with RV a => eq a | NR => eq e0 end) as TruSt_me1.
  { destruct t0 as [a'|]; apply meE.
    assert (a' <> e0) as a'Ne0.
    { intro; desf; inv TS; by destruct e0 as [|??[]]. }
    { split; [by eapply hb_max_rv; [|eauto]|].
      apply NNPP; intros F; clarify_not.
      cdes F; eapply acts_G' in ACT; eauto.
      unfolder in ACT; destruct ACT as [ACT|EQ].
      { destruct ACT as [ACT NDn].
        edestruct (LR_tot TS n a') as [|[|a'n]]; vauto.
        { left; inv TS. }
        generalize NDn; clarify_not; intro NDn0.
        { rewrite <-seqA in LR_l1.
          destruct (LR_l1 n a') as [? [[? [? []]]]].
          { split; eauto.
            hahn_rewrite (l'_order TS TS0); left.
            unfolder; splits; eauto.
            { inv TS. }
            { apply r_not_in_Del; [|eby eapply e_not_in_l].
              eby eapply TruSt_NoDup. }
            edestruct total_order_from_list_total with (a := a') (b := n) as [an|na].
            { eby eapply a_in_l. }
            { eapply (TruSt_G_corr_ord TS0).
              split; eauto; intro INI.
              apply F1, sb_LR; destruct n; ins.
              assert (R := (is_r_a TS)); by destruct a'. }
            all: eauto || contradiction. }
          eapply N_HB; unfolder; exists n, n; split; eauto.
          apply (rewrite_trans_seq_cr_l (@hb_trans _)); eexists; split; eauto.
         apply ct_step; vauto. }
        eapply N_HB with (x := e0); unfolder; exists n, n; split; eauto.
        eapply hb_Add_in_G'; eauto.
        unfolder; splits; eauto.
        { by cdes F. }
        eby eapply G'_e. }
      subst; destruct (rf_l_e_a TS TS0).
      eapply N_HB; unfolder; exists n, n.
      split; eauto; apply ct_step; vauto. }
    split; [by eapply hb_max_nr; [|eauto]|].
    apply NNPP; intros F; clarify_not.
    cdes F.
    assert (acts G2 n) as G2_n.
    { inv TS; ins; destruct ACT; desf. }
    edestruct (LR_tot TS n e0) as [|[ne0|e0n]]; vauto.
    rewrite <-seqA in LR_l1.
    edestruct LR_l1 as [? [[z [? []]] _]].
    { split; eauto.
      inv TS; apply total_order_from_list_cons; left; split; eauto.
      all: apply (TruSt_G_corr_ord TS0); split; eauto.
      all: intro INI; eby eapply LR_init in INI. }
    eapply N_HB with (x := x); unfolder.
    exists n, n; split; eauto.
    apply (rewrite_trans_seq_cr_l (@hb_trans _)); eexists; split; eauto.
    apply ct_step; vauto. }
  assert (match t0 with
  | RV a =>
      restr_rel (Del (Add G2 e0) l2 a e0 ∪₁ eq a)
        (total_order_from_list l2)⁻¹
      ≡ restr_rel (Del (Add G2 e0) l2 a e0 ∪₁ eq a) LR
  | NR => True
  end) as t_rv1.
  destruct t0 as [a'|]; eauto.
  { symmetry; apply total_eqv; eauto.
    { intros ? Dax ? Day NEQ.
      eapply Da_in_l, TruSt_G_corr_ord in Dax, Day; eauto.
      unfolder in Dax; unfolder in Day.
      destruct (LR_tot TS a b); desf; vauto. }
    { assert (Dal := (Da_in_l TS TS0)); unfold Da ,D in Dal.
      rewrite <- total_transp, Dal.
      apply total_order_from_list_total. }
    { by destruct LR. }
    { eapply total_order_from_list_irreflexive, TruSt_NoDup; eauto. }
    rewrite transp_inv; split; [|basic_solver].
    intros x y [z [_ [w [LLR Dy]]]].
    apply LR_l in LLR. destruct LLR as [? [HB [x' RFL]]].
    eapply (Da_hb_rf_l TS TS0) with (x := w) (y := x'); eauto.
    exists y; split; eauto; generalize HB RFL Dy; basic_solver. }
  splits; eauto.
  intros e1 e2 [M A].
  destruct t0 as [a'|]; apply TruSt_me1, eq_sym in M; subst.
  { assert (a' <_next e0) as a'e0.
    { edestruct (LR_tot TS a' e0) as [|[a'e0|e0a']]; vauto.
      { left; inv TS. }
      { inv TS; by destruct e0 as [|??[]]. }
      exfalso; eapply rf_l_next1; split; eauto.
      eby eapply (rf_l_e_a TS). }
    eapply avail_G' in A; eauto.
    des; eauto.
    { apply t_rv1; unfolder; splits; eauto.
      unfold D, Del in A; desf. }
    inv TS; cdes Next; apply Next1 in A; des; subst; eauto.
    all: destruct LR; ins; eauto. }
  assert (A' := A).
  apply (avail_nr TS) in A; [|eby econstructor].
  destruct A as [AV|SB]; [|by apply sb_LR].
  assert (next G2 e0) as [N M] by inv TS.
  destruct (M _ AV); subst; eauto.
  cdes A'; destruct NInG; inv TS; vauto.
Qed.

Lemma codom_hbGe a (RVt : t = RV a) :
  codom_rel (<|eq e|> ;; hb G2) ≡₁ eq a.
Proof.
  assert (H := B23); desc.
  subst; destruct (rf_l_e_a TS) as [? _]; eauto.
  split.
  { assert (forall x, (sb G2 ∪ rf G2) e x -> a = x) as SBRF.
    { intros x [SB|RF].
      { inv TS; unfold sb in SB; ins; unfolder in SB.
        desc; destruct SB1; subst; desc.
        { cdes Next; eapply avail_sb_max in SB0; eauto; desf. }
        by apply ext_sb_irr in SB0. }
      assert (WF: Wf G1) by eby eapply TruSt_Wf.
      assert (~ rf G1 e x).
      { intro F; apply WF in F; unfolder in F; desc.
        inv TS; cdes Next; cdes Next0; contradiction. }
      inv TS; ins; unfolder in RF; desf. }
    intros x HB; unfolder in HB; desf.
    apply ct_step_ct in HB0; destruct HB0 as [[? [SBRF' HB]]|]; eauto 21.
    apply SBRF in SBRF'; subst; apply meE in TruSt_me.
    exfalso; eapply TruSt_me; vauto. }
  unfolder; ins; subst; exists e; splits; vauto.
Qed.

End Alg_Properties.

End AlgDef.

