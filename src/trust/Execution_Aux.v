From hahn Require Import Hahn.
Require Import Execution Events.
Require Import Util.

Set Implicit Arguments.

(******************************************************************************)
(** ** Aux defenitions  *)
(******************************************************************************)

Definition G_ord_corr G l :=
    forall e, (G.(acts) \₁ is_init) e <-> In e l.

Definition index_corr P := forall a b,
  P a /\ P b /\ tid a = tid b /\ same_index a b /\ ~ is_init a ->
       a = b.

Definition tid_init P := forall e, P e -> tid e = 0 <-> is_init e.

Declare Scope exec_scope.
Delimit Scope exec_scope with Ex.

Notation "G ⊆ G'" := (sub_execution G G') (at level 60) : exec_scope.

(******************************************************************************)
(** ** Equal executions  *)
(******************************************************************************)

Definition eq_execution G G' :=
  ⟪ EQ_ACT : acts G ≡₁ acts G' ⟫ /\
  ⟪ EQ_RF  : rf   G ≡  rf   G' ⟫ /\
  ⟪ EQ_CO  : co   G ≡  co   G' ⟫.

Lemma Wf_eq G' G
  (EQ : eq_execution G G') (WF_G : Wf G) : Wf G'.
Proof.
  destruct WF_G; unfold eq_execution in EQ; desf; split; ins; desc.
  all: rewrite <- ?EQ_ACT, <- ?EQ_RF, <- ?EQ_CO; ins.
  { rewrite <- ?(set_equiv_exp EQ_ACT) in *; eauto 8. }
  apply EQ_ACT in ACT; eauto.
Qed.

Lemma eq_execution_refl G :
  eq_execution G G.
Proof.
  unfold eq_execution; basic_solver.
Qed.

Lemma eq_execution_sym G G' :
  eq_execution G G' -> eq_execution G' G.
Proof.
  unfold eq_execution; basic_solver.
Qed.

Lemma eq_execution_trans G G' G'' :
  eq_execution G G' ->
  eq_execution G' G'' ->
  eq_execution G G''.
Proof.
  unfold eq_execution; ins; desf; splits;
    etransitivity; eassumption.
Qed.

Add Parametric Relation : (execution) (@eq_execution)
  reflexivity proved by eq_execution_refl
  symmetry proved by eq_execution_sym
  transitivity proved by eq_execution_trans
    as eq_execution_rel.

Add Parametric Morphism : sub_execution with signature
  eq_execution ==> eq_execution ==> Basics.flip Basics.impl as sub_exec_mori.
Proof.
  unfold eq_execution, sub_execution; ins; desf.
  split; splits; eauto; desf; unfold sb in DOMsb; unfold sb.
  all: by rewrite EQ_ACT0, ?EQ_ACT, ?EQ_RF0, ?EQ_RF, ?EQ_CO0, ?EQ_CO.  
Qed.

Add Parametric Morphism : sub_execution with signature
  eq_execution ==> eq_execution ==> iff as sub_exec_mor.
Proof.
  by ins; split; apply sub_exec_mori; eauto; symmetry.
Qed.

Add Parametric Morphism : Wf with signature
  eq_execution ==> iff as Wf_more.
Proof using.
  split; eauto using eq_execution_sym, Wf_eq.
Qed.

Lemma sub_execution_eq_acts G G' 
  (WF : Wf G')
  (SUB : (G ⊆ G')%Ex) 
  (ACTE : acts G ≡₁ acts G') : 
  eq_execution G G'.
Proof.
  cdes SUB; unfold eq_execution; splits; eauto.
  { rewrite SUBrf, ACTE, (wf_rfE WF). basic_solver. }
  rewrite SUBco, ACTE; by rewrite (wf_coE WF) at 2.
Qed.

(******************************************************************************)
(** **  Adding event to execution  *)
(******************************************************************************)

Definition Add G e : execution :=
  {|
    acts := G.(acts) ∪₁ eq e;
    rf   := G.(rf);
    co   := G.(co)
  |}.

Lemma Add_eq {G e} (InG : acts G e) :
  eq_execution (Add G e) G.
Proof using.
  unfold eq_execution; splits; try basic_solver.
  simpl; basic_solver.
Qed.

Add Parametric Morphism : Add with signature
  eq_execution ==> eq ==> eq_execution as Add_more.
Proof using.
  unfold eq_execution; ins; desf; splits; ins; rewrite EQ_ACT; ins.
Qed.

Lemma Add_hb {G e} : hb G ⊆ hb (Add G e).
Proof using.
  apply inclusion_t_t, inclusion_union_mon; unfold sb.
  { simpls; apply inclusion_seq_mon; try apply inclusion_seq_mon.
    all: basic_solver. }
  basic_solver.
Qed.

Lemma sb_add_max {G e e1 e2}
  (MAX_e : forall e', acts G e' -> ~ ext_sb e e'):
  sb (Add G e) e1 e2 <->
  sb G e1 e2 \/ acts G e1 /\ ext_sb e1 e2 /\ (e2 = e).
Proof using.
  unfold sb, Add; unfolder; split.
  { ins; desf; eauto 11.
    { left; exists z; splits; eauto.
      exfalso; eapply MAX_e; eauto. }
    eby exfalso; eapply ext_sb_irr. }
  ins; desf; eauto 11.
Qed.

Lemma hb_Add_e_ne G e e1 e2
  (MAX_e : forall e', acts G e' -> ~ ext_sb e e')
  (Ne : e2 <> e)
  (W : ~ acts G e)
  (Wf_G : Wf G)
  (HB : hb (Add G e) e1 e2) :
  hb G e1 e2.
Proof using.
  apply clos_trans_tn1 in HB.
  assert (forall e1 e2, e2 <> e -> (sb (Add G e) ∪ rf (Add G e)) e1 e2 ->
          (sb G ∪ rf G) e1 e2) as B.
  { intros x y ? [SB|RF]; vauto.
    left; unfold sb in *; ins; unfolder in SB; unfolder.
    by desf; splits; eauto; destruct (MAX_e y). }
  induction HB as [x SBRF|x y SBRF]; [apply ct_step|]; eauto.
  assert (x <> e) as Ney.
  { intros ?; subst; ins; destruct SBRF as [SB|RF].
    { unfold sb in SB; unfolder in SB; desf; eapply MAX_e; eauto.
      destruct SB1; basic_solver. }
    apply (wf_rfE Wf_G) in RF; unfolder in RF; desf. }
  eapply ct_ct; exists x; split; [eby eapply IHHB|].
  by eapply ct_step, B.
Qed.

Lemma hb_add_max G e e1
  (MAX_e : forall e', acts G e' -> ~ ext_sb e e')
  (W : is_w e)
  (Wf_G : Wf G)
  (ACT: acts G e1)
  (HB : hb (Add G e) e1 e) :
  exists e2,
    ⟪ ACT : acts G e2 ⟫ /\
    ⟪ HB  : (hb G)^? e1 e2 ⟫ /\
    ⟪ SB  : ext_sb e2 e ⟫.
Proof using.
  apply clos_trans_t1n in HB.
  remember e as e' eqn:Hee'; generalize Hee'.
  induction HB as [x y SBRF|x y z SBRF]; intros; subst.
  { simpls; unfolder in SBRF; desf.
    { eapply (sb_add_max MAX_e) in SBRF; desf.
      { exists x; splits; vauto. unfold sb in SBRF; unfolder in SBRF; desf. }
      exists x; splits; vauto. }
    apply (wf_rfD Wf_G) in SBRF; unfolder in SBRF; desf.
    by destruct e as [|??[]]. }
  simpls; unfolder in SBRF; desf.
  { apply (sb_add_max MAX_e) in SBRF; desf.
    { destruct IHHB as [z H]; eauto; desf.
      { apply wf_sbE in SBRF; unfolder in SBRF; desf. }
      exists z; splits; eauto.
      eapply (transitive_cr (@hb_trans G)); [|eauto].
      right; apply ct_step; vauto. }
    exists x; basic_solver. }
  apply wf_rfE in SBRF; unfolder in SBRF; desf.
  destruct IHHB as [z H]; eauto; desf.
  exists z; splits; eauto.
  eapply (transitive_cr (@hb_trans G)); [|eauto].
  right; apply ct_step; vauto.
Qed.

(******************************************************************************)
(** **  Deleted Set  *)
(******************************************************************************)

Definition Del G l r w : Event -> Prop :=
  fun e =>
    total_order_from_list l e r /\ ~ hb G e w.

Lemma r_not_in_Del G l r w
  (_ : NoDup l)
  (_ : ~ In w l) :
  ~ Del (Add G w) l r w r.
Proof using.
  unfold Del; intros F; desf.
  apply total_order_from_list_irreflexive in F; eauto using NoDup.
Qed.

(******************************************************************************)
(** ** Execution restriction *)
(******************************************************************************)


Definition Restr G D : execution :=
  {|
    acts := G.(acts) ∩₁ D;
    rf   := ⦗D⦘ ⨾ G.(rf) ⨾ ⦗D⦘;
    co   := ⦗D⦘ ⨾ G.(co) ⨾ ⦗D⦘;
  |}.

Lemma Wf_Restr G D
  (Ninit : is_init ⊆₁ D)
  (WF : Wf G) :
  Wf (Restr G D).
Proof using.
  destruct WF; split; ins; desf.
  all: try basic_solver.
  { apply wf_index; splits; unfold set_inter in *; desf. }
  { rewrite wf_rfE at 1; unfolder; splits; ins; desf; eauto. }
  { rewrite wf_rfD at 1; unfolder; splits; ins; desf; eauto. }
  { rewrite wf_coE at 1; unfolder; splits; ins; desf; eauto. }
  { rewrite wf_coD at 1; unfolder; splits; ins; desf; eauto. }
  { unfolder; ins; desf.
    cut (co G a b \/ co G b a); ins; desf; try basic_solver.
    eapply (wf_co_total (loc a)); basic_solver. }
  { unfolder; split; ins; desf; apply (eq_in_l wf_co_init x y); basic_solver. }
  apply wf_tid_init; by cdes ACT.
Qed.

Lemma sb_Restr G D: sb (Restr G D) ≡ ⦗D⦘ ⨾ sb G ⨾ ⦗D⦘.
Proof using.
  by unfold sb; ins; rewrite set_interC at 1; rewrite !id_inter, !seqA.
Qed.

Lemma Restr_eq_exec G G' 
  (SUB : (G ⊆ G')%Ex)
  (Wf_G : Wf G) : 
  eq_execution (Restr G' (acts G)) G.
Proof using.
  cdes SUB.
  unfold eq_execution; splits; ins; [basic_solver| |by symmetry].
  by rewrite (wf_rfE Wf_G), SUBrf, ?seqA, <-id_inter, set_interK.
Qed.

Lemma Restr_union G G' D
  (WF : Wf G)
  (SUB : (G ⊆ G')%Ex) :
  (G ⊆ Restr G' (acts G ∪₁ D))%Ex.
Proof using.
  cdes SUB.
  assert (acts G ∩₁ (acts G ∪₁ D) ≡₁ acts G) as ACT.
  { basic_solver. }
  unfold sub_execution; splits; ins.
  { basic_solver. }
  { rewrite ?seqA, seq_eqvC.
    rewrite <-(seqA (rf G') _ _), <-SUBrf, (wf_rfE WF).
    rewrite <-?seqA, <-id_inter, ?seqA, <-id_inter.
    by rewrite set_interC, ?ACT. }
  { rewrite <-?seqA, <-id_inter, ?seqA, <-id_inter.
    by rewrite ACT, set_interC, ACT. }
  rewrite sb_Restr, ?seqA, dom_eqv1, seq_eqvC, <-seqA.
  rewrite dom_seq, DOMsb; basic_solver.
Qed.

Lemma Resrt_in_G G D 
  (Wf_G : Wf G): 
  eq_execution (Restr G D) (Restr G (acts G ∩₁ D)).
Proof.
  unfold eq_execution; splits; ins; [basic_solver| |].
  { rewrite (wf_rfE Wf_G) at 1. basic_solver. }
  rewrite (wf_coE Wf_G) at 1. basic_solver.
Qed.


Lemma Restr_clos_sub G D
  (Wf_G : Wf G)
  (INID : is_init ⊆₁ D)
  (hb_clos : dom_rel (hb G ;; <|D|>) ⊆₁ D) : 
  (Restr G D ⊆ G)%Ex.
Proof using.
  assert (acts G ∩₁ (acts G ∩₁ D) ≡₁ acts G ∩₁ D) as ACT.
  { basic_solver. }
  unfold sub_execution; splits; ins.
  { basic_solver. }
  { rewrite (wf_rfE Wf_G), ?seqA, <-id_inter.
    rewrite <-seqA, <-?id_inter, ACT.
    split; [basic_solver|].
    unfolder; intros e1 e2 RF; desf; splits; eauto.
    apply hb_clos; unfolder; exists e2, e2; splits; eauto.
    apply ct_step; vauto. }
  { rewrite (wf_coE Wf_G) at 1.
    rewrite ?seqA, <-id_inter, <-?seqA, <-id_inter.
    basic_solver. }
  { apply set_subset_inter_r; split.
    { unfold sb; basic_solver. }
    etransitivity; [|apply hb_clos]; unfolder; ins; desf.
    eexists; splits; eauto; apply ct_step; vauto. }
  { rewrite dom_eqv1, set_interC.
    apply set_subset_inter; eauto.
    rewrite (wf_rfE Wf_G), seqA, dom_eqv1; basic_solver. }
  by apply set_subset_inter_r; splits; [apply Wf_G|].
Qed.


(******************************************************************************)
(** ** Value Relation  *)
(******************************************************************************)


Definition val G e v := 
  if is_r e then 
    forall w, rf G w e -> valw w = v
  else valw e = v.

Lemma val_r G r
  (R : is_r r)
  (ACT : acts G r)
  (Wf_G : Wf G)
  (RFC : rf_complete G) :
  exists v, val G r ≡₁ eq v.
Proof.
  destruct (RFC r) as [w RF]; [basic_solver|].
  exists (valw w); unfold val; desf; split; intros e RF'.
  { by apply RF'. }
  ins; desf; eby eapply f_equal, (wf_rff Wf_G).
Qed.

Lemma sub_execution_val G G' e 
  (SUB : (G ⊆ G')%Ex) 
  (InG : acts G e) : 
  val G e ≡₁ val G' e.
Proof.
  cdes SUB.
  unfolder; unfold val; split; intro; desf.
  { intros F w RF; apply F, SUBrf; basic_solver. }
  intros F w RF; apply F; apply SUBrf in RF; unfolder in RF; desf.
Qed.

(******************************************************************************)
(** **  Sub-executions  *)
(******************************************************************************)


Lemma sub_execution_sbrf G G' e e'
  (Wf_G : Wf G)
  (InG : acts G e)
  (SUB : (G ⊆ G')%Ex) 
  (SBRF : (sb G' ∪ rf G') e' e) : 
  acts G e'.
Proof using.
  cdes SUB.
  assert ((sb G ∪ rf G) e' e) as SBRFG.
  { hahn_rewrite SUBrf.
    hahn_rewrite (sub_execution_sb SUB).
    hahn_rewrite <- seq_union_l. basic_solver. }
  destruct SBRFG as [HI|HI]; [apply wf_sbE in HI|apply wf_rfE in HI];
  unfolder in HI; desf.
Qed.

Lemma sub_execution_hb G G' e e'
  (Wf_G : Wf G)
  (InG : acts G e)
  (SUB : (G ⊆ G')%Ex) 
  (HB : hb G' e' e) : 
  acts G e'.
Proof using.
  apply clos_trans_t1n in HB.
  induction HB as [?? HB|??? HB]; [eapply sub_execution_sbrf in HB|]; eauto.
  eapply sub_execution_sbrf in HB; eauto.
Qed.

Lemma sub_execution_refl G (Wf_G : Wf G) : (G ⊆ G)%Ex.
Proof using.
  destruct Wf_G.
  split; splits; eauto.
  1,3: rewrite wf_rfE; basic_solver.
  unfold sb; rewrite seqA, dom_seq; basic_solver.
Qed.

Lemma sub_execution_sbrfE G G' 
  (SUB : (G ⊆ G')%Ex) : 
  sb G ∪ rf G ≡ (sb G' ∪ rf G') ;; <|acts G|>.
Proof.
  cdes SUB.
  rewrite (sub_execution_sb SUB), SUBrf; basic_solver.
Qed.

Lemma wf_sbrfE G (WF: Wf G): 
  sb G ∪ rf G ≡ <|acts G|> ;; (sb G ∪ rf G) ;; <|acts G|>.
Proof.
  by rewrite wf_sbE, wf_rfE, <- seq_union_r, <- seq_union_l at 1.
Qed.


Lemma sub_execution_hbE G G' 
  (Wf_G' : Wf G')
  (SUB : (G ⊆ G')%Ex) : 
  hb G ≡ hb G' ;; <|acts G|>.
Proof.
  assert (Wf G).
  { eby eapply sub_execution_wf. }
  split.
  { by unfold hb; rewrite (sub_execution_sbrfE SUB), inclusion_ct_seq_eqv_r. }
  intros e1 e2 HB.
  unfolder in HB; desf.
  apply clos_trans_tn1 in HB; apply clos_tn1_trans.
  induction HB as [? SBRF|].
  { constructor; eapply sub_execution_sbrfE; basic_solver. }
  assert (((sb G' ∪ rf G') ;; <|acts G|>) y z) as SBRF by basic_solver.
  apply sub_execution_sbrfE, wf_sbrfE in SBRF; eauto.
  assert (acts G y/\(sb G ∪ rf G) y z) as S by (unfolder in SBRF; desf; vauto).
  desf; vauto; specialize (IHHB S); vauto.
Qed.

(* ************************************************************************* *)
(*                                 SetRF                                     *)
(* ************************************************************************* *)

Implicit Type l : list Event.
Implicit Type D : Event -> Prop.

Definition SetRF G r w : execution :=
  {|
    acts := G.(acts);
    rf   := G.(rf) ⨾ ⦗ fun e' => e' <> r ⦘ ∪ singl_rel w r ;
    co   := G.(co)
  |}.

Add Parametric Morphism : SetRF with signature
  eq_execution ==> eq ==> eq ==> eq_execution as SetRF_more.
Proof using.
  unfold eq_execution; ins; desf; splits; ins; rewrite EQ_RF; ins.
Qed.

Lemma Wf_SetRF' G' G r w
  (GG' : acts G ⊆₁ acts G')
  (InG' : acts G' r)
  (TI : tid_init (acts G'))
  (IC : index_corr (acts G'))
  (R : is_r r) (W : is_w w) (SL : same_loc w r) (WF : Wf G)
  (InGw : acts G w) :
  Wf (SetRF (Add G r) r w).
Proof using.
  split; unfold SetRF; ins; unfolder in *.
  all: try by (destruct WF; eauto).
  4-5: (destruct WF; basic_solver).
  { desf.
    { eby eapply wf_index. }
    { apply IC; splits; eauto; apply GG'. }
    apply IC; splits; eauto. }
  { split; ins; desf; splits; eauto; left.
    all: apply (eq_in_l (wf_rfE WF)) in H; unfolder in *; desf. }
  { split; ins; desf; splits; eauto.
    all: apply (eq_in_l (wf_rfD WF)) in H; unfolder in *; desf. }
  { split; ins; splits; desf; left.
    all: apply (eq_in_l (wf_coE WF)) in H; unfolder in *; desf. }
  { split; ins; splits; desf; auto.
    1-2: apply (eq_in_l (wf_coD WF)) in H; unfolder in *; desf. }
  { ins; desf; destruct WF; unfolder in wf_co_total.
    { apply wf_co_total with (x := loc b); eauto. }
    { unfold is_w, is_r in *; destruct a; try destruct l; basic_solver. }
    unfold is_w, is_r in *; destruct b; try destruct l; basic_solver. }
  { destruct WF; by unfolder in wf_co_init. }
  destruct WF; desf; [basic_solver|].
  by apply TI.
Qed.

Lemma Wf_SetRF G' G r w
  (GG' : acts G ⊆₁ acts G')
  (InG' : acts G' r)
  (Wf_G' : Wf G')
  (R : is_r r) (W : is_w w) (SL : same_loc w r) (WF : Wf G)
  (InGw : acts G w) :
  Wf (SetRF (Add G r) r w).
Proof using.
  eapply Wf_SetRF'; eauto; by destruct Wf_G'.
Qed.

Lemma SetRF_rf_complete G (COM : rf_complete G) w r :
  rf_complete (SetRF (Add G r) r w).
Proof using.
  unfold rf_complete, SetRF in *; simpls; unfolder in *; ins; desf.
  2: exists w; eauto.
  tertium_non_datur (x = r) as [|N]; desf.
  { exists w; eauto. }
  by edestruct COM; eauto.
Qed.

Lemma sb_SetRF G r w: sb (SetRF G r w) ≡ sb G.
Proof using. ins. Qed.

Lemma sub_exec_SetRF G w r 
  (NGw' : ~ acts G r)
  (MAX_e : forall e', acts G e' -> ~ ext_sb r e')
  (Wf_G : Wf G) : 
  (G ⊆ SetRF (Add G r) r w)%Ex.
Proof using.
  unfold sub_execution; splits; ins.
  { basic_solver. }
  { rewrite seq_union_l, seqA, <-id_inter.
    assert ((fun e' => e' <> r) ∩₁ acts G ≡₁ acts G) as ACT.
    { unfolder; split; ins; desf; splits; eauto; intro; desf. }
    assert (singl_rel w r ⨾ ⦗acts G⦘ ≡ ∅₂) as ACT'.
    { unfolder; splits; [ins; desf|basic_solver]. }
    rewrite ACT, ACT', union_false_r, (wf_rfE Wf_G); basic_solver. }
  { rewrite (wf_coE Wf_G) at 1. basic_solver. }
  { rewrite sb_SetRF; unfolder; intros e1 SB; desf.
    apply (sb_add_max MAX_e) in SB; desf.
    unfold sb in SB; unfolder in SB; desf. }
  { rewrite (wf_rfE Wf_G). basic_solver. }
  by destruct Wf_G.
Qed.

Lemma val_SetRF G r w 
  (R : is_r r): 
  forall e v, val (SetRF G r w) e v <-> 
  (fun x => ifP x = r then eq (valw w) else val G x) e v.
Proof.
  ins; unfold val; ins.
  tertium_non_datur (e = r) as [|NEQ]; desf.
  { unfolder; split; intro F.
    { apply F; vauto. }
    ins; desf. }
  unfolder; split; intros F ? RF; desf; apply F; vauto.
Qed.

Lemma sub_sub_exec_SetRF G G' r w 
  (Wf_G : Wf G)
  (SUB : (G ⊆ G')%Ex)
  (NInG : ~ acts G r) : 
  (G ⊆ SetRF G' r w)%Ex.
Proof using.
  cdes SUB; unfold sub_execution; splits; eauto.
  ins.
  rewrite seq_union_l, seqA, <-id_inter.
  assert ((fun e' => e' <> r) ∩₁ acts G ≡₁ acts G) as ACT.
  { unfolder; split; ins; desf; splits; eauto; intro; desf. }
  assert (singl_rel w r ⨾ ⦗acts G⦘ ≡ ∅₂) as ACT'.
  { unfolder; splits; [ins; desf|basic_solver]. }
  by rewrite ACT, ACT', union_false_r.
Qed.

(* ************************************************************************* *)
(*                                SetCO                                      *)
(* ************************************************************************* *)

Lemma Wf_co_actsl G w w' (WF : Wf G) (CO : co G w' w) :
  acts G w'.
Proof using.
  destruct WF; apply (eq_in_l wf_coE) in CO.
  by unfolder in CO; basic_solver.
Qed.

Lemma Wf_co_actsr G w w' (WF : Wf G) (CO : co G w w'):
  acts G w'.
Proof using.
  destruct WF; apply (eq_in_l wf_coE) in CO.
  by unfolder in CO; desf; eauto.
Qed.

Definition SetCO G w w' : execution :=
  {|
    acts := G.(acts);
    rf   := G.(rf);
    co   := into_rel (co G) w w'
  |}.

Add Parametric Morphism : SetCO with signature
  eq_execution ==> eq ==> eq ==> eq_execution as SetCO_more.
Proof using.
  unfold eq_execution; ins; desf; splits; ins; rewrite EQ_CO; ins.
Qed.

Lemma not_in_Wf_Ninit G e (WF : Wf G) (_ : ~ acts G e) :
  ~ is_init e.
Proof using.
  destruct WF; desf; eauto.
Qed.

Lemma Wf_SetCO' G' G w w'
  (NInG : ~ acts G w')
  (GG' : acts G ⊆₁ acts G')
  (InG' : acts G' w')
  (TI : tid_init (acts G'))
  (IC : index_corr (acts G'))
  (SL : same_loc w w')
  (W : is_w w) (W' : is_w w') (WF : Wf G)
  (InGw : acts G w) : Wf (SetCO (Add G w') w w').
Proof using.
  assert (WF' := WF).
  split; unfold SetCO; ins; unfolder in *; destruct WF; eauto;
  unfold into_rel.
  { desf.
    { by apply wf_index. }
    { apply IC; splits; eauto; apply GG'. }
    apply IC; splits; eauto. }
  { split; ins; desf; splits; eauto; try left.
    all: apply (eq_in_l wf_rfE) in H; unfolder in *; desf. }
  { split; ins; desf; splits; eauto.
    all: apply (eq_in_l wf_rfD) in H; unfolder in *; desf. }
  { split; ins; desf; splits; eauto; left.
    1-3: apply (eq_in_l wf_coE) in H; unfolder in *; desf.
    apply (eq_in_l wf_coE) in H0; unfolder in *; desf. }
  { split; ins; desf; splits; eauto.
    1-3: apply (eq_in_l wf_coD) in H; unfolder in *; desf.
    apply (eq_in_l wf_coD) in H0; unfolder in *; desf. }
  { ins; desf; eauto.
    { eapply (@same_loc_trans x w); eauto. }
    eapply eq_sym, (@same_loc_trans y w); eauto.
    by apply eq_sym, wf_col. }
  { apply into_rel_trans; eauto; ins.
    { by intros CO; apply Wf_co_actsr in CO. }
    by intros CO; apply Wf_co_actsl in CO. }
  { ins; desf.
    { cut (co G a b \/ co G b a).
      { intro CO; desf; vauto. }
      by eapply wf_co_total. }
    { tertium_non_datur (w = b) as [|NEQwb]; desf; eauto 7.
      cut (co G w b \/ co G b w).
      { intro CO; desf; eauto 7. }
      eapply (wf_co_total (loc a)); basic_solver. }
    tertium_non_datur (w = a) as [|NEQwb]; desf; eauto 7.
      cut (co G w a \/ co G a w).
      { intro CO; desf; eauto 7. }
      eapply (wf_co_total (loc b)); basic_solver. }
  { apply into_rel_irr; eauto; ins.
    { by intros CO; apply Wf_co_actsr in CO. }
    { by intros CO; apply Wf_co_actsl in CO. }
    intro WW'; subst; eauto. }
  { split; ins; desf.
    1,4: unfolder in wf_co_init; desf; basic_solver.
    all: eapply not_in_Wf_Ninit; eauto. }
  desf; try basic_solver.
Qed.

Lemma Wf_SetCO G' G w w'
  (NInG : ~ acts G w')
  (GG' : acts G ⊆₁ acts G')
  (InG' : acts G' w')
  (Wf_G' : Wf G')
  (SL : same_loc w w')
  (W : is_w w) (W' : is_w w') (WF : Wf G)
  (InGw : acts G w) : Wf (SetCO (Add G w') w w').
Proof using.
  eapply Wf_SetCO'; eauto; by destruct Wf_G'.
Qed.

Lemma SetCO_rf_complete G (COM : rf_complete G) w w'
  (W : is_w w') :
  rf_complete (SetCO (Add G w') w w').
Proof using.
  unfold rf_complete in *; simpls; unfolder in *; ins; desf.
  { edestruct COM; eauto. }
  destruct x; desf; by destruct l.
Qed.

Lemma sb_SetCO G r w: sb (SetCO G r w) ≡ sb G.
Proof using. done. Qed.

Lemma hb_SetCO G r w: hb (SetCO G r w) ≡ hb G.
Proof using. done. Qed.

Lemma sub_exec_SetCO G w w' 
  (NGw' : ~ acts G w')
  (MAX_e : forall e', acts G e' -> ~ ext_sb w' e')
  (Wf_G : Wf G) : 
  (G ⊆ SetCO (Add G w') w w')%Ex.
Proof using.
  unfold sub_execution; splits; ins.
  { basic_solver. }
  { rewrite (wf_rfE Wf_G); basic_solver. }
  { rewrite (wf_coE Wf_G) at 1.
    split; intros e1 e2 CO; unfolder in CO; desf; unfolder; splits; vauto.
    unfold into_rel in CO0; desf. }
  { rewrite sb_SetCO; unfolder; intros e1 SB; desf.
    apply (sb_add_max MAX_e) in SB; desf.
    unfold sb in SB; unfolder in SB; desf. }
  { rewrite (wf_rfE Wf_G). basic_solver. }
  by destruct Wf_G.
Qed.

Lemma sub_sub_exec_SetCO G G' r w 
  (Wf_G : Wf G)
  (SUB : (G ⊆ G')%Ex)
  (NInG : ~ acts G r) : 
  (G ⊆ SetCO G' w r)%Ex.
Proof using.
  cdes SUB; unfold sub_execution; splits; eauto; ins.
  rewrite SUBco; split.
  { unfolder. firstorder. }
  unfolder; intros ?? CO; desf; splits; eauto.
  unfold into_rel in CO0; desf.
Qed.

Lemma SetCORF G r wp w :
  SetCO (SetRF G r w) wp w =
  SetRF (SetCO G wp w) r w.
Proof using.
  ins.
Qed.

Lemma val_SetCO G w w'
  (R : is_w w'): 
  forall e v, val (SetCO (Add G w') w w') e v <-> val G e v.
Proof.
  ins.
Qed.

(* ************************************************************************* *)
(*                             Empty execution                               *)
(* ************************************************************************* *)

Definition G0 :=
  {|
    acts := is_init;
    rf   := ∅₂;
    co   := ∅₂;
  |}.

Lemma Wf_G0: Wf G0.
Proof using.
  split; unfolder; splits; ins; desf.
  { destruct a, b; basic_solver. }
  by destruct e; basic_solver.
Qed.

Lemma nil_acts G 
  (WF : Wf G) 
  (NACT : acts G ≡₁ is_init) : 
  eq_execution G G0.
Proof.
  unfold eq_execution; splits; ins.
  { rewrite <-(rf_ninit WF), NACT; basic_solver. }
  rewrite <-(co_ninit WF), NACT; basic_solver.
Qed.

(******************************************************************************)
(** **  Maximal elements  *)
(******************************************************************************)

Definition hb_max G e := 
  << ACT  : acts G e >> /\ 
  << N_HB : codom_rel (<|eq e|> ;; hb G) ≡₁ ∅ >>.

Definition sbrf_max G e := 
  << ACT  : acts G e >> /\ 
  << N_HB : codom_rel (<|eq e|> ;; (sb G ∪ rf G)) ≡₁ ∅ >>.


Lemma hb_maxE G : hb_max G ≡₁ sbrf_max G.
Proof using.
  split.
  1,2: unfold sbrf_max, hb_max; intros e ?; desf.
  1,2: split; eauto; split; [|basic_solver].
  { intros e' HB; apply N_HB; generalize HB. 
    by apply codom_rel_mori, seq_mori, ct_step. }
  unfolder; intros e' HB; desf.
  apply clos_trans_t1n in HB0.
  destruct HB0; eapply N_HB; unfolder; eauto.
Qed.

Lemma sub_execution_hb_max G G' e 
  (WF : Wf G')
  (SUB : sub_execution G G')
  (HBM : hb_max G' e)
  (ACT : acts G e) : 
  hb_max G e.
Proof.
  apply hb_maxE; apply hb_maxE in HBM.
  split; auto; red.
  split; [|basic_solver].
  assert (sb G ⊆ sb G') as SB.
  { rewrite sub_execution_sb; basic_solver. }
  assert (rf G ⊆ rf G') as RF.
  { cdes SUB; rewrite SUBrf; basic_solver. }
  rewrite SB, RF; by apply HBM.
Qed.

Lemma hb_max_Restr G D e
  (De  : D e)
  (HBM : ~ hb_max G e)
  (NHBM : hb_max (Restr G D) e) : 
  exists d, ~ D d /\ (sb G ∪ rf G) e d.
Proof.
  apply hb_maxE in NHBM; cdes NHBM.
  rewrite (set_equiv_exp (hb_maxE _)) in HBM. 
  clarify_not; ins.
  { generalize HBM ACT; basic_solver. }
  destruct HBM as [? [y [EQ SBRF]]]; unfolder in EQ; desf.
  eexists; split; eauto; intro F.
  eapply N_HB with (x := n).
  exists y,y; split; [basic_solver|].
  hahn_rewrite sb_Restr.
  hahn_rewrite <- seq_union_r.
  hahn_rewrite <- seq_union_l.
  unfolder in ACT; desf. basic_solver.
Qed.

Lemma hb_max_ex G e s 
  (WF : Wf G)
  (FIN : acts G \₁ is_init ⊆₁ (fun x : Event => In x s))
  (HBIRR : irreflexive (hb G))
  (ACT : acts G e) : 
  exists m, 
    << HBxm : (hb G)^? e m >> /\
    << HBMm : hb_max G m   >>.
Proof.
  assert (acyclic (hb G)) as AC.
  { intros ? HB; eapply (proj1 (ct_of_ct _)), HBIRR in HB; eauto. }
  destruct (@last_exists _ (e :: s) (hb G) AC e) as [x HB]; desf.
  { intros ? HB; unfold hb in HB.
    apply (proj1 (rt_of_ct _)), cr_of_ct in HB.
    destruct HB as [HB|HB]; desf; vauto; right.
    apply FIN; split.
    { apply (wf_hbE WF) in HB; unfolder in HB; desf. }
    intro. apply hb_init_r in HB; eauto. }
  apply (proj1 (rt_of_ct _)), cr_of_ct in HB.
  exists x; splits; eauto.
  split; eauto.
  { destruct HB as [|HB]; desf; eauto.
    apply (wf_hbE WF) in HB; unfolder in HB; desf. }
  red; generalize HB0. basic_solver.
Qed.

(******************************************************************************)
(** **  Lemmas about threads  *)
(******************************************************************************)

Implicit Type tr : Event -> Prop.

Definition thread_of G t := acts G ∩₁ (fun x => tid x = t).
Arguments thread_of /.

Definition sub_thread (tr1 tr2 : Event -> Prop) := 
  << SUBev : tr1 ⊆₁ tr2 >> /\
  << SUBsb : <|tr2|> ;; ext_sb ;; <|tr1|> ≡ <|tr1|> ;; ext_sb ;; <|tr1|> >>.

Definition sb_max tr1 t := <|eq t|> ;; ext_sb ;; <|tr1|> ≡ ∅₂.

Lemma hb_max_sb_max G e
  (HBM : hb_max G e) :
  sb_max (acts G) e.
Proof.
  cdes HBM.
  unfold sb_max; split; [|basic_solver].
  intros ?? SB; eapply N_HB.
  unfolder in SB; desf.
  exists x, x; splits; [basic_solver|].
  apply ct_step; left; unfold sb; basic_solver.
Qed.

Lemma sb_max_subset P1 P2 
  (SUB : P1 ⊆₁ P2) :
  sb_max P2 ⊆₁ sb_max P1 .
Proof.
  unfold sb_max.
  intros ? []; split; [|basic_solver].
  by rewrite SUB.
Qed.

Lemma sub_execution_thread t G G' 
  (SUB : (G ⊆ G')%Ex): 
  sub_thread (thread_of G t) (thread_of G' t).
Proof.
  cdes SUB; ins; apply sub_execution_sb in SUB.
  split; red; [by rewrite SUBev|].
  rewrite ?id_inter. 
  setoid_rewrite seq_eqvC at 1 3.
  rewrite ?seqA; apply seq_more; eauto.
  rewrite <-?seqA; apply seq_more; eauto.
  rewrite ?seqA; rewrite SUB; unfold sb; rewrite ?seqA, <-id_inter.
  do 2 (apply seq_more; eauto).
  by rewrite set_interC, (set_inter_absorb_r SUBev).
Qed.

Lemma index_corr_ex G 
  (TIC : forall t, index_corr (thread_of G t)) :
  index_corr (acts G).
Proof.
  intros e1 e2; intro I; desf.
  specialize (TIC (tid e1) e1 e2); apply TIC; splits; eauto; basic_solver.
Qed.

Lemma tid_init_union (P1 P2 : Event -> Prop)
  (T1 : tid_init P1)
  (T2 : tid_init P2) :
  tid_init (P1 ∪₁ P2).
Proof. intros ? []; basic_solver. Qed.

Lemma sub_execution_thread_e G G' e
  (WF : Wf G)
  (GG' : (G ⊆ G')%Ex)
  (HB  : forall e', hb G' e' e -> acts G e')
  (InG': acts G' e)
  (NInG: ~ acts G e) :
  sub_thread (thread_of G (tid e) ∪₁ eq e) (thread_of G' (tid e)) .
Proof.
  split; ins.
  { apply set_subset_union_l; split.
    { apply set_subset_inter; eauto; apply GG'. }
    basic_solver. }
  assert (SUB := GG').
  apply sub_execution_thread with (t := tid e) in GG'.
  cdes GG'; ins; red.
  rewrite <-restr_relE, restr_set_union.
  assert (restr_rel (eq e) ext_sb ≡ ∅₂) as IRR.
  { generalize (ext_sb_irr e); basic_solver. }
  rewrite IRR, union_false_r.
  assert 
    (⦗eq e⦘ ⨾ ext_sb ⨾ ⦗acts G ∩₁ (fun x : Event => tid x = tid e)⦘ ≡
    ∅₂) as ESB.
  { split; [|basic_solver].
    unfolder; intros e1 e2 F; desf.
    eapply NInG, sub_execution_hb, ct_step; eauto.
    left; unfold sb; unfolder; splits; eauto.
    by apply SUB. }
  rewrite ESB, union_false_r.
  rewrite id_union, ?seq_union_r, SUBsb, <- restr_relE.
  apply union_more; eauto; split.
  { unfolder; intros ?? SB; desf; splits; eauto.
    apply HB, ct_step; left; unfold sb; unfolder; splits; eauto. }
  apply seq_mori; rewrite ?SUBev; basic_solver.
Qed.

Lemma sb_max_in_tid P e'
  (NINI : ~ is_init e') :
  sb_max P e' <->
  sb_max (P ∩₁ (fun x => tid x = tid e')) e'.
Proof.
  unfold sb_max; ins; split; [basic_solver|].
  intro SB; rewrite <- SB; split; [|basic_solver].
  unfolder; intros ?? SB'; desf; splits; eauto.
  apply ext_sb_tid_init in SB'0; desf.
Qed.

Lemma sub_threadE t1 t2 
  (SBT : sub_thread t1 t2) : 
  t1 ≡₁ t2 \/
  exists e', 
  << T21  : (t2 \₁ t1) e' >> /\
  << SBM  : sb_max t1 e'  >> /\
  << TSEM : sub_thread (t1 ∪₁ eq e') t2 >>.
Proof.
  cdes SBT.
  destruct (classic (t2 \₁ t1 ≡₁ ∅)) as [T|T].
  { left. apply set_subsetE in T; split; eauto. }
  specialize (wf_impl_min_elt wf_ext_sb T); intro M; desf.
  right; eexists; splits; eauto.
  { split; [|basic_solver]; unfolder; intros ?? SB; desf.
    destruct M as [T2 T1]; apply T1.
    cdes SUBsb. destruct (SUBsb0 x y) as [? T']; [basic_solver|].
    unfolder in T'; desf. }
  split; red.
  { generalize M; basic_solver. }
  split.
  { rewrite id_union at 1; rewrite ?seq_union_r.
    apply inclusion_union_l.
    { rewrite SUBsb; basic_solver. }
    unfolder; intros e1 e2 SB; desf; splits; eauto.
    tertium_non_datur (t1 e1) as [T1|T1]; vauto.
    apply M0 in SB0; desf. }
  generalize M; basic_solver.
Qed.

Lemma sb_max_same_tid G1 e1 e2 P
  (SBM : sb_max P e2) 
  (WF : Wf G1)
  (NINI : ~ is_init e2)
  (ACT1 : acts G1 e1) (ACT2 : acts G1 e2)
  (Pe1 : P e1)
  (PNe2 : ~ P e2)
  (ST  : same_tid e1 e2) : 
  ext_sb e1 e2.
Proof.
  tertium_non_datur (is_init e1) as [INI|].
  { by unfold ext_sb; destruct e1, e2. }
  apply tid_ext_sb in ST; unfolder in ST; desf.
  { by erewrite (wf_index WF) in Pe1; eauto. }
  exfalso; eapply SBM. basic_solver.
Qed.

(******************************************************************************)
(** **  Memory model consistensy  *)
(******************************************************************************)

Definition MaximalWrite G e w :=
  << ACTw : acts G w >> /\
  << W    : is_w w   >> /\
  << LOC  : same_loc w e >> /\
  << MCO  : max_elt (co G) w >>.

Lemma MaximalWrite_ex G e s
  (WF : Wf G)
  (FIN : acts G \₁ is_init ⊆₁ (fun x : Event => In x s)): 
  exists w, MaximalWrite G e w.
Proof.
  edestruct (last_exists (InitEvent (loc e) :: s)) with 
  (s0 := co G)
  (a := InitEvent (loc e)) as [w C1]; desf.
  { by apply co_acyclic. }
  { intros ? C.
    apply clos_rt_rtn1 in C; destruct C as [|?? C']; vauto.
    apply WF in C'; unfolder in C'; desc.
    right; apply FIN; split; eauto; intros INI.
    eapply wf_co_init; basic_solver. }
  exists w; unfold MaximalWrite; splits; eauto.
  all: apply clos_rt_rtn1 in C1; assert (C1' := C1).
  all: destruct C1 as [|?? C']; vauto.
  { by apply WF. }
  { apply WF in C'; unfolder in C'; desf. }
  { apply (wf_coD WF) in C'; unfolder in C'; desf. }
  clear C' C1 C0.
  induction C1' as [|?? C]; ins.
  eby apply wf_col in C; eauto; etransitivity.
Qed. 

Record consType := {
  cons_of            :> execution -> Prop;

  _                  : cons_of G0;
  cons_complete      : cons_of ⊆₁ rf_complete;
  sub_execution_cons :
    forall G G', (G ⊆ G')%Ex -> cons_of G' -> cons_of G;
  cons_max_ext_r     :
    forall G w a,
    is_r a ->
    MaximalWrite G a w -> 
    cons_of G -> cons_of (SetRF (Add G a) a w);
  cons_max_ext_w     :
    forall G w a,
    is_w a -> same_loc w a ->
    MaximalWrite G (InitEvent (loc a)) w -> 
    cons_of G -> cons_of (SetCO (Add G a) w a);
  _                  : forall G, cons_of G -> irreflexive (hb G)
}.

Lemma cons0 (cons : consType) : cons G0.
Proof using.
  by destruct cons.
Qed.

Lemma cons_hb_irr (cons : consType) G : cons G -> irreflexive (hb G).
Proof using.
  destruct cons; eauto.
Qed.

(******************************************************************************)
(** ** prop eq  *)
(******************************************************************************)

Axiom prop_eq : forall P Q, P <-> Q -> P = Q.

Lemma set_equivE A : (@set_equiv A) = eq.
Proof.
  do 2 (apply functional_extensionality; ins).
  apply prop_eq; split; [|intros->; basic_solver].
  intros [].
  apply functional_extensionality; ins.
  apply prop_eq. firstorder.
Qed.

Lemma same_eqE A (r1 r2 : relation A) : 
  r1 ≡ r2 = (r1 = r2).
Proof.
  apply prop_eq; split; [|intros->; basic_solver].
  intros []; do 2 (apply functional_extensionality; ins).
  apply prop_eq; firstorder.
Qed.

Lemma eq_executionE G1 G2 : 
  eq_execution G1 G2 = (G1 = G2).
Proof.
  apply prop_eq; split; [|intros->; reflexivity].
  unfold eq_execution; ins; desf.
  rewrite set_equivE in EQ_ACT.
  rewrite same_eqE in EQ_RF, EQ_CO.
  by destruct G1, G2; ins; rewrite EQ_ACT, EQ_RF, EQ_CO.
Qed.

Lemma SetRF_Restr G w r
  (WF : Wf G) (RF : rf G w r) : 
  SetRF (Add (Restr G (set_compl (eq r))) r) r w = G.
Proof.
  apply WF in RF; unfolder in RF; desf.
  apply (wf_rfD WF) in RF0; unfolder in RF0; desf.
  rewrite <-eq_executionE.
  unfold eq_execution; splits; ins.
  { rewrite set_union_inter_l.
    arewrite (set_compl (eq r) ∪₁ eq r ≡₁ fun _ => True).
    { unfolder; split; ins; desf.
      tertium_non_datur (r = x); vauto. }
    basic_solver. }
  { unfolder; splits; intros ?? RF'; desf.
    assert (r <> x).
    { apply (wf_rfD WF) in RF'; unfolder in RF'; desf.
      intro; desf; eby eapply n_is_r. }
    tertium_non_datur (r = y); desf; eauto.
    apply (wf_rff WF _ _ _ RF2) in RF'; vauto. }
  apply n_is_w in RF3. rewrite (wf_coD WF).
  unfolder; splits; ins; desf; splits; eauto; intro; desf.
Qed.

Lemma well_founded_co G (WF : Wf G)
  (G_fin : set_finite (acts G \₁ is_init)) : 
  well_founded ((co G)⁻¹).
Proof.
  cdes G_fin. eapply wf_finite.
  { by apply acyclic_transp, co_acyclic. }
  intros ?? CO.
  apply WF in CO; unfolder in CO; desf.
  apply G_fin0; split; eauto; intro.
  eapply wf_co_init; basic_solver.
Qed.


Lemma SetCO_Restr G w'
  (WF : Wf G) (HB : hb_max G w')
  (W : is_w w')
  (nini : ~ is_init w')
  (G_fin : set_finite (acts G \₁ is_init)) : 
  exists w, 
  w <> w' /\
  SetCO (Add (Restr G (set_compl (eq w'))) w') w w' = G /\
  is_w w /\ 
  same_loc w w' /\
  acts G w.
Proof.
  assert (well_founded ((co G)⁻¹)) as wf_co.
  { by apply well_founded_co. }
  assert ((co G)⁻¹ w' (InitEvent (loc w'))) as ICO.
  { unfolder. 
    destruct (wf_co_total WF) with
      (a := w') 
      (b := InitEvent (loc w'))
      (x := loc w'); ins; eauto.
    { cdes HB. basic_solver. }
    { unfolder; splits; eauto; by apply WF. }
    { intro; destruct w'; ins. }
    exfalso; eapply (wf_co_init); eauto; basic_solver. }
  eapply wf_imm_succ in ICO; eauto; desf.
  apply (proj1 (transp_imm _)) in ICO.
  assert (co G c w') as CO.
  { apply immediateE in ICO; generalize ICO; basic_solver. }
  apply WF in CO; unfolder in CO; desf.
  apply (wf_coD WF) in CO0; unfolder in CO0; desf.
  exists c; splits; eauto; [| |eby eapply wf_col].
  { by intro; subst; apply co_irr in CO2. }
  rewrite <-eq_executionE.
  unfold eq_execution; splits; ins.
  { rewrite set_union_inter_l.
    arewrite (set_compl (eq w') ∪₁ eq w' ≡₁ fun _ => True).
    { unfolder; split; ins; desf.
      tertium_non_datur (w' = x); vauto. }
    basic_solver. }
  { split; [basic_solver|].
    unfolder; intros ?? RF; splits; eauto; intro; desf.
    { eapply HB with (x0 := y); exists x, x; split; vauto. }
    apply (wf_rfD WF) in RF; unfolder in RF; desf.
    by apply n_is_w in RF1. }
  unfold into_rel;  split; ins; desf.
  { unfolder; intros ?? CO'; desf.
    { destruct (wf_co_total WF) with (a := z) (b := w') (x := loc c); eauto.
      { apply WF in CO'1; unfolder in CO'1; desf.
        apply (wf_coD WF) in CO'0; unfolder in CO'0; desf.
        apply (wf_col WF) in CO'5; basic_solver. }
      { apply wf_col in CO2; eauto; basic_solver. }
      destruct (co_irr WF c); 
      eapply (co_trans WF _ _ _ CO2), co_trans; eauto. }
    destruct (wf_co_total WF) with (a := w') (b := y) (x := loc z); eauto.
    { apply wf_col in CO2; eauto; basic_solver. }
    { apply WF in CO'1; unfolder in CO'1; desf.
      apply (wf_coD WF) in CO'0; unfolder in CO'0; desf.
      apply (wf_col WF) in CO'5; basic_solver. }
    apply immediateE in ICO; unfolder in ICO; desf.
    destruct ICO0; vauto. }
  intros ?? CO'.
  tertium_non_datur (y = w') as [|NEQ]; desf.
  { tertium_non_datur (x = c) as [|NEQ1]; eauto.
    right; left; splits; eauto; unfolder; splits.
    { by intro; desf; apply co_irr in CO'. }
    { destruct (wf_co_total WF) with (a := x) (b := c) (x := loc w'); eauto.
      { apply WF in CO'; unfolder in CO'; desf.
        apply (wf_coD WF) in CO'0; unfolder in CO'0; desf.
        apply (wf_col WF) in CO'2; basic_solver. }
      { apply wf_col in CO2; eauto; basic_solver. }
      apply immediateE in ICO; unfolder in ICO; desf.
      destruct ICO0; vauto. }
    by intro; desf; apply co_irr in CO2. }
  tertium_non_datur (x = w') as [|NEQ']; desf.
  { do 3 right; splits; eauto.
    unfolder; splits; eauto.
    { intro; desf; by apply co_irr in CO2. }
    eby eapply co_trans. }
  left; basic_solver.
Qed.

Lemma sub_exec_same_acts G1 G2 G
  (SUB1 : (G1 ⊆ G)%Ex)
  (SUB2 : (G2 ⊆ G)%Ex) 
  (ACT  : acts G1 ≡₁ acts G2) :
  G1 = G2.
Proof.
  rewrite <-eq_executionE; unfold eq_execution; splits; eauto.
  1,2: destruct SUB1, SUB2; desc.
  { by rewrite SUBrf0, SUBrf, ACT. }
  by rewrite SUBco0, SUBco, ACT.
Qed.

Lemma Restr_eq_sub G D G'
  (WF : Wf G')
  (SUB : (G ⊆ G')%Ex)
  (ACT : acts G ≡₁ D) : 
  G = Restr G' D.
Proof.
  assert (Wf G) as WF'.
  { eby eapply sub_execution_wf. }
  eapply sub_exec_same_acts; eauto.
  { apply Restr_clos_sub; eauto.
    { rewrite <-ACT; by apply WF'. }
    unfolder; ins; desf.
    eapply ACT, sub_execution_hb; eauto; by apply ACT. }
  ins. rewrite <-ACT, set_inter_absorb_l; eauto; apply SUB.
Qed.

Lemma acts_revisitE G a e wp D 
  (R : is_r a)
  (WfG : Wf G)
  (ACT : acts G a)
  (NDa : ~ D a):
  SetCO (SetRF (Add (Restr G (set_compl D)) e) a e) wp e = 
  SetRF (
    Add (SetCO (
        Add (Restr G (set_compl (D ∪₁ eq a))) 
        e) 
        wp e) 
    a) 
    a e.
Proof.
  assert (forall x y, co G x y -> a <> x).
  { intros ?? CO; apply (wf_coD WfG) in CO; unfolder in CO; desc.
    intro; subst; by apply n_is_r in CO. }
  assert (forall x y, co G x y -> a <> y).
  { intros ?? CO; apply (wf_coD WfG) in CO; unfolder in CO; desc.
    intro; subst; by apply n_is_r in CO1. }
  assert (forall x y, rf G x y -> a <> x ).
  { intros ?? RF; apply (wf_rfD WfG) in RF; unfolder in RF; desc.
    intro; subst; by apply n_is_r in RF. }
  rewrite <-eq_executionE; unfold eq_execution; splits; ins.
  { rewrite set_compl_union; unfolder; splits; ins; desf; vauto.
    tertium_non_datur (x = a); eauto. }
  all: rewrite set_compl_union; unfolder; unfold into_rel;
       splits; ins; desf; eauto 21.
Qed.