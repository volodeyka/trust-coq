Require Import Lia IndefiniteDescription Arith.
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Labels.
Require Import Events.
Require Import Execution.
Require Import View.

Set Implicit Arguments.

Section RADeclarative.

Variable G: execution. 

Definition ra_consistent :=
  irreflexive (hb G ⨾ (co G ∪ fr G)^?) /\
  irreflexive ((rf G)⁻¹ ⨾ (co G ⨾ (co G))).

Lemma hb_irr (CONS : ra_consistent) : irreflexive (hb G).
Proof using.
  cdes CONS. eapply irreflexive_mori; [|by apply CONS0]. red. basic_solver.
Qed.

Lemma ra_rmw_atomicity (WF: Wf G) (CONS : ra_consistent) :
  rmw_atomicity G.
Proof using.
  unfold ra_consistent, rmw_atomicity in *; desc.
  rewrite wf_rfE, wf_rfD; ins; unfolder in *; ins; desf.
  destruct (classic (x = y)) as [|NEQ]; desf.
    by edestruct (CONS y); exists y; split; vauto.
  eapply (wf_co_total WF) in NEQ; ins; desf; ins.    
    splits; ins; intro; desf; eauto 10.  
  edestruct (CONS x); exists y; split; vauto.    
  apply wf_rfl in H0; ins.
Qed.

 
Lemma ra_rf_irr (CONS : ra_consistent) : irreflexive (rf G).
Proof using. rewrite rf_in_hb. by apply hb_irr. Qed.

Lemma rf_w_in_co (WF: Wf G) (CONS : ra_consistent) :
  (rf G) ⨾ ⦗is_w⦘ ⊆ (co G).
Proof using.
  unfolder. intros x y [RF WY].
  destruct (classic (x = y)) as [|NEQ]; subst.
  { exfalso. eapply ra_rf_irr; eauto. }
  apply (wf_rfE WF) in RF. unfolder in RF. desf.
  apply (wf_rfD WF) in RF0. unfolder in RF0. desf.
  edestruct (wf_co_total WF) with (a:=x) (b:=y) as [|HH]; eauto.
  1,2: unfolder; splits; eauto.
  { symmetry. by apply (wf_rfl WF). }
  exfalso.
  cdes CONS.
  eapply CONS0. eexists. split.
  2: { generalize HH. basic_solver. }
    by apply rf_in_hb.
Qed.

Lemma co_init_r (WF: Wf G) (CONS : ra_consistent) x y : (co G) x y -> is_init y -> False.
Proof.
  ins.
  eapply (proj1 CONS y); eexists x; split; vauto.
  apply (wf_coE WF) in H.
  apply t_step; left; unfold sb, ext_sb; unfolder in *; desf.
  assert (SL := wf_col WF _ _ H1); unfold same_loc, loc in *; ins; desf.
  edestruct (co_irr WF); eauto.
Qed.

End RADeclarative.
