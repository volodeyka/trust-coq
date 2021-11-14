Require Import Lia IndefiniteDescription Arith.
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Labels.
Require Import Events.
Require Import Execution.
Require Import View.

Set Implicit Arguments.

Section SCOHDeclarative.

Variable G: execution. 

Definition scoh_consistent :=
  SCpL G  /\
  irreflexive ((rf G)⁻¹ ⨾ (co G ⨾ (co G))) /\
  ⟪ PORF : irreflexive (hb G) ⟫.

Lemma hb_irr (CONS : scoh_consistent) : irreflexive (hb G).
Proof using. apply CONS. Qed.

Lemma scoh_rmw_atomicity (WF: Wf G) (CONS : scoh_consistent) :
  rmw_atomicity G.
Proof using.
  unfold scoh_consistent, rmw_atomicity in *; desc.
  rewrite wf_rfE, wf_rfD; ins; unfolder in *; ins; desf.
  destruct (classic (x = y)) as [|NEQ]; desf.
  { edestruct (CONS y). apply ct_step.
    basic_solver. }
  eapply (wf_co_total WF) in NEQ; ins; desf; ins.    
  { splits; ins; intro; desf; eauto 10. }
  { edestruct (CONS x). apply ct_ct.
    exists y; split; apply t_step; basic_solver. }
  unfolder. splits; auto.
  apply wf_rfl in H0; ins.
Qed.
 
Lemma scoh_rf_irr (CONS : scoh_consistent) : irreflexive (rf G).
Proof using. rewrite rf_in_hb. by apply hb_irr. Qed.

Lemma rf_w_in_co (WF: Wf G) (CONS : scoh_consistent) :
  (rf G) ⨾ ⦗is_w⦘ ⊆ (co G).
Proof using.
  unfolder. intros x y [RF WY].
  destruct (classic (x = y)) as [|NEQ]; subst.
  { exfalso. eapply scoh_rf_irr; eauto. }
  apply (wf_rfE WF) in RF. unfolder in RF. desf.
  apply (wf_rfD WF) in RF0. unfolder in RF0. desf.
  edestruct (wf_co_total WF) with (a:=x) (b:=y) as [|HH]; eauto.
  1,2: unfolder; splits; eauto.
  { symmetry. by apply (wf_rfl WF). }
  exfalso.
  cdes CONS. eapply CONS0.
  apply ct_ct. eexists. split; apply ct_step.
  all: basic_solver.
Qed.

(* TODO: move to more appropriate place or replace with co_ninit. *)
Lemma co_init_r (WF: Wf G)
      x y (CO : co G x y) (INITY : is_init y) :
  False.
Proof.
  apply co_ninit in CO; auto. unfolder in CO. desf.
Qed.

End SCOHDeclarative.
