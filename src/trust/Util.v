From hahn Require Import Hahn.
From Coq Require Import Lia.
Require Import Events.

Set Implicit Arguments.

(******************************************************************************)
(** ** Inserting into relation  *)
(******************************************************************************)

(** Update a partial order [r] by insert [b] right after [a]. *)
Definition into_rel A (r : relation A) (a b : A) :=
  fun e e' =>
      r e e'          \/
      r e a /\ e' = b \/
      e = a /\ e' = b \/
      e = b /\ r a e'.

Lemma into_rel_trans A (r : relation A) a b
  (TR_r : transitive r) (IRR_r : irreflexive r)
  (Nrxb : forall x, ~ r x b) (Nrbx : forall x, ~ r b x) :
  transitive (into_rel r a b).
Proof.
  unfold transitive, not, into_rel in *; ins; desf; eauto 8.
  all: solve [exfalso; eauto].
Qed.

Lemma into_rel_irr A (r : relation A) a b
  (IRR_r : irreflexive r)
  (Nrxb : forall x, ~ r x b) (Nrbx : forall x, ~ r b x)
  (Nab : a <> b) :
  irreflexive (into_rel r a b).
Proof.
  intros x; unfold not, into_rel in *; ins; desf; eauto.
Qed.

Add Parametric Morphism A : (@into_rel A) with signature
  inclusion ==> eq ==> eq ==> inclusion as into_rel_mori.
Proof. unfold into_rel; unfolder; ins; desf; eauto 8. Qed.

Add Parametric Morphism A : (@into_rel A) with signature
  same_relation ==> eq ==> eq ==> same_relation as into_rel_more.
Proof. unfold same_relation; intuition; auto using into_rel_mori. Qed.

(******************************************************************************)
(** ** Other lemmas  *)
(******************************************************************************)

Lemma total_order_from_list_filterP A l (P : A -> Prop):
  total_order_from_list (filterP P l) ≡
  ⦗P⦘ ⨾ total_order_from_list l ⨾ ⦗P⦘.
Proof.
  induction l as [ | a l]; unfolder in *; split; ins; desf.
  all: try solve [forward eapply total_order_from_list_in1; eauto; ins].
  all: rewrite total_order_from_list_cons in *; desf.
  all: try rewrite in_filterP_iff in *; desf; eauto.
  all: apply IHl in H; desf; eauto.
Qed.

Lemma total_order_from_list_total A (l : list A) : 
  is_total (fun x => In x l) (total_order_from_list l).
Proof.
  elim l; [basic_solver|intros ?? IHl ? IN1 ? IN2 NE; ins; desf]. 
  3: apply (IHl _ IN1 _ IN2) in NE; desf.
  all: by left+right; apply total_order_from_list_cons; eauto.
Qed.

Lemma total_order_from_list_cons_max A (l : list A) x y 
  (ND : NoDup (y :: l)) :
  ~ total_order_from_list (y :: l) x y.
Proof.
  intro T; apply total_order_from_list_cons in T; apply nodup_cons in ND; desf.
  by apply total_order_from_list_in2 in T.
Qed.

Lemma length_filterP A l (P : A -> Prop) : 
  length (filterP P l) <= length l.
Proof.
  induction l; ins; destruct (excluded_middle_informative _); ins; lia.
Qed.

Lemma total_sub A (ord1 ord2 : relation A) D 
  (T2 : is_total D ord2)
  (IRR1 : irreflexive ord1)
  (ordD : <|D|> ;; ord1 ∩ (ord2⁻¹) ;; <|D|> ≡ ∅₂): 
  restr_rel D ord1 ⊆ restr_rel D ord2.
Proof.
  intros x y [ORD [Dx Dy]].
  destruct (T2 _ Dx _ Dy); [|basic_solver|].
  { by intro; desf; apply IRR1 in ORD. }
  exfalso; eapply ordD with (x := x) (y := y); basic_solver.
Qed.

Lemma total_eqv A (ord1 ord2 : relation A) D 
  (T1   : is_total D ord1) 
  (T2   : is_total D ord2)
  (IRR1 : irreflexive ord1)
  (IRR2 : irreflexive ord2)
  (ordD : <|D|> ;; ord1 ∩ (ord2⁻¹) ;; <|D|> ≡ ∅₂): 
  restr_rel D ord1 ≡ restr_rel D ord2.
Proof. 
  split; apply total_sub; auto.
  generalize ordD. unfolder. firstorder.
Qed.

Lemma total_transp A (ord : relation A) D: 
  is_total D ord <-> is_total D ord⁻¹.
Proof. firstorder. Qed.

Lemma n_is_w : is_r ≡₁ set_compl is_w.
Proof using.
  unfolder; split; intro e; ins; by destruct e as [[]|??[]].
Qed.

Lemma n_is_r : is_w ≡₁ set_compl is_r.
Proof using.
  unfolder; split; intro e; ins; by destruct e as [[]|??[]].
Qed.

Lemma wf_ext_sb : well_founded ext_sb.
Proof.
  apply Wf_nat.well_founded_lt_compat with 
    (f := fun e => 
        match e with 
        | InitEvent _ => 0
        | _           => S (index e)
        end).
  intros x y SB; destruct x, y; ins; lia.
Qed.

Inductive Revisit :=
  | RV : Event -> Revisit
  | NR : Revisit.

Lemma ct_step_ct A (r : relation A) : r⁺ ≡ r ;; r⁺ ∪ r.
Proof using.
  split; intros ?? R.
  { apply clos_trans_t1n in R; destruct R; vauto.
    apply clos_t1n_trans in R; vauto. }
  apply clos_t1n_trans; destruct R as [R|R]; vauto.
  destruct R as [? R]; desf; apply clos_trans_t1n in R0; vauto.
Qed.

Lemma codom_seq A (r1 r2 : relation A) : 
  codom_rel (r1 ;; r2) ≡₁ 
  codom_rel (<|codom_rel r1|> ;; r2).
Proof using. basic_solver. Qed.

Lemma not_finite A (P : A -> Prop) 
  (NFIN : ~ exists s, P ⊆₁ (fun x => In x s)): 
  forall k : nat, exists s, 
    << NDs  : NoDup s                >> /\
    << LENs : length s = k           >> /\
    << SUBs : (fun x => In x s) ⊆₁ P >>.
Proof.
  ins; induction k.
  { exists nil; basic_solver. }
  desf.
  tertium_non_datur (P \₁ (fun x => In x s) ≡₁ ∅) as [F|F].
  { destruct NFIN; exists s. by apply set_subsetE. }
  exists (n :: s); splits; eauto.
  { apply nodup_cons; generalize F; basic_solver. }
  generalize SUBs F. basic_solver.
Qed.

Lemma transp_imm A (r : relation A) : 
  immediate r⁻¹ ≡ (immediate r)⁻¹.
Proof.
  rewrite ?immediateE, <-transp_seq.
  basic_solver.
Qed.

Lemma acyclic_transp A (r : relation A) : 
  acyclic r -> acyclic r⁻¹.
Proof.
  intros AC; intros ? R.
  by apply transp_ct, AC in R.
Qed.

Lemma pow_transp A (r : relation A) k : r⁻¹^^k ≡ r^^k⁻¹.
Proof.
  induction k; [firstorder|].
  rewrite pow_S_begin; ins.
  by rewrite transp_seq, IHk.
Qed.



