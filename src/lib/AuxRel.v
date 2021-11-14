From hahn Require Import Hahn.

Require Import Setoid.

Set Implicit Arguments.

Lemma doma_eqv {A} (s : A -> Prop) (r : relation A): doma (⦗s⦘ ⨾ r) s.
Proof using. apply doma_helper. basic_solver. Qed.

Lemma seq_eqv_inter_ll {A} S (r r' : relation A) :
  (⦗S⦘ ⨾ r) ∩ r' ≡ ⦗S⦘ ⨾ r ∩ r'.
Proof using.
basic_solver.
Qed.

Lemma seq_eqv_inter_lr {A} S (r r' : relation A) :
  (r ⨾ ⦗S⦘) ∩ r' ≡ r ∩ r' ⨾ ⦗S⦘.
Proof using.
basic_solver.
Qed.

Lemma id_inter {A} (s s' : A -> Prop) : ⦗s ∩₁ s'⦘ ≡ ⦗s⦘ ⨾ ⦗s'⦘.
Proof using.
basic_solver.
Qed. 

Lemma cr_seq {A} (r r' : relation A) : r^? ⨾ r' ≡ r' ∪ r ⨾ r'.
Proof using. split; basic_solver 5. Qed.

Lemma seq_eqv_minus_lr :
forall (A : Type) (S : A -> Prop) (r r' : relation A),
(r ⨾ ⦗S⦘) \ r' ≡ (r \ r') ⨾ ⦗S⦘.
Proof using.
basic_solver 21.
Qed.

Lemma seq_eqv_minus_ll :
forall (A : Type) (S : A -> Prop) (r r' : relation A),
(⦗S⦘ ⨾ r) \ r' ≡ ⦗S⦘ ⨾ (r \ r').
Proof using.
basic_solver 21.
Qed.

Lemma path_union A (r1 r2: relation A) : (r1 ∪ r2)⁺ ⊆ r1⁺ ∪ (r1＊ ⨾ r2)⁺ ⨾ r1＊.
Proof using.
apply inclusion_t_ind_right.
unionL; [vauto|].
by rewrite rtE; rewrite <- !ct_step; basic_solver 12.
relsf; unionL.
- by unionR left; rewrite ct_unit.
- by rewrite !seqA; rewrite <- ct_end; basic_solver 12.
- rewrite (ct_step (r1⁺ ⨾ r2)).
  rewrite <- inclusion_t_rt at 1; basic_solver 22.
- rewrite !seqA, inclusion_t_rt at 1.
  rewrite <- (ct_end (r1＊ ⨾ r2)); basic_solver 12.
Qed.

Lemma path_union1 A (r1 r2: relation A) : (r1 ∪ r2)⁺ ⊆ r2⁺ ∪ r2＊ ⨾ (r1 ∪ r1 ⨾ r2⁺)⁺.
Proof using.
apply inclusion_t_ind_right.
unionL; [|vauto].
by rewrite rtE; rewrite <- !ct_step; basic_solver 12.
relsf; unionL; rewrite ?seqA.
- unionR right.
  arewrite (r2⁺ ⊆ r2＊); hahn_frame.
  rewrite <- !ct_step; basic_solver 12.
- by arewrite (r1 ⊆ (r1 ∪ r1 ⨾ r2⁺)＊) at 3; relsf.
- arewrite (r2⁺ ⊆ r2＊) at 1.
  rewrite <- ct_end; basic_solver.
- unionR right.
  rewrite ct_end, !seqA.
  arewrite ((r1 ∪ r1 ⨾ r2⁺) ⨾ r2 ⊆ (r1 ∪ r1 ⨾ r2⁺)).
  relsf; unionL.
  * rewrite <- !ct_step; basic_solver 12.
  * rewrite !seqA.
    arewrite (r2⁺ ⊆ r2＊) at 1.
    rewrite <- ct_end; basic_solver.
  * relsf.
Qed.

Lemma path_union2 A (r1 r2: relation A) : 
  (r1 ∪ r2)⁺ ⊆ r1⁺ ∪ r2⁺ ⨾ r1＊ ∪ r2＊ ⨾ (r1⁺ ⨾ r2⁺)⁺ ⨾ r1＊.
Proof using.
rewrite path_union1; unionL.
basic_solver 12.
rewrite path_union.
relsf.
unionL.
basic_solver 12.
arewrite (r1＊ ⨾ r1 ⊆ r1⁺).
basic_solver 12.
Qed.

Lemma acyclic_union A (r1 r2: relation A) (R1: acyclic r1) (FF: acyclic (r2 ⨾ r1＊)):
  acyclic (r1 ∪ r2).
Proof using.
unfold acyclic; ins; rewrite path_union.
apply irreflexive_union; split; auto.
rewrite irreflexive_seqC. 
rewrite ct_begin, !seqA; relsf.
rewrite <- seqA; rewrite <- ct_begin.
by rewrite acyclic_seqC in FF.
Qed.

Lemma acyclic_union1 A (r1 r2: relation A) (R1: acyclic r1) 
(R2: acyclic r2)
(FF: acyclic (r1⁺ ⨾ r2⁺)):
  acyclic (r1 ∪ r2).
Proof using.
unfold acyclic; ins; rewrite path_union.
apply irreflexive_union; split; auto.
rewrite irreflexive_seqC.
rewrite ct_begin, !seqA; relsf.
rewrite <- seqA, <- ct_begin.
rewrite rtE; relsf.
rewrite path_union.
apply irreflexive_union; split; auto.
rewrite irreflexive_seqC. 
rewrite ct_begin, !seqA; relsf.
rewrite <- !seqA, <- ct_begin.
apply acyclic_rotl.
rewrite <- seqA, <- ct_begin.
by apply acyclic_rotl.
Qed.

Lemma seq_minus_transitive : 
  forall (A : Type) (r r1 r2 : relation A), transitive r -> r1 ⨾ r2 \ r ⊆ 
(r1 \ r) ⨾  r2 ∪ (r1 ∩ r) ⨾  (r2 \ r).
Proof using.
unfolder; ins; desf.
destruct (classic (r x z)); [|eauto].
right; eexists; splits; try edone; intro; eauto.
Qed.

Lemma ct_minus_transitive : 
  forall (A : Type) (r r1: relation A), transitive r -> r1⁺ \ r ⊆ 
(r1 ∩ r)＊ ⨾  (r1 \ r) ⨾  r1＊.
Proof using.
ins.
arewrite (r1 ⊆ (r1 ∩ r) ∪ (r1 \ r)) at 1.
by unfolder; ins; desf; tauto.
rewrite path_ut_first, minus_union_l.
unionL.
by arewrite (r1 ∩ r ⊆ r); relsf.
arewrite ((r1 ∩ r) ∪ (r1 \ r) ⊆ r1) at 1.
basic_solver 12.
Qed.

Lemma restr_eqv_def {A} (cond : A -> Prop) (r : relation A) :
  restr_rel cond r ≡ ⦗cond⦘ ⨾ r ⨾ ⦗cond⦘.
Proof using.
basic_solver.
Qed.

Lemma dom_rel_ext (A: Type) (r1 r2: relation A):
dom_rel (r1 ⨾ r2^?) ≡₁ dom_rel r1.
Proof using.
basic_solver 10.
Qed.
(*
Lemma dom_rel_helper (A: Type) (r1 r2: relation A) S (IN: r1 ⊆ r2):
dom_rel (r1 ⨾ ⦗fun x => dom_rel (r2 ⨾ ⦗eq x⦘) ⊆₁ S⦘) ⊆₁ S.
Proof using.
basic_solver 10.
Qed.*)

Lemma dom_rel_eqv_dom_rel {A} (r r' : relation A):
  dom_rel (r ⨾ ⦗dom_rel r'⦘) ≡₁ dom_rel (r ⨾ r').
Proof using.
basic_solver 42.
Qed.

Lemma dom_rel_eqv_codom_rel {A} (r r' : relation A):
  dom_rel (r ⨾ ⦗codom_rel r'⦘) ≡₁ dom_rel (r ⨾ r'⁻¹).
Proof using.
basic_solver 42.
Qed.

Lemma dom_rel_fun_alt {A} (r : relation A) w :
  (fun a => r a w) ≡₁ dom_rel (r ⨾ ⦗ eq w ⦘).
Proof using.
basic_solver 10.
Qed.

Lemma dom_rel_helper {A} (r : relation A) d (IN:  dom_rel r ⊆₁ d) : r ≡ ⦗d⦘ ⨾ r.
Proof using.
unfolder in *; basic_solver.
Qed.

Lemma dom_rel_helper_in {A} (r : relation A) d (IN:  dom_rel r ⊆₁ d) : r ⊆ ⦗d⦘ ⨾ r.
Proof using.
unfolder in *; basic_solver.
Qed.

Lemma cr_helper {A} (r r' : relation A) d (H: r ⨾ ⦗d⦘ ⊆ ⦗d⦘ ⨾ r') : r^? ⨾ ⦗d⦘ ⊆ ⦗d⦘ ⨾ r'^? .
Proof using.
rewrite crE; relsf.
rewrite H; basic_solver 20. 
Qed.

Lemma acyc_simple_helper (A:Type) (r1 r2: relation A): 
acyclic (r1 ∪ r2) -> acyclic (r1⨾ r2).
Proof using.
ins.
arewrite (r1 ⊆ r1 ∪ r2).
arewrite (r2 ⊆ r1 ∪ r2) at 2.
rewrite (ct_step (r1 ∪ r2)).
rewrite inclusion_t_rt at 1.
relsf.
red; rels.
Qed.

Tactic Notation "rotate" int_or_var(i) := do i (
 rewrite <- ?seqA; (apply irreflexive_seqC || apply acyclic_seqC); rewrite ?seqA).
Tactic Notation "rotate" := rotate 1.

(******************************************************************************)
(** ** Adjacency (new file in hahn?)  *)
(******************************************************************************)

Definition adjacent A (rel: relation A) a b :=
  ⟪ LA_ac : forall c, rel b c -> rel a c ⟫ /\ 
  ⟪ LA_ca : forall c, rel c b -> rel^? c a ⟫ /\
  ⟪ LA_cb : forall c, rel c a -> rel c b ⟫ /\
  ⟪ LA_bc : forall c, rel a c -> rel^? b c ⟫.

Definition adjacentW A (rel: relation A) a b :=
  ⟪ LA_ac : forall c, rel b c -> rel a c ⟫ /\ 
  ⟪ LA_cb : forall c, rel c a -> rel c b ⟫.

Lemma adjacent_weaken A (rel: relation A) a b : 
  adjacent rel a b -> adjacentW rel a b.
Proof using. unfold adjacent, adjacentW; intuition. Qed.

Lemma immediate_adjacent A (r: relation A) (dom: A -> Prop)
  (STOT1: ⦗dom⦘ ⨾ r ⨾ r⁻¹ ⊆ r^? ∪ r^{-1})
  (STOT2: r⁻¹ ⨾ ⦗dom⦘ ⨾ r ⊆ r^? ∪ r^{-1})
  (T: transitive r) (IRR: irreflexive r):  
⦗dom⦘ ⨾ immediate r ≡ ⦗dom⦘ ⨾ (adjacent r ∩ r).
Proof using.
unfold adjacent; unfolder in *; ins.
split; splits; desf; ins; try done.
1, 3: by eauto with hahn.
assert (AA: dom x /\ (exists z : A, r x z /\ r c z) ) by eauto.
by specialize (STOT1 x c AA) ; desf; [auto|exfalso; eauto |econs].
assert (AA: (exists z : A, r z y /\ dom z /\ r z c) ) by eauto.
by specialize (STOT2 y c AA) ; desf; [auto|econs | exfalso; eauto].
apply LA_bc in R1; apply LA_ca in R2; desf; eapply IRR, T; eauto.
Qed.

Lemma adjacent_uniqe1 A (r: relation A) (ACYC: acyclic r):
  forall a b c : A,  r a b ->  r a c -> adjacent r a b -> adjacent r a c -> b = c.
Proof using.
ins; unfold adjacent in *; desc.
assert (r^? b c) by eauto.
assert (r^? c b) by eauto.
unfolder in *; desf.
by exfalso; eapply ACYC; eapply t_trans; econs; eauto.
Qed.

Lemma adjacent_uniqe2 A (r: relation A) (ACYC: acyclic r):
  forall a b c : A,  r b a ->  r c a -> adjacent r b a -> adjacent r c a -> b = c.
Proof using.
ins; unfold adjacent in *; desc.
assert (r^? b c) by eauto.
assert (r^? c b) by eauto.
unfolder in *; desf.
by exfalso; eapply ACYC; eapply t_trans; econs; eauto.
Qed.

(******************************************************************************)
(** ** dom_cond  *)
(******************************************************************************)

  Definition dom_cond (A: Type) (r: relation A) s := (fun e => dom_rel (r ⨾ ⦗ eq e ⦘) ⊆₁ s).

Add Parametric Morphism A : (@dom_cond A) with signature
  inclusion --> set_subset ==> set_subset as dom_cond_mori.
Proof using.
ins. unfold dom_cond.
red; ins.
by rewrite H, <- H0.
Qed.

Add Parametric Morphism A : (@dom_cond A) with signature
  same_relation ==> set_equiv ==> set_equiv as dom_cond_more.
Proof using.
unfold dom_cond; unfolder; ins; splits; ins; desf; eauto 10.
Qed.

  Lemma dom_cond_elim {A} r (s : A -> Prop) : r ⨾ ⦗dom_cond r s⦘ ⊆ ⦗s⦘ ⨾ r.
  Proof using.
    unfold dom_cond; basic_solver 12.
  Qed.

  Lemma dom_cond_elim1 {A} r1 r2 (s : A -> Prop) (IN: r1 ⊆ r2) :
    r1 ⨾ ⦗dom_cond r2 s⦘ ⊆ ⦗s⦘ ⨾ r1.
  Proof using. unfold dom_cond; basic_solver 21. Qed.

  Lemma dom_cond_elim2 {A} r (s s' : A -> Prop) :
    s' ∩₁ dom_cond r s ⊆₁ dom_cond (⦗ s' ⦘ ⨾ r) s.
  Proof using. unfold dom_cond. basic_solver 12. Qed.

  Lemma dom_cond_union {A} r1 r2 (s : A -> Prop) :
    dom_cond (r1 ∪ r2) s ≡₁ dom_cond r1 s ∩₁ dom_cond r2 s.
  Proof using. unfold dom_cond; split; basic_solver 21. Qed.

  Lemma dom_cond_in {A} r r1 (s t : A -> Prop) :
    r ⨾ ⦗t⦘ ⊆ ⦗s⦘ ⨾ r1 -> t ⊆₁ dom_cond r s.
  Proof using.
    unfold dom_cond; unfolder; ins; desf.
   splits; eauto; eapply H; eauto.
  Qed.

(******************************************************************************)
(** ** ifthenelse  *)
(******************************************************************************)

Definition ifthenelse T K L (c : {K} + {L}) (x y : T) :=
  if c then x else y.

Definition ifthenelse_b T (c : bool) (x y : T) :=
  if c then x else y.

Add Parametric Morphism {A} (K : Prop) (L : Prop) (c : {K} + {L}) :
  (@ifthenelse (A -> Prop) K L c) with signature
    set_equiv ==>
    set_equiv ==>
    set_equiv as ifthenelse_more.
Proof using. intros; unfold ifthenelse; desf. Qed.

Add Parametric Morphism {A} (c : bool) :
  (@ifthenelse_b (A -> Prop) c) with signature
    set_equiv ==>
    set_equiv ==>
    set_equiv as ifthenelse_b_more.
Proof using. intros; unfold ifthenelse_b; desf. Qed.

Lemma ite_alt {A} K L (c : {K} + {L}) (x y : A -> Prop) :
  (if c then x else y) ≡₁ ifthenelse c x y.
Proof using. rels. Qed.

Lemma iteb_alt {A} (c : bool) (x y : A -> Prop) :
  (if c then x else y) ≡₁ ifthenelse_b c x y.
Proof using. rels. Qed.

Lemma ite_union_t {A} K L (c : {K} + {L}) (x y z : A -> Prop) :
  ifthenelse c (x ∪₁ y) z ≡₁ ifthenelse c x z ∪₁ ifthenelse c y z.
Proof using. by rewrite <- !ite_alt; destruct c; [|rewrite set_unionK]. Qed.

(******************************************************************************)
(** **   *)
(******************************************************************************)

Lemma rewrite_helper (A: Type) (r: relation A) (S S': A -> Prop)
(IN: r ⨾ ⦗S⦘ ⊆ ⦗S'⦘ ⨾ r) :
r ⨾ ⦗S⦘ ≡ ⦗S'⦘ ⨾ r ⨾ ⦗S⦘.
Proof using.
split; [| basic_solver].
arewrite (⦗S⦘ ⊆ ⦗S⦘ ⨾ ⦗S⦘) at 1.
basic_solver.
sin_rewrite IN.
basic_solver 12.
Qed.

  Lemma eq_predicate {A} (P : A -> Prop) a (H : P a): eq a ⊆₁ P.
  Proof using. by intros x H'; subst. Qed.

  Add Parametric Morphism A : (@doma A) with signature
      same_relation ==> set_equiv ==> iff as doma_more.
  Proof using.
    ins; split; ins; intros x' y' H';
      apply H0; eapply H1; eauto; apply H; eauto.
  Qed.

  Add Parametric Morphism A : (@domb A) with signature
      same_relation ==> set_equiv ==> iff as domb_more.
  Proof using.
    ins; split; ins; intros x' y' H';
      apply H0; eapply H1; eauto; apply H; eauto.
  Qed.

Lemma ind_helper {A} (r r': relation A) (D1 D2: A -> Prop) (ACYC: acyclic r) :
r＊ ⨾ ⦗D1⦘ ⊆ ⦗D2⦘ ⨾ r'＊ -> r⁺ ⨾ ⦗D1⦘ ⊆ ⦗D2⦘ ⨾ r'⁺. 
Proof using.
rewrite !rtE; unfolder; ins; desf.
specialize (H x y); desf.
assert (D2 x /\ (x = y /\ True \/ r'⁺ x y)) by tauto; desf.
exfalso; eapply ACYC; edone.
Qed.

Lemma cr_empty A : (fun (_ _: A) => False)^? ≡ ⦗fun _ => True⦘.
Proof using.
split; [|basic_solver].
unfolder; ins; desf.
Qed.

Lemma rtc_empty A : (fun (_ _: A) => False)＊ ≡ ⦗fun _ => True⦘.
Proof using.
split; [|basic_solver].
unfolder; ins.
induction H; eauto.
contradiction.
desf; congruence.
Qed.

Lemma tc_empty A : (fun (_ _: A) => False)⁺ ≡ ∅₂.
Proof using.
split; [|basic_solver].
unfolder; ins.
induction H; eauto.
Qed.

Lemma transp_empty A : (fun (_ _: A) => False)⁻¹ ≡ ∅₂.
Proof using.
basic_solver.
Qed.

Lemma inclusion_to_inter {X} (r1 r2: relation X) (INC: r1 ⊆ r2) :
  r1 ⊆ r1 ∩ r2.
Proof using.
unfolder in *; firstorder.
Qed.

Lemma total_case_split {X} (r: relation X) A (TOT: is_total A r) a b
(INa: A a) (INb: A b): r^? a b \/ r b a.
Proof using.
destruct (classic (a=b)); subst.
basic_solver.
apply TOT in H; basic_solver.
Qed.

Lemma not_dom_rel_rewrite_helper {X} (r1 r2: relation X) x 
(NIN: ~ dom_rel r1 x) (IN: dom_rel r2 ⊆₁ dom_rel r1) : ~ dom_rel r2 x.
Proof using.
firstorder.
Qed.

Lemma not_dom_rel_eq_helper {X} (r: relation X) x : 
  ⦗ eq x ⦘ ⨾ r ⊆ ∅₂ <-> ~ dom_rel r x.
Proof using.
unfolder in *.
split; ins; desf; eauto.
intro; desc; eauto.
Qed.

Lemma cross_union_l {X} (A B C: X -> Prop) : 
  (A ∪₁ B) × C ≡ A × C ∪ B × C.
Proof using.
basic_solver 21.
Qed.

Lemma cross_union_r {X} (A B C: X -> Prop) : 
  C × (A ∪₁ B) ≡ C × A ∪ C × B.
Proof using.
basic_solver 21.
Qed.

Lemma iff_helper (A1 A2 B C : Prop) (H1: A1 <-> A2) (H2: A1 -> (B <-> C)):
 (A1 /\ B <-> A2 /\ C).
Proof using. tauto. Qed.

Lemma eq_subset_helper {X:Type} (A : X -> Prop) a: 
 eq a ⊆₁ A <-> A a.
Proof using.
unfolder; split; ins; eauto; desf.
Qed.

Lemma subset_implication_helper {X:Type} (A B C: X -> Prop): 
 A ∩₁ B ⊆₁ A ∩₁ C -> A ⊆₁ B -> A ⊆₁ C.
Proof using.
unfolder; firstorder.
Qed.

Lemma equiv_implication_helper {X:Type} (A B C: X -> Prop): 
 A ∩₁ B ≡₁ A ∩₁ C -> A ⊆₁ B <-> A ⊆₁ C.
Proof using.
unfolder; firstorder.
Qed.

Lemma union_subset_helper {X:Type} (A B C: X -> Prop)
(UNIQUE: exists ! a, A a)
: 
(A ⊆₁ B) \/ (A ⊆₁ C) 
<-> A ⊆₁ (B ∪₁ C).
Proof using.
unfolder; firstorder.
specialize (H1 x H); desf.
left; ins; replace x0 with x; eauto.
right; ins; replace x0 with x; eauto.
Qed.


Definition rel_max A (rel: relation A) x y :=
  if excluded_middle_informative (rel x y) then y else x.

Definition latest_of_by {A: Type} (S: A -> Prop) r x :=
  S x /\ forall y (S': S y), r^? y x.

Lemma latest_unique {A: Type} (S: A -> Prop) r (AS: antisymmetric r):
  (exists e, latest_of_by S r e) -> (exists! e, latest_of_by S r e).
Proof.
  intros [e LATEST].
  exists e. red. split; auto. ins.
  red in LATEST, H. desc.
  destruct (classic (e = x')); auto.
  specialize (LATEST0 x' H). specialize (H0 e LATEST).
  red in LATEST0, H0. des; vauto.
  destruct (AS e x'); vauto.
Qed. 

Lemma antisymmetric_inclusion {A: Type} (r r': relation A) (AS: antisymmetric r) (INCL: r' ⊆ r):
  antisymmetric r'.
Proof.
  red. ins. red in AS. intuition.
Qed.

Lemma fold_right_prop {A: Type} (l: list A) r S e
      (PROP: forall x (IN: In x l), S x) (Se: S e):
  S (fold_right (rel_max r) e l).
Proof. 
  induction l.
  { simpl. auto. }
  simpl in *. unfold rel_max.
  destruct (excluded_middle_informative _).
  2: { specialize (PROP a). intuition. }
  apply IHl. auto.
Qed. 
  
Lemma fold_right_ge {A: Type} (l: list A) r (S: A -> Prop) e
      (PROP: forall x (IN: In x l), S x) (Se: S e)
      (STO: strict_total_order S r):
  forall y, In y l -> r^? y (fold_right (rel_max r) e l).
Proof.
  induction l.
  { ins.  }
  assert (forall y : A, In y l -> r^? y (fold_right (rel_max r) e l)) as IHl'.
  { apply IHl. intuition. }
  clear IHl.
  ins. 
  remember (fold_right (rel_max r) e l) as prev.
  des.
  2: { specialize (IHl' y H). 
       unfold rel_max. destruct (excluded_middle_informative _); auto.
       cdes STO. cdes STO0. 
       assert (S prev). 
       { subst. apply fold_right_prop; auto. }
       specialize (PROP a (or_introl eq_refl)).
       destruct (classic (prev = a)); [by vauto| ].
       specialize (STO1 prev H0 a PROP H1). des; [| by vauto].
       red in IHl'. des; [by vauto| ]. right. basic_solver. }
  subst a. unfold rel_max. destruct (excluded_middle_informative _); auto.
Qed. 

Lemma latest_fin {A: Type} (S: A -> Prop) r (FIN: set_finite S)
      (NEMPTY: ~ S ≡₁ ∅) (STO: strict_total_order S r):
  exists x, latest_of_by S r x.
Proof.
  red in FIN. desc.
  apply set_nonemptyE in NEMPTY. desc.
  set (m := fold_right (rel_max r) x (filterP S findom)).
  exists m. red. split.
  { apply fold_right_prop; auto.
    ins. apply in_filterP_iff in IN. by desc. }
  ins. 
  forward eapply (@fold_right_ge _ (filterP S findom) r S x); eauto.
  { ins. apply in_filterP_iff in IN. by desc. }
  specialize (FIN y S'). apply in_filterP_iff. split; auto. 
Qed.


Hint Rewrite cr_empty rtc_empty tc_empty transp_empty : hahn.
