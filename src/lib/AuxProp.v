Require Import Lia.
Require Import Arith.
From hahn Require Import Hahn.
Require Import PropExtensionality.

Set Implicit Arguments.

Lemma rel_extensionality A (r r' : relation A) :
  r ≡ r' -> r = r'.
Proof using.
  ins; extensionality x; extensionality y.
  apply propositional_extensionality; split; apply H.
Qed.

Lemma set_extensionality A (s s' : A -> Prop) :
  s ≡₁ s' -> s = s'.
Proof using.
  ins; extensionality x.
  apply propositional_extensionality; split; apply H.
Qed.

Lemma in_max_of_list a l : In a l -> a <= max_of_list l.
Proof using.
  induction l; ins; desf; auto with arith.
  specialize_full IHl; eauto with arith.
Qed.

Lemma incl_max_of_list l l' : incl l l' -> max_of_list l <= max_of_list l'.
Proof using.
  unfold incl; induction l; ins; auto with arith.
  specialize_full IHl; ins; eauto.
  specialize_full H; eauto; apply Nat.max_lub; auto using in_max_of_list.
Qed.

Lemma eq_max_of_list l l' : incl l l' -> incl l' l -> max_of_list l = max_of_list l'.
Proof using.
  ins; eapply Nat.le_antisymm; auto using incl_max_of_list.
Qed.

Lemma maxE n m : Nat.max n m = if Nat.leb n m then m else n.
Proof using.
  desf; try first [apply Nat.max_r | apply Nat.max_l]; lia.
Qed.

Lemma lt_max_of_list_r n l :
  n < max_of_list l <-> (exists m, In m l /\ n < m).
Proof using.
  induction l; ins.
  intuition; desf; try lia.
  rewrite Nat.max_lt_iff, IHl; clear.
  intuition; desf; eauto.
Qed.

Lemma le_max_of_list_l n l :
  max_of_list l <= n <-> (forall m, In m l -> m <= n).
Proof using.
  induction l; ins.
  intuition; desf; try lia.
  rewrite Nat.max_lub_iff, IHl; clear.
  intuition; desf; eauto.
Qed.

Lemma lt_max_of_list_l n l :
  max_of_list l < n <-> (n <> 0 /\ forall m, In m l -> m < n).
Proof using.
  induction l; ins.
  intuition; desf; try lia.
  rewrite Nat.max_lub_lt_iff, IHl; clear.
  intuition; desf; eauto.
Qed.

Lemma max_of_list_eq_zero l :
  max_of_list l = 0 <-> forall m, In m l -> m = 0.
Proof using.
  induction l; ins; rewrite maxE; desf.
  all: split; ins; desf; eauto; try lia.
Qed.

Fixpoint min_of_list (l : list nat) : option nat :=
  match l with
  | nil => None 
  | n :: l0 =>
    match min_of_list l0 with
    | None     => Some n
    | Some min => Some (Init.Nat.min n min)
    end
  end.

Lemma min_of_list_in l m (DEF : min_of_list l = Some m) :
  In m l.
Proof using.
  induction l; desf. simpls.
  destruct (min_of_list l); simpls; desf; auto.
  destruct (Nat.min_spec_le a n); desf; auto.
Qed.

Lemma min_of_listP P l m (DEF : min_of_list l = Some m)
      (PP : forall a (IN : In a l), P a) :
  P m.
Proof using. apply min_of_list_in in DEF; auto. Qed.

Lemma min_of_list_exists l (NEMP : l <> nil) :
  exists m, min_of_list l = Some m.
Proof using.
  destruct l; desf. ins.
  destruct (min_of_list l); eauto.
Qed.

Lemma set_union_minus_alt {A} (s s' : A -> Prop) : s ≡₁ s ∩₁ s' ∪₁ (s \₁ s').
Proof using. unfolder. split; ins; tauto. Qed.

Lemma set_finite_r_min_precise_bounded {A}
      (s : A -> Prop) (r : relation A) n
      (SF : set_finite s)
      (TR : transitive r)
      (IR : irreflexive r)
      (SN : s n) :
  exists bound,
    ⟪ INS : s bound ⟫ /\
    ⟪ BND : forall m (SM : s m), ~ (r m bound) ⟫.
Proof using.
  apply set_finiteE in SF. desf.
  generalize dependent n.
  generalize dependent s.
  induction findom.
  { ins. by apply SF0 in SN. }
  ins.
  destruct (classic (exists b, (s \₁ eq a) b)) as [[b NH]|NH].
  2: { exists n. splits; auto. ins.
       enough (m = a /\ n = a); desf.
       { intros AA. eapply IR; eauto. }
       apply set_union_minus_alt with (s' := eq a) in SM.
       apply set_union_minus_alt with (s' := eq a) in SN.
       split.
       2: unfolder in SN.
       unfolder in SM.
       all: desf; exfalso; apply NH; basic_solver. }
  edestruct IHfindom with (s:=s \₁ eq a); eauto.
  { eby eapply nodup_consD. }
  { rewrite SF0. unfolder. split; ins; desf.
    split; eauto. intros HH; subst. inv SF. }
  desf. unfolder in INS. desf.
  destruct (classic (r a x)) as [RR|RR].
  2: { exists x. splits; auto.
       ins.
       destruct (classic (m = a)); desf.
       apply BND. basic_solver. }
  exists a. splits; auto.
  { apply SF0. auto. }
  ins.
  destruct (classic (m = a)); desf.
  { intros AA. eapply IR; eauto. }
  intros HH. eapply BND with (m:=m).
  { basic_solver. }
  eapply TR; eauto.
Qed.

Lemma set_finite_nat_precise_bounded s n
      (SF : set_finite s) (SN : s n) :
  exists bound,
    ⟪ INS : s bound ⟫ /\
    ⟪ BND : forall m (SM : s m), m <= bound ⟫.
Proof using.
  eapply set_finite_r_min_precise_bounded with (r:=gt) (n0:=n) in SF; auto.
  3: { red. apply gt_irrefl. }
  2: { red. apply gt_trans. }
  desf. exists bound. splits; auto.
  ins. apply BND in SM.
  destruct (le_lt_dec m bound); auto.
  intuition.
Qed.

Lemma filterP_length {A} (l : list A) (P : A -> Prop) :
  length (filterP P l) <= length l.
Proof using.
  induction l; ins.
  desf; ins; lia.
Qed.

Lemma set_infinite_nat_exists_bigger (s : nat -> Prop) n (INF : ~ set_finite s) :
  exists m, ⟪ LT : n <= m ⟫ /\ ⟪ SM : s m ⟫.
Proof using.
  apply set_infinite_natE with (n:=n) in INF. desf.
  exists m. splits; auto.
  etransitivity.
  { apply filterP_length. }
  rewrite seq_length. lia.
Qed.

Lemma set_nat_exists_min (s : nat -> Prop) n (IN : s n) :
  exists min, ⟪ INM : s min ⟫ /\ ⟪ MIN : forall m (IN : s m), min <= m ⟫.
Proof using.
  unnw.
  generalize IN. pattern n.
  eapply (well_founded_induction Nat.lt_wf_0).
  ins.
  destruct (classic (exists y, s y /\ y < x)) as [|NEQ]; desf.
  { eapply H; eauto. }
  exists x. splits; auto. ins.
  apply Nat.le_ngt; intros AA. apply NEQ; eauto.
Qed.

Lemma nnil_last_default_irrelevance {A} x y (l : list A) (NNIL : l <> nil) :
  last l x = last l y.
Proof using.
  destruct l; desf. induction l; ins. desf.
  apply IHl. ins.
Qed.

Lemma last_map {A B} a l (f : A -> B) :
  last (map f l) (f a) = f (last l a).
Proof using.
  induction l; ins.
  destruct l; ins.
Qed.

Lemma last_seq start len a (NNIL : len <> 0) :
  last (List.seq start len) a = start + len - 1.
Proof using.
  generalize dependent start.
  induction len; ins.
  rewrite seqS_hd. ins.
  destruct len; ins.
  { rewrite seq0. lia. }
  rewrite IHlen; auto.
  rewrite seqS_hd. lia.
Qed.

Lemma last_cons_def {A} (a : A) l :
  last l a = last (a :: l) a.
Proof using. induction l; ins. Qed.

Fixpoint list_elem_related {A} (R : relation A) (l : list A) :=
  match l with
  | nil     => True
  | a :: l' =>
    match l' with
    | nil => True
    | b :: l => 
      ⟪ AB : R a b ⟫ /\
      ⟪ LER : list_elem_related R l' ⟫
    end
  end.

Lemma rt_to_list {A} (R : relation A) x y (HH : R＊ x y) :
  exists l : list A, list_elem_related R (x :: l) /\ y = last l x.
Proof using.
  apply clos_rt_rt1n in HH.
  induction HH; ins.
  { exists nil. ins. }
  desc; ins.
  exists (y :: l). splits; auto.
  desf. clear.
  rewrite nnil_last_default_irrelevance with (y0:=x); ins.
Qed.

Definition pair_list_elem_related {A} (R : relation A) (p : A * list A) :=
  let a := fst p in
  let l := snd p in
  ⟪ SER :
    match l with
    | nil => True
    | b :: _ => R a b
    end ⟫ /\
  ⟪ LER : list_elem_related R l ⟫.
    
Lemma list_elem_related_map {A B} (R : relation B) l (f : A -> B)
      (LER : list_elem_related R (map f l)) :
  list_elem_related (f ↓ R) l.
Proof using.
  induction l; ins. do 2 desf.
  splits; intuition.
  inv Heq.
Qed.

Lemma list_elem_related_app_r {A} (R : relation A) l l' 
      (LER : list_elem_related R (l ++ l')) :
  list_elem_related R l'.
Proof using.
  induction l; ins. do 2 desf.
  { destruct l; desf. ins; desf. }
  intuition.
Qed.

Lemma trace_nodup_mapE' {A B} (f : A -> B) (t : trace A)
      (INJ : forall a b (NEQ : a <> b)
                    (INA : trace_elems t a)
                    (INB : trace_elems t b),
          f a <> f b)
      (NODUP : trace_nodup t) :
  trace_nodup (trace_map f t).
Proof using.
  destruct t; red; ins.
  { assert (exists al, In al l); desc.
    { destruct l as [|a]; vauto; ins. lia. }
    rewrite nth_indep with (n:=i) (d':=f al); [|lia].
    rewrite nth_indep with (n:=j) (d':=f al); auto.
    rewrite !map_nth.
    rewrite map_length in LTj.
    apply INJ.
    { by apply NODUP. }
    all: apply nth_In; lia. }
  apply INJ; eauto.
  red in NODUP; ins. apply NODUP; auto.
Qed.

Lemma filterP_cons {A} (P : A -> Prop) (hd : A) (tl : list A) :
  filterP P (hd :: tl) =
  (ifP P hd then hd :: nil else nil) ++ filterP P tl.
Proof using. unfold filterP. desf. Qed.


Lemma le_diff x y (LE: x <= y): exists d, y = x + d.
Proof.
  generalize dependent y. 
  induction x.
  { ins. eauto. }
  ins. destruct y; [lia | ].
  specialize (IHx y). specialize_full IHx; [lia| ]. desc.
  exists d. lia.
Qed. 

Lemma lt_diff x y (LT: x < y): exists d, y = x + S d.
Proof.
  unfold lt in LT. apply le_diff in LT. desc.
  exists d. lia. 
Qed. 

Lemma opt_val {A: Type} (ov: option A): ov <> None <-> exists v, ov = Some v.
Proof. destruct ov; split; ins; desc; vauto. Qed. 

Lemma set_equiv_exp_iff (A : Type) (s s' : A -> Prop):
  s ≡₁ s' <-> (forall x, s x <-> s' x).
Proof.
  split; [apply set_equiv_exp| ].
  intros EQ. red. split; red; ins; apply EQ; auto. 
Qed.

Lemma last_app {A: Type} (l1 l2: list A) d x:
  last (l1 ++ (x :: l2)) d = last (x :: l2) d.
Proof.
  induction l1; [done| ].
  rewrite <- app_comm_cons. simpl.
  destruct (l1 ++ x :: l2) eqn:H; [| done]. by destruct l1, l2. 
Qed.

