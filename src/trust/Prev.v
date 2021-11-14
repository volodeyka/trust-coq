From hahn Require Import Hahn.
Require Import Execution Execution_Aux Events Labels.
From Coq Require Import Lia.
Require Import Util Sem Path TerminateGen.

Set Implicit Arguments.

Section Prev.

Variable thread_sem : tsemType.
Variable LR         : LRType thread_sem.
Variable cons       : consType.

Notation "e1 '<_next' e2" := (LR_of LR e1 e2) (at level 20).
Notation avail := (avail thread_sem).
Notation p_sem := (p_sem thread_sem).
Notation next  := (next LR).
Notation me    := (me LR).

Variable K : nat.

Hypothesis p_sem_finite :
  forall G, p_sem G -> 
    exists l, 
      << OC : G_ord_corr G l >> /\
      << ND : NoDup l        >> /\
      << LK : length l < K   >>.

Inductive Completion G : execution -> Prop :=
  | Read_Compl w a (Next : next G a) (R : is_r a)
    (MW : MaximalWrite G a w) :
    Completion G (SetRF (Add G a) a w)
  | Write_Compl w a (Next : next G a) (W : is_w a)
    (LOC : same_loc w a)
    (MW : MaximalWrite G (InitEvent (loc a)) w) :
    Completion G (SetCO (Add G a) w a).

Lemma Completion_det G G1 G2 
  (WF : Wf G) 
  (C1 : Completion G G1)
  (C2 : Completion G G2) : G1 = G2.
Proof using.
  inv C1; inv C2; apply (next_uniq Next) in Next0; desf; cdes MW; cdes MW0.
  { tertium_non_datur (w = w0); vauto.
    destruct (wf_co_total WF) with (a := w) (b := w0) (x := loc a0); eauto.
    1,2: basic_solver.
    { eby edestruct MCO. }
    eby edestruct MCO0. }
  1,2: by apply n_is_r in W.
  tertium_non_datur (w = w0); vauto.
  destruct (wf_co_total WF) with (a := w) (b := w0) (x := loc a0); eauto.
  1,2: basic_solver.
  { eby edestruct MCO. }
  eby edestruct MCO0.
Qed.


Lemma Completion_Restr G G' e
  (C : Completion G G') 
  (N : next G e): 
  G = Restr G' (set_compl (eq e)).
Proof using.
  assert (Wf G) by eby eapply next_Wf.
  inv C; ins.
  all: rewrite (next_uniq N Next); cdes Next; cdes Next0.
  { eby eapply Restr_SetRF. }
  eby eapply Restr_SetCO.
Qed.

Lemma Completion_cons : forall G G', 
  Completion G G' -> cons G -> cons G'.
Proof using.
  by intros ?? []; [apply cons_max_ext_r|apply cons_max_ext_w].
Qed.

Definition full G := avail G ≡₁ ∅.

Lemma Completions_cons G G' 
  (CM : Completion^* G G')
  (cons_G : cons G) : cons G'.
Proof using.
  apply clos_rt_rt1n in CM; induction CM as [|??? C]; auto.
  apply Completion_cons in C; eauto.
Qed.

Lemma Completion_Wf G G' 
  (CM : Completion G G')
  (Wf_G : Wf G) : Wf G'.
Proof using.
  inv CM; cdes MW; cdes Next; cdes Next0; cdes GG'.
  { eapply Wf_SetRF with (G' := G'); eauto.
    eby eapply p_sem_Wf. }
  eapply Wf_SetCO with (G' := G'); eauto.
  eby eapply p_sem_Wf.
Qed.

Lemma Completions_Wf G G' 
  (CM : Completion^* G G')
  (Wf_G : Wf G) : Wf G'.
Proof using.
  apply clos_rt_rt1n in CM; induction CM as [|??? C]; auto.
  apply Completion_Wf in C; eauto.
Qed.

Lemma Completion_semi_total G G1 G2 
  (WF : Wf G) 
  (C1 : Completion^* G G1)
  (C2 : Completion^* G G2) : 
  Completion^* G1 G2 \/ Completion^* G2 G1.
Proof using.
  apply clos_rt_rtn1 in C1.
  induction C1 as [|?? C]; vauto.
  desf.
  { apply clos_rt_rt1n in IHC1. destruct IHC1 as [|?? C']; vauto.
    apply clos_rtn1_rt in C1.
    assert (WFy : Wf y).
    { eby eapply Completions_Wf. }
    apply (Completion_det WFy C) in C'; desf.
    apply clos_rt1n_rt in IHC1; vauto. }
  right; apply rt_unit; vauto.
Qed.

Lemma sub_Completion G G'
  (Wf_G : Wf G)
  (CM : Completion G G') :
  (G ⊆ G')%Ex.
Proof using.
  inv CM; cdes Next; cdes Next0.
  { apply sub_exec_SetRF; eauto; ins; eby eapply avail_sb_max. }
  apply sub_exec_SetCO; eauto; ins; eby eapply avail_sb_max.
Qed.

Lemma sub_Completions G G'
  (Wf_G : Wf G)
  (CM : Completion^* G G') :
  (G ⊆ G')%Ex.
Proof using.
  apply clos_rt_rt1n in CM; induction CM as [|??? C].
  { by apply sub_execution_refl. }
  specialize (sub_Completion Wf_G C) as S1.
  eapply sub_execution_trans; eauto.
  eby eapply IHCM, Completion_Wf.
Qed.

Lemma next_Completion G G' e1 e2
  (COMPL : Completion G G')
  (Wf_G : Wf G)
  (N1 : next G e1) (N2 : next G' e2) : 
  e1 <_next e2.
Proof using.
  assert (acts G' e1).
  { inv COMPL; ins; apply (next_uniq Next) in N1; vauto. }
  tertium_non_datur (e1 = e2) as [|NEQ]; desf.
  { cdes N2; cdes N0; contradiction. }
  cdes N1; cdes N2.
  assert (avail G' ⊆₁ avail G ∪₁ (fun x => ext_sb e1 x)) as AV.
  { inv COMPL; apply (next_uniq Next) in N1; desf; cdes MW.
    { apply avail_SetRF; eauto. }
    apply avail_SetCO; eauto. }
  apply AV in N4; unfolder in N4; desf.
  { destruct (N3 _ N4); desf. }
  by apply sb_LR.
Qed.

Lemma next_Completions G G' e1 e2
  (COMPL : Completion^* G G')
  (Wf_G : Wf G)
  (N1 : next G e1) (N2 : next G' e2) 
  (NEQ : e1 <> e2): 
  e1 <_next e2.
Proof using.
  apply clos_rt_rt1n in COMPL.
  generalize dependent e1.
  generalize dependent e2.
  induction COMPL as [|G1 G2 G3 C]; ins.
  { apply (next_uniq N1) in N2; contradiction. }
  destruct COMPL as [|G2' G3 CM].
  { eby eapply next_Completion. }
  assert (exists e, next G2 e) as N' by (inv CM; vauto); desf.
  assert (e1 <_next e).
  { by apply (next_Completion C). }
  tertium_non_datur (e = e2); desf.
  apply LR_trans with (y := e); auto.
  apply IHCOMPL; eauto.
  by apply Completion_Wf in C.
Qed.

Lemma next_max_Completion G G' e x
  (Wf_G : Wf G)
  (COMPL : Completion^* G G')
  (N     : next G' e) 
  (G'G   : (acts G' \₁ acts G) x) : 
  x <_next e.
Proof using.
  apply clos_rt_rt1n in COMPL.
  generalize dependent e.
  generalize dependent x.
  induction COMPL as [|G1 G2 G3 C]; [basic_solver|ins].
  unfolder in G'G; desf.
  specialize (Completion_Wf C) as Wf_G2.
  tertium_non_datur (acts G2 x) as [ACT|]; [|apply IHCOMPL; basic_solver].
  assert (x <> e).
  { cdes N; cdes N0; intro; desf. }
  assert (next G1 x) as N1.
  { inv C; ins; generalize ACT; basic_solver. }
  eapply next_Completions; eauto.
  apply clos_rt1n_rt; vauto.
Qed.

Lemma in_Comletions x e G G' G''
  (Wf_G : Wf G)
  (PSEM : p_sem G'')
  (IRR : irreflexive (hb G''))
  (SUB : (G' ⊆ G'')%Ex)
  (ACT : acts G'' x)
  (COMPL : Completion^* G G')
  (N     : next G' e) 
  (xLRe  : x <_next e) : 
  acts G' x.
Proof using.
  tertium_non_datur (acts G' x); eauto.
  assert (well_founded (sb G'')) as wfs.
  { unfold sb; rewrite <-restr_relE; apply wf_restr, wf_ext_sb. }
  destruct (wf_impl_min_elt wfs) with 
    (B := set_compl (acts G') ∩₁ fun y => (sb G'')^? y x) as [y F].
  { unfolder; intro F; desf; eauto. }
  desf.
  unfolder in F; desc.
  assert (avail G' y) as AV.
  { apply avail_avail_sb; eauto.
    { eapply Completions_Wf in COMPL; eauto. }
    exists G''; splits; eauto.
    { desf; unfold sb in F1; unfolder in F1; desf. }
    intros e' SB.
    tertium_non_datur (acts G' e'); eauto.
    destruct (F0 e'); eauto; split; eauto.
    eby desf; vauto; right; eapply sb_trans. }
  desf; exfalso; apply N in AV.
  { eby desf; eapply LR_irr; eauto; eapply LR_trans. }
  unfold sb in F1; unfolder in F1; desc; apply (sb_LR LR) in F2.
  assert (y <_next e) by eby eapply LR_trans.
  eby desf; eapply LR_irr; eauto; eapply LR_trans.
Qed.

Lemma sbrf_irr G (WF : Wf G) : irreflexive (sb G ∪ rf G).
Proof using.
  intros ? [SB|RF]; [eby eapply sb_irr|].
  apply (wf_rfD WF) in RF; unfolder in RF; desf.
  by apply n_is_r in RF.
Qed.


Lemma Completion_hb_max G G' 
  (Wf_G : Wf G)
  (CM : Completion G G') : 
  exists e, next G e /\ hb_max G' e.
Proof using.
  destruct CM; exists a; splits; eauto; apply hb_maxE; split; vauto.
  all: split; [|basic_solver]; intros e F; unfolder in F; desf.
  all: cdes Next.
  { unfold sb in F0; unfolder in F0; desf.
    ins; unfolder in F2; desf.
    { eapply avail_sb_max in Next0; eauto; basic_solver. }
    eby eapply ext_sb_irr. }
  { cdes Next0.
    ins; unfolder in F0; desf.
    { apply Wf_G in F0; unfolder in F0; desf. }
    cdes MW; by apply n_is_r in W. }
  { unfold sb in F0; unfolder in F0; desf.
    ins; unfolder in F2; desf.
    { eapply avail_sb_max in Next0; eauto; basic_solver. }
    eby eapply ext_sb_irr. }
  ins; apply Wf_G in F0; unfolder in F0; desf.
  by cdes Next0.
Qed.

Lemma Completions_hb_max G G' 
  (Wf_G : Wf G)
  (CM : Completion^* G G') 
  (GG' : G <> G'): 
  exists e, ~ acts G e /\ hb_max G' e.
Proof using.
  apply clos_rt_rtn1 in CM; destruct CM as [|?? C]; [contradiction|].
  apply Completion_hb_max in C; desf.
  { exists e; split; eauto.
    eapply clos_rtn1_rt, sub_Completions in CM; auto.
    intro; cdes C; cdes C1; destruct NInG. by apply CM. }
  by apply clos_rtn1_rt, Completions_Wf in CM.
Qed.

Lemma In_Completion G G' e 
  (CM : Completion G G')
  (ACT : acts G' e) : 
  next G e \/ acts G e.
Proof using.
  destruct CM; ins; unfolder in ACT; desf; vauto.
Qed.

Lemma Completions_Adds G G' e1 e2 
  (CM   : Completion^* G G')
  (N    : next G e1) 
  (ACTS : (acts G' \₁ acts G) e2) : 
  LR^? e1 e2.
Proof using cons.
  apply clos_rt_rtn1 in CM.
  induction CM as [|G' G'' C]; [firstorder|].
  unfolder in ACTS; desf.
  assert (acts G' e2 \/ next G' e2) as AN.
  { inv C; vauto; ins; unfolder in ACTS; desf; vauto. }
  desf.
  { apply IHCM; basic_solver. }
  tertium_non_datur (e1 = e2); desf; vauto; right.
  eapply next_Completions; eauto.
  { apply clos_rtn1_rt; vauto. }
  eby eapply next_Wf.
Qed.

Lemma Completion_finite G G' s
  (C : Completion^* G G')
  (G'f : (acts G \₁ is_init) ⊆₁ fun x => In x s): 
  exists s, (acts G' \₁ is_init) ⊆₁ fun x => In x s.
Proof using.
  apply clos_rt_rtn1 in C; induction C as [|?? C]; eauto; desf.
  destruct C; ins; exists (a :: s0); ins.
  all: rewrite set_minus_union_l, IHC; basic_solver.
Qed.

Lemma Completions_p_sem G G' 
  (PSEM : p_sem G) 
  (CM   : Completion^* G G') : 
  p_sem G'.
Proof using.
  assert (Wf G').
  { eapply Completions_Wf; eauto; by cdes PSEM. }
  apply clos_rt_rtn1 in CM; induction CM as [|G1 G2 C]; eauto.
  inv C.
  { apply p_sem_Add_avail_r; eauto.
    eby eapply next_avail. }
  apply p_sem_Add_avail_w; eauto.
  eby eapply next_avail.
Qed.

Definition MaxCompletion G e G' := 
  << COMPL : Completion^* G G' >> /\ 
  << MAX   : next G' e >>.

Lemma MaxCompletion_det G G1 G2 e 
  (WF : Wf G)
  (MC1 : MaxCompletion G e G1)
  (MC2 : MaxCompletion G e G2) : G1 = G2.
Proof using.
  cdes MC1; cdes MC2.
  apply (Completion_semi_total WF COMPL) in COMPL0.
  assert (forall G1 G2 e 
            (WF : Wf G1)
            (C : Completion^* G1 G2) 
            (N1 : next G1 e)
            (N2 : next G2 e), G1 = G2) as A.
  { ins; apply clos_rt_rtn1 in C; destruct C as [|G' ? C]; eauto.
    apply clos_rtn1_rt in C0; assert (C0' := C0).
    apply Completions_Wf in C0'; eauto.
    assert (Ne := C); apply Completion_hb_max in C; desc; eauto.
    eapply next_Completion in Ne; eauto.
    eapply next_Completions in C0; eauto.
    { eby edestruct LR_irr; eapply LR_trans. }
    by intro; subst; apply LR_irr in Ne. }
  desf; eauto; [|symmetry]; eapply A; eauto; eapply Completions_Wf; eauto.
  by cdes MC2.
Qed.

Section Completion_terminate.

Variable G : execution.
Variable e : Event.
Hypothesis AV : avail G e.

Lemma p_sem_G_compl : p_sem G.
Proof using AV.
  cdes AV. eapply p_sem_mori; eauto.
Qed.

Variable s : list Event.
Hypothesis G_fin : (acts G \₁ is_init) ⊆₁ fun x => In x s.

Definition measure_compl G k := 
  exists l, 
    G_ord_corr G l /\ NoDup l /\ length l = k.

Definition mcG := length (undup (filterP (acts G \₁ is_init) s)).

Lemma measure_mcG : measure_compl G mcG.
Proof using G_fin.
  exists (undup (filterP (acts G \₁ is_init) s)); splits; eauto.
  split; in_simp; generalize G_fin; basic_solver.
Qed.

Definition Compl G G' := Completion G G' /\ ~ next G e.

Lemma ComplE : 
  Compl^* ⊆ Completion^*.
Proof using.
  apply inclusion_rt_rt; unfold Compl; basic_solver.
Qed.

Lemma measure_prev_ex : 
  forall x, Compl^* G x -> exists m, measure_compl x m.
Proof using G_fin.
  intros G' C; eapply ComplE, Completion_finite in C; eauto; desf.
  set (s' := undup (filterP (acts G' \₁ is_init) s0)).
  exists (length s'), s'; splits; unfold s'; eauto.
  split; in_simp; generalize C; basic_solver.
Qed.

Lemma in_remove_iff A eq_dec (l : list A) (x y : A) :
  In x (remove eq_dec y l) <-> In x l /\ x <> y.
Proof using.
  split; [apply in_remove|].
  induction l; intro F; ins; desf; eauto.
  right; eauto.
Qed.

Lemma dec_compl
      G1 G2 (C1: Compl^* G G1) (C2: Compl G1 G2)
      n1 n2 (M : measure_compl G1 n1) (M': measure_compl G2 n2) :
  n1 < n2.
Proof using.
  unfold measure_compl, G_ord_corr in *; desf.
  destruct C2 as [C2 _]; inv C2; ins.
  { assert (forall x y : Event, {x = y} + {x <> y}) as eq_dec.
    { ins; destruct (excluded_middle_informative (x = y)); vauto. }
    assert (Permutation l0 (remove eq_dec a l)) as P.
    { apply NoDup_Permutation; eauto.
      { generalize M'0; elim l; ins; apply nodup_cons in M'1; desf; eauto.
        apply nodup_cons; split; eauto.
        intro F; apply in_remove in F; desf. }
      intro e'. rewrite <-M, in_remove_iff, <-M'.
      split; [|basic_solver].
      cdes Next; cdes Next0.
      unfolder; split; [basic_solver|]; intro; desf. }
    rewrite P. apply remove_length_lt, M'.
    apply not_init_next in Next; basic_solver. }
  assert (forall x y : Event, {x = y} + {x <> y}) as eq_dec.
  { ins; destruct (excluded_middle_informative (x = y)); vauto. }
  assert (Permutation l0 (remove eq_dec a l)) as P.
  { apply NoDup_Permutation; eauto.
    { generalize M'0; elim l; ins; apply nodup_cons in M'1; desf; eauto.
      apply nodup_cons; split; eauto.
      intro F; apply in_remove in F; desf. }
    intro e'. rewrite <-M, in_remove_iff, <-M'.
    split; [|basic_solver].
    cdes Next; cdes Next0.
    unfolder; split; [basic_solver|]; intro; desf. }
  rewrite P. apply remove_length_lt, M'.
  apply not_init_next in Next; basic_solver.
Qed.

Lemma avail_Compl G' 
  (C : Compl^* G G') : 
  avail G' e.
Proof using AV.
  assert (p_sem G').
  { apply ComplE, Completions_p_sem in C; eauto.
    by apply p_sem_G_compl. }
  apply clos_rt_rtn1 in C; induction C as [|G1 G2 [C N] CM]; eauto.
  assert (C' := C).
  apply Completion_hb_max in C'; desf.
  eapply Completion_Restr in C; eauto; desf.
  apply avail_Restr in IHCM; eauto.
  { unfolder in IHCM; desf. }
  { by apply not_init_next in C'. }
  { cdes C'; cdes C'1; eby eapply p_sem_mori. }
  eapply clos_rtn1_rt, ComplE, Completions_Wf in CM; eauto.
  by destruct p_sem_G_compl.
Qed.

Lemma MaxCompletion_Compl G'
  (MC : MaxCompletion G e G') : 
  Compl^* G G'.
Proof using AV.
  assert (Wf G) as WF.
  { by destruct p_sem_G_compl. }
  cdes MC; apply clos_rt_rt1n in COMPL.
  apply clos_rt1n_rt.
  clear G_fin MC AV.
  induction COMPL as [|??? C]; vauto.
  assert (Wf y) by eby eapply Completion_Wf.
  econstructor; eauto; split; eauto; intro N.
  assert (C'' := COMPL).
  apply clos_rt1n_rt in COMPL.
  destruct C'' as [|?? C'].
  { eapply (next_Completion C) in MAX; eauto.
    by apply LR_irr in MAX. }
  apply clos_rt1n_rt in C''.
  apply Completion_hb_max in C'; desf.
  apply (LR_irr LR e). 
  apply (rewrite_trans_seq_cr_r (LR_trans LR)); exists e0; split.
  { eby eapply next_Completion. }
  tertium_non_datur (e0 = e); vauto; right.
  eapply (next_Completions COMPL); eauto.
Qed.


Lemma bounded_compl G' m (C: Compl^* G G') (M: measure_compl G' m) : m < K.
Proof using p_sem_finite AV.
  unfold measure_compl in *.
  apply ComplE in C; desf.
  apply (Completions_p_sem p_sem_G_compl) in C.
  apply p_sem_finite in C; desf.
  assert (Permutation l l0) as P.
  { apply NoDup_Permutation; eauto; ins.
    by cdes OC; cdes M; rewrite <-OC0, <-M1. }
  by rewrite P.
Qed.

Lemma G_min_ex : 
  exists G', Compl^* G G' /\ forall y, ~ Compl G' y.
Proof using p_sem_finite G_fin AV.
  by apply (r_min_ex _ measure_prev_ex dec_compl bounded_compl).
Qed.

Lemma MaxCompletion_ex : 
  exists G', MaxCompletion G e G'.
Proof using AV G_fin p_sem_finite.
  destruct G_min_ex as [G' [C NC]].
  exists G'; split; [by apply ComplE|].
  assert (~ next G' ≡₁ ∅) as N.
  { assert (F := C); eapply ComplE, Completion_finite in F; eauto; desf.
    intros N; apply avail_Compl in C.
    eapply next_avail_emp in N; eauto.
    by apply N in C. }
  clarify_not.
  tertium_non_datur (is_r n) as [R|W].
  { assert (Wf G') by by apply next_Wf in N.
    eapply ComplE, Completion_finite in C; eauto; desf.
    eapply MaximalWrite_ex with (e := n) in C; desf.
    specialize (NC (SetRF (Add G' n) n w)).
    clarify_not; destruct NC; by constructor. }
  assert (Wf G') by by apply next_Wf in N.
  eapply ComplE, Completion_finite in C; eauto; desf.
  eapply MaximalWrite_ex with (e := (InitEvent (loc n))) in C; desf.
  specialize (NC (SetCO (Add G' n) w n)).
  clarify_not; destruct NC. constructor; eauto.
  { by apply n_is_r. }
  cdes C; ins.
Qed.

End Completion_terminate.

Inductive Prev_step : execution -> Event -> Revisit -> execution -> Prop :=
  | Prev_rv G G' a e (ME : me G a) (R : is_r a)
    (RF : rf G e a) (Next : a <_next e) 
    (HBe : codom_rel (<| eq e |> ;; hb G) ≡₁ eq a)
    (MC : MaxCompletion (Restr G (set_compl (eq a ∪₁ eq e))) e G') :
    Prev_step G' e (RV a) G
  | Prev_nr_w G a (NINI : ~ is_init a) (ME : me G a) (W : is_w a) :
    Prev_step (Restr G (set_compl (eq a))) a NR G
  | Prev_nr_not_max G a e (ME : me G a) (R : is_r a)
    (RF : rf G e a) 
    (NMAX : e <_next a \/ ~ codom_rel (<| eq e |> ;; hb G) ≡₁ eq a) : 
    Prev_step (Restr G (set_compl (eq a))) a NR G.

Inductive Prev : relation execution := 
  | PBase G : Prev G G
  | PStep G1 G2 G3 e rv
    (PR1 : Prev G2 G3) (PR2 : Prev_step G1 e rv G2) :
    Prev G1 G3.

Lemma sub_execution_NR G G' e
  (Wf_G' : Wf G')
  (PR : Prev_step G e NR G') : 
  (G ⊆ G')%Ex.
Proof using.
  inv PR.
  all: apply Restr_clos_sub; eauto.
  1,3: unfolder; intros ???; destruct x; desf.
  all: cdes ME; cdes HBM_e; unfolder; intros ? HB ?; desf.
  all: eapply N_HB; vauto.
Qed.

Lemma Prev_p_sem G Gf 
  (Gf_p_sem : p_sem Gf) 
  (PR : Prev G Gf) : p_sem G.
Proof using.
  induction PR; eauto; specialize (IHPR Gf_p_sem).
  destruct rv as [a|].
  { inv PR2; cdes MC; cdes MAX; cdes MAX0. eby eapply p_sem_mori. }
  all: specialize (p_sem_Wf IHPR) as WF.
  all: eapply p_sem_mori; eauto; eby eapply sub_execution_NR.
Qed.

Lemma Prev_Wf G Gf 
  (Gf_Wf : Wf Gf) 
  (PR : Prev G Gf) : Wf G.
Proof using.
  induction PR; eauto; specialize (IHPR Gf_Wf).
  inv PR2.
  { cdes MC; apply Completions_Wf in COMPL; eauto.
    apply Wf_Restr; eauto; apply not_init_next in MAX.
    intros [] ? []; desf. }
  all: apply Wf_Restr; eauto; intros [] ??; desf.
Qed.

Section Prev_NR.

Context {Gf G G' : execution}.
Context {e : Event}.

Hypothesis Gf_full  : full Gf.
Hypothesis Gf_cons  : cons Gf.
Hypothesis Gf_Wf    : Wf Gf.
Hypothesis Gf_p_sem : p_sem Gf.

Hypothesis PR  : Prev_step G e NR G'.
Hypothesis PRf : Prev G' Gf.

Lemma Wf_G'_NR : Wf G'.
Proof using Gf_Wf PRf. eby eapply Prev_Wf. Qed.

Lemma me_LR_e_NR : me G × eq e ⊆ LR.
Proof using Gf_Wf PR PRf.
  assert (Wf_G' := Wf_G'_NR).
  unfolder; intros e1 e2 MEE; desf.
  assert (e1 <> e2).
  { intro; desf; inv PR; cdes MEE; cdes HBM_e; ins; unfolder in ACT; desf. }
  assert (hb_max G' e1 -> e1 <_next e2).
  { intro HBM; inv PR; apply ME in HBM; desf. }
  assert (sb G' e1 e2 -> e1 <_next e2).
  { intro SB; apply sb_LR; unfold sb in SB; unfolder in SB; desf. }
  inv PR; desf; apply me_Restr in MEE; desf; unfolder in MEE; desf; eauto.
  { apply (wf_rfD Wf_G') in MEE; unfolder in MEE; desf.
    by apply n_is_r in MEE1. }
  all: assert (R' := RF); eapply (wf_rff Wf_G') in RF; apply RF in MEE; desf.
Qed.

Lemma avail_G_NR : 
  avail G ⊆₁ avail G' ∪₁ eq e.
Proof using PRf PR Gf_p_sem.
  apply Prev_p_sem in PRf; eauto.
  inv PR; apply avail_Restr; cdes ME; eauto.
  by destruct e.
Qed.

Lemma GE_NR : G = Restr G' (set_compl (eq e)).
Proof using PR. inv PR. Qed.

Lemma me_e : me G' e.
Proof using PR. inv PR. Qed.

Lemma avail_e_Resrt_e : 
  avail G e.
Proof using PRf PR Gf_p_sem Gf_Wf.
  assert (Wf_G' := Wf_G'_NR).
  apply avail_avail_sbrf.
  { eapply Prev_Wf; vauto. }
  exists G'; splits.
  { eby eapply Prev_p_sem. }
  { by inv PR; cdes ME; cdes HBM_e. }
  { rewrite GE_NR; ins; unfolder; intros ?; desf. }
  { eapply sub_execution_NR; eauto. }
  rewrite GE_NR; unfolder; intros ? SBRF; ins.
  split.
  { desf; [unfold sb in SBRF|apply Wf_G' in SBRF];
    unfolder in SBRF; desf. }
  intro; desf; [by apply sb_irr in SBRF|].
  apply (wf_rfD Wf_G') in SBRF; unfolder in SBRF; desf.
  by apply n_is_r in SBRF.
Qed.

End Prev_NR.

Section Prev_RV.

Context {Gf G G' : execution}.
Context {e a : Event}.

Hypothesis Gf_full  : full Gf.
Hypothesis Gf_cons  : cons Gf.
Hypothesis Gf_Wf    : Wf Gf.
Hypothesis Gf_p_sem : p_sem Gf.

Hypothesis PR  : Prev_step G e (RV a) G'.
Hypothesis PRf : Prev G' Gf.

Lemma sub_execution_RV : 
  (Restr G' (set_compl (eq a ∪₁ eq e)) ⊆ G')%Ex.
Proof using PRf PR Gf_Wf.
  inv PR.
  apply Prev_Wf in PRf; eauto.
  cdes MC; apply not_init_next in MAX.
  apply Restr_clos_sub; eauto.
  { intros ??[]; desf; by destruct x. }
  unfolder; intros ? HB F; desf; clarify_not.
  { cdes ME; cdes HBM_e; eapply N_HB; vauto. }
  apply HB0, HBe; vauto.
Qed.

Lemma next_G : next G e.
Proof using PR. by inv PR; cdes MC. Qed.

Lemma me_LR_e_RV : me G × eq e ⊆ LR.
Proof using PR PRf Gf_Wf.
  inv PR.
  cdes MC.
  assert (Wf G) as WF by (eapply Prev_Wf; vauto).
  assert (Wf G') as WF' by (eapply Prev_Wf in PRf; eauto).
  assert (Wf (Restr G' (set_compl (eq a ∪₁ eq e)))).
  { apply not_init_next in MAX; apply Wf_Restr; eauto.
    unfolder; intros ???; desf; by destruct x. }
  intros e1 e2 [ME' ]; desf.
  tertium_non_datur (e1 = e2) as [|NEQ12]; desf.
  { cdes MAX; cdes MAX0.
    cdes ME'; cdes HBM_e; desf. }
  tertium_non_datur (acts G' e1) as [ACT|ACT].
  { tertium_non_datur (e1 = a) as [|NEQ]; desf.
    assert ((set_compl (eq a ∪₁ eq e2)) e1) as De1.
    { unfolder; intro; desf. }
    destruct (classic (hb_max G' e1)) as [HBM|NHBM].
    { eapply LR_trans; eauto.
      cdes ME; destruct (NM_e _ HBM); basic_solver. }
    cdes ME'; apply sub_Completions in COMPL; eauto.
    apply (sub_execution_hb_max WF COMPL) in HBM_e.
    { specialize (hb_max_Restr De1 NHBM HBM_e) as F; desf.
      clarify_not. unfolder in F; desf; destruct F0 as [F|F].
      { unfold sb in F; unfolder in F; desf; apply (sb_LR LR) in F0; eauto.
        by destruct LR; ins; eauto. }
      { destruct NEQ12; eby eapply (wf_rff WF'). }
      { apply sb_LR; unfold sb in F; unfolder in F; desf. }
      apply (wf_rfD WF') in F; unfolder in F; desf.
      apply (wf_rfD WF') in RF; unfolder in RF; desf.
      apply n_is_w in F1; desf. }
    basic_solver. }
  cdes MC.
  eapply next_max_Completion; [|eauto| |]; eauto.
  cdes ME'; cdes HBM_e.
  ins; split; eauto; unfolder; intro; desf.
Qed.

Lemma Wf_Restr_RV : 
  Wf (Restr G' (set_compl (eq a ∪₁ eq e))).
Proof using Gf_Wf PR PRf.
  apply Prev_Wf in PRf; eauto.
  inv PR; cdes MC.
  apply not_init_next in MAX.
  apply Wf_Restr; eauto; intros [] ? []; desf.
Qed.

Lemma hb_RV e' x
  (ACT1 : acts G' e')
  (ACT2 : acts G x) 
  (HB   : hb G e' x) : 
  hb G' e' x \/ (acts G \₁ acts G') x \/ x = a.
Proof using Gf_Wf PR PRf.
  inv PR.
  tertium_non_datur 
    (acts (Restr G' (set_compl (eq a ∪₁ eq e))) x) as [ACT|NACT]; vauto.
  { left.
    cdes MC; apply sub_Completions in COMPL.
    { assert (hb (Restr G' (set_compl (eq a ∪₁ eq e))) e' x) as HB'.
      { eapply sub_execution_hbE; [|eauto|basic_solver].
        eapply Prev_Wf; vauto. }
      assert (SUB := sub_execution_RV).
      assert (Wf G') as WF by (apply Prev_Wf in PRf; auto).
      apply (sub_execution_hbE WF) in HB'; auto.
      unfolder in HB'; desf. }
    by apply Wf_Restr_RV. }
  unfolder in NACT; desf; vauto.
  cdes MC; cdes MAX; cdes MAX0. contradiction.
Qed.

End Prev_RV.

Section Prev_Properties.

Context {Gf : execution}.

Hypothesis Gf_full  : full Gf.
Hypothesis Gf_cons  : cons Gf.
Hypothesis Gf_Wf    : Wf Gf.
Hypothesis Gf_p_sem : p_sem Gf.

Context {G : execution}.
Hypothesis PR : Prev G Gf.

Lemma me_avail : me G × avail G ⊆ LR.
Proof using PR Gf_p_sem Gf_full Gf_cons Gf_Wf.
  induction PR.
  { unfold full in Gf_full; rewrite Gf_full; basic_solver. }
  destruct rv as [a|].
  { intros e1 e2 [ME AV].
    destruct (next_G PR2) as [_ []]; [| |eapply LR_trans; eauto]; desf.
    all: eapply me_LR_e_RV; basic_solver. }
  assert (meLRe := PR2).
  eapply me_LR_e_NR in meLRe; vauto.
  erewrite avail_G_NR; eauto.
  rewrite cross_union_r. 
  apply inclusion_union_l; eauto.
  apply me_e, meE in PR2. rewrite PR2 in IHp.
  unfolder; unfolder in meLRe; unfolder in IHp.
  intros ???; desf; eapply LR_trans; [apply meLRe|]; eauto.
Qed.

Lemma Prev_cons : cons G.
Proof using PR Gf_p_sem Gf_cons Gf_Wf.
  clear Gf_full.
  induction PR; eauto.
  destruct rv as [a|].
  { inv PR2; cdes MC.
    eapply Completions_cons; eauto.
    eapply sub_execution_cons; [eby eapply sub_execution_RV|]; eauto. }
  erewrite GE_NR; eauto.
  inv PR2.
  all: eapply sub_execution_cons with (G' := G2); eauto.
  all: eapply sub_execution_NR; eauto; eby eapply Prev_Wf.
Qed.

Lemma next_Prev G' rv e
  (PR' : Prev_step G' e rv G) : 
  next G' e.
Proof using PR Gf_p_sem Gf_full Gf_cons Gf_Wf.
  destruct rv as [a|].
  { eby eapply next_G. }
  split.
  { eby eapply avail_e_Resrt_e. }
  intros ? AV; eapply avail_G_NR in AV; eauto.
  unfolder in AV; desf; vauto; right.
  apply me_avail; split; eauto.
  inv PR'.
Qed.

Lemma avail_Restr_RV G' e a
  (PR1 : Prev_step G' e (RV a) G) : 
  avail (Restr G (set_compl (eq a ∪₁ eq e))) a.
Proof.
  inv PR1; cdes MC.
  assert (C := Prev_cons).
  apply avail_avail_sb; eauto; [eby eapply Wf_Restr_RV|].
  exists G; splits.
  { by apply Prev_p_sem in PR. }
  { by cdes ME; cdes HBM_e. }
  { ins; unfolder; intro; desf; clarify_not. }
  { eby eapply sub_execution_RV. }
  { intros ? SB; ins; unfold sb in SB; unfolder in SB; desf.
    split; eauto; unfolder; intro; desf.
    { by apply ext_sb_irr in SB0. }
    eapply LR_irr, LR_trans; eauto; by apply sb_LR. }
  by intro HB; apply (cons_hb_irr cons) in HB.
Qed.

Lemma avail_Restr_e_RV e a
  (RF : rf G e a)
  (R : is_r a)
  (HBe : codom_rel (⦗eq e⦘ ⨾ hb G) ≡₁ eq a)
  (MAX: ~ is_init e)
  (ME: me G a) :
  avail (Restr G (set_compl (eq a ∪₁ eq e))) e.
Proof.
  assert (C := Prev_cons).
  exists G; splits.
  { by apply Prev_p_sem in PR. }
  { apply (Prev_Wf Gf_Wf PR) in RF; unfolder in RF; basic_solver. }
  { ins; unfolder; intro; desf; clarify_not. }
  { apply Restr_clos_sub; eauto.
    { eby eapply Prev_Wf. }
    { intros ??[]; desf; by destruct x. }
    unfolder; intros ? HB F; desf; clarify_not.
    { cdes ME; cdes HBM_e; eapply N_HB; vauto. }
    apply HB0, HBe; vauto. }
  intros ? HB; ins; split.
  { apply (wf_hbE (Prev_Wf Gf_Wf PR)) in HB.
    unfolder in HB; basic_solver. }
  unfolder; intro; desf.
  { eapply cons_hb_irr; eauto.
    eapply hb_trans; eauto; vauto. }
  by apply (cons_hb_irr _ C) in HB.
Qed.

Lemma G_NRestr G' e a
  (PR1 : Prev_step G' e (RV a) G): 
  Restr G (set_compl (eq a ∪₁ eq e)) <> G'.
Proof.
  inv PR1; cdes MC.
  intro; desf; cdes MAX.
  specialize (MAX1 _ (avail_Restr_RV PR1)); desf.
  { by apply LR_irr in Next. }
  by apply (LR_trans _ _ _ _ Next), LR_irr in MAX1.
Qed.

End Prev_Properties.

Section Terminate.

Context {Gf : execution}.
Context {sf : list Event}.

Hypothesis Gf_full  : full Gf.
Hypothesis Gf_cons  : cons Gf.
Hypothesis Gf_Wf    : Wf Gf.
Hypothesis Gf_p_sem : p_sem Gf.
Hypothesis Gf_finite : (acts Gf \₁ is_init) ⊆₁ fun x => In x sf.

Notation "G '~~>*' G'" := (Prev G G') (at level 20).
Notation "G '~(' e ')~(' rv ')~>' G'" := (Prev_step G e rv G') (at level 20).

Inductive Prev_step_RW G : list Event -> execution -> list Event -> Prop :=
  | NREVISIT_RW G' RW e (nr : Prev_step G e NR G') :
    Prev_step_RW G RW G' RW
  | REVISIT_RW G' RW e a (rv : Prev_step G e (RV a) G') :
    Prev_step_RW G (e :: RW) G' RW.

Inductive Prev_RW  G RW : execution -> list Event -> Prop :=
  | Base_RW : Prev_RW G RW G RW
  | Step_RW G1 RW1 G2 RW2
    (PR1 : Prev_RW      G1 RW1 G2 RW2)
    (PR2 : Prev_step_RW G  RW  G1 RW1) :
    Prev_RW G RW G2 RW2.

Lemma r_str_cont A (P : A -> Prop) (r : relation A) x y 
  (Px : P x) (NPy : ~ P y) (rxy : r^* x y) :
  exists z w, r^* x z /\ r z w /\ r^* w y /\ P z /\ ~ P w.
Proof.
  apply clos_rt_rt1n in rxy.
  induction rxy; [basic_solver|].
  tertium_non_datur (P y) as [Py|Py].
  { specialize (IHrxy Py NPy); desf; exists z0, w; splits; eauto.
    apply clos_rt1n_rt; econstructor; eauto.
    by apply clos_rt_rt1n. }
  exists x, y; splits; vauto;  by apply clos_rt1n_rt.
Qed.

Lemma Completion_nextE G G' 
  (CM : Completion G G') : 
  next G ≡₁ acts G' \₁ acts G.
Proof.
  assert (forall a, next G a -> next G ≡₁ eq a) as N.
  { split; [intros ??; eby eapply next_uniq|basic_solver]. }
  destruct CM; ins; rewrite (N _ Next); cdes Next; cdes Next0; basic_solver.
Qed.

Lemma Prev_n1 G1 G2 G3 e rv
  (PR1 : G1 ~~>* G2)
  (PR2 : G2 ~(e)~(rv)~> G3) : 
  G1 ~~>* G3.
Proof.
  induction PR1; vauto.
  econstructor; vauto; by apply IHPR1.
Qed.

Lemma Prev_finite G G' s
  (S  : (acts G' \₁ is_init) ⊆₁ fun x => In x s)
  (PR : G ~~>* G') :
  exists s, (acts G \₁ is_init) ⊆₁ fun x => In x s.
Proof.
  induction PR; eauto; specialize (IHPR S); desf.
  inv PR2; ins.
  { cdes MC.
    eapply Completion_finite with (s := s0) in COMPL; eauto.
    ins. rewrite <-set_inter_minus_l, IHPR; basic_solver. }
  all: exists s0; rewrite <-set_inter_minus_l, IHPR; basic_solver.
Qed.

Lemma Prev_trans : transitive Prev.
Proof.
  intros G1 G2 G3 PR1 PR2.
  induction PR1; auto.
  econstructor; [|eauto]; auto.
Qed.

Lemma me_Add_evs G1 G2 e a 
  (PR1 : G1 ~(e)~(RV a)~> G2)
  (PR2 : G2 ~~>* Gf) : 
  me G2 × (acts G1 \₁ acts G2) ⊆ LR^?.
Proof.
  intros e1 e2 [ME [ACT NACT]].
  assert (PR := PR2).
  apply me_avail in PR2; auto.
  inv PR1. eapply (meE LR G2 e1) in ME0; desf.
  cdes MC.
  apply clos_rt_rt1n in COMPL.
  destruct COMPL as [|G' G1 C].
  { ins; unfolder in ACT; desf. }
  assert (C' := C).
  assert (~ is_init a) as NINIa.
  { by destruct a. }
  assert (~ is_init e) as NINIe.
  { by apply not_init_next in MAX.  }
  apply Completion_hb_max in C; desf.
  { tertium_non_datur (e2 = a); desf; vauto.
    tertium_non_datur (e2 = e); desf; vauto.
    cdes MC.
    apply LRcr_trans with (y := e0).
    { tertium_non_datur (e0 = a); desf; vauto.
      tertium_non_datur (e0 = e); desf; vauto.
      right; apply PR2; split; eauto.
      cdes C; apply avail_Restr2 in C1; eauto.
      { unfolder in C1; desf. }
      { by apply Prev_p_sem in PR. }
      by cdes ME. }
    eapply Completions_Adds; eauto.
    ins; split; eauto; unfolder; intro; desf. }
  apply Prev_Wf in PR; eauto.
  apply Wf_Restr; auto; unfolder; intros ???; desf.
Qed.

Lemma next_Restr_RV G1 G2 e a 
  (PR1 : G1 ~(e)~(RV a)~> G2)
  (PR2 : G2 ~~>* Gf) : 
  next (Restr G2 (set_compl (eq a ∪₁ eq e))) a.
Proof.
  split.
  { eby eapply avail_Restr_RV. }
  intros ? AV; inv  PR1; cdes ME.
  apply avail_Restr2 in AV; eauto.
  { unfolder in AV; desf; vauto.
    right; eapply me_avail; eauto; split; eauto. }
  { by destruct a. }
  { eapply next_Prev, not_init_next in PR1; eauto. }
  eby eapply Prev_p_sem.
Qed.

Lemma In_RV_a G1 G2 e a 
  (PR1 : G1 ~(e)~(RV a)~> G2)
  (PR2 : G2 ~~>* Gf) : acts G1 a.
Proof.
  inv PR1; cdes MC.
  apply clos_rt_rt1n in COMPL; destruct COMPL as [|?? C].
  { apply (next_uniq (next_Restr_RV PR1 PR2)) in MAX; desf.
    by apply LR_irr in Next. }
  apply clos_rt1n_rt, sub_Completions in COMPL.
  { apply COMPL; apply next_Restr_RV in PR1; eauto.
    destruct C; ins; apply (next_uniq Next0) in PR1; desf; vauto. }
  eapply Completion_Wf; eauto; eby eapply next_Wf, next_Restr_RV.
Qed.

Definition Prev_RW_rel := 
  fun '(G, RW) '(G', RW') => Prev_step_RW G' RW' G RW.

Definition Prev_rel := 
  fun G G' => exists e rv, Prev_step G' e rv G.

Lemma Prev_RW_path {G RW G' RW'} : 
  Prev_RW G RW G' RW' <-> 
  exists p : list (execution * list Event),
    path Prev_RW_rel (G', RW') p /\ last p (G', RW') = (G, RW).
Proof.
  split; intro PR; desf.
  { induction PR; [exists nil|]; desf; vauto.
    exists (p ++ (G, RW) :: nil); split.
    { apply cat_path; rewrite IHPR0; vauto. }
    apply last_last. }
  generalize dependent G.
  generalize dependent RW.
  induction p using rev_ind; ins; vauto.
  apply cat_path in PR; desf.
  rewrite last_last in PR0; destruct x; desf; ins; desf.
  destruct (last p (G', RW')); ins; econstructor; eauto.
Qed.

Lemma Prev_RW_Prev G RW G' RW' 
  (PR: Prev_RW G RW G' RW') : 
  G ~~>* G'.
Proof.
  induction PR; vauto.
  destruct PR2; vauto.
Qed.

Lemma path_RW_path p G RW
  (PT : path Prev_RW_rel (G, RW) p) :
  path Prev_rel G (map fst p).
Proof.
  generalize dependent G.
  generalize dependent RW.
  induction p; ins; destruct a; ins; split; desf; eauto.
  inv PT; vauto.
Qed.

Lemma Prev_path {G G'} : 
  G ~~>* G' <-> 
  exists p : list execution,
    path Prev_rel G' p /\ last p G' = G.
Proof.
  split; intro PR; desf.
  { induction PR; [exists nil|]; desf; vauto.
    exists (p ++ G1 :: nil); split.
    { apply cat_path; ins; splits; vauto. }
    apply last_last. }
  generalize dependent G'.
  induction p using rev_ind; ins; vauto.
  apply cat_path in PR; ins; desf.
  rewrite last_last; desf; ins.
  unfold Prev_rel in PR0; desf.
  econstructor; eauto.
Qed.

Lemma Prev_rel_Prev G G' : 
  G ~~>* G' <-> Prev_rel^* G' G.
Proof.
  split; intros PR.
  { apply clos_rtn1_rt.
    induction PR; vauto; econstructor; vauto. }
  apply clos_rt_rtn1 in PR; induction PR as [|?? P]; vauto.
  unfold Prev_rel in P; desf; vauto.
Qed.

Lemma before_revisit G e' e a G''' G'' p
  (PRf : G'' ~~>* Gf)
  (NACT : ~ acts G'' e \/ e = a) (ACT : acts G''' e)
  (Inp : In G (G''' :: p)) (PT : path Prev_rel G''' p)
  (InG : Forall (fun x => acts x e) p)
  (PR3: G''' ~(e')~(RV a)~> G''): 
  << ME_G : eq e × me G ⊆ LR^? >> /\
  << HB_e : <|eq e|> ;; hb G ⊆ LR^? >>.
Proof.
  assert (S := Prev_finite _ Gf_finite PRf); desc.
  assert (WF := Prev_Wf Gf_Wf PRf).
  elim Inp using in_list_ind.
  { clear G Inp; inv PR3.
    assert (e <> e') as Nee'.
    { intro; desf; apply WF in RF; unfolder in RF; desf.
      by apply LR_irr in Next. }
    cdes MC; apply clos_rt_rtn1 in COMPL. destruct COMPL as [|Gt G CM].
    { ins; unfolder in ACT; desf; clarify_not. }
    apply clos_rtn1_rt in COMPL.
    assert (Wf (Restr G'' (set_compl (eq a ∪₁ eq e')))).
    { apply Wf_Restr; eauto; apply not_init_next in MAX.
      intros [] ? []; desf. }
    splits.
    { assert (CM' := CM).
      apply Completion_hb_max in CM; desc.
      { intros e1 e2 [? ME2]; desc.
        apply LRcr_trans with (y := e0).
        { apply (In_Completion _ CM') in ACT; desc; subst.
          destruct ACT as [ACT|ACT].
          { apply (next_uniq CM) in ACT; vauto. }
          right; eapply next_max_Completion; try (eapply COMPL); eauto.
          unfolder; splits; eauto; ins; unfolder; intro; desf.
          clarify_not. }
        by cdes ME2; apply NM_e. }
      eby eapply Completions_Wf. }
    set (P := fun G => ~ acts G e); cdes MC.
    apply r_str_cont with (P := P) in COMPL0; ins. 
    { desc; unfold P in *; clarify_not.
      assert (Wf z).
      { eapply Completions_Wf; eauto. }
      assert (Wf w).
      { eapply Completion_Wf; eauto. }
      specialize (Completion_nextE COMPL1) as [? N].
      assert ((acts w \₁ acts z) e) as ACT' by basic_solver.
      specialize (N e ACT'); assert (C := COMPL1).
      apply Completion_hb_max in C; desc; eauto.
      apply (next_uniq C) in N; desc.
      intros e1 e2 HB; unfolder in HB; desc; clear P; subst.
      set (P := fun G => ~ acts G e2).
      unfolder in ACT';
      apply r_str_cont with (P := P) in COMPL2; ins.
      { desc; clarify_not; right.
        eapply next_max_Completion with (G := z) (G' := z0); vauto.
        { eapply Completion_nextE; basic_solver. }
        split; eauto.
        apply sub_Completions in COMPL2; eauto.
        by apply COMPL2. }
      { intro ACT2; eapply C0 with (x := e2).
        exists e1, e1; split; [basic_solver|].
        eapply sub_execution_hbE; [| |basic_solver].
        { eby eapply Completions_Wf. }
        by apply sub_Completions. }
      unfold P; intros [].
      apply wf_hbE in HB0; unfolder in HB0; desc; eauto.
      by apply next_Wf in MAX0. }
    unfold P; ins; unfolder; intro; desf; clarify_not. }
  intros G1 [p1[p2 [G2 PR0]]]; desc.
  assert (G2 ~~>* G'').
  { eapply Prev_n1; eauto.
    destruct p1; ins; injection PR0; ins; vauto.
    eapply Prev_rel_Prev, path_r_str; eauto.
    apply in_app_iff; basic_solver. }
  assert (E := PR0).
  eapply path_neigb_rel in PR0; eauto.
  unfold Prev_rel in PR0; desc.
  destruct rv as [a'|].
  { splits.
    { intros e1 e2 [? ME]; desc; subst.
      assert (me G2 a') by inv PR0.
      apply LRcr_trans with (y := a').
      { apply ME_G; split; auto. }
      inv PR0.
      cdes MC; apply Completions_hb_max in COMPL.
      { desc. clear NACT. clarify_not. subst.
        { apply LRcr_trans with (y := e).
          { eapply me_Add_evs; [apply PR0| |].
            { eapply Prev_trans; vauto. }
            cdes COMPL0; basic_solver. }
          by apply ME. }
        unfolder in COMPL; desf.
        { by apply ME. }
        cdes COMPL0; cdes MAX; cdes MAX0; contradiction. }
      { assert (Wf G2).
        { eapply Prev_Wf; eauto; eapply Prev_trans; vauto. }
        apply Wf_Restr; eauto; apply not_init_next in MAX.
        intros [] ? []; desf. }
      eapply G_NRestr; eauto; eapply Prev_trans; vauto. }
    intros e1 e2 HB; unfolder in HB; desc; subst.
    assert (G2 ~~>* Gf) as PR2f.
    { eapply Prev_trans; vauto. }
    assert (Wf G1).
    { eapply Prev_Wf; eauto.
      econstructor; eauto. }
    apply wf_hbE in HB0; eauto; unfolder in HB0; desc.
    assert (acts G2 e1) as ACT1.
    { assert (In G2 (G''' :: p)) as IN.
      { rewrite E, in_app_iff; basic_solver. }
      clear Inp; ins; desf; eapply ForallE in InG; eauto. }
    assert (me G2 a') as ME by inv PR0.
    apply (hb_RV Gf_Wf PR0 PR2f ACT1 HB2) in HB1; desc.
    destruct HB1 as [HB1|[HB1|HB1]]; subst.
    { apply HB_e; basic_solver. }
    { apply LRcr_trans with (y := a').
      { apply ME_G; basic_solver. }
      eapply me_Add_evs; [apply PR0| |]; auto.
      split; auto. }
    by apply ME_G; basic_solver. }
  assert (Wf G2) as Wf_G2. 
  { eapply Prev_Wf; eauto. }
  assert (⦗eq e⦘ ⨾ hb G1 ⊆ LR^?) as EHB.
  { eapply sub_execution_NR in PR0; eauto.
    rewrite (sub_execution_hbE Wf_G2 PR0), <-seqA, HB_e.
    basic_solver. }
  splits; eauto; ins.
  assert (G1 ~~>* G''); vauto.
  assert (Wf G1) as WF1.
  { by eapply Prev_Wf; [apply WF|]. }
  apply Prev_finite with (G := G1) in S; eauto.
  clear Inp; desc.
  apply hb_max_ex with (e := e) in S; desc; eauto.
  { intros e1 e2 [? ME]; desc; apply LRcr_trans with (y := m); subst.
    { destruct HBxm as [HB|HB]; desc; vauto.
      apply EHB; basic_solver. }
    by apply ME. }
  { eapply cons_hb_irr, Prev_cons; eauto; eby eapply Prev_trans. }
  eapply ForallE in InG; eauto.
  destruct p1; ins; injection E; ins; desc; subst; vauto.
  apply in_app_iff; basic_solver.
Qed.

Lemma RV_hb_LR e' e a G' G
  (PRf : G ~~>* Gf)
  (NACT : ~ acts G e \/ e = a) (ACT : acts G' e)
  (PR3: G' ~(e')~(RV a)~> G) :
  <|eq e|> ;; hb G' ⊆ LR^?.
Proof.
  eapply before_revisit in PR3; vauto; by desc.
Qed.

Lemma RV_RV G1 G2 a e
  (PR : G1 ~(e)~(RV a)~> G2) :
  ~ exists G3 G4 e' a' p, 
    << PR23 : path Prev_rel G3 p           >> /\
    << lp   : last p G3 = G2               >> /\
    << ALL  : Forall (fun x => acts x e) p >> /\
    << PR34 : G3 ~(e')~(RV a')~> G4        >> /\
    << PR4f : G4 ~~>* Gf                   >> /\
    << ACT3 : acts G3 e                    >> /\
    << ACT4 : ~ acts G4 e                  >>.
Proof.
  intro; desf.
  eapply (@before_revisit (last p G3)) with (e := e) in PR34; eauto.
  { inv PR; desf.
    assert (LR^? e a) as [|F]; desf.
    { apply HB_e; unfolder; splits; vauto. }
    { by apply LR_irr in Next. }
    eby eapply LR_irr, LR_trans. }
  apply last_in.
Qed.

Lemma RV_in_Gf G1 G2 e a 
  (PR : G1 ~(e)~(RV a)~> G2)
  (PRf : G2 ~~>* Gf) : 
  acts Gf e.
Proof.
  tertium_non_datur (acts Gf e) as [|NACT]; auto; exfalso.
  assert (Wf G2) by by apply Prev_Wf in PRf.
  apply Prev_path in PRf; desf.
  set (P := (fun x => acts x e)).
  assert (PT := PRf).
  apply path_cont with (P0 := P) in PRf; try basic_solver.
  { desf.
    apply RV_RV in PR; apply PR.
    unfold Prev_rel in P12; desf.
    destruct rv as [a0|].
    { exists x2, x1, e0, a0, p2; splits; eauto.
      { rewrite app_comm_cons' in pE;
        eapply sub_path in pE; eauto. }
      { by rewrite <- (last_cons Gf Gf), pE, last_app_cons, last_cons. }
      { apply Forall_cons in P1; desf. }
      { destruct p1; injection pE; ins; desf; vauto.
        eapply Prev_rel_Prev, path_r_str; eauto.
        apply in_app_iff; basic_solver. }
      apply Forall_cons in P1; desf. }
    erewrite GE_NR in P1; eauto.
    apply Forall_cons in P1; cdes P1.
    unfold P in P0, NP2; ins; unfolder in P0; desf. }
  inv PR. apply wf_rfE in RF; unfolder in RF; desf.
Qed.

Lemma Prev_step_RW_rv G RW G' e
  (PR: Prev_step_RW G (e :: RW) G' RW) : 
  exists a, Prev_step G e (RV a) G'.
Proof.
  inv PR; vauto.
  apply f_equal with (f := (@length _)) in H1; ins; lia.
Qed.

Lemma RW_in_Gf G RW
  (PR : Prev_RW G RW Gf nil) :
  (fun x => In x RW) ⊆₁ (acts Gf \₁ is_init).
Proof.
  intros e ?.
  assert (RV_in_Gf := RV_in_Gf).
  remember nil.
  induction PR; desf.
  inv PR2; eauto; ins; desf; eauto.
  apply Prev_step_RW_rv in PR2; desf.
  apply Prev_RW_Prev in PR; split.
  { eby eapply RV_in_Gf. }
  inv rv; cdes MC.
  by apply not_init_next in MAX.
Qed.

Lemma RW_dec G G' RW e
  (PR1 : Prev_step_RW G (e :: RW) G' RW)
  (PRf : Prev_RW G' RW Gf nil) :
  ~ In e RW.
Proof.
  assert (Wf G') as Wf_G' by by apply Prev_RW_Prev, Prev_Wf in PRf.
  intro IN.
  set (P := fun '(G,RW) => acts G e /\ In e RW).
  assert (Pf := proj1 Prev_RW_path PRf); desf.
  assert (PATH := Pf).
  apply path_cont with (P0 := P) in Pf; desf; eauto; [|firstorder|].
  { destruct x1 as [G0 RW2].
    destruct x2 as [G2 RW1]; ins.
    clarify_not.
    { inv P12.
      apply Forall_cons in P1; destruct P1 as [PG1 P1].
      { inv nr; ins; unfolder in PG1; desf. }
      assert (G0 ~~>* Gf) as PR3.
      { destruct p1; ins; injection pE; ins; desf; vauto.
        apply path_RW_path in PATH.
        eapply Prev_rel_Prev, path_r_str; eauto.
        rewrite map_app, in_app_iff; basic_solver. }
      assert (path Prev_rel G2 (map fst p2)) as PT.
      { destruct p1; ins; injection pE; ins; desf; ins; desf.
        { by apply path_RW_path in PATH0. }
        rewrite 2?app_comm_cons', cat_path, last_last in PATH; desf.
        by apply path_RW_path in PATH0. }
      eapply (@before_revisit G') with (e := e) in rv; eauto.
      { desf.
        apply Prev_step_RW_rv in PR1; desf; inv PR1.
        specialize (HB_e e a0); destruct HB_e as [|HB_e]; desf.
        { unfolder; split; eauto.
          destruct HBe as [? HBe]; specialize (HBe _ eq_refl).
          generalize HBe; basic_solver. }
        { by apply LR_irr in Next. }
        eapply LR_irr, LR_trans; eauto. }
      { apply Forall_cons in P1; basic_solver. }
      { apply (f_equal (fun p => last p (Gf, nil))) in pE.
        rewrite last_app_cons, ?last_cons, Pf0 in pE.
        apply (f_equal fst) in pE; rewrite last_map in pE.
        simpl in pE; rewrite pE; apply last_in. }
      apply Forall_cons in P1; desf.
      apply ForallE; intros x INx.
      apply in_map_iff in INx; desf.
      eapply ForallE in P0; eauto; destruct x0; basic_solver. }
    apply Forall_cons in P1; desf.
    inv P12; ins; desf; eapply next_Prev in rv; vauto.
    { by cdes rv; cdes rv0. }
    destruct p1; ins; injection pE; ins; desf; vauto.
    apply path_RW_path in PATH; eapply Prev_rel_Prev, path_r_str; eauto.
    rewrite map_app, in_app_iff; basic_solver. }
  rewrite Pf0; split; eauto.
  inv PR1.
  { apply (f_equal (@length _)) in H1; ins; lia. }
  inv rv; apply Wf_G' in RF; unfolder in RF; desf.
Qed.

Lemma NoDup_RW G RW (PR : Prev_RW G RW Gf nil) : 
  NoDup RW.
Proof.
  assert (RW_dec := RW_dec).
  remember nil.
  induction PR; desf.
  destruct PR2; eauto; apply nodup_cons; splits; eauto.
  eapply RW_dec; vauto.
Qed.

Lemma nil_acts_n_prev G 
  (PRf : G ~~>* Gf)
  (NPR : ~ exists G', Prev_rel G G') : 
  G = G0.
Proof.
  assert (PRf' := PRf).
  destruct (Prev_finite _ Gf_finite PRf) as [s FIN].
  assert (PSEM := Prev_p_sem Gf_p_sem PRf); desf.
  assert (CONS := Prev_cons Gf_cons Gf_Wf Gf_p_sem PRf).
  apply Prev_Wf in PRf; eauto.
  rewrite <-eq_executionE.
  apply nil_acts; eauto.
  split; [apply NNPP; intro F|by apply PRf].
  clarify_not.
  eapply ninit_me_ex with (LR := LR) in F; eauto; [|eby eapply cons_hb_irr].
  desf; apply NPR.
  tertium_non_datur (is_w m) as [W|R].
  { exists (Restr G (set_compl (eq m))), m; vauto. }
  apply n_is_w in R.
  apply cons_complete in CONS.
  cdes MEm; cdes HBM_e.
  specialize (CONS _ (conj ACT R)); destruct CONS as [e RF].
  destruct 
    (classic (~ (m <_next e /\ codom_rel (<| eq e |> ;; hb G) ≡₁ eq m))) 
    as [M|M].
  { exists (Restr G (set_compl (eq m))), m, NR.
    eapply Prev_nr_not_max; eauto.
    apply not_and_or in M; desf; vauto; left.
    edestruct (LR_total LR) with (a := m) (b := e); eauto.
    { apply PRf in RF; unfolder in RF; desf. }
    { intro; desf; apply (wf_rfD PRf) in RF.
      unfolder in RF; desf; by apply n_is_w in R. }
    contradiction. }
  clarify_not; desf.
  assert (avail (Restr G (set_compl (eq m ∪₁ eq e))) e) as AVR.
  { eapply avail_Restr_e_RV; eauto; intro.
    eapply LR_irr, LR_trans; eauto.
    by apply sb_LR; destruct e, m. }
  eapply MaxCompletion_ex in AVR.
  { desf; exists G'; exists e; vauto. }
  ins. generalize FIN. basic_solver.
Qed.

Lemma Prev_RW_rel_Prev_RW G1 RW1 G2 RW2 
  (PR : Prev_RW_rel＊ (G1, RW1) (G2, RW2)): 
  Prev_RW G2 RW2 G1 RW1.
Proof using.
  apply clos_rt_rtn1 in PR.
  remember (G1, RW1) as p1.
  remember (G2, RW2) as p2.
  generalize dependent G2.
  generalize dependent RW2.
  induction PR; ins; desf; vauto.
  destruct y as [G RW]; ins; econstructor; eauto.
Qed.

Lemma p_sem_finite_all G (SEM : p_sem G) l
  (GC : G_ord_corr G l) (ND : NoDup l) :
  length l < K.
Proof using p_sem_finite.
  apply p_sem_finite in SEM; desf.
  enough (length l = length l0) by lia.
  enough (Permutation l l0) as P by by rewrite P.
  apply NoDup_Permutation; eauto; ins.
  unfold G_ord_corr in GC, OC.
  by rewrite <-OC,<-GC.
Qed.

Lemma GRW_min_ex : 
  exists GRW, Prev_RW_rel^* (Gf, nil) GRW /\ forall y, ~ Prev_RW_rel GRW y.
Proof.
  set (measure := 
    fun '(G, RW) n => 
    exists l, G_ord_corr G l /\ NoDup l /\ 
      n = length (RW : list Event) * (K + 1) + (K - length l)).
  eapply r_min_ex with (measure := measure) (B := K * (K + 2) + (K + 1)).
  { intros [G RW] PR.
    eapply Prev_RW_rel_Prev_RW, Prev_RW_Prev, Prev_finite in PR; eauto.
    desf.
    set (s' := filterP (acts G \₁ is_init) (undup s)).
    exists (length RW * (K + 1) + (K - length s')), s'; splits; unfold s'; eauto.
    unfold G_ord_corr. ins. in_simp.
    split; generalize PR; basic_solver. }
  { intros [G1 RW1] [G2 RW2] PR1 PR2 m1 m2 M1 M2.
    apply Prev_RW_rel_Prev_RW in PR1; ins; desf.
    destruct PR2; ins; [|lia].
    enough (length l < length l0 < K) by lia.
    split.
    { tertium_non_datur (length l0 <= length l) as [L|]; [|lia].
      apply NoDup_Permutation_bis in L; eauto.
      { apply Permutation_sym in L.
        apply Permutation_in with (x := e) in L.
        { inv nr; apply M2 in L; ins;
          unfolder in L; desf. }
        apply M1; inv nr; cdes ME; cdes HBM_e; split; eauto.
        by destruct e. }
      intros ? IN; apply M2 in IN; apply M1.
      inv nr; ins; generalize IN; basic_solver. }
    apply Prev_RW_Prev, Prev_p_sem in PR1; eauto.
    eapply p_sem_finite_all; eauto. }
  intros [G RW] m PR M.
  apply Prev_RW_rel_Prev_RW in PR.
  assert (NoDup RW) by by apply NoDup_RW in PR.
  apply RW_in_Gf in PR; ins; desf.
  apply Plus.plus_lt_compat; try lia.
  enough (length RW < K).
  { apply PeanoNat.Nat.mul_lt_mono; lia. }
  assert (FIN := p_sem_finite Gf_p_sem); desf.
  enough (length RW <= length l0) by lia.
  apply NoDup_incl_length; eauto.
  intros ??. by apply OC, PR.
Qed.

Theorem G0_prev_Gf : G0 ~~>* Gf.
Proof.
  destruct GRW_min_ex as [[G RW] [PR M]].
  apply Prev_RW_rel_Prev_RW in PR.
  assert (G = G0) as EQ.
  {  apply nil_acts_n_prev.
    { by apply Prev_RW_Prev in PR. } 
    intros PRr; desf.
  unfold Prev_rel in PRr; desf.
  set (RW' := match rv with RV a => e :: RW | _ => RW end).
  destruct (M (G', RW')); ins; destruct rv; vauto. }
  rewrite <-EQ.
  by apply Prev_RW_Prev in PR.
Qed.

Lemma hb_Add_Prev G1 G2 e a x y
  (PR1 : G1 ~(e)~(RV a)~> G2)
  (W : is_w y)
  (PR2 : G2 ~~>* Gf) 
  (ACTx : (acts G1 \₁ acts G2 ∪₁ eq a) x) 
  (ACTy : acts G1 y)
  (HBT  : y <_next x \/ hb (Add G1 e) y e \/ acts G2 y) :
    exists G'1 G'2, 
      << ACT1 : acts G'2 y         >> /\
      << ACT2 : acts G'2 x         >> /\
      << COMP : Completion G'1 G'2 >> /\
      << Next : next G'1 x         >> /\
      << SUB1 : (G'1 ⊆ G1)%Ex      >> /\
      << SUB2 : (G'2 ⊆ G1)%Ex      >>.
Proof.
  assert (Wf G2) as Wf_G2 by by eapply Prev_Wf; vauto.
  assert (Wf G1) by by eapply Prev_Wf; vauto.
  inv PR1; cdes MC.
  assert (Wf (Restr G2 (set_compl (eq a ∪₁ eq e)))) as Wf_R.
  { eapply sub_execution_wf; [|apply Wf_G2].
    eapply sub_execution_RV; [apply Gf_Wf| |]; eauto. }
  apply (wf_rfD Wf_G2) in RF; unfolder in RF; desc.
  assert (y <_next x \/ acts G2 y) as LRACT.
  { desf; vauto; right.
    assert (forall e' : Event, acts G1 e' -> ~ ext_sb e e').
    { eby ins; eapply avail_sb_max; eauto; cdes MAX. }
    apply hb_add_max in HBT; eauto; desf.
    destruct (classic (acts (Restr G2 (set_compl (eq a ∪₁ eq e))) e2)) as [A|A].
    { unfolder in HB; desf; [ins; generalize A; basic_solver|].
      apply sub_Completions in COMPL; eauto.
      eapply sub_execution_hb in A; eauto.
      ins; generalize A; basic_solver. }
    apply ext_sb_tid_init' in SB; unfolder in SB; desf.
    { set (P := fun x =>  ~ acts x e2).
      assert (~ is_init e) by eby eapply not_init_next.
      apply MaxCompletion_Compl in MC; [|eapply avail_Restr_e_RV; eauto].
      eapply (r_str_cont P A) in MC; ins; desf.
      clear A; unfold P in *; clarify_not; cdes MC0.
      exfalso.
      assert (next z e2) as N by by eapply Completion_nextE; basic_solver.
      assert (avail z e) as N'.
      { by apply avail_Compl in MC; [|eapply avail_Restr_e_RV; eauto]. }
      cdes N.
      eapply avail_same_tid in SB0; eauto; desf. }
    by apply Wf_R in SB. }
  inv PR1; cdes MC.
  set (P := fun G => ~ acts G x).
  assert (P (Restr G2 (set_compl (eq a ∪₁ eq e)))).
  { intro A; ins. unfolder in A; unfolder in ACTx; desf; clarify_not. }
  assert (~ P G1).
  { unfold P; intros []; destruct ACTx as [[]|]; eauto; subst.
    eby eapply In_RV_a. }
  apply r_str_cont with (P := P) in COMPL; eauto.
  desc; exists z, w.
  assert (Wf z) by eby eapply Completions_Wf.
  assert (w ⊆ G1)%Ex as SUB.
  { apply sub_Completions; eauto.
    eby eapply Completion_Wf. }
  assert (z ⊆ w)%Ex as SUB' by by apply sub_Completion.
  assert (next z x) as N.
  { eapply Completion_nextE; eauto;
    unfold P in COMPL4, COMPL3; clarify_not. }
  splits; eauto.
  { unfold P in COMPL4.
    destruct LRACT as [yLRx|ACT].
    { apply NNPP; intro NACT.
      set (P' := fun G => ~ acts G y).
      apply r_str_cont with (P := P') in COMPL2; eauto; desc.
      unfold P' in COMPL8. clarify_not.
      assert (next z0 y) by (eapply Completion_nextE; vauto).
      eapply (LR_irr LR y), LR_trans; eauto;
      eapply next_Completions with (G := z) (G' := z0); eauto.
      { eapply inclusion_seq_rt with (r := Completion) (r' := Completion＊).
        { by apply inclusion_step_rt. } 
        { reflexivity. }
        by exists w. }
      intro; subst; by apply LR_irr in yLRx. }
    apply sub_Completions in COMPL; auto.
    apply SUB', COMPL; ins; split; auto.
    intros []; subst.
    { by apply n_is_r in W. }
    by cdes MC0; cdes MAX; cdes MAX2. }
  { unfold P in COMPL4; clarify_not. }
  eapply sub_execution_trans; eauto; by apply sub_Completion.
Qed.

Lemma Prev_rv_nr G G1 G2 e1 a e2
  (WF : Wf G) 
  (PR1 : G1 ~(e1)~(RV a)~> G)
  (PR2 : G2 ~(e2)~(NR)~> G) : False.
Proof.
  inv PR1; inv PR2; apply meE in ME; apply ME in ME0; subst.
  { by apply n_is_r in W. }
  apply (wf_rff WF _ _ _ RF) in RF0; subst.
  desf; eby eapply LR_irr, LR_trans.
Qed.

Lemma Prev_rv_det G G1 G2 e1 a e2 t2 
  (WF : Wf G) 
  (PR1 : G1 ~(e1)~(RV a)~> G)
  (PR2 : G2 ~(e2)~(t2)~> G) : e1 = e2 /\ t2 = RV a /\ G1 = G2.
Proof.
  inv PR1.
  inv PR2.
  { apply meE in ME; apply ME in ME0; desf.
    apply (wf_rff WF _ _ _ RF) in RF0; desf; splits; eauto.
    assert (Wf (Restr G (set_compl (eq a0 ∪₁ eq e2)))).
    { eapply Wf_Restr; eauto; intros x INI []; desf.
      { by destruct x. }
      eapply LR_irr, LR_trans; eauto.
      by apply sb_LR; destruct x, a0. }
    eby eapply MaxCompletion_det. }
  all: eby eapply Prev_rv_nr in PR1.
Qed.

Lemma Prev_nr_det G G1 G2 e1 e2 t2 
  (WF : Wf G) 
  (PR1 : G1 ~(e1)~(NR)~> G)
  (PR2 : G2 ~(e2)~(t2)~> G) : e1 = e2 /\ t2 = NR /\ G1 = G2.
Proof.
  inv PR1; inv PR2; apply meE in ME; apply ME in ME0; desf.
  all: try by eby eapply Prev_rv_nr in PR2.
Qed.

Lemma Prev_det G G1 G2 e1 t1 e2 t2 
  (WF : Wf G) 
  (PR1 : G1 ~(e1)~(t1)~> G)
  (PR2 : G2 ~(e2)~(t2)~> G) : 
  << EQG : G1 = G2 >> /\ 
  << EQe : e1 = e2 >> /\
  << EQt : t1 = t2 >>.
Proof.
  inv PR1.
  { eapply (Prev_rv_det WF PR1) in PR2; desf. }
  all: eapply (Prev_nr_det WF PR1) in PR2; desf.
Qed.

End Terminate.

End Prev.
