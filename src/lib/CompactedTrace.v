Require Import Lia IndefiniteDescription.
Require Import Arith.
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import AuxProp.

Require Import PropExtensionality.

Set Implicit Arguments.

Section CompactedTrace.
  Variables State Label : Type.
  Variable st_init : State.
  Variable labdom  : nat -> Prop.
  Variable lab     : nat -> Label.
  Variable cstate  : nat -> State.
  Variable STEP    : Label -> relation State.
  Variable INTSTEP : Label -> relation State.
  (* Variable INTLBL  : Label -> Prop. *)

  Definition internal_step a b :=
    exists lbl, INTSTEP lbl a b.
  
  Record compacted_step :=
    cs_mk {
        (* Begin state *)
        bs : State;
        (* Intermediate steps *)
        islist : list State;
        (* End state*)
        es : State;
      }.
  
  Definition CompactedTrace := nat -> compacted_step.
  
  Definition compacted_trace (ct : CompactedTrace) :=
      forall n,
        let bs  := bs     (ct n) in
        let lst := islist (ct n) in
        let es  := es     (ct n) in
        ⟪ BS : bs = cstate n ⟫ /\
        ⟪ ES : es = cstate (1 + n) ⟫ /\
        ⟪ BAR : labdom n -> STEP (lab n) bs (nth 0 lst es) ⟫ /\
        ⟪ LER : labdom n -> list_elem_related internal_step lst ⟫ /\
        ⟪ EAR :
          labdom n -> 
          match lst with
          | nil => (* Deducible from BAR *)
            STEP (lab n) bs es
          | a :: lst' =>
            internal_step (last lst' a) es
          end ⟫.
  
  Hypothesis CSTEP : forall n (LT : labdom n),
      ((STEP (lab n)) ⨾ internal_step＊)
                      (cstate n) (cstate (1 + n)).

  Lemma compacted_trace_exists : exists ct, compacted_trace ct.
  Proof.
    unfold compacted_trace. unnw.
    apply functional_choice with
        (R:=fun n fn =>
              bs fn = cstate n /\
              es fn = cstate (1 + n) /\
              (labdom n -> STEP (lab n) (bs fn) (nth 0 (islist fn) (es fn))) /\
              (labdom n -> list_elem_related internal_step (islist fn)) /\
              (labdom n ->
               match islist fn with
               | nil => STEP (lab n) (bs fn) (es fn)
               | a :: lst' => internal_step (last lst' a) (es fn)
               end)).
    intros n.
    destruct (classic (labdom n)) as [LT|].
    2: { exists (cs_mk (cstate n) nil (cstate (1 + n))); ins. }
    destruct (CSTEP LT) as [y [FSTEP HH]].
    apply rtE in HH. destruct HH as [HH|HH].
    { unfolder in HH. desf.
      exists (cs_mk (cstate n) nil (cstate (1 + n))). ins. }
    apply ct_end in HH.
    destruct HH as [z [HH LSTEP]].
    apply rt_to_list in HH. desf.
    exists (cs_mk (cstate n) (y :: l) (cstate (1 + n))). ins.
  Qed.

Section TraceUnpack.
  Implicit Type ct : CompactedTrace.
  
  Fixpoint ct2r_helper ct n base : State :=
    let st := bs     (ct base) in
    let l  := islist (ct base) in
    let ll := length l         in
    match n with
    | 0   => st
    | S n => if le_lt_dec ll n
             then ct2r_helper ct (n - ll) (1 + base)
             else nth n l st
    end.
  
  (* The compacted trace to a normal run. *)
  Definition ct2r ct n : State := ct2r_helper ct n 0.
  
  Fixpoint cti2ri_helper ct n base : nat :=
    let st := bs     (ct base) in
    let l  := islist (ct base) in
    match n with
    | 0   => 0
    | S n => 1 + length l + (cti2ri_helper ct n (S base))
    end.
  
  (* The compacted trace index to a normal trace index. *)
  Definition cti2ri ct n : nat := cti2ri_helper ct n 0.
  
  Lemma ct2r_helper_base_move ct n base dlt :
    ct2r_helper ct n (dlt + base) = ct2r_helper (fun x => ct (dlt + x)) n base.
  Proof.
    generalize dependent base.
    generalize dependent dlt.
    pattern n. apply (well_founded_induction lt_wf).
    ins.
    destruct x; ins. desf.
    rewrite <- H; [|lia].
      by arewrite (S (dlt + base) = dlt + S base).
  Qed.

  Lemma cti2ri_helper_base_move ct n base dlt :
    cti2ri_helper ct n (dlt + base) = cti2ri_helper (fun x => ct (dlt + x)) n base.
  Proof.
    generalize dependent base.
    generalize dependent dlt.
    pattern n. apply (well_founded_induction lt_wf).
    ins.
    destruct x; ins. desf.
    rewrite <- H; [|lia].
      by arewrite (S (dlt + base) = dlt + S base).
  Qed.

  Lemma wf_cti2ri ct n : ct2r ct (cti2ri ct n) = bs (ct n).
  Proof.
    generalize dependent ct.
    induction n; ins.
    unfold ct2r.
    unfold cti2ri.
    ins. desf; [|lia].
    arewrite (length (islist (ct 0)) + cti2ri_helper ct n 1 - length (islist (ct 0)) =
              cti2ri_helper ct n 1) by lia.
    arewrite (1 = 1 + 0).
    rewrite cti2ri_helper_base_move.
    rewrite ct2r_helper_base_move.
    unfold ct2r in IHn.
    rewrite IHn. ins.
  Qed.
  
  Lemma wf_cti2ri_gen ct n m :
    ct2r_helper ct (cti2ri (fun x => ct (m + x)) n) m = bs (ct (m + n)).
  Proof.
    generalize dependent ct.
    generalize dependent m.
    induction n; ins; rewrite !Nat.add_0_r; auto.
    desf; [|lia].
    arewrite (length (islist (ct m)) + cti2ri_helper (fun x : nat => ct (m + x)) n 1 -
              length (islist (ct m)) =
              cti2ri_helper (fun x : nat => ct (m + x)) n 1) by lia.
    arewrite (m + S n = S m + n) by lia.
    rewrite <- IHn.
    unfold cti2ri.
    arewrite (1 = 1 + 0).
    rewrite cti2ri_helper_base_move. ins.
    arewrite ((fun x : nat => ct (m + S x)) = (fun x : nat => ct (S (m +  x)))); auto.
    extensionality x. by arewrite (m + S x = S (m + x)).
  Qed.

  Lemma ct2r_helper_base_move_dlt ct dlt n m :
    ct2r_helper ct (cti2ri (fun x => ct (m + x)) n + dlt) m =
    ct2r_helper (fun x => ct (n + x)) dlt m.
  Proof.
    generalize dependent ct.
    generalize dependent n.
    generalize dependent dlt.
    induction n; ins.
    rewrite Nat.add_0_r.
    desf; [|lia].
    match goal with
    | |- ct2r_helper _ (?X + ?Y + ?U - ?Z) _ = _ =>
      arewrite (X + Y + U - Z = Y + U) by lia
    end.
    arewrite (S m = 1 + m).
    rewrite ct2r_helper_base_move.
    arewrite (1 = 1 + 0).
    rewrite cti2ri_helper_base_move.
    rewrite Nat.add_0_r; ins.
    rewrite <- IHn with (ct := fun x => ct (S x)).
    arewrite ((fun x : nat => ct (m + S x)) = (fun x : nat => ct (S (m + x)))); auto.
    extensionality x. by rewrite Nat.add_succ_r.
  Qed.

  Lemma cti2ri_S_mon ct n : cti2ri ct n < cti2ri ct (S n).
  Proof.
    unfold cti2ri.
    generalize 0.
    induction n; ins; [lia|].
    specialize (IHn (S n0)). lia.
  Qed.

  Lemma cti2ri_mon_helper ct m n (LT : m < n) : cti2ri ct m < cti2ri ct n.
  Proof.
    generalize LT.
    arewrite (n = (n - m) + m) by lia.
    remember (n-m) as x. ins. clear n LT Heqx.
    generalize dependent m.
    induction x; ins; [lia|].
    specialize (IHx m).
    destruct x; ins.
    { apply cti2ri_S_mon. }
    etransitivity; [|by apply cti2ri_S_mon].
    apply IHx. lia.
  Qed.
  
  Lemma cti2ri_mon ct m n : m < n <-> cti2ri ct m < cti2ri ct n.
  Proof.
    split; intros LT.
    { by apply cti2ri_mon_helper. }
    destruct (lt_eq_lt_dec m n) as [[XX|XX]|XX]; desf.
    { lia. }
    apply cti2ri_mon_helper with (ct:=ct) in XX. lia.
  Qed.
  
  Lemma cti2ri_lt_n ct n : n <= cti2ri ct n.
  Proof.
    induction n; ins.
    enough (cti2ri ct n < cti2ri ct (S n)) ; [lia|].
    apply cti2ri_S_mon.
  Qed.

  Lemma cti2ri_inj ct m n (REP : cti2ri ct m = cti2ri ct n) : m = n.
  Proof.
    edestruct (lt_eq_lt_dec m n) as [[AA|]|AA]; auto.
    all: apply cti2ri_mon with (ct:=ct) in AA; lia.
  Qed.

  Lemma cti2ri_helper_plus ct n base dlt :
    cti2ri_helper ct (dlt + n) base =
    cti2ri_helper ct dlt base +
    cti2ri_helper ct n (dlt + base).
  Proof.
    generalize dependent base.
    generalize dependent n.
    generalize dependent ct.
    induction dlt; ins.
    match goal with
    | |- S (_ + ?X) = S (_ + ?Y + ?Z) => arewrite (X = Y + Z); [|lia]
    end.
    rewrite IHdlt. by rewrite Nat.add_succ_r.
  Qed.

  Lemma islist_length ct n :
    cti2ri ct (1 + n) - (1 + cti2ri ct n) = length (islist (ct n)).
  Proof.
    unfold cti2ri. rewrite cti2ri_helper_plus.
    ins. rewrite Nat.add_0_r.
    generalize dependent ct.
    induction n; ins; [lia|].
    match goal with
    | |- ?X = _ =>
      arewrite (X = length (islist (ct 1)) + cti2ri_helper ct n 2 - cti2ri_helper ct n 1)
               by lia
    end.
    arewrite (1 = 1 + 0).
    arewrite (2 = 1 + 1).
    rewrite !cti2ri_helper_base_move.
    rewrite <- IHn with (ct:=fun x => ct (S x)); ins.
  Qed.

  Lemma cti2ri2_to_islist ct n :
        islist (ct n) =
        map (ct2r ct)
            (List.seq (1 + cti2ri ct n) (cti2ri ct (1 + n) - (1 + cti2ri ct n))).
  Proof.
    erewrite map_seq_shift with (g:=fun x => ct2r ct (cti2ri (fun x => ct (0 + x)) n
                                                      + (1 + x)))
                                (b:=0).
    2: by ins; arewrite (S (cti2ri ct n + i) = cti2ri (fun x : nat => ct x) n + S i).
    unfold ct2r.
    arewrite
      ((fun x => ct2r_helper ct (cti2ri (fun x0 : nat => ct (0 + x0)) n + (1 + x)) 0) =
       (fun x => ct2r_helper (fun x : nat => ct (n + x)) (1 + x) 0)).
    { extensionality x. apply ct2r_helper_base_move_dlt. }
    rewrite islist_length.
    erewrite map_nth_seq; auto.
    ins. rewrite Nat.add_0_r. desf. lia.
  Qed.

End TraceUnpack.

Section Properties.
  Variable ct : CompactedTrace.
  Hypothesis CT : compacted_trace ct.
  Hypothesis LDMPRCLOS : dom_rel (lt ⨾ ⦗labdom⦘) ⊆₁ labdom.

  Lemma ct2r_lblstep_preserved n (LT : labdom n) :
    STEP (lab n) (ct2r ct (cti2ri ct n)) (ct2r ct (1 + cti2ri ct n)).
  Proof.
    rewrite wf_cti2ri.
    unfold ct2r.
    rewrite Nat.add_comm.
    arewrite (ct = fun x => ct (0 + x)) at 3.
    rewrite ct2r_helper_base_move_dlt. ins.
    rewrite Nat.add_0_r.
    destruct (CT n) as [AA].
    destruct (CT (S n)) as [BB].
    desc. unnw.
    rewrite Nat.add_1_r. 
    destruct (islist (ct n)) eqn:HH; ins; auto.
    rewrite BB. rewrite <- ES0; auto.
  Qed.

  Definition compacted_trace_dom i :=
    exists n,
      ⟪ LBDOM  : labdom n ⟫ /\
      ⟪ BEFLST : i <= cti2ri ct (1 + n) ⟫.
  
  Lemma compacted_trace_dom_lt_clos :
    dom_rel (lt ⨾ ⦗compacted_trace_dom⦘) ⊆₁ compacted_trace_dom.
  Proof.
    unfold compacted_trace_dom. unfolder. ins. desf.
    exists n. splits; eauto. lia.
  Qed.
  
  Lemma wf_compacted_trace_dom i (CTD : compacted_trace_dom i) :
    exists n,
      ⟪ LBDOM  : labdom n ⟫ /\
      ((⟪ AFTLST : cti2ri ct n <= i ⟫ /\
        ⟪ BEFLST : i < cti2ri ct (1 + n) ⟫) \/
        ⟪ BEFLST : i = cti2ri ct (1 + n) ⟫).
  Proof.
    red in CTD. desf.
    apply le_lt_or_eq in BEFLST. desf.
    2: { exists n. splits; auto. }
    unnw.
    enough (exists n0,
               labdom n0 /\ cti2ri ct n0 <= i < cti2ri ct (1 + n0)); desf.
    { exists n0. splits; auto. }
    generalize dependent i.
    generalize dependent LBDOM.
    induction n; ins.
    { exists 0. splits; auto.
      unfold cti2ri, cti2ri_helper. lia. }
    destruct (NPeano.Nat.lt_ge_cases i (cti2ri ct (S n))).
    2: { by exists (S n). }
    destruct IHn with (i:=i); eauto. 
    eapply LDMPRCLOS. exists (S n). basic_solver.
  Qed.
  
  Lemma ct2r_step_preserved i (CTDs : compacted_trace_dom (1 + i)) :
    match excluded_middle_informative
            (exists n,
                ⟪ REP   : i = cti2ri ct n ⟫ /\
                ⟪ LBDOM : labdom n ⟫)
    with
    | left PF =>
      let n := proj1_sig (constructive_indefinite_description _ PF) in
      STEP (lab n) (ct2r ct i) (ct2r ct (1 + i))
    | right _ =>
      internal_step (ct2r ct i) (ct2r ct (1 + i))
    end.
  Proof.
    assert (CTD : compacted_trace_dom i).
    { apply compacted_trace_dom_lt_clos. exists (1 + i). basic_solver. }
    do 2 desf.
    { ins. unfold proj1_sig. do 2 desf. clear Heq.
      apply cti2ri_inj in REP; subst. by apply ct2r_lblstep_preserved. }
    rename n into ZZ.
    edestruct (wf_compacted_trace_dom CTD) as [n]; auto. desf.
    2: { edestruct (wf_compacted_trace_dom CTDs) as [n']; auto. desc.
         destruct (lt_eq_lt_dec n' n) as [[AA|]|AA]; subst.
         2: desf; lia.
         { desf.
           all: assert (cti2ri ct (1 + n') < cti2ri ct (1 + n)); [apply cti2ri_mon|]; lia. }
         assert (labdom (1 + n)).
         { destruct (lt_eq_lt_dec n' (1 + n)) as [[BB|]|BB]; subst; auto.
           { lia. }
           apply LDMPRCLOS. exists n'. basic_solver. }
         exfalso. apply ZZ; eauto. }
    apply le_lt_or_eq in AFTLST. desf.
    2: { exfalso. apply ZZ; eauto. }
    destruct (CT n) as [AA]. desc. unnw.
    specialize (BAR LBDOM). specialize (LER LBDOM). specialize (EAR LBDOM).
    remember (cti2ri2_to_islist ct n) as QQ. clear HeqQQ.
    destruct (classic (islist (ct n) = nil)) as [NIL|NNIL].
    { rewrite NIL in QQ. symmetry in QQ. apply map_eq_nil in QQ.
      apply seq_eq_nil in QQ. lia. }
    destruct (lt_eq_lt_dec (1 + i) (cti2ri ct (1 + n))) as [[DD|DD]|DD].
    3: lia.
    2: { rewrite DD. rewrite wf_cti2ri.
         destruct (CT (1 + n)) as [EE]. unnw. rewrite EE.
         rewrite <- ES.
         destruct (islist (ct n)) as [|a lst'] eqn:PP.
         { desf. }
         arewrite (ct2r ct i = last lst' a); auto.
         rewrite last_cons_def.
         rewrite nnil_last_default_irrelevance with (y:=ct2r ct i); auto.
         rewrite QQ.
         rewrite last_map, last_seq.
         2: lia.
         arewrite (1 + cti2ri ct n + (cti2ri ct (1 + n) - (1 + cti2ri ct n)) - 1 = i); auto.
         lia. }
    clear EAR.
    rewrite QQ in LER. apply list_elem_related_map in LER.
    rewrite seq_split with (x := i - (1 + cti2ri ct n)) in LER; [|lia].
    apply list_elem_related_app_r in LER.
    assert (i - (1 + cti2ri ct n) + (1 + cti2ri ct n) = i) as TT by lia.
    rewrite TT in LER. clear TT.
    assert (cti2ri ct (1 + n) - (1 + cti2ri ct n) - (i - (1 + cti2ri ct n)) =
            cti2ri ct (1 + n) - i) as TT by lia.
    rewrite TT in LER. clear TT.
    assert (cti2ri ct (1 + n) - i = 2 + (cti2ri ct (1 + n) - i - 2)) as TT by lia.
    rewrite TT in LER. clear TT. ins.
    repeat (rewrite seqS_hd in LER). apply LER.
  Qed.

  Lemma c2tr_trace_istep_helper i n (LBDOM  : labdom n)
        (AFTLST : cti2ri ct n <= i)
        (BEFLST : i < cti2ri ct (1 + n)) :
    exists n',
      i <= cti2ri ct n' /\
      internal_step＊ (ct2r ct i) (ct2r ct (cti2ri ct n')).
  Proof.
    apply le_lt_or_eq in AFTLST. desf.
    2: { exists n. splits; auto. apply rt_refl. }
    exists (1 + n).
    remember (cti2ri ct (1 + n) - i) as p.
    assert (0 < p) as HH by lia.
    generalize AFTLST.
    arewrite (i = cti2ri ct (1 + n) - p) by lia.
    clear Heqp. clear dependent i. intros CC.
    splits; [lia|].
    induction p; [lia|].
    destruct p.
    { apply rt_step. clear IHp.
      assert (compacted_trace_dom (1 + (cti2ri ct (1 + n) - 1))) as BB.
      { red. exists n. splits; auto. lia. }
      remember (ct2r_step_preserved BB) as AA. clear HeqAA.
      do 2 desf.
      2: arewrite (cti2ri ct (1 + n) = 1 + (cti2ri ct (1 + n) - 1)) at 2 by lia.
      clear AA.
      assert (n < n0 /\ n0 < 1 + n); desf.
      { split; apply cti2ri_mon with (ct:=ct); lia. }
      lia. }
    apply rt_rt. exists (ct2r ct (cti2ri ct (1 + n) - S p)).
    split.
    2: { apply IHp; lia. }
    apply rt_step.
    arewrite (cti2ri ct (1 + n) - S p = 1 + (cti2ri ct (1 + n) - S (S p))) by lia.
    assert (compacted_trace_dom (1 + (cti2ri ct (1 + n) - S (S p)))) as BB.
    { red. exists n. splits; auto. lia. }
    remember (ct2r_step_preserved BB) as AA. clear HeqAA.
    do 2 desf. clear AA.
    enough (n < n0 /\ n0 < 1 + n); desf.
    { lia. }
    split; apply cti2ri_mon with (ct:=ct); lia.
  Qed.
  
Section CT2T.
  Variable   l   : Label.
  Hypothesis ISS : forall l, INTSTEP l ⊆ STEP l.
  
  Definition ct2t (t : nat -> Label) :=
    forall i (CTDs : compacted_trace_dom (1 + i)),
      ⟪ ST : STEP (t i) (ct2r ct i) (ct2r ct (1 + i)) ⟫ /\
      match excluded_middle_informative
              (exists n,
                  ⟪ REP   : i = cti2ri ct n ⟫ /\
                  ⟪ LBDOM : labdom n ⟫)
      with
      | left PF =>
        let n := proj1_sig (constructive_indefinite_description _ PF) in
        t i = lab n
      | right _ =>
        INTSTEP (t i) (ct2r ct i) (ct2r ct (1 + i))
      end.

  Lemma ct2t_exists : exists (t : nat -> Label), ct2t t.
  Proof.
    unfold ct2t. unnw.
    apply functional_choice with
        (R:=fun (i  : nat) (fi : Label) =>
              compacted_trace_dom (1 + i) ->
              STEP fi (ct2r ct i) (ct2r ct (1 + i)) /\
              match excluded_middle_informative
                      (exists n : nat, i = cti2ri ct n /\ labdom n) with
              | left PF =>
                fi =
                lab
                  (proj1_sig
                     (constructive_indefinite_description
                        (fun n : nat => i = cti2ri ct n /\ labdom n) PF))
              | right _ =>
                INTSTEP fi (ct2r ct i) (ct2r ct (1 + i))
              end).
    intros i.
    destruct (classic (compacted_trace_dom (S i))) as [AA|]; [|by exists l].
    apply ct2r_step_preserved in AA. do 2 desf.
    { unfold proj1_sig in *. do 2 desf. clear Heq Heq0.
      apply cti2ri_inj in REP; subst.
      apply cti2ri_inj in e; subst.
      apply cti2ri_inj in a; subst.
      exists (lab x). ins. }
    cdes AA. eexists. ins. splits; eauto. by apply ISS.
  Qed.

  Lemma ct2t_steps m n (LE : m <= n) (CTD : compacted_trace_dom n) :
    (fun a b => exists l, STEP l a b)＊ (ct2r ct m) (ct2r ct n).
  Proof.
    generalize dependent CTD.
    arewrite (n = (n - m) + m) by lia.
    remember (n - m) as k.
    clear dependent n.
    induction k; ins.
    { apply rt_refl. }
    eapply rt_unit. eexists. split.
    { apply IHk. apply compacted_trace_dom_lt_clos. generalize CTD. basic_solver 10. }
    eapply ct2r_step_preserved in CTD; ins. 
    desf; eauto.
    cdes CTD. apply ISS in CTD0. eauto.
  Qed.

  Lemma cti2ri_filter_alt t (CT2T : ct2t t)
        (P    : Label -> Prop)
        (PLAB : lab ↑₁ labdom ⊆₁ P)
        (PINT : forall l, ~ (INTSTEP l ≡ ∅₂) -> ~ P l) :
    forall x (LABDOM : labdom x),
      length (filterP (t ↓₁ P) (List.seq 0 (cti2ri ct x))) = x.
  Proof.
    intros x. induction x; ins.
    assert (labdom x) as LABDOMX.
    { apply LDMPRCLOS. generalize LABDOM. basic_solver 10. }
    specialize (IHx LABDOMX).
    assert (cti2ri ct x < cti2ri ct (S x)) as AA by apply cti2ri_S_mon.
    arewrite (cti2ri ct (S x) =
              cti2ri ct x + (cti2ri ct (S x) - cti2ri ct x)).
    { apply le_plus_minus. lia. }
    rewrite seq_add. rewrite filterP_app, length_app.
    rewrite IHx.
    match goal with
    | |- x + ?Y = _ => enough (Y = 1); [lia|]
    end.
    rewrite plus_0_l.
    rewrite seq_split_gen with (a := cti2ri ct x).
    2: split; lia.
    rewrite NPeano.Nat.sub_add; [|lia].
    rewrite Nat.sub_diag, seq0, app_nil_l.
    rewrite filterP_cons, length_app.
    assert (compacted_trace_dom (1 + (cti2ri ct x))) as BB.
    { red. exists x. splits; auto. }
    match goal with
    | |- ?A + _ = _ => arewrite (A = 1)
    end.
    { desf. exfalso. apply n. red.
      apply PLAB. red. exists x. splits; auto.
      specialize (CT2T (cti2ri ct x) BB); desf; desf.
      2: by exfalso; apply n0; eauto. 
      unfold proj1_sig in CT2T0; desf; desf.
      rewrite CT2T0. clear Heq. apply cti2ri_inj in REP0. desf. }
    match goal with
    | |- _ + length ?A = _ => arewrite (A = nil); auto
    end.
    apply filterP_eq_nil.
    intros y HH. apply in_seq_iff in HH. eapply PINT. intros CC.
    assert (S (cti2ri ct x) + (cti2ri ct (S x) - cti2ri ct x - 1) =
            cti2ri ct (S x)) as DD by lia.
    rewrite DD in HH. clear DD.
    assert (compacted_trace_dom (1 + y)) as BB'.
    { red. exists x. splits; auto. ins. lia. }
    specialize (CT2T y BB'); desf; desf.
    2: eby eapply CC.
    unfold proj1_sig in CT2T0; desf; desf.
    assert (n < S x) by eby eapply cti2ri_mon.
    assert (x < n) by eby eapply cti2ri_mon.
    lia.
  Qed.
  
  Lemma ct2t_infinite_filtered (t : nat -> Label) (CT2T : ct2t t)
        (P    : Label -> Prop)
        (LBDOMINF : labdom ≡₁ fun _ => True)
        (PLAB : lab ↑₁ labdom ⊆₁ P)
        (PINT : forall l, ~ (INTSTEP l ≡ ∅₂) -> ~ P l) :
    trace_filter P (trace_inf t) = trace_inf lab.
  Proof.
    assert (forall n, compacted_trace_dom (S n)) as CTD.
    { ins. exists n. splits; [by apply LBDOMINF|]. ins. by apply cti2ri_lt_n. }
    set (QQ:=CT2T).
    unfold trace_filter. desf.
    { exfalso. apply set_finite_nat_bounded in s. desf.
      specialize (s (cti2ri ct bound)).
      assert (bound <= cti2ri ct bound) as BB by apply cti2ri_lt_n.
      assert (cti2ri ct bound < bound); [clear BB|lia].
      apply s. red. apply PLAB. red.
      specialize (QQ (cti2ri ct bound)). desf.
      2: { exfalso. apply n. exists bound. splits; auto. by apply LBDOMINF. }
      eexists; splits; [|symmetry; apply QQ]; ins.
      unfold proj1_sig. desf. by apply LBDOMINF. }
    match goal with
    | |- _ ?X = _ ?Y => enough (X = Y) as AA; [by rewrite AA|]
    end.
    apply functional_extensionality. ins. unfold proj1_sig in *.
    do 2 desf. clear Heq. red in a.
    specialize (QQ x0 (CTD x0)). desf.
    2: { exfalso. eapply PINT; [|by eauto].
         intros HH. apply HH in QQ0. desf. }
    rewrite QQ0. unfold proj1_sig. do 2 desf.
    set (AA:=REP). apply cti2ri_inj in AA. subst.
    match goal with
    | |- _ ?X = _ ?Y => assert (X = Y); subst; auto
    end.
    rewrite cti2ri_filter_alt; auto.
  Qed.

  Lemma ct2t_finite_filtered (t : nat -> Label) (CT2T : ct2t t)
        (P    : Label -> Prop) x 
        (FF : (fun y => y < x) ⊆₁ labdom)
        (PLAB : lab ↑₁ labdom ⊆₁ P)
        (PINT : forall l, ~ (INTSTEP l ≡ ∅₂) -> ~ P l) :
    trace_filter P (trace_fin (map t (List.seq 0 (cti2ri ct x)))) =
    trace_fin (map lab (List.seq 0 x)).
  Proof.
    unfold trace_filter.
    match goal with
    | |- _ ?X = _ ?Y => enough (X = Y) as AA; [by rewrite AA|]
    end.
    induction x; ins.
    assert (cti2ri ct x < cti2ri ct (S x)) as AA
        by apply cti2ri_S_mon.
    arewrite (S x = x + (S x - x)) at 2 by lia.
    rewrite seq_add. rewrite map_app.
    arewrite (cti2ri ct (S x) =
              cti2ri ct x +
              (cti2ri ct (S x) - cti2ri ct x)).
    { apply le_plus_minus. lia. }
    rewrite seq_add. rewrite map_app, filterP_app.
    rewrite IHx.
    2: { etransitivity; [|by apply FF]. basic_solver. }
    match goal with
    | |- _ ++ ?X = _ ++ ?Y => arewrite (X = Y); auto
    end.
    rewrite !plus_0_l.
    arewrite (S x - x = 1) by lia.
    arewrite (map lab (List.seq x 1) = (lab x) :: nil).
    arewrite (cti2ri ct (S x) - cti2ri ct x = 
              S (cti2ri ct (S x) - cti2ri ct x - 1)) by lia.
    rewrite seqS_hd. rewrite map_cons, filterP_cons.
    match goal with
    | |- _ ++ ?X = _ => arewrite (X = nil); auto
    end.
    2: { desf; ins.
         { match goal with
           | |- ?X :: _ = ?Y :: _ => arewrite (X = Y); auto
           end.
           red in CT2T. specialize (CT2T (cti2ri ct x)).
           desf.
           2: { exfalso. apply n; eexists. splits; eauto. }
           unfold proj1_sig in *; desf; desf.
           clear Heq. apply cti2ri_inj in REP0; subst.
           destruct CT2T; auto. red. exists x0. splits; auto. }
         exfalso. red in CT2T. specialize (CT2T (cti2ri ct x)).
         desf; desf.
         2: { apply n0. eexists. splits; eauto. }
         destruct CT2T.
         { red. exists x. splits; auto. }
         unfold proj1_sig in *. desf. desf. clear Heq.
         apply n. apply PLAB. red. rewrite H0. eauto. }
    apply filterP_eq_nil.
    intros y HH. eapply PINT. intros CC.
    apply in_map_iff in HH. desf. apply in_seq_iff in HH0.
    assert (S (cti2ri ct x) + (cti2ri ct (S x) - cti2ri ct x - 1) =
            cti2ri ct (S x)) as DD by lia.
    rewrite DD in HH0. clear DD.
    assert (compacted_trace_dom (1 + x0)) as BB.
    { red. exists x. splits.
      { apply FF. lia. }
      ins. lia. }
    specialize (CT2T x0 BB). desf; desf.
    2: eby eapply CC.
    unfold proj1_sig in *. desf; desf. clear Heq.
    apply cti2ri_inj in REP. desf.
    assert (x0 < S x) by eby eapply cti2ri_mon.
    assert (x < x0) by eby eapply cti2ri_mon.
    lia.
  Qed.
End CT2T.

End Properties.

End CompactedTrace.
