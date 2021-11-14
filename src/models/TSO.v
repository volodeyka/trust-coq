Require Import Labels.
Require Import Events.
Require Import Execution.
Require Import List.
From hahn Require Import Hahn. 
Require Import TraceWf.
Require Import IndefiniteDescription.
Require Import Lia.

Section TSO. 

Definition shared_memory := Loc -> Val.  
Definition buffer := list (Loc * Val).
Definition TSOMemory := (shared_memory * (Tid -> buffer))%type.

Definition TSO_label := sum Event Tid.

Inductive latest_buffered (buf: buffer) (loc: Loc) (opt_val: option Val) : Prop :=
  | no_loc_buffer
      (EMPTY_BUF: filter (fun loc_val: Loc * Val => Nat.eqb (fst loc_val) loc) buf = nil)
      (NO_LATEST: opt_val = None)
  | latest_loc
      val
      (LATEST_VALUE: opt_val = Some val)
      (LATEST_BUF:
         let buf_thread_loc := filter (fun loc_val: Loc * Val => Nat.eqb (fst loc_val) loc) buf in
         Some (loc, val) = nth_error buf_thread_loc (length buf_thread_loc - 1)). 
(* 
Inductive TSO_step: TSOMemory -> TSO_label -> TSOMemory -> Prop :=
| tso_Read_buf sh_mem bufs loc val thread index
               (BUF: latest_buffered (bufs thread) loc (Some val)):
    TSO_step (sh_mem, bufs)
             (inl (ThreadEvent thread index (Aload loc val)))
             (sh_mem, bufs)
| tso_Read_mem sh_mem bufs loc val thread index
            (BUF: latest_buffered (bufs thread) loc None)
            (MEM: sh_mem loc = val):
    TSO_step (sh_mem, bufs)
             (inl (ThreadEvent thread index (Aload loc val)))
             (sh_mem, bufs)
| tso_Write sh_mem bufs loc (val: Val) thread index:
    TSO_step (sh_mem, bufs)
             (inl (ThreadEvent thread index (Astore loc val)))
             (sh_mem, upd bufs thread (bufs thread ++ cons (loc, val) nil))
| tso_RMW sh_mem bufs loc val_r val_w thread index
          (NO_BUF: bufs thread = nil)
          (MEM: sh_mem loc = val_r):
    TSO_step (sh_mem, bufs)
             (inl (ThreadEvent thread index (Armw loc val_r val_w)))
             (upd sh_mem loc val_w, bufs)
| tso_prop sh_mem bufs buf' loc val thread
           (BUF: bufs thread = cons (loc, val) buf'):
    TSO_step (sh_mem, bufs)
             (inr thread)
             (upd sh_mem loc val, upd bufs thread buf'). 

Definition empty_buffer : buffer := nil.
Definition Minit : TSOMemory := (fun _ => 0, fun _ => empty_buffer).  

Definition TSO_lts :=
  {| LTS_init := eq Minit ;
     LTS_step := TSO_step ;
     LTS_final := ∅ |}.

Definition ppo G := sb G \ (is_w × is_r). 
Definition implied_fence G := sb G ⨾ ⦗is_rmw⦘ ∪ ⦗is_rmw⦘ ⨾ sb G.
Definition TSO_hb G := (ppo G ∪ implied_fence G ∪ rfe G ∪ co G ∪ fr G)⁺. 

Definition TSO_consistent G := acyclic (TSO_hb G) /\ SCpL G.

Definition def_lbl: TSO_label := inl (InitEvent 0). 

Definition enabled st tid := exists st', TSO_step st (inr tid) st'. 
Definition TSO_fair tr st :=
  forall i tid
    (DOM_EXT: NOmega.le (NOnum i) (trace_length tr)) (* le accounts for the final state if any*)
    (ENABLED: enabled (st i) tid),
  exists j, i <= j /\ (NOmega.lt_nat_l j (trace_length tr)) /\
       trace_nth j tr def_lbl = inr tid.



Definition TSO_trace_wf (t: trace TSO_label) :=
  forall i j d thread index1 index2 lbl1 lbl2
    (LTij: i < j)
    (LTj : NOmega.lt_nat_l j (trace_length t))
    (TR_I: trace_nth i t d = inl (ThreadEvent thread index1 lbl1))
    (TR_J: trace_nth j t d = inl (ThreadEvent thread index2 lbl2)),
    index1 < index2.

Definition is_regular_write' := (is_w \₁(is_rmw ∪₁ is_init)). 
Definition regular_write' := 
fun lbl : TSO_label =>
match lbl with
| inl e => is_regular_write' e
| inr _ => False           
end.

Definition is_prop (lbl: TSO_label) := match lbl with | inr _ => True | _ => False end. 

Definition lbl_thread_opt (lbl: TSO_label) :=
  match lbl with
  | inl (ThreadEvent thread _ _)
  | inr thread => Some thread
  | _ => None
  end.

Definition in_thread thread := fun lbl => lbl_thread_opt lbl = Some thread. 

Definition is_external (x: TSO_label) := match x with | inl _ => True | inr _ => False end.
*)
End TSO. 
(*
Ltac unfolder' := unfold set_compl, cross_rel, regular_write', is_regular_write', set_minus, set_inter, set_union, is_r, is_r_l, is_w, is_w_l, is_rmw, is_rmw_l, is_init, is_prop, def_lbl, in_thread, lbl_thread_opt, same_loc, loc, loc_l, valr, valw, lab, tid in *.

Section TSO_facts. 

(* Lemma TS0 {State Label: Type} {lts: LTS State Label} t st (TRACE: LTS_trace_param lts st t): *)
(*   LTS_init lts (st 0). *)
(* Proof. *)
(*   unfold trace_states.  *)
(*   destruct (constructive_indefinite_description _ _). by desc.  *)
(* Qed. *)

(* Lemma TSi {st lb: Type} {lts: LTS st lb} t (TRACE: LTS_trace lts t): *)
(*   forall i (LT: NOmega.lt_nat_l i (trace_length t)), *)
(*     let fl' := trace_states t TRACE in *)
(*     forall d, LTS_step lts (fl' i) (trace_nth i t d) (fl' (S i)). *)
(* Proof. *)
(*   unfold trace_states.  *)
(*   destruct (constructive_indefinite_description _ _). by desc.  *)
(* Qed.    *)

Lemma init_non_r r (Rr: is_r r) (INIT: is_init r): False.
Proof. generalize Rr, INIT. unfolder'. by destruct r. Qed. 

Lemma init_non_rw': forall l, ~ is_regular_write' (InitEvent l).
Proof.
  ins. red. ins. do 2 red in H. desc.
  apply H0. vauto.
Qed. 

Lemma reg_write_structure tlab (W: regular_write' tlab):
  exists thread index loc val, tlab = inl (ThreadEvent thread index (Astore loc val)).
Proof.
  unfolder'. 
  unfold regular_write', is_regular_write' in W.
  destruct tlab eqn:WW.
  2: { simpl in W. vauto. }
  destruct e. 
  { destruct (init_non_rw' x). intuition. }
  generalize W. unfolder'. destruct l; vauto; intuition. 
  repeat eexists.
Qed. 

End TSO_facts. 

(* Lemma opt_val {A: Type} (ov: option A): ov <> None <-> exists v, ov = Some v. *)
(* Proof. destruct ov; split; ins; desc; vauto. Qed.  *)

(* Lemma set_equiv_exp_iff (A : Type) (s s' : A -> Prop): *)
(*   s ≡₁ s' <-> (forall x, s x <-> s' x). *)
(* Proof. *)
(*   split; [apply set_equiv_exp| ]. *)
(*   intros EQ. red. split; red; ins; apply EQ; auto.  *)
(* Qed. *)
 *)
