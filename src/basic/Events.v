(******************************************************************************)
(** * Definition of execution graph events *)
(******************************************************************************)
Require Import Lia.
Require Import FinFun.
Require Import List.
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import basic.Labels.

Set Implicit Arguments.

Definition Tid := nat.

Section Events.

(******************************************************************************)
(** ** Execution graph events  *)
(******************************************************************************)

Inductive Event := 
  | InitEvent (x : Labels.Loc)
  | ThreadEvent (thread : Tid) (index : nat) (l : Lab).

Definition is_init a := 
  match a with
    | InitEvent _ => True
    | _ => False
  end.

Definition tid a := 
  match a with
    | InitEvent _ => 0
    | ThreadEvent i _ _ => i
  end.

Definition index a := 
  match a with
    | InitEvent _ => 0
    | ThreadEvent _ n _ => n
  end.

Definition lab a := 
  match a with
    | InitEvent x => (Astore x 0)
    | ThreadEvent _ _ l => l
  end.

Definition loc a := loc_l (lab a).
Definition valr a := valr_l (lab a).
Definition valw a := valw_l (lab a).
Definition is_r a := is_r_l (lab a).
Definition is_w a := is_w_l (lab a).
Definition is_rmw a := is_rmw_l (lab a).

Lemma r_or_w a : is_r a \/ is_w a.
Proof using.
  unfold is_r, is_w. destruct (lab a); ins; auto.
Qed.

(******************************************************************************)
(** ** is_init properties *)
(******************************************************************************)
Lemma is_init_InitEvent x :
  is_init (InitEvent x).
Proof using.
  done.
Qed.

(******************************************************************************)
(** ** Same tid restriction *)
(******************************************************************************)

Definition is_tid i a : Prop := tid a = i.

Definition same_tid := (fun x y => tid x = tid y).

Lemma restr_eq_rel_same_tid r :  restr_eq_rel tid r  ≡ r ∩ same_tid.
Proof using. unfold same_tid; basic_solver. Qed.

Lemma funeq_same_tid (r: relation Event) (H: funeq tid r):
 r ⊆ r ∩ same_tid.
Proof using.
unfold same_tid; basic_solver.
Qed.

Lemma same_tid_funeq (r: relation Event) (H: r ⊆ r ∩ same_tid):
 funeq tid r.
Proof using.
unfold same_tid; unfolder; firstorder.
Qed.

(******************************************************************************)
(** ** Same location restriction *)
(******************************************************************************)

Definition is_loc x a : Prop := loc a = x.

Definition same_loc := (fun x y => loc x = loc y).

Lemma restr_eq_rel_same_loc r :  restr_eq_rel loc r  ≡ r ∩ same_loc.
Proof using. unfold same_loc; basic_solver. Qed.

Lemma funeq_same_loc (r: relation Event) (H: funeq loc r):
 r ⊆ r ∩ same_loc.
Proof using.
unfold same_loc; basic_solver.
Qed.

Lemma same_loc_funeq (r: relation Event) (H: r ⊆ r ∩ same_loc):
 funeq loc r.
Proof using.
unfold same_loc; unfolder; firstorder.
Qed.

Lemma same_loc_trans : transitive same_loc.
Proof using. unfold same_loc; red; ins. by rewrite H. Qed.

Lemma same_loc_sym : symmetric same_loc.
Proof using. unfold same_loc; red; ins. Qed.

(******************************************************************************)
(** ** Values and locations getters  *)
(******************************************************************************)

Lemma exists_valw a : exists vw, valw a = vw.
Proof using. unfold valw; desc; eexists; eauto. Qed.

Lemma exists_valr a : exists vw, valr a = vw.
Proof using. unfold valr; desc; eexists; eauto. Qed.

Lemma exists_loc a : exists x, loc a = x.
Proof using. unfold loc; desc; eexists; eauto. Qed.


(******************************************************************************)
(** ** Sequenced-Before *)
(******************************************************************************)

Definition same_index := (fun x y => index x = index y).

Definition ext_sb a b := 
  match a, b with 
    | _, InitEvent _ => False
    | InitEvent _, ThreadEvent _ _ _ => True
    | ThreadEvent t i _, ThreadEvent t' i' _ => t = t' /\ i < i' 
   end.

Lemma ext_sb_trans : transitive ext_sb.
Proof using.
unfold ext_sb; red; ins.
destruct x,y,z; ins; desf; splits; eauto.
by rewrite H2.
Qed.

Lemma ext_sb_irr : irreflexive ext_sb.
Proof using.
unfold ext_sb; red; ins.
destruct x; firstorder; lia.
Qed.

Lemma ext_sb_to_non_init : ext_sb ⊆ ext_sb ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
unfold is_init, ext_sb; basic_solver.
Qed.

Lemma ext_sb_semi_total_l x y z 
  (N: ~ is_init x) (NEQ: index y <> index z) (XY: ext_sb x y) (XZ: ext_sb x z): 
  ext_sb y z \/ ext_sb z y.
Proof using.
unfold ext_sb in *.
destruct x,y,z; ins; desf.
cut(index1 < index2 \/ index2 < index1).
tauto.
lia.
Qed.

Lemma ext_sb_semi_total_r x y z 
  (NEQ: index y <> index z) (XY: ext_sb y x) (XZ: ext_sb z x): 
  ext_sb y z \/ ext_sb z y.
Proof using.
unfold ext_sb in *.
destruct x,y,z; ins; desf; eauto.
cut(index1 < index2 \/ index2 < index1).
tauto.
lia.
Qed.

Lemma ext_sb_tid_init x y (SB : ext_sb x y): tid x = tid y \/ is_init x.
Proof using.
unfold ext_sb in *; desf; ins; desf; eauto.
Qed.

Lemma ext_sb_tid_init': ext_sb ⊆ ext_sb ∩ same_tid ∪ ⦗is_init⦘ ⨾ ext_sb.
Proof using.
generalize ext_sb_tid_init; firstorder.
Qed.

Lemma tid_ext_sb: same_tid ⊆ same_tid ∩ same_index ∪ ext_sb ∪ ext_sb⁻¹ ∪ (is_init × is_init).
Proof using.
  unfold ext_sb, same_tid, same_index, tid, is_init, cross_rel; unfolder.
  ins; destruct x, y; desf; eauto.
  cut (index0 < index1 \/ index1 < index0 \/ index0 = index1).
  ins; desf; eauto 10.
  lia.
Qed.

Lemma tid_n_init_ext_sb: same_tid ⨾ ⦗set_compl is_init⦘ ⊆ same_index ∪ ext_sb ∪ ext_sb⁻¹.
Proof using.
  rewrite tid_ext_sb at 1.
  unfold cross_rel.
  basic_solver 12.
Qed.

End Events.

(******************************************************************************)
(** ** Tactics *)
(******************************************************************************)

#[global]
Hint Unfold set_union set_inter is_r is_w is_rmw : type_unfolderDb.
#[global]
Hint Unfold is_r_l is_w_l is_rmw_l : type_unfolderDb.
Tactic Notation "type_unfolder" :=  repeat autounfold with type_unfolderDb in *.

Tactic Notation "type_solver" int_or_var(index) := 
  type_unfolder; basic_solver index.

Tactic Notation "type_solver" :=  type_solver 4.
