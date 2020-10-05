From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order.
From mathcomp Require Import eqtype fingraph path. 
From event_struct Require Import utilities EventStructure.

Section transition_system.

Context {val : eqType} {dv : val}.

Notation exec_event_struct := (@exec_event_struct val).
Notation cexec_event_struct := (@cexec_event_struct val).

Notation label := (@label val).
Notation n := (@n val).

Implicit Types (x : var) (a : val) (t : tid).

(* Section with definitions for execution graph with added event *)
Section adding_event.

(* execution graph in which we want to add l *)
Variable es : exec_event_struct.

Notation n      := (n es).
Notation lab    := (lab es).
Notation fpred  := (fpred es).
Notation frf    := (frf es).

(* label of an event which we want to add *)
Variable l : label.

 (* predecessor of the new event (if it exists) *)
Variable p : option 'I_n.

Definition add_lab : 'I_n.+1 -> label := 
  @upd (fun _ => label) n lab l.

Definition add_fpred : forall m : 'I_n.+1, option 'I_m := 
  @upd (fun m => option 'I_m) n fpred p.

(* auxiliary lemma  *)
Lemma advance_is_read {m : 'I_n} : 
  (orel compatible) (ext lab m)     (ext add_lab n) ->
  (orel compatible) (ext add_lab m) (ext add_lab n).
Proof. Admitted.

(* auxiliary lemma *)
(* Lemma is_read_add_lab k neq:  *)
(*   is_read (add_lab k) -> is_read (lab (decr_ord k neq)). *)
(* Proof. *)
(* have->//: add_lab k = lab (decr_ord k neq). case: k neq=> /= m ? neq. *)
(* case: eqP=> [/neq|?]//. by apply/congr1/ord_inj. *)
(* Qed. *)

Arguments add_lab : simpl never.

Lemma add_lab_is_read {r : 'I_n} : 
  (is_read \o lab) r <-> (is_read \o add_lab) (inc_ord r).
Proof. Admitted.

Lemma add_lab_ext_is_read {r : 'I_n} : 
  (opred is_read \o ext add_lab) r -> (opred is_read \o ext lab) r.
Proof. Admitted.

Lemma add_lab_compatible {w r : nat} :
  (orel compatible \o2 ext lab    ) w r ->
  (orel compatible \o2 ext add_lab) w r.
Proof. Admitted.

(* TODO: generalize to `subType` *)
Definition sproof_map {A : Type} {P Q : A -> Prop} 
                      (f : forall a : A, P a -> Q a) 
                      (e : {x | P x}) : 
           {x | Q x} := 
  exist Q (sval e) (f (sval e) (sproof e)).

Definition add_frf (ow : { m :? 'I_n | 
                              (opred is_read \o ext add_lab) n
                           |- (orel compatible \o2 ext add_lab) m n    
                         }
                   ) :
           forall (r : 'I_n.+1) (is_r : (opred is_read \o ext add_lab) r),
             { w : 'I_r | (orel compatible \o2 ext add_lab) w r }.
Proof. 
  refine (
      let T (r : nat) := 
          forall (is_r : (opred is_read \o ext add_lab) r), 
            { w : 'I_r | (orel compatible \o2 ext add_lab) w r }
      in
      let frf' (r : 'I_n) : T r := 
          fun is_r =>
            let fP (w : 'I_r) := @add_lab_compatible w r in
            sproof_map fP (frf r (add_lab_ext_is_read is_r))
      in
      @upd T n frf' (oguardT ow)
  ).
Qed.

Lemma add_lab_N : ext add_lab n = some l.
Proof. Admitted.

End adding_event.


Section add_event_def.
Variables (e : exec_event_struct) (ipred : option 'I_(n e)).

Inductive add_label := 
| add_W : tid -> var -> val -> add_label
| add_R (n : 'I_(n e)) t x a : ocompatible (ext (lab e) n) (some (R t x a)) -> add_label.

Definition add_event (l : add_label) := 
  match l with
  | add_W t x a      => Pack 
                         (n e).+1 
                         (add_lab (W t x a) e)
                         (add_pred e ipred) 
                         (add_rf_None (W t x a) e ipred not_false_is_true)
  | add_R k t x a RF => Pack
                         (n e).+1 
                         (add_lab (R t x a) e)
                         (add_pred e ipred)
                         (add_rf_some (R t x a) e ipred k RF)
  end.

End add_event_def.

End transition_system.
