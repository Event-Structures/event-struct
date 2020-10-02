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

Lemma add_lab_ext_is_read {r : nat} : 
  (opred is_read \o ext lab) r <-> (opred is_read \o ext add_lab) r.
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

Definition frf_foo : 
      forall r : 'I_n,
        { w :? 'I_r | 
             (opred is_read \o ext add_lab) r
          |- (orel compatible \o2 ext add_lab) w r
        } := 
  fun r =>
    sproof_map
      (oguard_mapP_iffB (fun w : 'I_r => @add_lab_compatible w r) 
                        (@add_lab_ext_is_read r)
      ) 
      (frf r).

Definition frf_n (m : 'I_n)
                 (is_r : (opred is_read \o ext add_lab) n)
                 (rf : (orel compatible \o2 ext add_lab) m n) :
  (* { w :? 'I_n |  *)
    oguard ((opred is_read \o ext add_lab) n) 
           (fun w : 'I_n => (orel compatible \o2 ext add_lab) w n)
           (some m).
  (* }. *)
Proof. exact (oguard_some is_r m rf). Qed.

Definition add_rf_some (m : 'I_n)
                       (is_r : (opred is_read \o ext add_lab) n)
                       (rf : (orel compatible \o2 ext add_lab) m n) :
           forall r : 'I_n.+1,
             { w :? 'I_r | 
                  (opred is_read \o ext add_lab) r
               |- (orel compatible \o2 ext add_lab) w r
             }.
Proof. 
  exact (@upd 
           (fun r => { w :? 'I_r | 
                          (opred is_read \o ext add_lab) r
                       |- (orel compatible \o2 ext add_lab) w r
                     })
           n frf_foo 
           (exist (fun ow : option 'I_n => 
                     oguard ((opred is_read \o ext add_lab) n) 
                            (fun m : 'I_n => (orel compatible \o2 ext add_lab) m n) 
                            ow)
                  (some m) (oguard_some is_r m rf)
           )
        ).
Qed.

(* Definition incr_rf_codom *)
(*   {k : 'I_n.+1} {r : 'I_n} (eq : r = k :> nat) *)
(*   (m : {l : 'I_r | (ocompatible (ext lab l)     (ext lab r))}) : *)
(*        {l : 'I_k | (ocompatible (ext add_lab l) (ext add_lab k))} := *)
(*   let '(Ordinal r L) := r in  *)
(*   let '(Ordinal k L') := k in  *)
(*   let 'erefl := eq in *)
(*   let '(@exist _ _ o H) := m in  *)
(*   match o, H with *)
(*   | Ordinal m i, H' =>  *)
(*       @exist _ _ (Ordinal i) (compatible_lab_decr_ord H') *)
(*   end.  *)

Lemma add_lab_N : ext add_lab n = some l.
Proof. Admitted.

(* Definition add_rf_some *)
(*   (m : 'I_N) *)
(*   (RF : ocompatible (ext lab m) (some l)) *)
(*   (k : 'I_N.+1) *)
(*   (IR : is_read (add_lab k)) : *)
(*   {l : 'I_k | (ocompatible (ext add_lab l) (ext add_lab k))} :=  *)
(*     match N =P k with *)
(*     | ReflectF p => *)
(*       incr_rf_codom  *)
(*         (decr_ord_ord k p) *)
(*         (frf (decr_ord k p) (is_read_add_lab k p IR)) *)
(*     | ReflectT eq =>  *)
(*       match eq, m with *)
(*         erefl, m' =>  *)
(*         @exist _ _  *)
(*         m'  *)
(*         (advance_is_read  *)
(*           (@eq_ind_r _ _ (fun i => ocompatible _ i) RF _ add_lab_N)) *)
(*       end *)
(*     end. *)

Lemma ord_P (k : 'I_n.+1) : n = k ->
  (~ is_read l) -> (~ is_read (add_lab k)).
Proof. Admitted.

Definition add_rf_None
  (NR : ~ is_read l)
  (k : 'I_n.+1)
  (IR : is_read (add_lab k)) :
  {l : 'I_k | (ocompatible (ext add_lab l) (ext add_lab k))} :=
  match N =P k with
  | ReflectF p =>
    incr_rf_codom 
      (decr_ord_ord k p)
      (frf (decr_ord k p) (is_read_add_lab k p IR))
  | ReflectT eq => match ord_P _ eq NR IR with end
  end.

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
