From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order choice.
From mathcomp Require Import eqtype fingraph path finmap. 
From event_struct Require Import utilities EventStructure InhType TransitionSystem.

Section RegMachine.
(*****************************************************************************)
(********* Simple Definitions ************************************************)
(*****************************************************************************)

Open Scope fmap.
Context {val : inhType}.
Notation exec_event_struct := (@exec_event_struct val).
Notation lab := (@lab val).

(* Registers --- thread local variables *)
Definition reg := nat. 

(* Instruction *)
Inductive instr :=
| WriteReg : val -> reg -> instr
| ReadLoc  : reg -> loc -> instr
| WriteLoc : val -> loc -> instr
| CJmp     : reg -> nat -> instr.

Definition seqprog := seq instr.

Definition parprog := seq seqprog.

Definition thrd_state := 
  (nat *            (* instruction pointer                     *)
  {fmap reg -> val} (* finite mapping from registers to values *)
  )%type. 

(*****************************************************************************)
(********* Adding event with "hole" ******************************************)
(*****************************************************************************)

Variable (es : exec_event_struct).
Notation n := (n es).

Definition ocompatible (k : 'I_n) (v : val) (x : loc) : 
  {? k : 'I_n |
      compatible (te_ext (lab es) k) (Read x v)} := 
  insub k.

Fixpoint compatible_seq_aux (x : loc) (k : nat) :
  seq {v : val &
      {k : 'I_n |
         compatible (te_ext (lab es) k) (Read x v)}}
 := 
  if k is k'.+1 then
    if insub k is some r then
      if lab es r is Write y v then
        if x == y then
          if ocompatible r v x is some comp then
            (existT _ v comp) :: (compatible_seq_aux x k')
          else compatible_seq_aux x k'
        else compatible_seq_aux x k'
      else compatible_seq_aux x k'
    else [::]
  else [::].

Definition compatible_seq (x : loc) :
  seq {v : val & {k : 'I_n | compatible (te_ext (lab es) k) (Read x v)}}
  := compatible_seq_aux x n.-1.

Fixpoint es_seq x op
  (s : seq {v : val &
           {k : 'I_n |
              compatible (te_ext (lab es) k) (Read x v)}}) : 
           seq (exec_event_struct * val) := 
  if s is (existT v comp) :: st then
      (add_event es (Add es (Read x v) op (fun=> comp)), v) :: 
      es_seq x op st
  else [::].

Definition add_label_unit_val 
  (l : label unit val) (op : option 'I_n) :
  seq (exec_event_struct * val) :=
  match l with
  | Read x tt   => es_seq x op (compatible_seq x)
  | Write x v   => [:: (add_event es 
      (Add es (Write x v) op (fun x => match Bool.diff_false_true x with end)), v)]
  | _           => [::]
  end.

(*****************************************************************************)
(********* Step of regmachine definition *************************************)
(*****************************************************************************)

Variable p : seqprog.

Notation nth := (nth (CJmp 0 0)).

Definition thrd_sem (st : thrd_state) :
  (option (label unit val) * (val -> thrd_state)) :=
  let: (ip, map) := st in
  match nth p ip with
  | WriteReg v r => (none,             fun _ => (ip.+1, map.[r <- v]))
  | ReadLoc  r x => (some (Read x tt), fun v => (ip.+1, map.[r <- v]))
  | WriteLoc v x => (some (Write x v), fun _ => (ip.+1, map))
  | CJmp     r n => (none,             fun _ => 
                                             (if map.[? r] is some v then
                                                if v == inh then ip.+1 else n
                                              else ip.+1, map))
  end.

Definition ltr_thrd_sem (l : option (label val val)) (st1 st2 : thrd_state) : bool :=
  match thrd_sem st1, l with
  | (some (Write x v), st), some (Write y u) => [&& x == y, v == u & st inh == st2]
  | (some (Read  x _), st), some (Read  y u) => (x == y) && (st u == st2)
  | (none            , st), none             => st inh == st2
  | _, _                                     => false
  end.

End RegMachine.
