From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order choice.
From mathcomp Require Import eqtype fingraph path finmap. 
From event_struct Require Import utilities EventStructure inhType.

Section RegMachine.

Open Scope fmap.
Context {val : inhType}.

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

Definition thrd_state := (nat * {fmap reg -> val})%type. 

Variable p : seqprog.

Notation nth := (nth (CJmp 0 0)).

Definition thrd_sem (st : thrd_state) :
  (option (label unit val) * (val -> thrd_state))%type :=
  let: (ip, map) := st in
  match nth p ip with
  | WriteReg v r => (none,             fun=> (ip.+1, map.[r <- v]))
  | ReadLoc  r x => (some (Read x tt), fun v => (ip.+1, map.[r <- v]))
  | WriteLoc v x => (some (Write x v), fun=> (ip.+1, map))
  | CJmp     r n => (none,             fun=> (if map.[? r] is some v then
                                                if v == inh then n else ip.+1
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
