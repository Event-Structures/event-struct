From RelationAlgebra Require Import lattice monoid rel kat_tac kleene.
From mathcomp Require Import ssreflect ssrbool ssrfun.
From event_struct Require Import utilities.

(******************************************************************************)
(* General theory of rewriting systems                                        *)
(* Fisrt section called RewritingSystem. Here the theory of general rewriting *)
(* systems with to rewriing rules derived:                                    *)
(*   s1 ~>  s2                ==  the first rewriting rule                    *)
(*   s2 ~>+ s2                ==  transitive closure of the first rule        *)
(*   s2 >>  s2                ==  the second rewriting rule                   *)
(*   s2 >>+ s2                ==  transitive closure of the second rule       *)
(*   diamond_prop s1 s2 s3    ==  the dainomd property on s1 s2 and s3. It    *)
(*                            states that if one can rewrite s1 with the fist *)
(*                            rule to s2 (ie. s1 ~> s2) and with the second   *)
(*                            rule to s3 (ie. s1 >> s3) then exists some s4   *)
(*                            s.t. s2 >> s4 and s3 ~> s4:                     *)
(*                                                                            *)
(*                              s1 ~> s2                                      *)
(*                              v     v                                       *)
(*                              v     v                                       *)
(*                              s3 ~> s4 - exists                             *)
(*                                                                            *)
(*   half_confluence s1 s2 s3 == auxilary lemma about confluence              *)
(*   confluence s1 s2 s3      <-> the confluence theorem: it states that if   *)
(*                            the rewriting sysytem satisfies the dianomd     *)
(*                            property s1 ~>+ s2 and s2 >>+ s3 then exists s4 *)
(*                            s.t. s2 >>+ s4 and s3 ~>+ s4:                   *)
(*                                                                            *)
(*                              s1 ~>  ...  ~> s2                             *)
(*                              v              v                              *)
(*                              v              v                              *)
(*                              .              .                              *)
(*                              .              .                              *)
(*                              .              .                              *)
(*                              v              v                              *)
(*                              v              v                              *)
(*                              s3 ~>  ...  ~> s4 - exists                    *)
(* In the ERewritingSystem we have the general theory of the rewriting systems*)
(* with some equivalence relation. It is more comfortible to derive a such    *)
(* theory using lemmas about casual rewriting system with two rewriting rules *)
(*   s1 ~>   s2             ==  the rewriting rule                            *)
(*   s1 ~~   s2             ==  the equivalence relation                      *)
(*   s2 ~>~  s2             ==   ~> ⋅ ~~                                      *)
(*   s1 ~>+~ s2             ==  ~>⁺ ⋅ ~~                                      *)
(*   s1 ~>~+ s2             ==  (~> ⋅ ~~)⁺                                    *)
(*   ediamond_prop s1 s2 s3 <-> version of the diamond property for the       *)
(*                         rewriting systems with equivalence: it states that *)
(*                         s1 ~> s2 and s1 ~> s3 implies existance of some s4 *)
(*                         and s4' s.t. s2 ~> s4, s3 ~> s4' and s4 ~~ s4'.    *)
(*   equiv_prop s1 s2 s3   <-> if s1 ~> s2 and s1 ~~ s3 then there is some s4 *)
(*                         s.t. s3 ~> s4 and s2 ~~ s4                         *)
(*   econfluence s1 s2 s3  <-> the confluence principle for the rewriting     *)
(*                         systems with an equivalence relation:              *)
(*             s1 ~>⁺ s2 |                                                    *)
(*                       | ==> exists s4 ~~ s4' s.t. s2 ~>⁺ s4 and s3 ~>⁺ s4' *)
(*             s1 ~>⁺ s3 |                                                    *)
(******************************************************************************)

Section RewritingSystem.

Context {S : Type} (rw1 rw2 : hrel S S).

Notation "s1 ~> s2" := (rw1 s1 s2) (at level 20).
Notation "s1 >> s2" := (rw2 s1 s2) (at level 20).

Definition diamond_prop := forall s1 s2 s3, 
  s1 ~> s2 -> s1 >> s3 -> exists2 s4, s2 >> s4 & s3 ~> s4.

Hypothesis ((* shine on you crazy *) diamond : diamond_prop).

Notation "s1 ~>+ s2" := (rw1^+ s1 s2) (at level 20).
Notation "s1 >>+ s2" := (rw2^+ s1 s2) (at level 20).

Lemma half_confluence {s1 s2 s3}: 
  s1 ~> s2 -> s1 >>+ s3 -> exists2 s4 : S, s2 >>+ s4 & s3 ~> s4.
Proof.
  move=> + str; move: str s2.
  suff: (rw2^+ ≦ (fun s1 s3 => forall s2 : S, s1 ~> s2 -> exists2 s4 : S, s2 >>+ s4 & s3 ~> s4)).
  - apply.
  apply/itr_ind_l1=> {s1 s3} [?? /diamond d ? /d[x /(itr_ext rw2) *]|s1 s3 /=].
  - by exists x.
  move=> [? /diamond d IH ? /d[x ? /IH[y *]]]; exists y=> //.
  apply/(itr_cons rw2); by exists x.
Qed.

Lemma confluence s1 s2 s3: 
  s1 ~>+ s2 -> s1 >>+ s3 -> exists2 s4, s2 >>+ s4 & s3 ~>+ s4.
Proof.
  move: s3=> /[swap].
  suff: (rw1^+ ≦ (fun s1 s2 => forall s3, s1 >>+ s3 -> exists2 s4, s2 >>+ s4 & s3 ~>+ s4)).
  - apply.
  apply/itr_ind_l1=> {s1 s2} [?? s?|s1 s2 /= [s5 /half_confluence c IH s3 /c]].
  - case/(half_confluence s)=> x ? /(itr_ext rw1) ?; by exists x.
  case=> s6 /IH[s4 *]; exists s4=> //; apply/(itr_cons rw1); by exists s6.
Qed.

(* TODO: add lemma about maximal element *)

End RewritingSystem.

Arguments confluence {_ _ _}.

Section ERewritingSystem.

Variables (S : Type) (rw eqv : hrel S S).

Notation "s1 ~> s2"   := (rw           s1 s2) (at level 20).
Notation "s1 ~>+ s2"  := (rw^+         s1 s2) (at level 20).
Notation "s1 ~~ s2"   := (eqv          s1 s2) (at level 20).
Notation "s1 ~>~ s2"  := (rw ⋅ eqv     s1 s2) (at level 20).
Notation "s1 ~>+~ s2" := (rw^+ ⋅ eqv   s1 s2) (at level 20).
Notation "s1 ~>~+ s2" := ((rw ⋅ eqv)^+ s1 s2) (at level 20).

Definition ediamond_prop := forall s1 s2 s3, 
  s1 ~> s2 -> s1 ~> s3 -> 
  exists s4 s4', (s2 ~> s4 * s3 ~> s4' * s4 ~~ s4')%type.

Definition equiv_prop := forall s1 s2 s3, 
    s1 ~~ s2 -> s1 ~> s3 -> 
      exists2 s4 , s2 ~> s4 & s3 ~~ s4.

Hypothesis eqv_trans : forall e2 e1 e3, e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3.
Hypothesis eqv_symm  : forall e1 e2, e1 ~~ e2 -> e2 ~~ e1.
Hypothesis eqv_refl  : 1 ≦ eqv.
Hypothesis ediamond : ediamond_prop.
Hypothesis equiv : equiv_prop.

Lemma diamond_rwe : diamond_prop rw (rw ⋅ eqv).
Proof.
move=> s1 s2 s3 /= /ediamond d [s3' {d}/d[s4'' [s4' [[? e ? /equiv]]]]].
case/(_ _ e)=> x ??; exists x=> //; exists s4''=> //; exact/(eqv_trans s4').
Qed.

Lemma diamond_eqv s1 s2 s3 :
  s1 ~>+ s3 -> s1 ~~ s2 -> exists2 s4, s2 ~>+ s4 & s3 ~~ s4.
Proof.
  have: eqv^+ ≡ eqv.
  - by apply/(antisym _ _ _ (itr_ext eqv))/itr_ind_l1=> // ++ [/[swap]/[swap]]. 
  move=> E /(confluence equiv) H /E /H [x +]; exists x=> //; exact/E. 
Qed.

Lemma rwe_itr: (rw ⋅ eqv)^+ ≡ rw^+ ⋅ eqv.
Proof.
  apply/(antisym (rw ⋅ eqv)^+ )=> [|s1 s2 [x ]].
  apply/itr_ind_l1=> [|s1 s3 [s2 [x + /eqv_symm e [y /diamond_eqv/(_ e)]]]]. 
  - exact/(dot_leq (itr_ext rw) (leq_Reflexive eqv)).
  move=> s [s5 ? /eqv_symm/eqv_trans t/t ?]; exists s5=> //. 
  apply/(itr_cons rw); by exists x.
  suff: (rw^+ ≦ (fun s1 x => x ~~ s2 -> s1 ~>~+ s2)).
  - apply.
  apply/itr_ind_l1=> {s1 x} [s1 x ??|s1 x /= [y ? /[apply] ?]].
  - apply/(itr_ext (rw ⋅ eqv)); by exists x.
  apply/(itr_cons (rw ⋅ eqv)); do ? exists y=> //; exact/eqv_refl.
Qed.

Theorem econfluence s1 s2 s3: 
  s1 ~>+ s2 -> s1 ~>+ s3 -> 
  exists s4 s4', (s2 ~>+ s4 * s3 ~>+ s4' * s4 ~~ s4')%type.
Proof.
  move/(confluence diamond_rwe)=> /[swap]/[dup] ? /[-! dotx1 rw^+ s1].
  move/(dot_leq (leq_Reflexive rw^+) eqv_refl) /rwe_itr=> r /(_ _ r)[x].
  by case/rwe_itr=> y; exists y, x.
Qed.

End ERewritingSystem.