From RelationAlgebra Require Import lattice monoid rel kat_tac kleene.
From mathcomp Require Import ssreflect ssrbool ssrfun.
From event_struct Require Import utilities.

(*****************************************************************************)
(* General theory of rewriting systems                                       *)
(* Fisrt section called RewritingSystem. Here the theory of general rewriting*)
(* systems with to rewriting rules derived:                                  *)
(*   s1 ~>  s2                ==  the first rewriting rule                   *)
(*   s2 ~>+ s2                ==  transitive closure of the first rule       *)
(*   s2 >>  s2                ==  the second rewriting rule                  *)
(*   s2 >>+ s2                ==  transitive closure of the second rule      *)
(* We define several properties of rewriting systems and prove some          *)
(* relationships between them                                                *)
(*   commutative_diamond_prop (~>) (>>) == ∀ s1 s2 s3                        *)
(*                              s1 ~> s2                                     *)
(*                              v     v                                      *)
(*                              v     v                                      *)
(*                              s3 ~> s4 - exists                            *)
(*                                                                           *)
(*   strong_commute (~>) (>>)           == ∀ s1 s2 s3                        *)
(*                              s1 ~> s2                                     *)
(*                              v     v                                      *)
(*                              v     v                                      *)
(*                              ⋮     ⋮                                      *)
(*                              v     v                                      *)
(*                              v     v                                      *)
(*                              s3 ~> s4 - exists                            *)
(*   commute (~>) (>>)                  == ∀ s1 s2 s3                        *)
(*                              s1 ~>  ...  ~> s2                            *)
(*                              v              v                             *)
(*                              v              v                             *)
(*                              ⋮              ⋮                             *)
(*                              v              v                             *)
(*                              v              v                             *)
(*                              s3 ~>  ...  ~> s4 - exists                   *)
(*   diamond_prop (~>)                   == commuting_diamond_prop (~>) (~>) *)
(*   confluence   (~>)                   == commute (~>) (~>)                *)
(*   commutation_lemma                   <-> commuting_diamond_prop (~>) (>>)*)
(*                                       implies commute (~>) (>>)           *)
(*   Newman                              <-> diamond_prop (~>) implies       *)
(*                                       confluence (~>)                     *)
(* In the ERewritingSystem we have the general theory of the rewriting system*)
(* with some equivalence relation. It is more comfortible to derive a such   *)
(* theory using lemmas about casual rewriting system with two rewriting rules*)
(*   s1 ~>   s2              ==  the rewriting rule                          *)
(*   s1 ~~   s2              ==  the equivalence relation                    *)
(*   s2 ~>~  s2              ==   ~> ⋅ ~~                                    *)
(*   s1 ~>+~ s2              ==  ~>⁺ ⋅ ~~                                    *)
(*   s1 ~>~+ s2              ==  (~> ⋅ ~~)⁺                                  *)
(*   ediamond_prop (~>) (~~) == version of the diamond property for the      *)
(*                         rewriting systems with equivalence: it states that*)
(*                         s1 ~> s2 and s1 ~> s3 implies existance of some s4*)
(*                         and s4' s.t. s2 ~> s4, s3 ~> s4' and s4 ~~ s4'.   *)
(*   econfluence (~>) (~~)   == the confluence principle for the rewriting   *)
(*                         systems with an equivalence relation:             *)
(*             s1 ~>⁺ s2 |                                                   *)
(*                       | ==> exists s4 ~~ s4' s.t. s2 ~>⁺ s4 and s3 ~>⁺ s4'*)
(*             s1 ~>⁺ s3 |                                                   *)
(*   ENewman               <-> commuting_diamond_prop (~>) (~~) with         *)
(*                      ediamond_prop (~>) (~~) implies econfluence (~>) (~~)*)
(*****************************************************************************)

Section RewritingSystem.

Context {S : Type} (rw : hrel S S).

Notation "s1 ~> s2" := (rw s1 s2) (at level 20).
Notation "s1 ~>+ s2" := (rw^+ s1 s2) (at level 20).

Definition diamond_prop := forall s1 s2 s3, 
  s1 ~> s2 -> s1 ~> s3 -> exists2 s4, s2 ~> s4 & s3 ~> s4.

Definition confluence := forall s1 s2 s3, 
  s1 ~>+ s2 -> s1 ~>+ s3 -> exists2 s4, s2 ~>+ s4 & s3 ~>+ s4.

Section Commutation.

Context (rw' : hrel S S).

Notation "s1 >> s2" := (rw' s1 s2) (at level 20).
Notation "s1 >>+ s2" := (rw'^+ s1 s2) (at level 20).

Definition commuting_diamond_prop := forall s1 s2 s3,
  s1 ~> s2 -> s1 >> s3 -> exists2 s4, s2 >> s4 & s3 ~> s4.

Definition strong_commute := forall s1 s2 s3,
  s1 ~> s2 -> s1 >>+ s3 -> exists2 s4 : S, s2 >>+ s4 & s3 ~> s4.

Definition commute := forall s1 s2 s3,
  s1 ~>+ s2 -> s1 >>+ s3 -> exists2 s4, s2 >>+ s4 & s3 ~>+ s4.

Lemma semi_commute: 
  commuting_diamond_prop -> strong_commute.
Proof.
  move=> diamond s1 s2 s3 + str; move: str s2.
  suff: (rw'^+ ≦ (fun s1 s3 => forall s2 : S, s1 ~> s2 -> exists2 s4 : S, s2 >>+ s4 & s3 ~> s4)).
  - exact.
  apply/itr_ind_l1=> {s1 s3} [?? /diamond d ? /d[x /(itr_ext rw') *]|s1 s3 /=].
  - by exists x.
  move=> [? /diamond d IH ? /d[x ? /IH[y *]]]; exists y=> //.
  apply/(itr_cons rw'); by exists x.
Qed.

Lemma commutation_lemma: 
  commuting_diamond_prop -> commute.
Proof.
  move=> d s1 s2 s3.
  move: s3=> /[swap].
  suff: (rw^+ ≦ (fun s1 s2 => forall s3, s1 >>+ s3 -> exists2 s4, s2 >>+ s4 & s3 ~>+ s4)).
  - exact.
  apply/itr_ind_l1=> {s1 s2} [?? s?|s1 s2 /= [s5 /(semi_commute d) c IH s3 /c]].
  - case/(semi_commute d _ _ _ s)=> x ? /(itr_ext rw) ?; by exists x.
  case=> s6 /IH[s4 *]; exists s4=> //; apply/(itr_cons rw); by exists s6.
Qed.

End Commutation.

Lemma Newman : diamond_prop -> confluence.
Proof. exact/commutation_lemma. Qed.

End RewritingSystem.

Arguments commutation_lemma {_ _ _}.

Section ERewritingSystem.

Context {S} (rw eqv : hrel S S).
Hypothesis eqv_trans : Transitive eqv.
Hypothesis eqv_symm  : Symmetric eqv.
Hypothesis eqv_refl  : 1 ≦ eqv.

Notation "s1 ~>   s2" := (rw           s1 s2) (at level 20).
Notation "s1 ~>+  s2" := (rw^+         s1 s2) (at level 20).
Notation "s1 ~~   s2" := (eqv          s1 s2) (at level 20).
Notation "s1 ~>~  s2" := (rw ⋅ eqv     s1 s2) (at level 20).
Notation "s1 ~>+~ s2" := (rw^+ ⋅ eqv   s1 s2) (at level 20).
Notation "s1 ~>~+ s2" := ((rw ⋅ eqv)^+ s1 s2) (at level 20).

Definition ediamond_prop := forall s1 s2 s3, 
  s1 ~> s2 -> s1 ~> s3 -> 
  exists s4 s4', (s2 ~> s4 * s3 ~> s4' * s4 ~~ s4')%type.

Definition econfluence := forall s1 s2 s3,
  s1 ~>+ s2 -> s1 ~>+ s3 -> 
  exists s4 s4', (s2 ~>+ s4 * s3 ~>+ s4' * s4 ~~ s4')%type.

Hypothesis ediamond : ediamond_prop.
Hypothesis equiv : commuting_diamond_prop eqv rw.

Lemma comm_rw_e : commuting_diamond_prop rw (rw ⋅ eqv).
Proof.
move=> s1 s2 s3 /= /ediamond d [s3' {d}/d[s4'' [s4' [[? e ? /equiv]]]]].
case/(_ _ e)=> x ??; exists x=> //; exists s4''=> //; exact/(eqv_trans _ s4').
Qed.

Lemma diamond_eqv : strong_commute eqv rw.
Proof.
  move=> s1 s2 s3 /[swap].
  have: eqv^+ ≡ eqv.
  - by apply/(antisym _ _ _ (itr_ext eqv))/itr_ind_l1=> // ++ [/[swap]]. 
  move=> E /(commutation_lemma equiv) H /E /H [x +]; exists x=> //; exact/E. 
Qed.

Lemma rwe_itr: (rw ⋅ eqv)^+ ≡ rw^+ ⋅ eqv.
Proof.
  apply/(antisym (rw ⋅ eqv)^+ )=> [|s1 s2 [x ]].
  apply/itr_ind_l1=> [|s1 s3 [s2 [x + /eqv_symm e [y /diamond_eqv-/(_ _ e)]]]]. 
  - exact/(dot_leq (itr_ext rw) (leq_Reflexive eqv)).
  move=> s [s5 ? /eqv_symm/eqv_trans t/t ?]; exists s5=> //. 
  apply/(itr_cons rw); by exists x.
  suff: (rw^+ ≦ (fun s1 x => x ~~ s2 -> s1 ~>~+ s2)).
  - apply.
  apply/itr_ind_l1=> {s1 x} [s1 x ??|s1 x /= [y ? /[apply] ?]].
  - apply/(itr_ext (rw ⋅ eqv)); by exists x.
  apply/(itr_cons (rw ⋅ eqv)); do ? exists y=> //; exact/eqv_refl.
Qed.

Theorem ENewman: econfluence.
Proof.
  move=> s1 s2 s3.
  move/(commutation_lemma comm_rw_e) => /[swap]/[dup] ? /[-! dotx1 rw^+ s1].
  move/(dot_leq (leq_Reflexive rw^+) eqv_refl) /rwe_itr=> r /(_ _ r)[x].
  by case/rwe_itr=> y; exists y, x.
Qed.


End ERewritingSystem.
