Require Export SfLib.
Require Import ListSet.
(* see http://coq.inria.fr/distrib/V8.4/stdlib/Coq.Lists.ListSet.html 
   for the ListSet library *)


Definition var: Type := nat.

Inductive iexp : Type :=
  | econ : nat -> iexp
  | evar : var -> iexp
  | eplus: iexp -> iexp -> iexp
  | eminus: iexp -> iexp -> iexp.

(* 3 + x *)
Check (eplus (econ 3) (evar 1)).

Definition Env := var -> nat.

Fixpoint interp_iexp (e: iexp) (sigma: Env) : nat :=
  match e with
  | econ n => n
  | evar v => sigma v
  | eplus e1 e2 => (interp_iexp e1 sigma) + (interp_iexp e2 sigma)
  | eminus e1 e2 => (interp_iexp e1 sigma) - (interp_iexp e2 sigma)
  end.

(* acon true , acon false *)
Inductive assert: Type :=
  | atrue: assert  (* true *)
  | afalse: assert (* false *)
  | eeq: iexp -> iexp -> assert  (* e1 = e2 *)
  | elt: iexp -> iexp -> assert  (* e1 < e2 *)
  | aimp: assert -> assert -> assert (* a1 ==> a2 *)
  | aand: assert -> assert -> assert (* a1 /\ a2 *)
  | anot: assert -> assert (* not a *)
  | aor : assert -> assert -> assert (* a1 \/ a2 *)
  | aforall: var -> assert -> assert (* forall x. a *)
  | aexist: var -> assert -> assert  (* exists x. a *).

Check True.

Check (forall n: nat, n < 0).

Check (3 = 5).

Check (beq_nat 3 5).

Definition update (sigma: Env) (v: var) (n: nat) : Env :=
  fun (v' : var) => if (beq_nat v v') then n else sigma v'.

Fixpoint interp_assert (a: assert) (sigma: Env): Prop :=
  match a with
  | atrue => True
  | afalse => False
  | eeq e1 e2 => (interp_iexp e1 sigma) = (interp_iexp e2 sigma)
  | elt e1 e2 => (interp_iexp e1 sigma) < (interp_iexp e2 sigma)
  | aimp a1 a2 => (interp_assert a1 sigma) -> (interp_assert a2 sigma)
  | aand a1 a2 => 
       (interp_assert a1 sigma) /\ (interp_assert a2 sigma)
  | aor a1 a2 => (interp_assert a1 sigma) \/ (interp_assert a2 sigma)
  | anot a1 => ~ (interp_assert a1 sigma)
  | aforall v a1 => 
       forall n: nat, interp_assert a1 (update sigma v n) 
  | aexist v a1 =>
       exists n: nat, interp_assert a1 (update sigma v n)
  end.

(* exercise: give the following definitions *)
Definition valid (a: assert): Prop := 
  forall sigma:Env,interp_assert a sigma.
Check valid.
Definition strongerThan (a a': assert) : Prop :=
  forall sigma:Env,valid (aimp a a').



(* definition of judgment |- a *)
Inductive judge : assert -> Prop := 
  | xPlusZero : forall x: var, 
                  judge (eeq (eplus (evar x) (econ 0)) (evar x))
  | SymmObjEq : forall e0 e1 : iexp,
                  judge (aimp (eeq e0 e1) (eeq e1 e0))
  | ModusPonens: forall p q: assert, 
                  judge p -> judge (aimp p q) -> judge q
  | Generalization: forall (x: var) (p: assert),
                      judge p -> judge (aforall x p).

Check judge.

(* prove the judgment |- forall x, x = x+0 *)
Lemma test: judge (aforall 0 (eeq (evar 0) (eplus (evar 0) (econ 0)))).
Proof.
apply Generalization.
assert (judge (eeq (eplus (evar 0) (econ 0)) (evar 0))).
apply xPlusZero with (x:=0).
assert (judge (aimp (eeq (eplus (evar 0) (econ 0)) (evar 0)) (eeq (evar 0) (eplus (evar 0) (econ 0))) )).
apply SymmObjEq.
assert (judge (eeq (eplus (evar 0) (econ 0)) (evar 0)) ->
           judge (aimp (eeq (eplus (evar 0) (econ 0)) (evar 0)) (eeq (evar 0) (eplus (evar 0) (econ 0)))) ->
          judge (eeq (evar 0) (eplus (evar 0) (econ 0)) )).
apply ModusPonens.
apply H1.
apply H.
apply H0.
Qed.

(* exercise: prove the soundness of the simple logic theory *)
Lemma soundJudge: forall a, judge a -> valid a.
Proof.
intros a H.
induction H.
unfold valid.
intro sigma.
simpl. 
apply plus_0_r with (n:=sigma x).
unfold valid.
intro sigma.
simpl.
intro H.
rewrite H;reflexivity.
unfold valid.
intro sigma.
unfold valid in IHjudge1.
unfold valid in IHjudge2.
simpl in IHjudge2.
apply IHjudge2.
apply IHjudge1.
unfold valid.
simpl.
intro sigma.
intro n.
simpl.
apply IHjudge.
Qed.

(* set of variables *)
Definition varSet := set var.
Definition emp_vs : varSet := nil.

Definition veqDec : forall v1 v2: var, {v1 = v2} + {v1 <> v2} := eq_nat_dec.

Definition vs_add (v: var) (vs: varSet) := set_add veqDec v vs.

Definition vs_remove (v: var) (vs: varSet) := set_remove veqDec v vs.

Definition vs_union (vs1 vs2: varSet) := set_union veqDec vs1 vs2.

Definition vs_In (v: var) (vs: varSet) : Prop := set_In v vs.

Fixpoint fv_iexp (e : iexp) : varSet := 
  match e with
  | econ _ => emp_vs
  | evar v => [v]
  | eplus e1 e2 => vs_union (fv_iexp e1) (fv_iexp e2)
  | eminus e1 e2 => vs_union (fv_iexp e1) (fv_iexp e2)
  end.
  

Fixpoint fv_ast (a: assert) : varSet := 
  match a with
  | aforall v a' => vs_remove v (fv_ast a')
  | aexist v a' => vs_remove v (fv_ast a')
  | atrue => nil
  | afalse => nil
  | eeq e1 e2 => vs_union (fv_iexp e1) (fv_iexp e2)
  | elt e1 e2 => vs_union (fv_iexp e1) (fv_iexp e2)
  | aimp a1 a2 => vs_union (fv_ast a1) (fv_ast a2)
  | aand a1 a2 => vs_union (fv_ast a1) (fv_ast a2)
  | anot a => fv_ast a
  | aor a1 a2 => vs_union (fv_ast a1) (fv_ast a2)
  end.

(* exercise: prove the coincidence theorem shown in class *)
Lemma coincidence_exp: forall (sigma sigma': Env) (e: iexp),
  (forall v: var, vs_In v (fv_iexp e) -> sigma v = sigma' v)
  -> interp_iexp e sigma = interp_iexp e sigma'.
Proof.
intros sigma sigma' e.
intro H.
induction e.
simpl. reflexivity.
simpl.
apply H.
simpl.
left. reflexivity.
simpl.
rewrite IHe2.  rewrite IHe1. reflexivity.
intro v.
intro H1.
simpl in H.
apply H.
apply set_union_intro1.
apply H1.
intros v H1.
apply H.
simpl.
apply set_union_intro2.
apply H1.
simpl.
rewrite IHe1. rewrite IHe2.
reflexivity.
intros v H1. 
apply H;simpl. apply set_union_intro2. apply H1.
intros v H1. apply H; simpl. apply set_union_intro1. apply H1.
 Qed.

Theorem vs_In_rm:forall (vs:varSet) (v v':var),vs_In v' vs -> false=beq_nat v v'->vs_In v' (vs_remove v vs).
Proof.
intros.
induction vs.
inversion H.
simpl.
simpl in H.
destruct H.
remember (veqDec v a) as H1.
destruct H1.
rewrite <- e in H. rewrite H in H0.
assert (true=beq_nat v' v').
apply beq_nat_refl. rewrite <- H1 in H0. inversion H0.
simpl. left. apply H. 
remember (veqDec v a) as H1.
destruct H1.
apply H. simpl. right. apply IHvs. apply H.
Qed.


Theorem coincidence: forall (sigma sigma': Env) (a: assert),
  (forall v: var, vs_In v (fv_ast a) -> sigma v = sigma' v)
  -> (interp_assert a sigma <-> interp_assert a sigma').
Proof.
intros sigma sigma' a.
intro H.
generalize dependent  sigma.
generalize dependent sigma'.
induction a. 
split.
simpl. reflexivity.
simpl.  reflexivity. 
split. intro. simpl in H0.
 inversion H0.
 intro H0. simpl in H0. inversion H0.
split.
intro H0. simpl in H0. simpl.
assert (interp_iexp i0 sigma=interp_iexp i0 sigma').
apply coincidence_exp.
intros v H2. apply H. apply set_union_intro2. apply H2.
rewrite <- H1.
assert (interp_iexp i sigma=interp_iexp i sigma').
apply coincidence_exp. intros v H2. apply H. apply set_union_intro1. apply H2.
rewrite <- H2. apply H0.
intro H0. simpl in H0. simpl.
assert (interp_iexp i0 sigma=interp_iexp i0 sigma').
apply coincidence_exp.
intros v H2. apply H. apply set_union_intro2. apply H2.
rewrite  H1.
assert (interp_iexp i sigma=interp_iexp i sigma').
apply coincidence_exp. intros v H2. apply H. apply set_union_intro1. apply H2.
rewrite H2. apply H0.
split. intro H0. simpl in H0. simpl.
assert (interp_iexp i0 sigma=interp_iexp i0 sigma').
apply coincidence_exp. intros v H2. apply H. apply set_union_intro2. apply H2. rewrite <- H1.
assert (interp_iexp i sigma=interp_iexp i sigma').
apply coincidence_exp. intros v H2. apply H. apply set_union_intro1. apply H2. rewrite <-  H2.
apply H0.
simpl. intro H0.
assert (interp_iexp i0 sigma=interp_iexp i0 sigma').
apply coincidence_exp. intros v H2. apply H. apply set_union_intro2. apply H2. rewrite  H1.
assert (interp_iexp i sigma=interp_iexp i sigma').
apply coincidence_exp. intros v H2. apply H. apply set_union_intro1. apply H2. rewrite  H2.
apply H0.
split. simpl. intros H0 H1.
apply IHa2 with (sigma:=sigma). intros v H3.  apply H.
simpl. apply set_union_intro2. apply H3. 
apply H0.  apply IHa1 with (sigma':=sigma'). intros v H2. apply H. simpl. apply set_union_intro1. apply H2. apply H1.
simpl. intros H0 H1. apply IHa2 with (sigma':=sigma'). intros v H2. apply H. simpl. apply set_union_intro2. apply H2.
apply H0. apply IHa1 with (sigma:=sigma). intros v H2. apply H. simpl. apply set_union_intro1. apply H2. apply H1.
split. simpl. intros H0.
split. apply IHa1 with (sigma:=sigma). intros v H1. apply H. simpl.  apply set_union_intro1. apply H1. apply H0.
apply IHa2 with (sigma:=sigma). intros v H1. apply H. simpl. apply set_union_intro2. apply H1. apply H0.
simpl. intro H0. split.
apply IHa1 with (sigma':=sigma'). intros v H1. apply H. simpl. apply set_union_intro1. apply H1. apply H0.
apply IHa2 with (sigma':=sigma'). intros v H1. apply H. simpl. apply set_union_intro2. apply H1. apply H0.
simpl. split.
intro H0.  unfold not. unfold not in H0. intro H1. apply H0. apply IHa with (sigma':=sigma'). intros v H2.
apply H. simpl. apply H2. apply H1.
unfold not. intros H0 H1. apply H0. apply IHa with (sigma:=sigma). intros v H2.
apply H. simpl. apply H2. apply H1.
simpl. split.
intros H0. 
destruct H0. left. apply IHa1 with (sigma:=sigma). intros v H1. apply H. simpl. apply set_union_intro1. apply H1. apply H0.
right. apply IHa2 with (sigma:=sigma). intros v H1. apply H. simpl. apply set_union_intro2. apply H1. apply H0.
intros H0. 
destruct H0. left. apply IHa1 with (sigma':=sigma'). intros v H1. apply H. simpl. apply set_union_intro1. apply H1. apply H0.
right. apply IHa2 with (sigma':=sigma'). intros v H1. apply H. simpl. apply set_union_intro2. apply H1. apply H0.
intros.
simpl. split.
intros.
apply IHa with (sigma:=(update sigma v n)).
intros.
unfold update.
remember (beq_nat v v0) as E.
destruct E.
reflexivity.
apply H. simpl.
apply vs_In_rm. apply H1. apply HeqE. 
apply H0.
intros.
apply IHa with (sigma:=(update sigma' v n)).
intros.
unfold update.
remember (beq_nat v v0) as E.
destruct E.
reflexivity. 
rewrite H. reflexivity.
simpl. apply vs_In_rm. apply H1. apply HeqE. apply H0.
intros. simpl.   split.
intro.
destruct H0.
exists x.
apply IHa with (sigma:=(update sigma v x)).
intros. unfold update. 
remember (beq_nat v v0) as E.
destruct E. reflexivity.
apply H.  simpl. apply vs_In_rm. apply H1. apply HeqE. apply H0.
intro. destruct H0.
exists x.
apply IHa with (sigma':= (update sigma' v x)).
intros. unfold update.
remember (beq_nat v v0) as E.
destruct E. reflexivity. apply H. simpl. apply vs_In_rm. apply H1. apply HeqE. apply H0.
Qed.



Definition subst : Type := list (var * iexp). 

Fixpoint lookup_subst (v: var) (delta: subst) : option iexp :=
  match delta with
  | nil => None
  | (v', e') :: d => if veqDec v v' then Some e' else lookup_subst v d
  end.

(* this is a five star exercise (very difficult):
   define substitution, then formulate and prove 
   the substitution theorem shown in class. 
   *** Try to work on it early. Don't wait till 
       the last minute ***
*)



(*收集subst中所有替换式的自由变量*)
Fixpoint fv_subst (delta:subst) (vs:varSet):varSet:=
match delta with
| nil => vs
| (v,e)::delta' =>fv_subst delta' ( vs_union vs (fv_iexp e)) 
end.

(*找到自由变量集中的最大值*)
Fixpoint fv_max  (fvs:varSet) (m:var):var:=
match fvs with
| nil => m
| (v::fvs') => if ble_nat m v then fv_max  fvs' v else fv_max fvs' m
end.


(*判断v是否在自由集中*)
Fixpoint vs_in (v:var) (vs:varSet):bool:=
match vs with
| nil => false
| (v'::vs') => if veqDec v v' then true else vs_in v vs'
end.

(*
对表达式中的受约束变量进行重命名
vs:需要重命名的变量
m:需要重命名的变量加上该值即得到新的变量名
*)
Fixpoint rename_bound_var_exp (e:iexp) (vs:varSet) (m:var):iexp:=
match e with
| econ n => econ n
| evar x => if vs_in x vs then evar (x+m) else evar x
| eplus e1 e2 => eplus (rename_bound_var_exp e1 vs m) (rename_bound_var_exp e2 vs m)
| eminus e1 e2 => eminus (rename_bound_var_exp e1 vs m) (rename_bound_var_exp e2 vs m) 
end.

(*对assert中的受约束变量进行重命名*)
Fixpoint rename_bound_var (a:assert) (vs:varSet) ( m:var):assert:=
match a with
| atrue => atrue
| afalse =>afalse
| eeq e1 e2 => eeq (rename_bound_var_exp e1 vs m) (rename_bound_var_exp e2 vs m)
| elt e1 e2 => elt (rename_bound_var_exp e1 vs m) (rename_bound_var_exp e2 vs m)
| aimp  a1 a2 => aimp (rename_bound_var a1 vs m) (rename_bound_var a2 vs m)
| aand a1 a2 => aand (rename_bound_var a1 vs m) (rename_bound_var a2 vs m)
| anot a' => anot (rename_bound_var a' vs m)
| aor a1 a2 => aor (rename_bound_var a1 vs m) (rename_bound_var a2 vs m)
| aforall v' a' => aforall (v'+m) (rename_bound_var a' (vs_add v' vs) m)
| aexist v' a' => aexist (v'+m) (rename_bound_var a' (vs_add v' vs) m)
end.



Fixpoint substitution_exp (e:iexp) (s:subst) :iexp:=
match e with
| econ n => econ n
| evar x => match lookup_subst x s with
                  | None => evar x
                  | Some e' => e'
                  end
| eplus e1 e2 => eplus (substitution_exp e1 s) (substitution_exp e2 s)
| eminus e1 e2 => eminus (substitution_exp e1 s) (substitution_exp e2 s)
end.

(*
对delta中任意两个元素(v1,e1)和(v2,e2),消除v1在e2(或v2出现在e1中)中出现的情况
*)
(*
Fixpoint subst_refl1 (delta:subst) (s:(var*iexp)):subst:=
match delta with
| nil => nil
| (v,e)::delta' => match s with 
                         |(v',e') => if veqDec v v then 
                                         else (v,(substitution_exp e [s]))::(subst_refl1 delta' s)
                         end 
end.

Fixpoint subst_refl (hdelta:subst) (tdelta:subst):subst:=
match tdelta with
| nil => hdelta
| (s::tdelta') => subst_refl (subst_refl1 hdelta s) tdelta'
end.  
*)

(*
在调用该函数前，必须确保
1. a 中的所有约束变量都重命名过了，且重命名后的名字不出在 a 或 delta 的自由变量中

*)

Fixpoint substitution1 (a:assert) (delta:subst):assert:=
match a with
| atrue => atrue
| afalse => afalse
| eeq e1 e2 => eeq (substitution_exp e1 delta) (substitution_exp e2 delta)
| elt e1 e2 => elt (substitution_exp e1 delta) (substitution_exp e2 delta)
| aimp a1 a2 => aimp (substitution1 a1 delta) (substitution1 a2 delta)
| aand a1 a2 => aand (substitution1 a1 delta) (substitution1 a2 delta)
| anot a' => anot (substitution1 a' delta)
| aor a1 a2 => aor (substitution1 a1 delta) (substitution1 a2 delta)
| aforall v a' => aforall v (substitution1 a' delta) (* v has been renamed early *)
| aexist v a' => aexist v (substitution1 a' delta)
end.


Definition substitution (a:assert) (delta:subst):assert:=
substitution1 (rename_bound_var a [] (1+(fv_max (vs_union (fv_ast a) (fv_subst delta [] )) 0)))
                     delta.


(*


Fixpoint substitution1 (a:assert) (v:(var*iexp)) :assert:=
match a with
| atrue => atrue
| afalse => afalse
| eeq e1 e2 => eeq (substitution_exp e1 v ) (substitution_exp e2 v )
| elt e1 e2 => elt (substitution_exp e1 v ) (substitution_exp e2 v )
| aimp a1 a2 => aimp (substitution1 a1 v ) (substitution1 a2 v )
| aand a1 a2 => aand (substitution1 a1 v ) (substitution1 a2 v )
| anot a' => anot (substitution1 a' v )
| aor a1 a2 => aor (substitution1 a1 v) (substitution1 a2 v )
| aforall v' a' => aforall v' (substitution1 a' v)
| aexist v' a' => aexist v' (substitution1 a' v)
end. 

Fixpoint substitution2 (a:assert)  (delta:subst) :assert:=
match delta with
| nil => a
| (v::delta') => substitution2 (substitution1 a  v ) (delta')
end.

Definition substitution (a:assert) (delta:subst):assert :=
substitution2 
(rename_bound_var a []  (1+ (fv_max (vs_union (fv_ast a) (fv_subst delta [])) 0)) )
delta.
*)
Check Env.
Fixpoint interp_subst (delta:subst) (sigma:Env):list (var*nat):=
match delta with
| nil => nil
| (v,e)::delta' => (v,interp_iexp e sigma)::(interp_subst delta' sigma)
end.

Fixpoint update_sigma1 (sigma:Env) (delta:list (var*nat)):Env:=
match delta with
| nil => sigma
| (v,e)::delta' =>update_sigma1 (update sigma v e) delta'
end.
Definition update_sigma (sigma:Env) (delta:subst):Env:=
update_sigma1 sigma (interp_subst delta sigma).

Theorem Substitution:forall (a:assert) (delta:subst) (sigma:Env) ,
interp_assert (substitution a delta) sigma <-> interp_assert a (update_sigma sigma delta).
Proof.
intros a delta.
split.
intro.
induction delta.
assert (interp_assert a sigma -> interp_assert (substitution a []) sigma).
intro.
unfold substitution.
simpl.
induction a.
simpl. reflexivity.
simpl. inversion H0.
simpl.
simpl in H0. 
simpl.
Admitted.











