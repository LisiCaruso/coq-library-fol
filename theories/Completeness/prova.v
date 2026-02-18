(** ** toy to understand if things work out **)
(*from https://rocq-prover.org/doc/V8.20.0/stdlib/Coq.Sets.Ensembles.html#Included*)
From FOL Require Import FullSyntax Theories Deduction.FullSequentFacts.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
Require Import Vector List Lia.
Import ListAutomationNotations ListAutomationHints ListAutomationInstances ListAutomationFacts.
From FOL.Completeness Require Export TarskiCompleteness.
From FOL.Utils Require Import MPFacts.
Require Import Nat.

Section Ensembles.

  Variable U : Type.

  Definition Ensemble := U -> Prop.
  Inductive Empty_set : Ensemble :=.
  Definition In (A:Ensemble) (x:U) : Prop := A x.

  Definition Included (B C:Ensemble) : Prop := forall x:U, In B x -> In C x.

  Inductive Singleton (x:U) : Ensemble :=
    In_singleton : In (Singleton x) x.

  Inductive Union (B C:Ensemble) : Ensemble :=
    | Union_introl : forall x:U, In B x -> In (Union B C) x
    | Union_intror : forall x:U, In C x -> In (Union B C) x.

  Definition Add (B:Ensemble) (x:U) : Ensemble := Union B (Singleton x).
  
  Inductive Intersection (B C:Ensemble) : Ensemble :=
    Intersection_intro :
    forall x:U, In B x -> In C x -> In (Intersection B C) x.


  (*
  Print "∈".
  Print contains.
  Notation "x ∈ A" := (In x A) (at level 200). (*RANDOM NUMber 20!?!!?*)
  Notation "_ ∈ _" is already defined at level 70 with arguments constr at next level, constr
at next level while it is now required to be at level 200 with arguments constr
at next level, constr at next level.
  
  *)

  Inductive Full_set : Ensemble :=
    Full_intro : forall x:U, In Full_set x.
End Ensembles.
(* Definition U : Type. *)
Definition setA := Singleton 0.
Definition setB := Singleton 1.
Definition setC := Singleton 2.
Definition setD := Union setA setB.
Definition setE := Union setB setC.
Definition emp :=Intersection setA setB.

Inductive node : Type :=
  | bottom
  | a
  | b
  | c
  | d
  | e.

Definition my_world (u : node):=
  match u with 
  | bottom => emp
  | a => setA
  | b => setB
  | c => setC
  | d => setD
  | e => setE
  end.
  Check my_world.
  Definition aa := my_world a.
  Definition bb := my_world b.
  Print aa.
  Print bb.
  Check (Included (my_world a) (my_world b)).

Definition my_reach (u v: node) : Prop := Included (my_world u) (my_world v).

Lemma my_reach_refl (u : node) : my_reach u u.
Proof.
  unfold my_reach.
  unfold Included.
  intro. auto.
Qed.

Lemma my_reach_tran (u v w: node) : my_reach u v -> my_reach v w -> my_reach u w.
Proof.
  intros. unfold my_reach in *.
  unfold Included in *. auto.
Qed.



Definition my_vec_in_dom (u: node) (P : preds) (vv : (Vector.t _ (ar_preds P))) : Prop := 
Vector.Forall (In (my_world u)) vv.


Section VariableDomainKripke.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

(*
Class interp := B_I
      {
        i_func : forall f : syms, vec domain (ar_syms f) -> domain ;
        i_atom : forall P : preds, vec domain (ar_preds P) -> Prop
      }

_*)
Definition vec_in_dom''  (u: node) (P : preds) (vv : (Vector.t nat (ar_preds P))) : Prop := 
      Vector.Forall (In (my_world u)) vv.

      Print preds_signature.
Print Vector.Forall.
  Class kmodel_base :=
      {  
        U : Type; (* it is basically the universe set *)
        nodes : Type ;
        world : nodes -> Ensemble U;

        reachable : nodes -> nodes -> Prop ;
        reach_refl u : reachable u u ;
        reach_tran u v w : reachable u v -> reachable v w -> reachable u w ;

        my_vec_in_dom: forall u: nodes, forall P :preds, forall vv : (Vector.t U (ar_preds P)), 
          Vector.Forall (In (world u)) vv;

        vec_in_dom_P: forall u: nodes, forall P :preds, forall vv : (Vector.t U (ar_preds P)), Prop; 
        vec_in_dom_f: forall u: nodes, forall f :syms, forall vv : (Vector.t U (ar_syms f)), Prop; 

        monotone u v : reachable u v -> Included (world u) (world v);
        monotone_vec_P (u v: nodes) {P: preds} (vv : (Vector.t U (ar_preds P))): vec_in_dom_P u vv -> vec_in_dom_P v vv;
        monotone_vec_f (u v: nodes) {f: syms} (vv : (Vector.t U (ar_syms f))): vec_in_dom_f u vv -> vec_in_dom_f v vv;

        k_P u P (vv:Vector.t U (ar_preds P)): @vec_in_dom_P u P vv -> Prop ; 

        mon_P (u v:nodes) (P: preds) (vv: (Vector.t U (ar_preds P))) (a : vec_in_dom_P u vv) (reach : reachable u v): 
           @k_P u P vv a -> @k_P v P vv (@monotone_vec_P u v P vv a);
        
        k_f u f (vv:Vector.t U (ar_syms f)): @vec_in_dom_f u f vv -> U; 
        k_f_wellDef u f vv (vv_in_dom : (@vec_in_dom_f u f vv)): (In (world u)) (k_f vv_in_dom);

        mon_f (u v:nodes) (f: syms) (vv: (Vector.t U (ar_syms f))) (a : vec_in_dom_f u vv) (reach : reachable u v): 
           @k_f u f vv a = @k_f v f vv (@monotone_vec_f u v f vv a);
      }.
    Locate preds_signature.

    Variable M : kmodel.
    Fixpoint ksat {ff : falsity_flag} u (rho : nat -> domain) (phi : form) : Prop :=
      match phi with
      | atom P v => k_P u (Vector.map (@eval _ _ _ k_interp rho) v)
      | falsity => False
      | bin Impl phi psi => forall v, reachable u v -> ksat v rho phi -> ksat v rho psi
      | bin Conj phi psi => (ksat u rho phi) /\ (ksat u rho psi)
      | bin Disj phi psi => (ksat u rho phi) \/ (ksat u rho psi) 
      | quant All phi => forall j : domain, ksat u (j .: rho) phi
      | quant Ex phi => exists j: domain, ksat u (j .: rho) phi
      end.

End VariableDomainKripke.