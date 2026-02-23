(** ** toy to understand if things work out **)
(*from https://rocq-prover.org/doc/V8.20.0/stdlib/Coq.Sets.Ensembles.html#Included*)
From FOL Require Import FullSyntax Theories Deduction.FullSequentFacts.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
Require Import Vector List Lia Ensembles.
Import ListAutomationNotations ListAutomationHints ListAutomationInstances ListAutomationFacts.
From FOL.Completeness Require Export TarskiCompleteness.
From FOL.Utils Require Import MPFacts.
Require Import Nat.
  (*
  Print "∈".
  Print contains.
  Notation "x ∈ A" := (In x A) (at level 200). (*RANDOM NUMber 20!?!!?*)
  Notation "_ ∈ _" is already defined at level 70 with arguments constr at next level, constr at next level while it is now required to be at level 200 with arguments constr at next level, constr at next level.
  



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

  *)


(*
Class interp := B_I
      {
        i_func : forall f : syms, vec domain (ar_syms f) -> domain ;
        i_atom : forall P : preds, vec domain (ar_preds P) -> Prop
      }

_*)

Section VariableDomainKripke.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Variable U : Type.

(*
  Class kframe :=
      {  
        (*U : Type; *) (* it is basically the universe set *)
        (*HOW do I make it so that I don't need to specify U as the universe every time I use 
        something from the library Ensembles?*)
        nodes : Type ;
        world : nodes -> Ensemble U;

        reachable : nodes -> nodes -> Prop ;
        reach_refl u : reachable u u ;
        reach_tran u v w : reachable u v -> reachable v w -> reachable u w ;

        monotone u v : reachable u v -> Included U (world u) (world v);
      }.
*)
        Class kframe :=
      {  
        (*U : Type; *) (* it is basically the universe set *)
        (*HOW do I make it so that I don't need to specify U as the universe every time I use 
        something from the library Ensembles?*)
        nodes : Type ;
        world : nodes -> Ensemble U;

        reachable : nodes -> nodes -> Prop ;
        reach_refl u : reachable u u ;
        reach_tran u v w : reachable u v -> reachable v w -> reachable u w ;

        monotone u v : reachable u v -> Included U (world u) (world v);
      }.
  Context {frm : kframe}.

  Definition in_dom (u : nodes) (n : nat) (vv: (Vector.t _ n)): Prop :=
    Vector.Forall (In U (world u)) vv.

  Class kmodel := {
        monotone_vec (u v: nodes) (n : nat) (vv : (Vector.t U n)): @in_dom u n vv -> @in_dom v n vv;

        k_P u P (vv:Vector.t U (ar_preds P)): @in_dom u (ar_preds P) vv -> Prop ; 

        mon_P (u v:nodes) (P: preds) (vv: (Vector.t U (ar_preds P))) (a : @in_dom u (ar_preds P) vv) (reach : reachable u v): 
           @k_P u P vv a -> @k_P v P vv (@monotone_vec u v (ar_preds P) vv a);
        
        k_f u f (vv:Vector.t U (ar_syms f)): @in_dom u (ar_syms f) vv -> U; 
        k_f_wellDef u f vv (vv_in_dom : (@in_dom u (ar_syms f) vv)): (In U (world u)) (k_f vv_in_dom);

        mon_f (u v:nodes) (f: syms) (vv: (Vector.t U (ar_syms f))) (a : @in_dom u (ar_syms f) vv) (reach : reachable u v): 
           @k_f u f vv a = @k_f v f vv (@monotone_vec u v (ar_syms f) vv a);
      }.

    (*
 Class kinterp (u: nodes):= B_I
      {
        i_func : forall f : syms, Vector.t (U) (ar_syms f) -> (Some Type);
        i_atom : forall P : preds, Vector.t (world u) (ar_preds P) -> Some Prop;
      }.

    Context {kI : kinterp}.
*)


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