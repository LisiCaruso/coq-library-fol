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
Require Import Program.Equality.
  (*
  
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
Arguments eval {_ _ _} _ _ _.
Arguments i_atom {_ _ _} _ _.
Arguments i_func {_ _ _} _ _.


Section VariableDomainKripke.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  

Variable U : Type.
  Class kframe :=
      {  
        (*U : Type; *) (* it is basically the universe set *)
        (*HOW do I make it so that I don't need to specify U as the universe every time I use 
        something from the library Ensembles?*)
        nodes : Type ;
        world : nodes -> U -> Prop;

        reachable : nodes -> nodes -> Prop ;
        reach_refl u : reachable u u ;
        reach_tran u v w : reachable u v -> reachable v w -> reachable u w ;

        monotone u v : reachable u v ->  forall x:U, world u x ->  world u x ;
      }.
  Context {frm : kframe}.

  Definition in_dom (u : nodes) (n : nat) (vv: (Vector.t _ n)): Prop :=
    Vector.Forall (world u) vv.

  Class kmodel := {
        I : nodes -> interp U;
        
        mon_f (u v:nodes) (f: syms) (vv: (Vector.t U (ar_syms f))) (reach : reachable u v) (a : in_dom u vv): 
           i_func (I u) f vv = i_func (I v) f vv;

        k_f_wellDef u f vv (vv_in_dom : (in_dom u vv)): world u (i_func (I u) f vv);

        mon_P (u v:nodes) (P: preds) (vv: (Vector.t U (ar_preds P))) (reach : reachable u v) (a : in_dom u vv) : 
           i_atom (I u) P vv -> i_atom (I v) P vv;
      }.

        Variable M : kmodel.

   Fixpoint ksat {ff : falsity_flag} (u: nodes) (rho : nat -> U) (phi : form) : Prop :=
      match phi with
      | atom P v => i_atom (I u) P (Vector.map (eval (I u) rho) v) 
      | falsity => False
      | bin Impl phi psi => forall v, reachable u v -> ksat v rho phi -> ksat v rho psi
      | bin Conj phi psi => (ksat u rho phi) /\ (ksat u rho psi)
      | bin Disj phi psi => (ksat u rho phi) \/ (ksat u rho psi) 
      | quant All phi => forall v, reachable u v -> forall j : U, world v j -> ksat v (j .: rho) phi 
      | quant Ex phi => exists j: U, world u j  /\  ksat u (j .: rho) phi
      end.

Definition good (u : nodes) (rho : nat -> U)  := 
      (forall n : nat, world u (rho n)).

Lemma good_eval (u : nodes) (rho : nat -> U) (t : term):
  good u rho -> world u (eval (I u) rho t).
  Proof.
    intros. unfold eval. induction t.
    * auto.
    * apply k_f_wellDef. unfold in_dom. 

End VariableDomainKripke.