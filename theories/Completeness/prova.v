(** ** Kripke Completeness **)

From FOL Require Import FullSyntax Theories Deduction.FullSequentFacts Deduction.FragmentSequentFacts.


From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec FOL.Deduction.FullND.
Require Import List Vector Lia.
Import ListAutomationNotations ListAutomationHints ListAutomationInstances ListAutomationFacts.
From FOL.Completeness Require Export TarskiCompleteness.
From FOL.Utils Require Import MPFacts.
Require Import Coq.Program.Equality.

Require Import Undecidability.FOL.Semantics.Tarski.FullCore.

(* ** Universal Models *)
Section VariableDomainKripke.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  
  Arguments eval {_ _ _} _ _ _.
  Arguments i_atom {_ _ _} _ _.
  Arguments i_func {_ _ _} _ _.

  (*Variable domain : Type.*)
  Class kframe :=
      { 
        domain : Type;
        nodes : Type ;
        world : nodes -> domain -> Prop;

        reachable : nodes -> nodes -> Prop ;
        reach_refl u : reachable u u ;
        reach_tran u v w : reachable u v -> reachable v w -> reachable u w ;

        monotone u v : reachable u v ->  forall x:domain, world u x ->  world v x ;
      }.
  Context {frm : kframe}.

  Definition world_opt (u: nodes) (j: option domain) : Prop :=
    match j with 
    | Some j => world u j
    | None => False
  end.

  Definition in_dom (u : nodes) (n : nat) (vv: (t (option _) n)): Prop :=
    forall x, In x vv -> match x with 
                        | Some x => (world u) x
                        | None => False
                        end.

  Lemma in_dom_mon (u v: nodes)(n : nat) (vv: (t (option _) n)) :
      reachable u v -> in_dom u vv -> in_dom v vv.
  Proof.
    unfold in_dom. intros. destruct x; 
    apply H0 in H1; eauto using monotone.
  Qed. 

  Class kmodel := {
        I : nodes -> interp (option domain);
        
        mon_f (u v: nodes) (f: syms) (vv: (t (option domain) (ar_syms f))): 
          reachable u v -> exists w:domain, i_func (I u) f vv = Some w ->  i_func (I v) f vv = Some w ;

        k_f_wellDef (u v:nodes) (f: syms) (vv: (t (option domain) (ar_syms f))) (a : in_dom u vv): 
          exists w:domain, i_func (I u) f vv = Some w -> world u w;

        mon_P (u v:nodes) (P: preds) (vv: (t (option domain) (ar_preds P))) (reach : reachable u v): 
          i_atom (I u) P vv -> i_atom (I v) P vv;

        k_P_wellDef u P vv: i_atom (I u) P vv -> in_dom u vv; 
  }.

   Context {M : kmodel}.

  Fixpoint k_eval (u : nodes) (rho : nat -> domain) (t : term) : option domain :=
      match t with
      | var s    => match (world u (rho s)) with
                    | True => Some (rho s)
                    end
      | func f v => i_func (I u) f (Vector.map (k_eval u rho) v)
      end. 

  Definition good (u : nodes) (rho : nat -> domain)  := 
      (forall n : nat, world u (rho n)).

  Lemma world_translation (u: nodes)(rho : nat -> domain)(op_t : option domain) : 
    world_opt u op_t <-> exists j: domain, op_t = Some j /\ world u j.
  Proof.
    split; intros.
    induction op_t.
    exists a; eauto.
    simpl in H; eauto.
    unfold world_opt; destruct op_t.
    discriminate.

Lemma good_eval (u : nodes) (rho : nat -> domain) (t : term):
  good u rho -> world_opt u (k_eval u rho t). 
  Proof.
    intros. induction t.
    * simpl. eauto.
    * cbn. 
      apply k_f_wellDef.  unfold in_dom.
      intros x [a [b <-]] % vector_in_map. now apply IH.
Qed.

   Lemma good_mon (u v: nodes) (rho : nat -> domain) :
      good u rho -> reachable u v -> good v rho.
    Proof.
      unfold good.
      intros.
      eauto using monotone.
    Qed.

   Fixpoint ksat{ff : falsity_flag}(u: nodes)(rho : nat -> domain)(phi : form) : Prop :=
      match phi with
      | atom P vv => i_atom (I u) P (map (eval (I u) rho) vv) 
      | falsity => False
      | bin Impl phi psi => forall v, reachable u v -> ksat v rho phi -> ksat v rho psi
      | bin Conj phi psi => (ksat u rho phi) /\ (ksat u rho psi)
      | bin Disj phi psi => (ksat u rho phi) \/ (ksat u rho psi) 
      | quant All phi => forall v, reachable u v -> forall j : domain, world v j -> ksat v (j .: rho) phi 
      | quant Ex phi => exists j: domain, world u j  /\  ksat u (j .: rho) phi
      end.


