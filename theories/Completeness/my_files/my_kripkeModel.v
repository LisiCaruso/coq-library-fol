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

  Definition in_dom (u : nodes) (n : nat) (vv: (t _ n)): Prop :=
    forall x, In x vv -> (world u) x.

  Lemma in_dom_mon (u v: nodes)(n : nat) (vv: (t _ n)) :
      reachable u v -> in_dom u vv -> in_dom v vv.
  Proof.
    unfold in_dom.
    eauto using monotone.
  Qed. 

  Class kmodel := {
        I : nodes -> interp domain;
        
        mon_f (u v:nodes) (f: syms) (vv: (t domain (ar_syms f))) (reach : reachable u v) (a : in_dom u vv): 
           i_func (I u) f vv = i_func (I v) f vv;

        k_f_wellDef u f vv (vv_in_dom : (in_dom u vv)): world u (i_func (I u) f vv) (*/\  in_dom u vv*);

        mon_P (u v:nodes) (P: preds) (vv: (t domain (ar_preds P))) (reach : reachable u v) (a : in_dom u vv): 
           i_atom (I u) P vv -> i_atom (I v) P vv;

        k_P_wellDef u P vv: i_atom (I u) P vv -> in_dom u vv;
      }.

   Context {M : kmodel}.

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

Definition good (u : nodes) (rho : nat -> domain)  := 
      (forall n : nat, world u (rho n)).

Lemma good_eval (u : nodes) (rho : nat -> domain) (t : term):
  good u rho -> world u (eval (I u) rho t). 
  Proof.
    intros. induction t.
    * eauto.
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

 Lemma eval_mon_t (u v: nodes) (rho : nat -> domain)(t: term):
      @good u rho -> reachable u v -> eval (I u) rho t = eval (I v) rho t.
      intros. induction t. 
      * simpl. reflexivity.
      * simpl.
        erewrite map_ext_in.
        apply mon_f. apply H0. unfold in_dom.
        intros x [a [b <-]] % vector_in_map. 
        erewrite <- IH.  
        now eapply good_eval.
        apply b. apply IH.
  Qed.     

  Lemma eval_mon (u v: nodes) (rho : nat -> domain):
      @good u rho -> reachable u v -> forall t: term, eval (I u) rho t = eval (I v) rho t.
  Proof.
    intros.
    now apply eval_mon_t.
  Qed.

  Lemma map_eval_vv (u v: nodes) (rho : nat -> domain) (n : nat)(vv: t term n):
      @good u rho -> reachable u v -> map (eval (I u) rho) vv = map (eval (I v) rho) vv.
  Proof.
    intros.
    eapply map_ext. now eapply eval_mon.
  Qed.

  Lemma in_dom_mix (u v: nodes) (rho : nat -> domain) (n : nat)(vv: t term n):
      @good u rho -> reachable u v -> in_dom u (map (eval (I u) rho) vv) -> in_dom u (map (eval (I v) rho) vv).
  Proof.
    intros. 
    erewrite map_ext_in. 
    erewrite <- map_eval_vv. apply H1.
    apply H. apply H0.  
    intros. 
    eauto using eval_mon, good_mon, reach_refl. 
  Qed.

   Lemma good_shift (u: nodes)(rho : nat -> domain)(j : domain):
      good u rho -> world u j -> good u (j .: rho).
    Proof.
      unfold good.
      intros H wj n.
      induction n; simpl; auto.
    Qed.  

    Lemma shift_ext (rho xi: nat -> domain)(j : domain): 
      (forall x : nat, rho x = xi x) -> forall x: nat, (j .: rho) x = (j .: xi) x.
    Proof.
      intros. unfold scons. destruct x. reflexivity. apply H. 
    Qed.
    
    Lemma good_ext (u: nodes) (rho xi: nat -> domain):
      good u rho ->  (forall x, rho x = xi x) -> good u xi.
    Proof.
      intros. unfold good in *. intros. rewrite <- H0. apply H.
    Qed.

    Lemma good_comp (u: nodes)(rho: nat -> domain)(xi : nat -> term):
     good u rho -> good u (xi >> eval (I u) rho).
    Proof.
    intros. unfold good. intros. eapply good_eval. apply H.
    Qed.

    Lemma good_comp_reach (u v: nodes)(rho: nat -> domain)(xi : nat -> term):
      good u rho -> reachable u v -> good v (xi >> eval (I u) rho).
    Proof.
    unfold good. intros. eapply good_mon; now eauto using good_comp. 
    Qed.

      
  
End VariableDomainKripke.

Arguments kmodel {_ _ _}.

#[local] Ltac comp := repeat (progress (cbn in *; autounfold in *)).

Section KripkeSat.
  Context {Σf : funcs_signature} {Σp : preds_signature}.
  Context {frm : kframe}.

  Context {M : kmodel}.
(* Context {ff : falsity_flag} *)



    
    Arguments eval {_ _ _} _ _ _.

    Lemma ksat_mon {ff : falsity_flag}(u v: nodes) (rho : nat -> domain) (phi : form) : 
      good u rho -> reachable u v -> ksat u rho phi -> ksat v rho phi.
    Proof.
      revert rho. 
      induction phi; intros rho gd R H; cbn.
      * apply H.
      * unfold ksat in H.
        apply (mon_P R). 
          ++ erewrite map_eval_vv; try apply reach_refl; eauto using in_dom_mix, k_P_wellDef, good_mon. 
          ++ erewrite <- map_eval_vv; eauto. 
      * destruct b0.
        + destruct H; split; eauto.
        + destruct H; [left | right]; eauto. 
        + simpl in H. intros w Rw IH. eauto using reach_tran. 
      * destruct q; simpl in H.
        + intros w Rw j wj. eauto using reach_tran. 
        + destruct H as (j, H). exists j. split.
          ++ eapply monotone; now eauto.
          ++ eapply IHphi. now eapply good_shift. apply R. apply H.
    Qed.

    Lemma ksat_iff {ff : falsity_flag}(u v: nodes) (rho : nat -> domain) (phi : form):
      good u rho -> (ksat u rho phi <-> forall v (H : reachable u v), ksat v rho phi).
    Proof.
      split; intros.
      - eapply ksat_mon; eauto.
      - auto using reach_refl.
    Qed.
    
  Notation "rho  '⊩(' u ')'  phi" := (ksat _ u rho phi) (at level 20).
  Notation "rho '⊩(' u , M ')' phi" := (@ksat _ _ _ M _ u rho phi) (at level 20).
  
Arguments ksat {_ _ _} _ _ _, _ _ _ _ _ _.
  Hint Resolve reach_refl : core.

  Section Substs.

    Lemma ksat_ext {ff : falsity_flag}(u: nodes)(rho xi: nat -> domain)(phi: form):
      good u rho -> (forall x, rho x = xi x) -> (rho ⊩(u,M) phi <-> xi ⊩(u,M) phi).
    Proof.
      induction phi as [ | b P v | | ] in rho, xi, u |-*; intros gdu Hext; comp.
      - tauto.
      - erewrite Vector.map_ext. reflexivity. intros t. now apply eval_ext.
      - destruct b0;  split; intros H; try intros v Huv; rewrite IHphi1, IHphi2; eauto using good_ext, good_mon.  
      - destruct q.
        + split; intros; erewrite IHphi; eauto using good_mon, shift_ext, good_shift, good_ext.
        + split; intros; repeat destruct H; exists x; split;
          [ | eapply (IHphi _ (x .: rho) (x .: xi)) |  | eapply (IHphi _ (x .: xi) (x .: rho))]; 
          try eauto using good_shift, good_ext; induction x0; eauto.
    Qed.

   Lemma eval_shift_up (u: nodes)(rho: nat -> domain)(xi : nat -> term)(j : domain)(n: nat):
    ( j .: xi >> eval (I u) rho) n = ((up xi) >> eval (I u) (j .:rho)) n.
   Proof.
     intros; induction n; cbn.
     * reflexivity.
     * unfold ">>" in *. now erewrite <- eval_up. 
   Qed.

   Lemma eval_mon_shift_up (u v: nodes)(rho: nat -> domain)(xi : nat -> term)(j : domain)(n: nat):
    good u rho -> reachable u v ->
    ( j .: xi >> eval (I u) rho) n = ((up xi) >> eval (I v) (j .:rho)) n.
   Proof.
     intros; induction n; cbn.
     * reflexivity.
     * unfold ">>" in *. erewrite eval_mon; [now erewrite <- eval_up | | ]; auto.
   Qed.
    
    Lemma ksat_comp {ff : falsity_flag}(u: nodes)(rho: nat -> domain)(xi : nat -> term)(phi: form) :
      good u rho -> (rho ⊩(u,M) phi[xi] <-> (xi >> eval (I u) rho) ⊩(u,M) phi).
    Proof.
      induction phi as [ | b P v | | ] in rho, xi, u |-*; comp.
      - tauto.
      - erewrite Vector.map_map. erewrite Vector.map_ext. 2: apply eval_comp. reflexivity.
      - destruct b0; intros.
        + split; [split; [eapply IHphi1| eapply IHphi2] | split; [eapply IHphi1| eapply IHphi2]]; now eauto.
        + split; intros; destruct H0; [left | right | left | right]; 
          [eapply IHphi1| eapply IHphi2 | eapply IHphi1| eapply IHphi2]; now eauto. 
        + split; intros.
          ++ eapply ksat_ext; [now eapply good_comp_reach| intros | eapply IHphi2]; 
            [ eapply eval_mon | | apply (H0 v H1);  eapply IHphi1].
            5: eapply ksat_ext. 7: eapply H2. 6: intros; unfold ">>"; erewrite <- (eval_mon_t (xi x)). 
            all: now eauto using good_mon, good_comp.
          ++ eapply IHphi2; [ | eapply ksat_ext]; [| |intros | eapply H0].
            5: eapply ksat_ext. 7: eapply IHphi1. 8: eapply H2. 5: intros. 6: intros.
            all: unfold ">>" . 
            3: erewrite <- (eval_mon_t (xi x)). 
            all: eauto using good_comp_reach, eval_mon, good_comp, good_mon.
      - destruct q; split; intros; try  destruct H0 as (j, (H0, H1)); try exists j; try split; try apply H0.
          * eapply ksat_ext; try eapply IHphi; try eapply H0;
            [unfold good; intros; eapply good_shift| intros |  |  | ]; 
            eauto using good_comp_reach, good_shift, good_mon. now eapply eval_mon_shift_up. 
          * eapply IHphi; [ | eapply ksat_ext]; [ | | intros | eapply H0]. 
            3: erewrite eval_mon_shift_up.  all: eauto using good_shift, good_mon, good_comp, H2.
          * eapply ksat_ext; [ |intros; now eapply eval_mon_shift_up |eapply IHphi]; 
            eauto using good_shift, good_comp.
          * eapply IHphi; [| eapply ksat_ext]; [ | |intros| eapply H1]; 
            eauto using good_shift, good_comp, eval_shift_up.          
    Qed.

    Lemma ksat_shift {ff : falsity_flag}(u: nodes)(rho: nat -> domain)(phi: form):
    good u rho-> forall j: domain, world u j -> (
    rho ⊩( u, M) phi <-> (j.: rho)  ⊩( u, M) phi [↑]).
    Proof.
      split; intros.
      rewrite ksat_comp; eauto using good_shift.
      rewrite ksat_comp in H1. eapply ksat_ext. all: now eauto using good_shift.
    Qed.

  End Substs.

End KripkeSat. 

  Notation "rho  '⊩(' u ')'  phi" := (ksat _ u rho phi) (at level 20).
  Notation "rho '⊩(' u , M ')' phi" := (@ksat _ _ _ M _ u rho phi) (at level 20).