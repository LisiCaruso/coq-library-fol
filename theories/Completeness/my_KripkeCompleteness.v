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


Section Soundness.
  Context {Σf : funcs_signature} {Σp : preds_signature}.
  (* #[local] Existing Instance falsity_on.*)

  Context {frm : kframe}.
  (* Context {M : kmodel}. *) 

    
  Arguments ksat {_ _ _} _ {_} _, _ _ _ _ _ _.

  Definition ktheo (M: kmodel)(phi : form) :=
    forall rho u, good u rho -> ksat M u rho phi.

  Definition kvalid_ctx(*_e*) {ff : falsity_flag}(A : list form) (phi: form) :=
    forall (M: kmodel) (u: nodes) (rho: nat -> domain),
     good u rho -> (forall psi, psi el A -> ksat M u rho psi) -> ksat M u rho phi.

  Definition kvalid phi {ff : falsity_flag}:=
    forall (M: kmodel) (u: nodes) (rho: nat -> domain), 
    good u rho -> ksat M u rho phi.

  Definition ksatis {ff : falsity_flag} phi :=
    exists (M: kmodel) (u: nodes) (rho: nat -> domain), good u rho /\ ksat M u rho phi.

  
  Arguments form {_ _ _} __.

  Lemma prv_ind_intu :
  forall P : (forall f : falsity_flag, list (form f) -> (form f) -> Prop),
    (forall (ff : falsity_flag) (A : list (form ff)) (phi psi : form ff),
        (phi :: A) ⊢I psi -> P ff (phi :: A) psi -> P ff A (phi → psi)) ->
    (forall (ff : falsity_flag)(A : list (form ff)) (phi psi : form ff),
        A ⊢I phi → psi -> P ff A (phi → psi) -> A ⊢I phi -> P ff A phi -> P ff A psi) ->
    (forall (ff : falsity_flag) (A : list (form ff)) (phi : form ff),
        (List.map (subst_form ↑) A) ⊢I phi -> P ff (List.map (subst_form ↑) A) phi -> P ff A (∀ phi)) ->
    (forall (ff : falsity_flag) (A : list (form ff)) (t : term) (phi : form ff),
        A ⊢I ∀ phi -> P ff A (∀ phi) -> P ff A phi[t..]) ->
    (forall (ff : falsity_flag) (A : list (form ff)) (t : term) (phi : form ff),
        A ⊢I phi[t..] -> P ff A phi[t..] -> P ff A (∃ phi)) ->
    (forall (ff : falsity_flag) (A : list (form ff)) (phi psi : form ff),
        A ⊢I ∃ phi ->
              P ff A (∃ phi) ->
              (phi :: [p[↑] | p ∈ A]) ⊢I psi[↑] -> P ff (phi :: [p[↑] | p ∈ A]) psi[↑] -> P ff A psi) ->
    (forall  (A : list (form falsity_on)) (phi : form falsity_on), A ⊢I ⊥ -> P falsity_on A ⊥ -> P falsity_on A phi) ->
    (forall (ff : falsity_flag) (A : list (form ff)) (phi : form ff), phi el A -> P ff A phi) ->
    (forall (ff : falsity_flag) (A : list (form ff)) (phi psi : form ff),
        A ⊢I phi -> P ff A phi -> A ⊢I psi -> P ff A psi -> P ff A (phi ∧ psi)) ->
    (forall (ff : falsity_flag) (A : list (form ff)) (phi psi : form ff),
        A ⊢I phi ∧ psi -> P ff A (phi ∧ psi) -> P ff A phi) ->
    (forall (ff : falsity_flag) (A : list (form ff)) (phi psi : form ff),
        A ⊢I phi ∧ psi -> P ff A (phi ∧ psi) -> P ff A psi) ->
    (forall (ff : falsity_flag) (A : list (form ff)) (phi psi : form ff),
        A ⊢I phi -> P ff A phi -> P ff A (phi ∨ psi)) ->
    (forall (ff : falsity_flag) (A : list (form ff)) (phi psi : form ff),
        A ⊢I psi -> P ff A psi -> P ff A (phi ∨ psi)) ->
    (forall (ff : falsity_flag) (A : list (form ff)) (phi psi theta : form ff),
        A ⊢I phi ∨ psi ->
        P ff A (phi ∨ psi) ->
        (phi :: A) ⊢I theta ->
        P ff (phi :: A) theta -> (psi :: A) ⊢I theta -> P ff (psi :: A) theta -> P ff A theta) ->
    forall (ff: falsity_flag) (l : list (form ff)) (f14 : form ff), l ⊢I f14 -> P ff l f14.
Proof.
  intros. 
  specialize (@prv_ind _ _ (fun ff => match ff with 
                                      | falsity_on  =>  (fun p => match p with 
                                                        | intu => P _  
                                                        | _ => fun  _ _ => True end)
                                      | falsity_off  => (fun p => match p with 
                                                        | intu => P falsity_off
                                                        | _ => fun  _ _ => True end) end)).
  intros H'; dependent destruction ff; 
  [apply H' with (ff := falsity_off) (p := intu) | apply H' with (ff := falsity_on) (p := intu)];
  clear H'; intros; try destruct ff; try destruct p;
  trivial; intuition eauto 2.
Qed.

Arguments prv {_ _ _} _.
(*
Lemma soundness {ff : falsity_flag} (A : list (form ff))(phi: (form ff)):
    prv intu A phi -> kvalid_ctx A phi.
  Proof.
    unfold kvalid_ctx.
    intros H M. 
    induction H using prv_ind_intu.

    simpl;  intros u rho gd Hp; intros; 
    try simpl in IHprv_intu_on.
    * eapply IHprv_intu_on; eauto using good_mon.
      simpl; intros. destruct H3; [rewrite <- H3 | eapply ksat_mon]; eauto.
    * simpl in IHprv_intu_on1; eapply IHprv_intu_on1. 4: eapply  IHprv_intu_on2. 
      all: eauto using reach_refl.
    * eapply IHprv_intu_on; eauto using good_mon, good_shift.
      intros psi [psi' [<- HH]] % in_map_iff. 
      rewrite ksat_comp; eauto using good_mon, good_shift.
      eapply ksat_mon; eauto using good_comp.
    * erewrite ksat_comp; eauto. 
      erewrite ksat_ext. 
      eapply (IHprv_intu_on u rho gd Hp u (reach_refl u) (eval rho t)).
      all: eauto using reach_refl, good_comp, good_eval.
      intros; unfold ">>"; induction x; simpl; reflexivity. 
    * exists (@eval _ _  _ (I u) rho t); split.
      now eapply good_eval.
      specialize (IHprv_intu_on  u rho);  
      apply ksat_comp in IHprv_intu_on; eauto.
      eapply ksat_ext. eapply good_shift; eauto using good_eval.
      2: eapply IHprv_intu_on. 
      intros. induction x; cbn; reflexivity.
    * specialize (IHprv_intu_on1 u rho gd Hp); simpl in IHprv_intu_on1.
      destruct IHprv_intu_on1 as [j (wj, IH)].
      eapply ksat_shift; eauto.
      eapply IHprv_intu_on2; eauto using good_shift.
      intros. simpl in H0; destruct H0.
      rewrite <- H0; eauto.
      eapply in_map_iff in H0; destruct H0 as [psh (eq, xelA)].
      rewrite <- eq; erewrite <- ksat_shift; eauto. 
    * simpl in IHprv_intu_on. specialize (IHprv_intu_on u rho gd Hp); eauto. 
    * apply Hp; eauto.
    * split; [eapply IHprv_intu_on1 | eapply IHprv_intu_on2]; eauto.
    * simpl in IHprv_intu_on. eapply IHprv_intu_on; eauto.
    * simpl in IHprv_intu_on. eapply IHprv_intu_on; eauto.
    * left; eapply IHprv_intu_on; eauto.
    * right; eapply IHprv_intu_on; eauto.
    * specialize (IHprv_intu_on1 u rho gd Hp); simpl in IHprv_intu_on1; destruct IHprv_intu_on1 as [IH1 | IH2];
      [eapply  IHprv_intu_on2 | eapply IHprv_intu_on3]; eauto; intros; simpl in H0; destruct H0 as [HH1 | HH2]; try rewrite <- HH1; eauto.
  Qed.  
    

  Lemma soundness_off {ff : falsity_flag} (A : list (form falsity_off))(phi: (form falsity_off)):
    ff = falsity_off -> prv_intu_off A phi -> kvalid_ctx A phi.
  Proof.
    intros;
    unfold kvalid_ctx. intros M.
    induction H0 using prv_ind_intu_falsity_off; simpl; intros u rho gd Hp; intros; 
    try simpl in IHprv_intu_on.
    * eapply IHprv_intu_off; eauto using good_mon.
      simpl; intros. destruct H3; [rewrite <- H3 | eapply ksat_mon]; eauto.
    * simpl in IHprv_intu_off1; eapply IHprv_intu_off1. 4: eapply  IHprv_intu_off2. 
      all: eauto using reach_refl.
    * eapply IHprv_intu_off; eauto using good_mon, good_shift.
      intros psi [psi' [<- HH]] % in_map_iff. 
      rewrite ksat_comp; eauto using good_mon, good_shift.
      eapply ksat_mon; eauto using good_comp.
    * erewrite ksat_comp; eauto. 
      erewrite ksat_ext. 
      eapply (IHprv_intu_off u rho gd Hp u (reach_refl u) (eval rho t)).
      all: eauto using reach_refl, good_comp, good_eval.
      intros; unfold ">>"; induction x; simpl; reflexivity. 
    * exists (@eval _ _  _ (I u) rho t); split.
      now eapply good_eval.
      specialize (IHprv_intu_off  u rho);  
      apply ksat_comp in IHprv_intu_off; eauto.
      eapply ksat_ext. eapply good_shift; eauto using good_eval.
      2: eapply IHprv_intu_off. 
      intros. induction x; cbn; reflexivity.
    * specialize (IHprv_intu_off1 u rho gd Hp); simpl in IHprv_intu_off1.
      destruct IHprv_intu_off1 as [j (wj, IH)].
      eapply ksat_shift; eauto.
      eapply IHprv_intu_off2; eauto using good_shift.
      intros. simpl in H0; destruct H0.
      rewrite <- H0; eauto.
      eapply in_map_iff in H0; destruct H0 as [psh (eq, xelA)].
      rewrite <- eq; erewrite <- ksat_shift; eauto. 
    * apply Hp; eauto.
    * split; [eapply IHprv_intu_off1 | eapply IHprv_intu_off2]; eauto.
    * simpl in IHprv_intu_off. eapply IHprv_intu_off; eauto.
    * simpl in IHprv_intu_off. eapply IHprv_intu_off; eauto.
    * left; eapply IHprv_intu_off; eauto.
    * right; eapply IHprv_intu_off; eauto.
    * specialize (IHprv_intu_off1 u rho gd Hp); simpl in IHprv_intu_off1; destruct IHprv_intu_off1 as [IH1 | IH2];
      [eapply  IHprv_intu_off2 | eapply IHprv_intu_off3]; eauto; intros; simpl in H0; destruct H0 as [HH1 | HH2]; try rewrite <- HH1; eauto.
  Qed.
  
  Lemma soundness {ff : falsity_flag} :
    forall (A : list (form ff))(phi: (form ff)), prv_intu A phi -> kvalid_ctx A phi.
  Proof.
    intros; unfold prv_intu in H. remember ff as current_ff.
    induction current_ff.
    eapply soundness_off; eauto. 
    eapply soundness_on; eauto.
  Qed.
  *)
End Soundness.  

Section ConstantDomain.
  Context {Σf : funcs_signature} {Σp : preds_signature}.
  Context {frm : kframe}.
  (* Context {M : kmodel}. *) 
  Definition constant_domain (fr : kframe)(M : kmodel) :  Prop :=
      (forall (u v: nodes) (j: domain), world u j <-> world v j).

  
  Definition constant_domain' (fr : kframe)(M : kmodel) :  Prop :=
      forall (u : nodes) (j: domain), world u j.
  
  Definition non_empty (fr : kframe)(M : kmodel) :  Prop :=
      exists (u : nodes) (j: domain), world u j.

  Definition constant_domain_meta :=
  forall (X: Type)(A: X -> Prop)(B: Prop),
    (forall x: X, (A x \/ B)) -> ((forall x: X, A x) \/ B).

  Lemma cdm_distr_impl_or :
  constant_domain_meta -> (forall (a b c: Prop), (a -> (b \/ c)) -> ((a -> b) \/ c)).
  Proof.
    intros. 
    eapply H. eauto.
  Qed.
(*
  Lemma CD_exist (fr : kframe)(M: kmodel)(u : nodes) (rho: nat -> domain) (phi: form): 
    constant_domain M -> (ksat u rho (quant All phi) <-> forall (j: domain), (exists (v: nodes), world v j) -> (j .: rho) ⊩( u, M) phi).
  Proof.
    split; intros.
    + destruct H1. eapply H0. eapply reach_refl. eapply H; eauto. 
    + cbn. intros. specialize (H0 j). eapply ksat_mon; eauto. unfold good. intros. eapply H. 
  Qed.

  Lemma CD_forall (fr : kframe) (M: kmodel)(u: nodes) (rho: nat -> domain) (phi: form): 
    constant_domain M -> (ksat u rho (quant Ex phi) <-> exists (j: domain), (j .: rho) ⊩( u, M) phi).
  Proof.
    split; intros.
    + simpl in H0; repeat destruct H0. exists x.
      eapply H1. 
    + cbn. destruct H0. exists x. split.
      eapply H. eapply H0.
  Qed.
  *)

(* rho ⊩( u, M) ((∀ phi ∨ psi [↑]) → (∀ phi) ∨ psi [↑])*)
  Lemma CD_imp_CD_axiom_ (M: kmodel)(rho: nat -> my_KripkeCompleteness.domain)(phi psi: form):
        non_empty M-> constant_domain M -> constant_domain_meta -> 
        forall (u : nodes), good u rho ->
        ksat u rho (bin Impl (quant All (bin Disj phi (psi[↑]))) (bin Disj (quant All  phi) (psi))).
    Proof.
    simpl.
    intros.
    unfold constant_domain_meta in H1.
    eapply H1; intros.
    eapply cdm_distr_impl_or; eauto; intros.
    eapply H1; intros.
    eapply cdm_distr_impl_or; eauto; intros.
    pose proof (H4 x H5 x0 H6).
    assert (world v x0).
    eapply H0; eauto.
    assert ((world v x0 -> (x0 .: rho) ⊩( v, M) phi) \/ (x0 .: rho) ⊩( v, M) psi [↑]).
    eapply H1; eapply H4; eapply reach_refl.
    destruct H9.
    left. eapply ksat_iff; eauto using good_shift, good_mon.
    left; eauto.
    right. erewrite <- ksat_shift in H7; eauto using good_mon.
    
    pose proof (H4 H8).
    eapply (cdm_distr_impl_or H1) in H4.
        
    Admitted.

     Definition CDA_meta (fr : kframe)(M : kmodel) :  Prop :=
    forall j : domain, (j .: rho) ⊩( v, M) phi \/ (j .: rho) ⊩( v, M) psi [↑]

End ConstantDomain.

Section Example_nonConstantDomain.

    Instance Σ_funcs : funcs_signature :=
      {|
        syms := Empty_set;
        ar_syms := fun _ => 0;
      |}.

    Inductive Preds : Type:=
    | P : Preds
    | Q : Preds.

    Instance Σ_preds : preds_signature :=
      {|
        preds := Preds;
        ar_preds := fun x => 1;
      |}.
    
    Instance ff : falsity_flag := falsity_on.

    Inductive my_domain : Type :=
      | a : my_domain
      | b : my_domain.

    Inductive my_nodes : Type :=
      | u : my_nodes
      | v : my_nodes.

    Definition my_reach x y: Prop :=
      match x with 
      | u => True
      | v => match y with
            | v => True
            | _ => False
            end
      end.

    Definition my_world node t: Prop :=
      match node with 
      | u => match t with 
            | a => True
            | b => False
            end
      | v => True
    end.

    Program Instance my_frm : kframe :=
      {|
        domain := my_domain;
        nodes := my_nodes;
        reachable := my_reach;
        world := my_world;
      |}.
    Next Obligation.
      induction u0; simpl; tauto.
    Qed.
    Next Obligation.
      induction u0; induction v0; induction w; eauto.
    Qed.
    Next Obligation.
      induction u0; induction v0; induction x; eauto.
    Qed.

    Instance my_I_u : @interp Σ_funcs Σ_preds my_domain :=
      {| 
        i_func := fun _ _ => a; 
        i_atom := fun pr x => match x with
                              | cons _ a _ (nil _) => match pr with 
                                                      | P => False
                                                      | Q => True
                                                      end
                              | cons _ b _ (nil _) =>  False
                              | _ => False
                              end;
      |}.

      Instance my_I_v : @interp Σ_funcs Σ_preds my_domain :=
      {| 
        i_func := fun _ _ => a; 
        i_atom := fun pr x => match x with
                              | cons _ a _ (nil _) => match pr with 
                                                      | P => False
                                                      | Q => True
                                                      end
                              | cons _ b _ (nil _) =>  match pr with 
                                                      | P => True
                                                      | Q => False
                                                      end
                              | _ => False
                              end;
      |}.

    Lemma in_u:
    forall x : my_domain, my_world u x -> x = a.
    Proof.
      intros. 
      unfold my_world in H.
      induction x.
      reflexivity.
      eauto.
    Qed.

    Lemma in_v:
    forall x : my_domain, my_world v x -> x = a \/ x = b.
    Proof.
      intros. 
      unfold my_world in H.
      induction x.
      left; reflexivity.
      eauto.
    Qed.

    Lemma In_inv {A: Type}{n: nat} {x: A} {v : t A n} :
        In x v ->
        (match n return t A n -> Prop with
        | 0 => fun _ => False
        | S n => fun v' => (x = Vector.hd v') \/ (In x (Vector.tl v'))
        end) v.
    Proof. 
    intros []; cbn; tauto.
    Qed.

    Lemma tail_vec_1 {A: Type} :
    forall vv: (t A 1), tl vv = nil A.
    Proof.
      intros. 
      dependent destruction vv. cbn. 
      dependent destruction vv. reflexivity.
    Qed.

    Lemma vec_in_u':
    forall vv: (t my_domain 1), forall x : domain, In x vv -> my_world u x ->  
    hd vv = a.
    Proof.
      intros. 
      erewrite  <- in_u.
      2: apply H0. eapply In_inv in H. simpl in H. 
      destruct H. rewrite H; eauto; tauto.
      apply In_inv in H; simpl in H; auto.
    Qed.

    Lemma vec_in_u:
    forall vv: (t my_domain 1), forall x : domain, In x vv -> my_world u x ->  
    vv = cons my_domain a 0 (nil my_domain).
    Proof.
      intros.
      eapply vec_in_u' in H; eauto.
      pose proof eta vv.
      rewrite H1. cbn. f_equal. eapply H.
      eapply tail_vec_1.
    Qed.

    Lemma vec_in_v':
    forall vv: (t my_domain 1), forall x : domain, In x vv -> my_world v x ->  
    hd vv = a \/ hd vv = b.
    Proof.
      intros. 
      pose proof (in_v H0). 
      eapply In_inv in H; simpl in H; destruct H;
      destruct H1; rewrite <- H1; eauto. 
      all: rewrite tail_vec_1 in H; eapply In_inv in H; simpl in H; eauto.
    Qed.

    Lemma vec_in_v:
    forall vv: (t my_domain 1), forall x : domain, In x vv -> my_world v x ->  
    vv = cons my_domain a 0 (nil my_domain) \/ vv = cons my_domain b 0 (nil my_domain).
    Proof.
      intros.
      eapply vec_in_v' in H; eauto.
      pose proof eta vv.
      rewrite H1. destruct H. 
      left; f_equal. eapply H. eapply tail_vec_1.
      right; f_equal. eapply H. eapply tail_vec_1.
    Qed.

    Program Instance my_kmodel: @kmodel _ _ my_frm :=
    {|
        I := fun (w: nodes) => match w with 
                              | u => my_I_u
                              | v => my_I_v
                              end
      |}.
    Next Obligation.
      induction u0; induction v0; simpl; reflexivity.
    Qed.
    Next Obligation.
      induction u0; simpl; auto.
    Qed.
    Next Obligation.
      remember P0 as PP.
      induction PP; induction u0; induction v0; cbn; eauto; unfold in_dom in a0.
      all : dependent destruction vv; destruct h.
      dependent destruction vv.
      simpl in H; eauto.
      all : dependent destruction vv. eauto.
      all: simpl in H; eauto.
    Next Obligation.
      induction u0; induction v0; induction P0; eauto.
      simpl in *; destruct vv in H; eauto;
      destruct h in H; eauto.
      all: dependent destruction vv; destruct h.
      dependent destruction vv. destruct t in H; eauto.
      all: dependent destruction vv; eauto. destruct t in H; eauto. 
    Qed.
    Next Obligation.
      induction u0; simpl in *; eauto. destruct x; eauto.
      dependent destruction vv; induction h; destruct vv; destruct P0; eauto.
      apply In_inv in H0; simpl in H0; destruct H0.
      discriminate H0; eauto.
      apply In_inv in H0; simpl in H0; eauto.
    Qed.

      End Example_nonConstantDomain.
  Definition A (alpha: t term 1): form :=  atom Q alpha.
  Definition B (alpha: t term 1): form := quant Ex (atom P alpha).

  Definition constant_domain_axiom (alpha : t term 1):  form :=
    bin Impl (quant All (bin Disj (A alpha) (B alpha))) (bin Disj (quant All (A alpha)) (B alpha)).
    
  Definition my_rho : nat -> my_domain :=
    fun _ => a.

  Lemma good_my_rho: 
    good u my_rho.
  Proof.
    unfold good. intros. unfold my_rho. now simpl.
  Qed.

  Definition aa := cons term (var 0) 0 (nil term).

  Lemma prop1 (rho: nat -> my_domain)(w : my_nodes):
    good w rho ->
    @ksat _ _ _ my_kmodel _ w rho (quant All (bin Disj (A aa) (B aa))).
  Proof.
    simpl. intros.
    induction v0.
    + left. simpl.
      eapply in_u in H1. rewrite H1; eauto.
    + right. exists b. split; eauto.
  Qed.

  Lemma prop2 (rho: nat -> my_domain):
  good u rho ->
    @ksat _ _ _ my_kmodel _ u rho (bin Disj (quant All (A aa)) (B aa)) -> False.
  Proof.
    intros. simpl in H0. destruct H0.
    + specialize (H0 v); assert True; eauto. specialize (H0 H1 b).
      simpl in H0. now eapply H0.
    + unfold good in H. specialize (H 0). destruct H0 as (j, (H1, H2)). 
      destruct j in H1, H2; eauto.
  Qed.

  Lemma not_CDA : 
    @ksat _ _ _ my_kmodel _ u my_rho (constant_domain_axiom aa) -> False.
  Proof.
    intros. eapply prop2. 2: eapply H. 3: eapply prop1.
    all: eauto using reach_refl, good_my_rho. 
  Qed.

  Definition anti_constant_domain_axiom (alpha : t term 1):  form :=
    bin Impl (bin Disj (quant All (A alpha)) (B alpha)) (quant All (bin Disj (A alpha) (B alpha))). 

  Lemma CDA (fr : kframe)(M: kmodel)(u: nodes)(rho: nat -> domain): 
    ksat u rho (anti_constant_domain_axiom aa).
  Proof.
    simpl. intros.
    destruct H0.
    + left. now eapply H0.
    + right. repeat destruct H0. exists x. split. eapply monotone; eauto using H0, H1.
      eapply mon_P; eauto using H1. unfold in_dom. intros.
      eapply In_inv in H4; simpl in H4. destruct H4. rewrite H4; eauto.
      eapply In_inv in H4; simpl in H4; eauto.
  Qed.


  End Example_nonConstantDomain.




  

    Locate ListAutomationNotations.


Section Bottom.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Locate subst_term.

 (* Lemma universal_interp_eval u rho t :
    eval rho t= t`[rho].
  Proof.
    now induction t; cbn. 
  Qed.
*)
  Instance model_bot : interp term :=
    {| i_func := func; i_atom := fun P v => False|}.

 Section Contexts.

  Print Vector.map.
(*
  Fixpoint term_in_form (nu : form)(t : term): Prop :=
    match nu with 
      | atom P vv => term_in_term ()
      | falsity => False
      | bin _ phi psi => term_in_form phi \/ term_in_form psi
      | quant _ phi =>  term_in_form phi
      end.

  Fixpoint world_ctx (A : list form)(t : term): Prop :=
    match A with 
      | [] => False
      | [phi] => 
*)
    Program Instance K_frm_ctx {ff:falsity_flag} : kframe :=
      {|
        domain := term;
        nodes := list form ;
        reachable := @incl form ;
        world := fun u t => True; (* this is wrong, I don't know what to put here*)
      |}.
 Qed.

  Program Instance K_ctx {ff: falsity_flag}: @kmodel _ _ K_frm_ctx:=
    {|
        I := fun (u: nodes) => model_bot; 
      |}.
    (*
    Next Obligation.
      admit.
    Next Obligation.
      abstr
      abstract (eauto using seq_Weak).
    Qed.
    *)
        (*k_interp := model_bot ;
        k_P := fun A P v => sprv A None (atom P v) 
        

Print FragmentSyntax.frag_operators.
Print FullSyntax.full_operators.

    Definition F_P {ff} : list (@form _ _ _ ff) -> Prop := 
        match ff with 
        | falsity_on => fun (n: list form) => sprv n Some ⊥ (*taken away sprv and Some*)
        | _ => fun _ => False end.

    Lemma mon_F {ff:falsity_flag} (u v : nodes) : reachable u v -> F_P u -> F_P v.
    Proof.
      cbn. unfold F_P. destruct ff; try easy. intros H H1. eapply seq_Weak; [ exact H1| exact H].
    Qed.

    Notation "rho '⊩⊥(' u , M ')' phi" :=  (@ksat_bot _ _ _ M _ F_P mon_F u rho phi) (at level 20).



  Program Definition kmodel_bot 
    (F_P : @nodes _ _ _ M -> Prop)
    (mon_F : forall u v, reachable u v -> F_P u -> F_P v)
     : @kmodel Σ_funcs (@Σ_preds_bot Σ_preds) domain := {|
    nodes := @nodes _ _ _ M ;
    reachable := @reachable _ _ _ M ;
    k_interp := interp_bot False (@k_interp _ _ _ M) ;
    k_P := fun n P => match P with inl _ => fun _ => F_P n | inr P' => @k_P _ _ _ M n P' end
  |}.
  Next Obligation. apply reach_refl. Qed.
  Next Obligation. now apply reach_tran with v. Qed.
  Next Obligation. destruct P as [|P'].
    + now apply mon_F with u.
    + now apply mon_P with u.
  Qed.

  Definition ksat_bot 
    {ff : falsity_flag} (F_P : @nodes _ _ _ M -> Prop)
    (mon_F : forall u v, reachable u v -> F_P u -> F_P v)
    u (rho : env domain) (phi : form) : Prop 
    := @ksat _ Σ_preds_bot domain (kmodel_bot mon_F) falsity_off u rho (falsity_to_pred phi).
  Arguments ksat_bot {_} _ _ _ _.

  Lemma sat_bot_False {ff:falsity_flag} u rho phi
    (e : forall u v, reachable u v -> False -> False)
    : @ksat_bot ff (fun _ => False) e u rho phi <-> @ksat _ _ domain M ff u rho phi.
  Proof.
    induction phi in rho,u|-*.
    - easy.
    - easy.
    - destruct b0. unfold sat_bot, falsity_to_pred in *. cbn.
      split; intros H v Hreach H1 %IHphi1; apply IHphi2; now apply H, H1.
    - destruct q. unfold sat_bot, falsity_to_pred in *. cbn.
      split; intros H d; apply IHphi, H.
  Qed.

End Bottom.

*)