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
      Print term_ind.
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
        + split; intros; destruct H; exists x; split; try now eauto.
          eapply (IHphi _ (x .: rho) (x .: xi)); try now eauto using shift_ext.
          now eapply good_shift. 
          eapply (IHphi _ (x .: xi) (x .: rho)); try now eauto using shift_ext. 
          eapply good_shift; now eauto using good_ext. 
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
          ++ eapply ksat_ext; [now eapply good_comp_reach| intros | eapply IHphi2]; try now eauto using eval_mon, good_mon.
            apply (H0 v H1). 
            eapply IHphi1. apply (good_mon H H1).
            eapply ksat_ext. 
            apply good_comp. apply (good_mon H H1). 
            2: apply H2. 
            intros. unfold ">>". erewrite <- (eval_mon_t (xi x)); now eauto.
          ++ eapply IHphi2; eauto using good_mon. eapply ksat_ext; [ | | eapply H0]; intros;
            eauto using good_comp, good_mon.
            unfold ">>". erewrite <- (eval_mon_t (xi x)); eauto. 
            eapply ksat_ext. now eapply good_comp_reach. 
            2: eapply IHphi1. 3: apply H2. intros. unfold ">>". now apply eval_mon. now eapply good_mon.
      - destruct q.
        + split; intros.
          * eapply ksat_ext; try eapply IHphi; try eapply H0;
            [unfold good; intros; eapply good_shift| intros |  |  | ]; 
            eauto using good_comp_reach, good_shift, good_mon. now eapply eval_mon_shift_up. 
          * eapply IHphi. 
            apply good_shift; eauto using  good_mon.
            eapply ksat_ext; [ | | eapply H0]; eauto using H2; [ |intros; erewrite eval_mon_shift_up]; 
            now eauto using good_comp, good_shift, good_mon.
        + split; intros.
          * destruct H0 as (j, (H0, H1)). exists j. split; try apply H0.
            eapply ksat_ext; try eapply IHphi; try eapply H1; [ |intros; now eapply eval_mon_shift_up |];
            now eauto using good_shift, good_comp.
          * destruct H0 as (j, (H0, H1)). exists j. split; try apply IHphi; eauto using good_shift.
            eapply ksat_ext; try eapply H1; [ |intros]; 
            now eauto using eval_shift_up, good_shift, good_comp.
    Qed. 

    Lemma ksat_shift {ff : falsity_flag}(u: nodes)(rho: nat -> domain)(phi: form):
    good u rho-> forall j: domain, world u j -> (
    rho ⊩( u, M) phi <-> (j.: rho)  ⊩( u, M) phi [↑]).
    Proof.
      split; intros.
      rewrite ksat_comp; eauto using good_shift.
      rewrite ksat_comp in H1. eapply ksat_ext; eauto using good_shift.
      now eapply good_shift.
    Qed.

  End Substs.


End KripkeSat. 


  Notation "rho  '⊩(' u ')'  phi" := (ksat _ u rho phi) (at level 20).
  Notation "rho '⊩(' u , M ')' phi" := (@ksat _ _ _ M _ u rho phi) (at level 20).


Section Completeness.
  Context {Σf : funcs_signature} {Σp : preds_signature}.
  (* #[local] Existing Instance falsity_on.*)

  Context {frm : kframe}.
  (* Context {M : kmodel}. *) 

    
    Arguments ksat {_ _ _} _ {_} _, _ _ _ _ _ _.

  Definition ktheo (M: kmodel)(phi : form) :=
    forall rho u, good u rho -> ksat M u rho phi.
    (*
  Definition k_std 
  Definition k_exp

  I would need some characterization of bottom...
  *)

    Definition kvalid_ctx(*_e*) {ff : falsity_flag}(A : list form) (phi: form) :=
    forall (M: kmodel) (u: nodes) (rho: nat -> domain),
     (*exp M -> *)
     good u rho -> (forall psi, psi el A -> ksat M u rho psi) -> ksat M u rho phi.

(*
  Definition kvalid_theo (T : form -> Prop) phi :=
  forall (M: kmodel) (u: nodes) (rho: nat -> domain), 
  good u rho -> (forall psi, T psi -> ksat M u rho psi) -> ksat M u rho phi.

  Definition kvalid_ctx (A : list form) (phi: form) :=
    forall (M: kmodel) (u: nodes) (rho: nat -> domain),
     good u rho -> (forall psi, psi el A -> ksat M u rho psi) -> ksat M u rho phi.
*)
  Definition kvalid phi {ff : falsity_flag}:=
    forall (M: kmodel) (u: nodes) (rho: nat -> domain), 
    good u rho -> ksat M u rho phi.

  Definition ksatis {ff : falsity_flag} phi :=
    exists (M: kmodel) (u: nodes) (rho: nat -> domain), good u rho /\ ksat M u rho phi.
(*
  Lemma contr_el {T: Type}(A : list T)(a b: T):
    b el (a :: A) <-> b el (a :: a :: A).
  Proof.
    split; intros; induction H; try rewrite H; eauto. (*could use List.in_cons*)
  Qed.

  Lemma exchange_el {T: Type}(A B: list T)(a b c: T):
   a el A ++ b :: c :: B <-> a el A ++ c :: b :: B.
  Proof.
    split; intros; eapply in_or_app; eapply in_app_or in H; destruct H.
    + auto.
    + induction H. right. apply in_cons. rewrite H. auto.
      right. induction H. rewrite H. auto.
      apply in_cons. auto.
    + left; auto .
    + induction H. 
      rewrite H. right. apply in_cons. auto.
      induction H. 
      right. rewrite H. auto.
      right. apply in_cons. auto.
  Qed.

  Lemma contraction_kvalid_ctx (A : list form)(a b: form):
    kvalid_ctx (a :: a :: A) b <-> kvalid_ctx (a :: A) b.
  Proof.
    unfold kvalid_ctx. split; intros; eapply H; intros; auto. apply H1.
    now eapply contr_el.
  Qed.

  Lemma and_left (A : list form)(a b c : form) u rho:
    good u rho ->
    (kvalid_ctx ((bin Conj a b) :: A) c -> rho ⊩( u, M) c )<-> (kvalid_ctx (a::b::A) c-> rho ⊩( u, M) c).
  Proof.
    intros; split; intros.
    + eapply H0. unfold kvalid_ctx. intros. eapply H1. apply H2. intros. eapply H3. induction H4.
        

  I was "forced" to use fprv (sequent calculus) instead of sprv (ND)
  because, when trying to use sprv I get a conflict of connectives. 
  Of course it's easier in my opinion to use ND, nevertheless I did not know how to proceed *)

Implicit Type p : peirce.
Context {p : peirce}.

  Lemma kvalid_ctx_shift {ff : falsity_flag} (A : list form)(phi: form):
  kvalid_ctx A phi <-> kvalid_ctx (List.map (subst_form ↑) A) phi [↑].
  Proof.
    split; unfold kvalid_ctx; intros.
    * apply ksat_comp; eauto.
      eapply H. now eapply good_comp.
      intros. eapply ksat_comp; eauto.
      eapply (in_map (subst_form ↑)) in H2; eauto.
    * eapply ksat_ext. 3: eapply (ksat_comp ↑ phi). 3: eapply (good_shift H0).


    
      4: eapply H.

      4: eapply ksat_comp.
    
     3: eapply ksat_comp. 4: eapply H.
      apply H0. 
      4: intros. 4: eapply (ksat_comp ↑ psi). 4: eapply H.
      (*
      5: eapply H. 
      5: intros. 5: exact ((↑ >> eval rho) ⊩( u, M) psi).
*)
    
    Search List.map.



  Lemma soundness {ff : falsity_flag} (A : list form)(phi: form):
     A ⊢I phi -> kvalid_ctx A phi.
  Proof. 
    unfold kvalid_ctx. intros H M. 
    induction H; simpl; intros u rho gd Hp; intros; try  simpl in IHprv. (*eapply IHprv; eauto.*)
    * eapply IHprv; eauto using good_mon.
      simpl; intros. destruct H2; [rewrite <- H2 | eapply ksat_mon]; eauto.
    * eapply IHprv1; try eapply IHprv2; eauto using reach_refl. 
    * apply IHprv; eauto using good_mon, good_shift.
       intros psi [psi' [<- HH]] % in_map_iff. 
       rewrite ksat_comp; eauto using good_mon, good_shift.
       eapply ksat_mon; eauto using good_comp.
    * erewrite ksat_comp; eauto. 
      erewrite ksat_ext.
      eapply (IHprv u rho gd Hp u (reach_refl u) (eval rho t)).
      all: eauto using reach_refl, good_comp, good_eval.
      intros; unfold ">>"; induction x; simpl; reflexivity.
    * exists (@eval _ _  _ (I u) rho t); split.
      now eapply good_eval.
      specialize (IHprv u rho).  
      apply ksat_comp in IHprv; eauto.
      eapply ksat_ext. eapply good_shift; eauto using good_eval.
      2: eapply IHprv. 
      intros. induction x; cbn; reflexivity.
    *  (*ExE {ff} {p} A phi psi : 
    A ⊢ ∃ phi -> phi::(map (subst_form ↑) A) ⊢ psi[↑] ->      A ⊢ psi  *)
    (*
    
    
    specialize (IHprv1 u rho gd Hp); simpl in IHprv1; destruct IHprv1 as [j (wj, HH)].
      erewrite ksat_shift; eauto. 
      eapply IHprv2; eauto using good_shift.
      intros. simpl in H1. destruct H1 as [HH1 | HH2].
      rewrite <- HH1. apply HH.
      rewrite ksat_ext. apply Hp.

      eapply Hp.
      split; intros. rewrite ksat_comp. eapply ksat_ext. 3: apply H1.
      eauto

    assert( rho ⊩( u, M) psi [↑] <->( (↑ >> @eval _ _ _ (I u) rho) ⊩( u, M) psi)).
      now apply ksat_comp.
      apply H1 in IHprv2. eapply  
    
    simpl in IHprv1; specialize (IHprv1 u rho gd Hp); destruct IHprv1 as [j HHH].
    
    simpl in IHprv2. 
      erewrite in_map_iff in IHprv2.
      specialize (IHprv1 u rho gd Hp); simpl in IHprv1; destruct IHprv1 as [j HHH].
      eapply Hp.
      eapply ksat_comp in IHfprv2.

    subsimpl_in IHprv2.     *) admit.
    * simpl in IHprv. specialize (IHprv u rho gd Hp); eauto. 
    * apply Hp; eauto.
    * split; [eapply IHprv1 | eapply IHprv2]; eauto.
    * simpl in IHprv. eapply IHprv; eauto.
    * simpl in IHprv. eapply IHprv; eauto.
    * left; eapply IHprv; eauto.
    * right; eapply IHprv; eauto.
    * specialize (IHprv1 u rho gd Hp); simpl in IHprv1; destruct IHprv1 as [IH1 | IH2];
      [eapply  IHprv2 | eapply IHprv3]; eauto; intros; simpl in H2; destruct H2 as [HH1 | HH2]; try rewrite <- HH1; eauto.
  Admitted.

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

Arguments ksat_bot {_} {_} {_} {_} {_} _ _ _ _.

Section BottomDef.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {ff : falsity_flag}.

  Definition kexploding D (M : kmodel D) F_P mon_F := forall v rho phi, ksat_bot F_P mon_F v rho (⊥ → phi).
  Arguments kexploding _ _ _ _ : clear implicits.

  Definition kvalid_exploding_ctx A phi :=
    forall D (M : kmodel D) F_P mon_F u rho, kexploding D M F_P mon_F -> (forall psi, psi el A -> ksat_bot F_P mon_F u rho psi) -> ksat_bot F_P mon_F u rho phi.

  Definition kvalid_exploding phi :=
    forall D (M : kmodel D) F_P mon_F u rho, kexploding D M F_P mon_F -> ksat_bot F_P mon_F u rho phi.

  Definition ksatis_exploding phi :=
    exists D (M : kmodel D) F_P mon_F u rho, kexploding D M F_P mon_F /\ ksat_bot F_P mon_F u rho phi.

End BottomDef.

  Section Contexts.

    

    Program Instance K_ctx {ff:falsity_flag} : kmodel :=
      {|
        nodes := list form ;
        reachable := @incl form ;
        k_interp := model_bot ;
        k_P := fun A P v => fprv A (atom P v) ; (*took away a "NONE"*)
      |}.
    Next Obligation.
      (* abstract (eauto using seq_Weak). *)
      abstract (eauto using weaken).
    Qed.

    Definition F_P {ff} : list (@form _ _ _ ff) -> Prop := match ff with falsity_on => fun n => fprv n ⊥ | _ => fun _ => False end.
    Lemma mon_F {ff:falsity_flag} (u v : @nodes K_ctx) : reachable u v -> F_P u -> F_P v. (*BEFORE (u v : @nodes _  _ K_ctx)*)
    Proof.
      cbn. unfold F_P. destruct ff; try easy. intros H H1. eapply weaken; [ exact H1| exact H]. intros. eapply weaken. apply H0. apply H.
    Qed.

    Notation "rho '⊩⊥(' u , M ')' phi" :=  (@    _ _ _ M _ F_P mon_F u rho phi) (at level 20).

    Lemma K_ctx_correct_exp {ff:falsity_flag} (A : list form) rho phi :
      (rho ⊩⊥(A, K_ctx ) phi-> A ⊢S phi[rho]) /\
      ((forall B psi, A <<= B -> B ;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊩⊥(A, K_ctx) phi).
    Proof.
      revert A rho.
       enough ((forall A rho, rho ⊩⊥( A, K_ctx) phi -> A ⊢S phi[rho]) /\
                          (forall A rho, (forall B psi, A <<= B -> B;; phi[rho] ⊢s psi -> B ⊢S psi)
                                  -> rho ⊩⊥( A, K_ctx) phi)) by intuition.
      (*                         
      induction phi as [|t1 t2|ff [] phi IHphi psi IHpsi|ff [] phi IHphi]; cbn; split; intros A rho.
      - tauto.
      - eauto.
      - erewrite Vector.map_ext. 1: eauto. apply universal_interp_eval.
      - intros H. erewrite Vector.map_ext. 1: now apply H. apply universal_interp_eval.
      - intros Hsat. apply IR, IHpsi. apply Hsat, IHphi. 1: intuition. eauto.
      - intros H B HB Hphi % IHphi. apply IHpsi. intros C xi HC Hxi. apply H.
        1: now transitivity B. eauto using seq_Weak.
      - intros Hsat. apply AllR.
        pose (phi' := phi[up rho]).
        destruct (find_bounded_L (phi' :: A)).
        eapply seq_nameless_equiv_all' with (n := x) (phi := phi').
        + intros xi Hxi. apply b. now right.
        + eapply bounded_up. 1: apply b; now left. lia.
        + unfold phi'. asimpl. apply IHphi, Hsat.
      - intros H t. apply IHphi. intros B psi HB Hpsi. apply H. assumption.
        apply AllL with (t := t). now asimpl.
      *)
      induction phi as [|t1 t2|ff [] phi IHphi psi IHpsi|ff [] phi IHphi].
      - cbn. split.
        + intros A rho. 
          tauto.
        + intros A rho.
          intros. eapply H.  reflexivity. apply Ax. (*AAAA non so bene cosa faccia qui*)
      - cbn. split.
        + intros A rho H. erewrite Vector.map_ext. 1 : exact H. apply universal_interp_eval.
        + intros A rho H. erewrite Vector.map_ext. now apply H. apply universal_interp_eval.
      - cbn. split.
        + intros A rho H. apply IR. eapply IHpsi. eapply H. 1: auto. 
        eapply IHphi. intros. simple eapply @Contr. exact H1. apply H0. simpl. left. reflexivity.
        + intros A rho H B HB Hphi %IHphi. apply IHpsi. intros C xi HC Hxi. apply H. 
          now transitivity B. apply IL. eapply seq_Weak. exact Hphi. apply HC. apply Hxi.
      - cbn. split.
        + intros A rho H. apply AllR.  (*AAAA non so esattamente cosa succede qui*)
          pose (phi' := phi[up rho]).
          destruct (find_bounded_L (phi' :: A)).
          eapply seq_nameless_equiv_all' with (n := x) (phi := phi').
          -- unfold bounded_L. intros xi Hxi. apply b. now right.
          -- eapply bounded_up. apply b. now left. auto.
          -- unfold phi'. asimpl. eapply IHphi. apply H.
        + intros A rho H t. eapply IHphi. intros B psi HB Hpsi. 
          apply H. apply HB. eapply AllL with (t:=t). asimpl. apply Hpsi. 
    Qed.

    Corollary K_ctx_sprv_exp {ff:falsity_flag} A rho phi :
      rho ⊩⊥(A, K_ctx) phi -> A ⊢S phi[rho].
    Proof.
      now destruct (K_ctx_correct_exp A rho phi).
    Qed.

    Lemma K_ctx_subst_exp {ff:falsity_flag} A phi rho :
      rho ⊩⊥( A, K_ctx) phi <-> var ⊩⊥( A, K_ctx) phi[rho].  (*AAAA cos'è qui var? var is the identity substitution from numbers to terms*)
    Proof.
    
      unfold ksat_bot, falsity_to_pred.
      rewrite <- atom_subst_comp. 2:easy.
      assert (forall {ff:falsity_flag} rho, (atom (Σ_preds := Σ_preds_bot) (inl tt) (Vector.nil _)) = (atom (Σ_preds := Σ_preds_bot) (inl tt) (Vector.nil _))[rho]) as Heq by easy.
      erewrite Heq.
      rewrite <- subst_falsity_comm. cbn.
      rewrite (ksat_comp A var rho).
      apply ksat_ext. intros x. unfold funcomp. induction (rho x); cbn; try easy.
      erewrite <- Vector.map_ext_in. 2: apply IH.
      now rewrite Vector.map_id.

    Qed.

    Lemma K_ctx_constraint_exp {ff:falsity_flag} A rho psi:
      rho ⊩⊥(A, K_ctx) (⊥ → psi).
    Proof.
      destruct ff eqn : Hff; try now intros.
      intros v B HB. cbn in HB. apply K_ctx_correct_exp.
      intros B' psi' HB' Hprv. subst. eauto using seq_Weak.
    Qed.

    Corollary K_ctx_ksat_exp {ff:falsity_flag} A rho phi :
      (forall B psi, A <<= B -> B ;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊩⊥(A, K_ctx) phi.
    Proof.
      now destruct (K_ctx_correct_exp A rho phi).
    Qed.
 
    #[local] Existing Instance falsity_off. 

    Lemma K_ctx_correct (A : list form) rho phi :
      (rho ⊩(A, K_ctx ) phi-> A ⊢S phi[rho]) /\
      ((forall B psi, A <<= B -> B ;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊩(A, K_ctx) phi).
    Proof.
      revert phi. remember falsity_off as ff eqn:Heqff. intros phi.
      revert A rho; enough ((forall A rho, rho ⊩( A, K_ctx) phi -> A ⊢S phi[rho]) /\
                          (forall A rho, (forall B psi, A <<= B -> B;; phi[rho] ⊢s psi -> B ⊢S psi)
                                  -> rho ⊩( A, K_ctx) phi)) by intuition.
      induction phi as [|t1 t2|ff [] phi IHphi psi IHpsi|ff [] phi IHphi]; cbn; split; intros A rho.
      - tauto.
      - congruence.
      - erewrite Vector.map_ext. 1: eauto. apply universal_interp_eval.
      - intros H. erewrite Vector.map_ext. 1: now apply H. apply universal_interp_eval.
      - intros Hsat. apply IR, IHpsi. 1:easy. apply Hsat, IHphi. 1: intuition. 1:easy. eauto.
      - intros H B HB Hphi % IHphi. 2:easy. apply IHpsi. 1:easy. intros C xi HC Hxi. apply H.
        1: now transitivity B. eauto using seq_Weak.
      - intros Hsat. apply AllR.
        pose (phi' := phi[up rho]).
        destruct (find_bounded_L (phi' :: A)).
        eapply seq_nameless_equiv_all' with (n := x) (phi := phi').
        + intros xi Hxi. apply b. now right.
        + eapply bounded_up. 1: apply b; now left. lia.
        + unfold phi'. asimpl. apply IHphi, Hsat. easy.
      - intros H t. apply IHphi. 1:easy. intros B psi HB Hpsi. apply H. assumption.
        apply AllL with (t := t). now asimpl.
    Qed.

    Corollary K_ctx_sprv A rho phi :
      rho ⊩(A, K_ctx) phi -> A ⊢S phi[rho].
    Proof.
      now destruct (K_ctx_correct A rho phi).
    Qed.

    Lemma K_ctx_subst A phi rho :
      rho ⊩( A, K_ctx) phi <-> var ⊩( A, K_ctx) phi[rho].
    Proof.
      rewrite (ksat_comp A var rho).
      apply ksat_ext. intros x. unfold funcomp. induction (rho x); cbn; try easy.
      erewrite <- Vector.map_ext_in. 2: apply IH.
      now rewrite Vector.map_id.
    Qed.

    Corollary K_ctx_ksat A rho phi :
      (forall B psi, A <<= B -> B ;; phi[rho] ⊢s psi -> B ⊢S psi) -> rho ⊩(A, K_ctx) phi.
    Proof.
      now destruct (K_ctx_correct A rho phi).
    Qed.
  End Contexts.

  Section ExplodingCompleteness.

    Lemma K_ctx_exploding {ff:falsity_flag}:
      kexploding mon_F.
    Proof.
      unfold kexploding.
      apply K_ctx_constraint_exp.
    Qed.

    Lemma K_exp_completeness A phi :
      kvalid_exploding_ctx A phi -> A ⊢SE phi.
    Proof.
      intros Hsat. erewrite <-subst_id. 1: apply K_ctx_sprv_exp with (rho := var). 2: reflexivity.
      apply Hsat. 1: apply K_ctx_exploding. intros psi Hpsi. apply K_ctx_ksat_exp. intros B xi HB Hxi.
      rewrite subst_id in Hxi. 2:reflexivity. eauto.
    Qed.

    Ltac clean_ksoundness :=
      match goal with
      | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
      | [ H : (?A -> ?B), H2 : (?A -> ?B) -> _ |- _] => specialize (H2 H)
      end.
    Lemma K_exp_ksoundness {ff:falsity_flag} A phi :
      A ⊢I phi -> kvalid_exploding_ctx A phi.
    Proof.
      intros Hprv. cbn in Hprv. intros D M F_P mon_F u rho Hexpl. revert u rho.
      remember intu as s in Hprv. induction Hprv; subst; cbn; intros u rho HA.
      all: repeat (clean_ksoundness + discriminate). all: (eauto || cbn ; eauto).
      - intros v Hr Hpi. eapply IHHprv. intros ? []; subst; eauto using ksat_mon. eapply ksat_mon. 2: now apply HA. easy.
      - eapply IHHprv1. 3: eapply IHHprv2. all: eauto. apply M.
      - intros d. apply IHHprv. intros psi [psi' [<- Hp]] % in_map_iff. cbn.
        unfold ksat_bot. rewrite falsity_to_pred_subst.
        rewrite ksat_comp. apply HA, Hp.
      - unfold ksat_bot. rewrite falsity_to_pred_subst.
        rewrite ksat_comp. eapply ksat_ext. 2: eapply (IHHprv u rho HA (eval rho t)). 
        unfold funcomp. now intros [].
      - apply (Hexpl u rho phi u (ltac:(apply M))).
        specialize (IHHprv u rho HA). cbn in IHHprv. apply IHHprv.
    Qed.

    Lemma K_exp_seq_ksoundness {ff:falsity_flag} A phi :
      A ⊢SE phi -> kvalid_exploding_ctx A phi.
    Proof.
      intros H%seq_ND. now apply K_exp_ksoundness.
    Qed.

    Fact SE_cut A phi psi :
      A ⊢SE phi -> A;;phi ⊢sE psi -> A ⊢SE psi.
    Proof.
      intros H1 % seq_ND H2 % seq_ND; cbn in *.
      apply H2 in H1. apply K_exp_completeness.
      apply K_exp_ksoundness. firstorder.
    Qed.
    
  End ExplodingCompleteness.

  Section BottomlessCompleteness.
    #[local] Existing Instance falsity_off.

    Lemma K_bottomless_completeness A phi :
      kvalid_ctx A phi -> A ⊢S phi.
    Proof.
      intros Hsat. erewrite <- subst_id. apply K_ctx_sprv with (rho := var). 2: reflexivity.
      apply Hsat. intros psi Hpsi. apply K_ctx_ksat. intros B xi HB Hxi.
      rewrite subst_id in Hxi. 2:easy. eauto.
    Qed.
  End BottomlessCompleteness.

(* *** Standard Models *)

  Section StandardCompleteness.
    #[local] Existing Instance falsity_on.

    Definition cons A := ~ A ⊢SE ⊥.
    Definition cons_ctx := { A | cons A }.
    Definition ctx_incl (A B : cons_ctx) := incl (proj1_sig A) (proj1_sig B).

    #[local] Hint Unfold cons cons_ctx ctx_incl : core.

    Notation "A <<=C B" := (ctx_incl A B) (at level 20).
    Notation "A ⊢SC phi" := ((proj1_sig A) ⊢SE phi) (at level 20).
    Notation "A ;; psi ⊢sC phi" := ((proj1_sig A) ;; psi ⊢sE phi) (at level 70).

    Ltac dest_con_ctx :=
      match goal with
      | [ |- forall u : cons_ctx, _] => let Hu := fresh "H" u in intros [u Hu]
      | [ A : cons_ctx |- _] => let HA := fresh "H" A in destruct A as [A HA]
      end.

    Ltac cctx := repeat (progress dest_con_ctx; unfold ctx_incl); cbn.

    Hint Extern 1 => cctx : core.

    Program Instance K_std : kmodel term :=
      {|
        reachable := ctx_incl ;
        k_interp := model_bot ;
        k_P := fun A P v => ~ ~ A ⊢SC (@atom _ _ _ _ P v) 
      |}.
    Next Obligation.
      abstract (apply H0; intros K; apply H1; eapply seq_Weak; eauto).
    Qed.

    Lemma K_std_correct (A : cons_ctx) rho phi :
      (rho ⊩(A, K_std) phi -> ~ ~ A ⊢SC phi[rho]) /\
      ((forall B psi, A <<=C B -> B ;; phi[rho] ⊢sC psi -> ~ ~ B ⊢SC psi) -> rho ⊩(A, K_std) phi).
    Proof.
      revert A rho; enough ((forall A rho, rho ⊩( A, K_std) phi -> ~ ~ A ⊢SC phi[rho])
                          /\ (forall A rho, (forall B psi, A <<=C B -> B;; phi[rho] ⊢sC psi -> ~ ~ B ⊢SC psi)
                                    -> rho ⊩( A, K_std) phi)) by firstorder.
      induction phi as [| t1 t2 | [ ] phi [IHphi1 IHphi2] psi [IHpsi1 IHpsi2] | [ ] phi [IHphi1 IHphi2] ] using form_ind_falsity.
      all: cbn; split; intros A rho.
      - tauto.
      - intros H. exfalso. apply (H A ⊥); auto.
      - now rewrite (Vector.map_ext _ _ _ _ (universal_interp_eval rho)).
      - rewrite <- (Vector.map_ext _ _ _ _ (universal_interp_eval rho)). intros H H'.
        eapply H. 3: { intros H1. apply H', H1. } all: auto.
      - intros Hsat H.
        assert (HA : ~ ~ ((phi[rho] :: proj1_sig A) ⊢SE ⊥ \/ ~ (phi[rho] :: proj1_sig A) ⊢SE ⊥)) by tauto.
        apply HA. clear HA. intros [HA|HA].
        + apply H. apply IR. apply Absurd. assumption.
        + pose (A' := exist cons (phi[rho] :: proj1_sig A) HA). apply (IHpsi1 A' rho).
          * apply Hsat. 1: now apply incl_tl. apply IHphi2. intros B theta HB HT.
            intros H'. apply H'. eauto.
          * intros H'. apply H. apply IR, H'.
      - intros H B HB Hphi % IHphi1. apply IHpsi2. intros C xi HC Hxi.
        intros HX. apply Hphi. intros Hphi'. apply (H C xi); trivial.
        + cctx. now transitivity B.
        + apply IL; trivial. eapply seq_Weak; eauto.
      - pose (phi' := subst_form ($0 .: (rho >> subst_term (S >> var))) phi).
        intros Hsat. intros H. cctx. destruct (find_bounded_L (phi' :: A)) as [x b].
        apply (IHphi1 (exist cons A HA) ($x.:rho)).
        rewrite ksat_ext. 2: reflexivity. now apply Hsat.
        intros H'. apply H, AllR. cbn.
        eapply seq_nameless_equiv_all' with (n := x) (phi := phi').
        + intros xi Hxi. apply b. now right.
        + eapply bounded_up. 1: apply b; now left. lia.
        + unfold phi'. cbn in H'. now asimpl.
      - intros H t. apply IHphi2. intros B psi HB Hpsi. apply H. assumption.
        apply AllL with (t := t). now asimpl.
    Qed.

    Corollary K_std_sprv A rho phi :
      rho ⊩(A, K_std) phi -> ~ ~ A ⊢SC phi[rho].
    Proof.
      now destruct (K_std_correct A rho phi).
    Qed.

    Corollary K_std_sprv' A rho phi :
       ~ ~ A ⊢SC phi[rho] -> rho ⊩(A, K_std) phi.
    Proof.
      intros H. apply (K_std_correct A rho phi).
      intros B psi H1 H2 H3. apply H. intros H'.
      apply H3. eapply SE_cut; try eassumption.
      now apply (seq_Weak H').
    Qed.

    Corollary K_std_ksat A rho phi :
      (forall B psi, A <<=C B -> B ;; phi[rho] ⊢sC psi -> ~ ~ B ⊢SC psi) -> rho ⊩(A, K_std) phi.
    Proof.
      now destruct (K_std_correct A rho phi).
    Qed.

    Lemma K_std_completeness A phi :
      kvalid_ctx A phi -> ~ ~ A ⊢SE phi.
    Proof.
      intros Hsat H.
      assert (HA : ~ ~ (A ⊢SE ⊥ \/ ~ A ⊢SE ⊥)) by tauto.
      apply HA. clear HA. intros [HA|HA].
      - apply H. apply Absurd. assumption.
      - specialize (Hsat _ K_std (exist cons A HA) var).
        apply K_std_sprv in Hsat.
        + apply Hsat. intros Hsat'. apply H.
          erewrite <- subst_id; trivial. apply Hsat'.
        + intros psi Hpsi. apply K_std_ksat.
          intros B xi HB Hxi. asimpl in Hxi. eauto.
    Qed.

    Lemma K_std_seq_ksoundness A phi :
      A ⊢SE phi -> kvalid_ctx A phi.
    Proof.
      intros H % seq_ND. apply ksoundness, H.
    Qed.
  End StandardCompleteness.


  Section Stability.
    Existing Instance falsity_on.
    Context (T_kind : theory -> Prop).
    Definition K_completeness := forall T phi, T_kind T -> closed_T T -> closed phi -> 
                  kvalid_theo T phi -> T ⊩SE phi.
    Lemma kcompleteness_implies_stability T phi : K_completeness ->
      T_kind (tmap negative_translation T) ->
      closed_T T -> closed phi ->
      ~ ~ T ⊢TC phi -> T ⊢TC phi.
    Proof.
      intros Hcomp kindT clT clphi HTDN.
      apply DN_T. apply nt_correct_theory. cbn. apply seq_ND_T.
      apply Hcomp.
      - easy.
      - apply tmap_closed. 1: apply nt_bounded. easy.
      - unfold closed. solve_bounds. apply nt_bounded. apply clphi.
      - intros D M u rho HT.
        intros v Huv Hphiv. cbn. apply HTDN.
        intros (A & HTA & HTphi). eapply nt_Cprv_to_Iprv in HTphi.
        eapply DN_into in HTphi.
        apply ksoundness in HTphi.
        unshelve eapply (@HTphi D M u rho _ v Huv Hphiv).
        intros ? (psi & <- & HApsi) %in_map_iff. apply HT.
        exists psi. split; try easy. now apply HTA.
    Qed.
  End Stability.

  Section MP_Equivalence.
    Definition kcompleteness_enumerable := K_completeness enumerable.

    Lemma bot_deriv_stable_enum_k (T : @theory _ _ _ falsity_on) : kcompleteness_enumerable -> closed_T T -> enumerable T ->
      stable (@FragmentND.tprv _ _ _ class T ⊥).
    Proof.
      intros Hcomp Hclosed Henum HC.
      apply (kcompleteness_implies_stability Hcomp); try easy. 2: econstructor.
      now apply enum_tmap.
    Qed.

(*
    Lemma MP_implies_kcompleteness_enum : MP -> kcompleteness_enumerable.
    Proof.
      intros Hmp T phi HT Hphi Henum Hvalid.
      apply completeness_classical_stability; eauto. unfold stable.
      eapply mp_tprv_stability; try tauto. now eapply enumerable_list_enumerable.
    Qed.
*)
    Lemma kcompleteness_enum_implies_MP : kcompleteness_enumerable -> MP.
    Proof.
      intros HC f Hf.
      pose (fun x : form => exists n, x = ⊥ /\ f n = true) as T.
      assert (closed_T T) as Hclosed by (now intros k [n [-> Hn]]; econstructor).
      assert (enumerable T) as Henum.
      { exists (fun n => if f n then Some (⊥) else None). intros phi; split; intros H.
        + destruct H as (n & Heq & Hfn). exists n. rewrite Hfn. now rewrite Heq.
        + destruct H as (n & Hn). unfold T. exists n. destruct (f n); try congruence.
          split; try easy. congruence.
       }
      pose proof (@bot_deriv_stable_enum_k T HC Hclosed Henum).
      enough (T ⊢TC ⊥) as [[|lx lr] [HL HL']].
      - exfalso. eapply consistent_ND. apply HL'.
      - destruct (HL lx) as (n & Heq & Hfn). 1:now left. now exists n.
      - apply H. intros Hc. apply Hf. intros [n Hn]. apply Hc. exists [⊥]. split.
        + intros ? [<- | []]. unfold T. exists n. split; try easy.
        + apply Ctx; now left.
    Qed.

  End MP_Equivalence.

  Section LEM_Equivalence.
    Definition kcompleteness_arbitrary := K_completeness (fun x => True).
    Definition LEM := forall (P:Prop), P \/ ~ P.

    Lemma bot_valid_stable (T : @theory _ _ _ falsity_on) : closed_T T -> stable (valid_theory_C (classical (ff := falsity_on)) T ⊥).
    Proof.
      intros Hclosed HH D I rho Hclass H.
      apply HH. intros Hc. apply (Hc D I rho Hclass H).
    Qed.
    Lemma bot_deriv_stable_k (T : @theory _ _ _ falsity_on) : kcompleteness_arbitrary -> 
      closed_T T -> stable (@FragmentND.tprv _ _ _ class T ⊥).
    Proof.
      intros Hcomp Hclosed HC.
      apply (kcompleteness_implies_stability Hcomp); try easy. econstructor.
    Qed.
    Existing Instance falsity_on.
    Lemma kcompleteness_implies_LEM : kcompleteness_arbitrary -> LEM.
    Proof.
      intros HC P.
      pose (fun x : form => closed x /\ (P \/ ~P)) as T.
      assert (closed_T T) as Hclosed by (intros k; cbv; tauto).
      pose proof (@bot_deriv_stable_k T HC Hclosed).
      enough (T ⊢TC ⊥) as [[|lx lr] [HL HL']].
      - exfalso. eapply consistent_ND. apply HL'.
      - eapply HL. now left.
      - enough (~~ (P \/ ~P)).
        + apply H. intros Hc. apply H0. intros Hc2. apply Hc. exists [⊥]. split; try (apply Ctx; now left).
          intros ? [<- | []]. cbv. split; try apply Hc2. econstructor.
        + tauto.
    Qed.
(*
    Lemma LEM_implies_kcompleteness : LEM -> kcompleteness_arbitrary.
    Proof.
      intros Hlem T phi HT Hphi Hvalid Htheo.
      destruct (Hlem (T ⊩SE phi)); try easy. exfalso.
      apply K_std_completeness.
      intros H. destruct (Hlem (T ⊢TC phi)); tauto.
    Qed.
*)
  End LEM_Equivalence.

End KripkeCompleteness.
*)