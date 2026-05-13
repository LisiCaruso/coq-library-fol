(** ** Kripke Completeness **)

From FOL Require Import FullSyntax Theories Deduction.FullSequentFacts Deduction.FragmentSequentFacts.


From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec FOL.Deduction.FullND.
Require Import Arith.
Require Import Nat List Vector Lia.
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

  Definition kvalid_ctx {ff : falsity_flag}(A : list form) (phi: form) :=
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
  remember intu as temp.
  induction H13; eauto.
  discriminate.
Qed.

Arguments prv {_ _ _} _.

Lemma soundness {ff : falsity_flag} (A : list (form ff))(phi: (form ff)):
    prv intu A phi -> kvalid_ctx A phi.
  Proof.
    unfold kvalid_ctx.
    intros H M.
    apply (prv_ind_intu (P := fun ff A phi => forall (u : nodes) (rho : nat -> domain),
          good u rho -> (forall psi : form ff, psi el A -> rho ⊩( u, M) psi) ->
          rho ⊩( u, M) phi)); eauto; simpl;  intros ff1 A1 ; intros.
    (*try simpl in IHprv_intu_on.*)
    * eapply H1; eauto using good_mon.
      simpl; intros. destruct H6; [rewrite <- H6 | eapply ksat_mon]; eauto.
    * eapply H1. 4: eapply  H3. 
      all: eauto using reach_refl.
    * eapply H1; eauto using good_mon, good_shift.
      intros psi0 [psi' [<- HH]] % in_map_iff. 
      rewrite ksat_comp; eauto using good_mon, good_shift.
      eapply ksat_mon; eauto using good_comp.
    * erewrite ksat_comp; eauto. 
      erewrite ksat_ext. 
      eapply (H1 u rho H2 H3 u (reach_refl u) (eval rho t)).
      all: eauto using reach_refl, good_comp, good_eval.
      intros; unfold ">>"; induction x; simpl; reflexivity. 
    * exists (@eval _ _  _ (I u) rho t); split.
      now eapply good_eval.
      specialize (H1  u rho);  
      apply ksat_comp in H1; eauto.
      eapply ksat_ext. eapply good_shift; eauto using good_eval.
      2: eapply H1. 
      intros. induction x; cbn; reflexivity.
    * specialize (H1 u rho H4 H5). 
      destruct H1 as [j (wj, IH)].
      eapply ksat_shift; eauto.
      eapply H3; eauto using good_shift.
      intros. destruct H1.
      rewrite <- H1; eauto.
      eapply in_map_iff in H1; destruct H1 as [psh (eq, elA1)].
      rewrite <- eq; erewrite <- ksat_shift; eauto. 
    * specialize (H1 u rho H2 H3); eauto. 
    * split; [eapply H1 | eapply H3]; eauto.
    * eapply H1; eauto.
    * eapply H1; eauto.
    * left; eapply H1; eauto.
    * right; eapply H1; eauto.
    * specialize (H1 u rho H6 H7); destruct H1 as [IH1 | IH2];
      [eapply  H3 | eapply H5]; eauto; intros; simpl in H1; destruct H1 as [HH1 | HH2]; try rewrite <- HH1; eauto.
  Qed.  
    
End Soundness.  

Section PropKsat.
  Context {Σf : funcs_signature} {Σp : preds_signature}.
  Context {frm : kframe}.
  Context {M : kmodel}. 
  #[local] Existing Instance falsity_on.

  Arguments ksat {_ _ _ _ _} _ _ _.

  Lemma ksat_DN_in (u: nodes)(rho: nat -> domain)(phi: form) :
    good u rho ->
    ksat u rho phi -> ksat u rho (bin Impl (bin Impl (phi) ⊥) ⊥).
  Proof.
    simpl; intros.
    eapply ksat_mon in H; eauto. 
    specialize (H2 v (reach_refl v)); eauto.
  Qed.

  Lemma ksat_neg_in_out (u: nodes)(rho: nat -> domain)(phi: form) :
    good u rho -> 
    ksat u rho (bin Impl (phi) ⊥) -> ((ksat u rho phi) -> False).
  Proof.
    intros.
    eapply H0; eauto using reach_refl.
  Qed.

  (*Lemma ksat_neg_out_in (u: nodes)(rho: nat -> domain) :
    good u rho -> 
    (forall phi : form, ((ksat u rho phi) -> False) -> ksat u rho (bin Impl (phi) ⊥)) 
    -> completeness -> EM???*)

    (*-> 
    (forall phi : form, (ksat u rho phi) \/ ((ksat u rho phi) -> False)). *)
  Lemma kvalid_ctx_bot_DNE (T : list form):
    (((kvalid_ctx T ⊥) -> False )-> False) <-> (kvalid_ctx T ⊥).
  Proof.
    split; intros; eauto.
    unfold kvalid_ctx in *; simpl; intros.
    eapply H; simpl; intros. eapply H2; eauto.
  Qed.

  Lemma ksat_neg (M0 : kmodel)(u: nodes)(rho: nat -> domain)(phi: form):
    (rho ⊩( u, M0) (¬ phi) <-> (forall v: nodes, reachable u v -> (rho ⊩( v, M0) phi) ->  False)).
  Proof. 
    simpl; now eauto.
  Qed.

  Lemma kvalid_ctx_DN_out_in (T : list form)(phi: form):
    (((kvalid_ctx T phi) -> False )-> False) -> (kvalid_ctx T (bin Impl (bin Impl (phi) ⊥) ⊥)).
  Proof.
    unfold kvalid_ctx; intros.
    eapply (ksat_neg M0 u rho (¬ phi)); simpl; intros. 
    eapply H; intros.
    assert (forall psi : form, psi el T -> rho ⊩( v, M0) psi); intros. eapply ksat_mon; eauto.
    specialize (H4 M0 v rho (good_mon H0 H2) H5).
    eapply H3; eauto using reach_refl.
  Qed.

 (* Lemma ksat_DN_in_out (u: nodes)(rho: nat -> domain)(phi: form) :
    good u rho ->
    ksat u rho (bin Impl (bin Impl (phi) ⊥) ⊥) -> ((ksat u rho phi -> False ) -> False).
THIS IS FALSE

  Definition EM (P: Prop): Prop := P \/ (P-> False).

  Lemma ksat_DNE' (u: nodes)(rho: nat -> domain)(phi: form) :
    good u rho ->
    (ksat u rho phi <-> ksat u rho (bin Impl (bin Impl (phi) ⊥) ⊥)) -> EM (ksat u rho phi).
  Proof.
    intros; 
THIS IS FALSE I THINK
  *)

    
    
End PropKsat.

Section ConstantDomain.
  Context {Σf : funcs_signature} {Σp : preds_signature}.
  Context {frm : kframe}.
  (* Context {M : kmodel}. *) 
  Definition constant_domain (fr : kframe)(M : kmodel) :  Prop :=
      (forall (u v: nodes) (j: domain), world u j <-> world v j).
  (*
  Definition constant_domain' (fr : kframe)(M : kmodel) :  Prop :=
      forall (u : nodes) (j: domain), world u j.
  
  Definition non_empty (fr : kframe)(M : kmodel) :  Prop :=
      exists (u : nodes) (j: domain), world u j.
  *)
  Definition constant_domain_meta :=
  forall (X: Type)(A: X -> Prop)(B: Prop),
    (forall x: X, (A x \/ B)) -> ((forall x: X, A x) \/ B).

  Lemma cdm_distr_impl_or :
  constant_domain_meta -> (forall (a b c: Prop), (a -> (b \/ c)) -> ((a -> b) \/ c)).
  Proof.
    intros. 
    eapply H. eauto.
  Qed.

  Lemma cdm_imp_EM :
    constant_domain_meta -> forall (A:Prop), (A->False) \/ A.
  Proof.
    intros. eapply cdm_distr_impl_or; eauto.
  Qed.

  Lemma EM_imp_cdm : 
    (forall (A:Prop), (A->False) \/ A) -> constant_domain_meta.
  Proof.
    unfold constant_domain_meta; intros.
    specialize (H B); destruct H.
    + left. intros. specialize (H0 x).
      destruct H0.
      ++  eapply H0. 
      ++  eapply H in H0. eauto.
    + right. eapply H.
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
  Lemma CD_imp_CD_axiom (M: kmodel)(rho: nat -> my_KripkeCompleteness.domain)(phi psi: form):
        constant_domain M -> constant_domain_meta -> 
        forall (u : nodes), good u rho ->
        ksat u rho (bin Impl (quant All (bin Disj phi (psi[↑]))) (bin Disj (quant All  phi) (psi))).
    Proof.
    simpl; intros.
    unfold constant_domain in H; unfold constant_domain_meta in H0.
    eapply H0; intros.
    eapply cdm_distr_impl_or; eauto; intros.
    eapply H0; intros.
    eapply cdm_distr_impl_or; eauto. 
    revert x0.
    assert ((forall x0 : domain, world x x0 -> (x0 .: rho) ⊩( x, M) phi \/ (x0 .: rho) ⊩( v, M) psi [↑])
    <-> (forall x0 : domain, world x x0 -> (x0 .: rho) ⊩( x, M) phi \/ rho ⊩( v, M) psi)
    ).
    * split; intros; specialize (H5 x0 H6); destruct H5. 
      1,3: left; eauto.
      1,2: right. 1: eapply ksat_shift. 4: erewrite <- ksat_shift. 
      all: eauto using good_mon; eapply H; eauto. 
    * eapply H5; intros.
      pose proof (H x v x0). eapply H7 in H6.
      specialize (H3 v (reach_refl v) x0 H6); destruct H3.
      left; eapply ksat_mon; eauto using H3, good_mon, good_shift.
      right; apply H3. 
    Qed.

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

    Print interp.

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

    #[refine] Instance my_kmodel: @kmodel _ _ my_frm :=
    {|
        I := fun (w: nodes) => match w with 
                              | u => my_I_u
                              | v => my_I_v
                              end;
    |}.
    Proof.
      - induction u0; induction v0; simpl; reflexivity.
      - induction u0; simpl; auto.
      - intros.
        remember P0 as PP.
        induction PP; induction u0; induction v0; cbn; eauto; unfold in_dom in a0.
        all : dependent destruction vv; destruct h.
        dependent destruction vv.
        simpl in H; eauto.
        all : dependent destruction vv. eauto.
        all: simpl in H; eauto.
      - unfold in_dom; intros; induction u0; simpl in *; eauto. 
        dependent destruction vv; induction h; destruct vv; destruct P0; eauto.
        destruct x; eauto.
        apply In_inv in H0; simpl in H0; destruct H0.
        discriminate H0.
        apply In_inv in H0; simpl in H0; eauto.
    Defined.

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
    + left. 
      eapply in_u in H1. rewrite H1.
      unfold i_atom; unfold my_I_u; eauto.
    + right; exists b; split. eauto. eauto.
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

Section Completeness.
   #[local] Existing Instance falsity_on.
  Context {Σf : funcs_signature} {Σp : preds_signature}.

  Instance C_Σf: funcs_signature :=
    {|
      syms := sum (syms)  (nat*nat);
      ar_syms := fun f => (match f with 
                | inl f => ar_syms f
                | inr (_, _) => 0 end)
    |}.

  Inductive term_c_bounded : nat-> term -> Prop :=
  | bounded_var : forall (n x : nat), term_c_bounded n (var x)
  | bounded_c   : forall (n k c: nat), k<n -> term_c_bounded n (func (inr (k, c)) (nil _) )
  | bounded_f   : forall (n:nat)f (vv: (t term (ar_syms (inl f)))), (forall (trm: term),  InT trm vv -> term_c_bounded n trm) -> term_c_bounded n (func (inl f) vv).
  
  Inductive c_bounded : nat -> form -> Prop :=
  | bounded_falsity : forall (n:nat), c_bounded n falsity 
  | bounded_p : forall (n : nat)(P: preds)(vv: (t term (ar_preds P))), (forall (trm: term),  InT trm vv -> term_c_bounded n trm) -> c_bounded n (atom P vv)
  | bounded_bin: forall (n: nat)(phi psi: form)(conn : full_logic_sym), (c_bounded n phi) ->(c_bounded n psi) -> c_bounded n (bin conn phi psi)
  | bounded_quant: forall (n: nat)(phi: form)(q : full_logic_quant), (c_bounded n phi) -> c_bounded n (quant q phi).

  Definition c_closed (phi: form):= c_bounded 0 phi.  

  Definition th_c_closed (Gamma: form -> Prop):=
    (forall psi: form, Gamma psi -> c_closed psi).

  Definition th_c_bounded (n: nat)(Gamma: form -> Prop):=
    (forall psi: form, Gamma psi -> c_bounded n psi).

  Lemma term_c_bound_mon :
    forall (n m: nat)(trm : term), n <= m -> term_c_bounded n trm -> term_c_bounded m trm.
  Proof.
    intros.
    induction H0.
    * eauto using bounded_var.
    * eapply bounded_c. eapply (Nat.lt_le_trans k n m); eauto.
    * eapply bounded_f. intros. eapply H1; eauto.
  Qed.  
    
  Definition prv_inf (Gamma : form -> Prop)(phi: form) :=
    exists (Gamma_fin : list form), (forall (psi:form), List.In psi Gamma_fin -> Gamma psi) /\ Gamma_fin ⊢I phi.
    
  Notation "A ⊢ phi" := (prv_inf A phi) (at level 55).

  Definition consistent A := ~ (A ⊢ ⊥).  

   Class n_saturated (n:nat)(Gamma: form -> Prop) :=
      { 
        consist        : consistent Gamma;
        c_bound phi    : Gamma phi -> c_bounded (n+1) phi;
        der_closed phi : Gamma ⊢ phi -> Gamma phi;
        prime phi psi  : Gamma ⊢ (bin Disj phi psi) -> ((Gamma phi) \/ (Gamma psi));
        ex_closed phi  : Gamma ⊢ (quant Ex phi) -> exists m c, m<=n /\ Gamma (phi[(func (inr (m, c)) (nil _) )..]);
      }.

  Definition ctx_incl (Gamma Delta : form -> Prop) :=
    forall phi: form, Gamma phi -> Delta phi. 

  Notation "A <<=C B" := (ctx_incl A B) (at level 20).  

  #[local] Hint Unfold consistent ctx_incl : core.
    
  Lemma saturation_lemma :
    forall (n: nat)(Gamma : form -> Prop)(phi: form), 
    th_c_bounded n Gamma -> c_bounded n phi ->  (Gamma ⊢ phi -> False) ->
    exists (Delta: form -> Prop), (Gamma <<=C Delta /\  n_saturated n Delta /\ ((Delta ⊢ phi) -> False) ).
  Proof.
    intros.
    admit.
  Admitted.

  Definition canonical_nodes := { G_n :  (form -> Prop)*nat | let (Gamma, n) := G_n in n_saturated n Gamma }.

  Definition c_n_set: canonical_nodes -> (form -> Prop) := 
    fun (G_n : canonical_nodes) => let (G_n, H):= G_n  in
                                   let (Gamma, n) := G_n in Gamma.

  Definition c_n_nat: canonical_nodes -> nat := 
    fun (G_n : canonical_nodes) => let (G_n, H):= G_n  in
                                   let (Gamma, n) := G_n in n.   
                                   
  Definition c_incl (Gamma Delta: canonical_nodes): Prop :=
    ctx_incl (c_n_set Gamma) (c_n_set Delta) /\ (c_n_nat Gamma <= c_n_nat Delta).

  Definition in_c_world (Gamma: canonical_nodes) (j: term): Prop :=
    term_c_bounded ((c_n_nat Gamma)+1) j.

  Program Instance canonical_model_frm : kframe :=
      {|
        domain := term;
        nodes := canonical_nodes;
        reachable := c_incl;
        world := in_c_world;
      |}.
    Next Obligation.
      unfold c_incl.
      split; eauto.
    Qed.
    Next Obligation.
      unfold c_incl in *.
      split. destruct H. destruct H0. all: eauto.
      transitivity (c_n_nat v0); now eauto using H, H0.
    Qed.
    Next Obligation.
      unfold c_incl in H; destruct H as (H1, H2).
      unfold in_c_world in *.
      dependent induction H0.
       * eauto using bounded_var.
       * eapply bounded_c. eauto.
         eapply Nat.lt_le_trans.
         eapply H. 
         repeat rewrite Nat.add_1_r.
         rewrite <- Nat.succ_le_mono; eauto.
       * eapply bounded_f. intros. eapply term_c_bound_mon.
         2: eapply H; eauto. 
         repeat rewrite Nat.add_1_r.
         rewrite <- Nat.succ_le_mono; eauto.
  Qed.
(*
  Instance can_I : @interp C_Σf Σp  :=
      {| 
        i_func := fun _ _ => a;  (*??????*)
        
        i_atom := fun Gamma P vv => A ⊢ phi
      |}.

 #[refine] Instance canonical_model: @kmodel _ _ canonical_model_frm :=
    {|
        fun A P v => sprv A None (atom P v) ;
    |}.

    Program Instance K_ctx {ff:falsity_flag} : kmodel term :=
      {|
        nodes := list form ;
        reachable := @incl form ;
        k_interp := model_bot ;
        k_P := fun A P v => sprv A None (atom P v) ;
      |}.
*)

  Definition kmodel_ctx (Gamma : form -> Prop) (phi: form)  :=
    forall (frm:kframe)(M: kmodel)(u: nodes)(rho: nat-> domain), (forall psi: form, Gamma psi -> @ksat _ _ frm M _ u rho psi) -> @ksat _ _ frm M _ u rho phi.
  
  Definition kmodel_ctx' (Gamma : @form Σf Σp _ _-> Prop) (phi: @form Σf Σp _ _)  :=
    forall (frm:kframe)(M: kmodel)(u: nodes)(rho: nat-> domain), (forall psi: @form Σf Σp _ _, Gamma psi -> @ksat Σf Σp frm M _ u rho psi) -> @ksat Σf Σp frm M _ u rho phi.  
(*
  estendi 
  - termini
  - formule
  - 
*)
  Axiom DNE : forall P:Prop, ((P -> False)-> False) -> P.  

  Lemma der_ax:
    forall(Gamma: form -> Prop)(phi: form), Gamma phi -> Gamma ⊢ phi.
  Proof.
    intros. unfold "⊢".
    exists [phi].
    split.
    * intros. simpl in H0. destruct H0. 
      rewrite <-H0; eauto.
      eauto.
    * eapply Ctx. eauto.
  Qed.

  Lemma classical_strong_completeness : 
    forall (Gamma : form -> Prop)(phi: form )(n: nat),
    th_c_bounded n Gamma -> c_bounded n phi ->
    kmodel_ctx Gamma phi -> Gamma ⊢ phi.
  Proof.
    intros.
    eapply DNE.
    intros.
    specialize (saturation_lemma H H0 H2).
    intros.
    destruct H3 as [Delta (H3, (H4, H5))].
    assert (Delta phi -> False).
    intros. eapply der_ax in H6. eauto.
    
    
    eapply der_closed del 
    eapply saturation_lemma.

    admit.
  Admitted.

End Completeness.
