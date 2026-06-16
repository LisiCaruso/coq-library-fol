(** ** Kripke Completeness **)

From FOL Require Import FullSyntax Theories Deduction.FullSequentFacts Deduction.FragmentSequentFacts.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From FOL.Completeness Require Export TarskiCompleteness.
From Undecidability Require Import Shared.ListAutomation Shared.Dec FOL.Deduction.FullND.
Require Import Undecidability.FOL.Semantics.Tarski.FullCore.
Require Import Arith.
Require Import Nat List Vector Lia.
Import ListAutomationNotations ListAutomationHints ListAutomationInstances ListAutomationFacts.
From FOL.Utils Require Import MPFacts.
Require Import Coq.Program.Equality.

Section VariableDomainKripke.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
  
Arguments eval {_ _ _} _ _ _.
Arguments i_atom {_ _ _} _ _.
Arguments i_func {_ _ _} _ _.
  
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

Class kmodel := 
{
  I : nodes -> interp domain;

  k_P_wellDef u P vv: i_atom (I u) P vv -> in_dom u vv;

  mon_P (u v:nodes) (P: preds) (vv: (t domain (ar_preds P))) (reach : reachable u v) (a : in_dom u vv): 
      i_atom (I u) P vv -> i_atom (I v) P vv;

  k_f_wellDef u f vv (vv_in_dom : (in_dom u vv)): world u (i_func (I u) f vv);

  mon_f (u v:nodes) (f: syms) (vv: (t domain (ar_syms f))) (reach : reachable u v): 
    in_dom u vv -> i_func (I u) f vv = i_func (I v) f vv;

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
  good u rho -> reachable u v -> eval (I u) rho t = eval (I v) rho t.
Proof.
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
  good u rho -> reachable u v -> forall t: term, eval (I u) rho t = eval (I v) rho t.
Proof.
  intros.
  now apply eval_mon_t.
Qed.

Lemma map_eval_vv (u v: nodes) (rho : nat -> domain) (n : nat)(vv: t term n):
  good u rho -> reachable u v -> map (eval (I u) rho) vv = map (eval (I v) rho) vv.
Proof.
  intros.
  eapply map_ext. now eapply eval_mon.
Qed.

Lemma in_dom_mix (u v: nodes) (rho : nat -> domain) (n : nat)(vv: t term n):
  good u rho -> reachable u v -> in_dom u (map (eval (I u) rho) vv) -> in_dom u (map (eval (I v) rho) vv).
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

Lemma eval_mon_shift_up (u v: nodes)(rho: nat -> domain)(xi : nat -> term)(j : domain)(n: nat):
  good u rho -> reachable u v -> ( j .: xi >> eval (I u) rho) n = ((up xi) >> eval (I v) (j .:rho)) n.
Proof.
  intros; induction n; cbn.
  * reflexivity.
  * unfold ">>" in *. erewrite eval_mon; [now erewrite <- eval_up | | ]; auto.
Qed.

Lemma eval_shift_up (u: nodes)(rho: nat -> domain)(xi : nat -> term)(j : domain)(n: nat):
( j .: xi >> eval (I u) rho) n = ((up xi) >> eval (I u) (j .:rho)) n.
Proof.
  intros; induction n; cbn.
  * reflexivity.
  * unfold ">>" in *. now erewrite <- eval_up. 
Qed.

End VariableDomainKripke.

Arguments kmodel {_ _ _}.

#[local] Ltac comp := repeat (progress (cbn in *; autounfold in *)).
#[local] Ltac temp_k_solve := (eauto using good_mon, good_shift, good_comp, good_eval, eval_mon, map_eval_vv, shift_ext, good_ext, good_comp, eval_mon_shift_up, eval_shift_up, reach_refl, reach_tran).
#[local] Ltac k_solve := (repeat (temp_k_solve)).

Section KripkeSat.

Context {Σf : funcs_signature} {Σp : preds_signature}.
Context {frm : kframe}.
Context {M : kmodel}.

Arguments eval {_ _ _} _ _ _.

Lemma ksat_consistent u rho phi:
  good u rho -> ksat u rho phi -> ksat u rho (bin Impl phi falsity) -> False.
Proof.
  intros.
  eapply H1; eauto using reach_refl.
Qed.

Lemma ksat_mon {ff : falsity_flag}(u v: nodes) (rho : nat -> domain) (phi : form) : 
  good u rho -> reachable u v -> ksat u rho phi -> ksat v rho phi.
Proof.
  revert rho. 
  induction phi; intros rho gd R H; cbn.
  * apply H.
  * unfold ksat in H.
    apply (mon_P R). 
    + erewrite map_eval_vv; k_solve; eauto using in_dom_mix, k_P_wellDef. 
    + erewrite <- map_eval_vv; eauto. 
  * destruct b0.
    + destruct H; split; eauto.
    + destruct H; [left | right]; eauto. 
    + simpl in H. intros w Rw IH. k_solve. 
  * destruct q; simpl in H.
    + intros w Rw j wj. k_solve.
    + destruct H as (j, H). exists j. split.
      - eapply monotone; now eauto.
      - eapply IHphi. now eapply good_shift. k_solve. eapply H.
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
  * tauto.
  * erewrite Vector.map_ext. reflexivity. intros t. now apply eval_ext.
  * destruct b0;  split; intros H; try intros v Huv; rewrite IHphi1, IHphi2; k_solve.
  * destruct q.
    + split; intros; erewrite IHphi; k_solve.
    + split; intros; repeat destruct H; exists x; split;
      [ | eapply (IHphi _ (x .: rho) (x .: xi)) |  | eapply (IHphi _ (x .: xi) (x .: rho))]; 
      try k_solve; induction x0; eauto.
Qed.

Lemma ksat_comp {ff : falsity_flag}(u: nodes)(rho: nat -> domain)(xi : nat -> term)(phi: form) :
  good u rho -> 
    (rho ⊩(u,M) phi[xi] <-> (xi >> eval (I u) rho) ⊩(u,M) phi).
Proof.
  induction phi as [ | b P v | | ] in rho, xi, u |-*; comp.
  * tauto.
  * erewrite Vector.map_map. erewrite Vector.map_ext. 2: apply eval_comp. reflexivity.
  * destruct b0; intros.
    + split; [split; [eapply IHphi1| eapply IHphi2] | split; [eapply IHphi1| eapply IHphi2]]; now eauto.
    + split; intros; destruct H0; [left | right | left | right]; 
      [eapply IHphi1| eapply IHphi2 | eapply IHphi1| eapply IHphi2]; now eauto. 
    + split; intros.
      -eapply ksat_ext; [| intros | eapply IHphi2].
        4: apply (H0 v H1);  eapply IHphi1; try eapply ksat_ext; try eapply H2.
        6: intros; unfold ">>"; erewrite <- (eval_mon_t (xi x)). 
        all: now k_solve.
      - eapply IHphi2; [ | eapply ksat_ext]; [| |intros | eapply H0].
        5: eapply ksat_ext. 7: eapply IHphi1. 8: eapply H2. 5: intros. 6: intros.
        all: unfold ">>" . 
        3: erewrite <- (eval_mon_t (xi x)). 
        all: try now k_solve. 
  * destruct q; split; intros; try  destruct H0 as (j, (H0, H1)); try exists j; try split; try apply H0.
    + eapply ksat_ext; try eapply IHphi; try eapply H0;
      [unfold good; intros; eapply good_shift| intros |  |  | ]; k_solve.
    + eapply IHphi; [ | eapply ksat_ext]; [ | | intros | eapply H0].
      3: erewrite eval_mon_shift_up. all: k_solve.
    + eapply ksat_ext; [ |intros; now eapply eval_mon_shift_up |eapply IHphi]; k_solve.
    + eapply IHphi; [| eapply ksat_ext]; [ | |intros| eapply H1]; k_solve.   
Qed.

Lemma ksat_shift {ff : falsity_flag}(u: nodes)(rho: nat -> domain)(phi: form):
  good u rho-> forall j: domain, world u j -> 
    (rho ⊩( u, M) phi <-> (j.: rho)  ⊩( u, M) phi [↑]).
Proof.
  split; intros.
  rewrite ksat_comp; k_solve.
  rewrite ksat_comp in H1. eapply ksat_ext. all: k_solve.
Qed.

End Substs.
End KripkeSat. 

Notation "rho  '⊩(' u ')'  phi" := (ksat _ u rho phi) (at level 20).
Notation "rho '⊩(' u , M ')' phi" := (@ksat _ _ _ M _ u rho phi) (at level 20).


Section Soundness.
Context {Σf : funcs_signature} {Σp : preds_signature}.
Context {frm : kframe}.

Arguments ksat {_ _ _} _ {_} _, _ _ _ _ _ _.

Definition ktheo (M: kmodel)(phi : form) :=
  forall rho u, good u rho -> ksat M u rho phi.

Definition kvalid phi {ff : falsity_flag}:=
  forall (M: kmodel) (u: nodes) (rho: nat -> domain), 
  good u rho -> ksat M u rho phi.

Definition ksatis {ff : falsity_flag} phi :=
  exists (M: kmodel) (u: nodes) (rho: nat -> domain), good u rho /\ ksat M u rho phi.

Definition kvalid_ctx {ff : falsity_flag}(A : list form) (phi: form) :=
  forall (M: kmodel) (u: nodes) (rho: nat -> domain),
    good u rho -> (forall psi, psi el A -> ksat M u rho psi) -> ksat M u rho phi.

Notation "A '⊩' phi" := (kvalid_ctx A phi) (at level 20). 

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
        A ⊢I ∃ phi -> P ff A (∃ phi) -> (phi :: [p[↑] | p ∈ A]) ⊢I psi[↑] -> P ff (phi :: [p[↑] | p ∈ A]) psi[↑] -> P ff A psi) ->
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
  A ⊢I phi -> A ⊩ phi.
Proof.
  intros H M.
  apply (prv_ind_intu (P := fun ff A phi => forall (u : nodes) (rho : nat -> domain),
        good u rho -> (forall psi : form ff, psi el A -> rho ⊩( u, M) psi) ->
        rho ⊩( u, M) phi)); eauto; simpl; intros ff1 A1 ; intros; 
        try eapply H1; eauto using good_mon, good_shift, reach_refl. (*k_solve. *)
  * simpl; intros; destruct H6; [rewrite <- H6 | eapply ksat_mon]; eauto.
  * intros psi0 [psi' [<- HH]] % in_map_iff. 
    rewrite ksat_comp. eapply ksat_mon. all: k_solve. 
  * erewrite ksat_comp. erewrite ksat_ext. eapply (H1 u rho H2 H3 u (reach_refl u) (eval rho t)).
    3: intros; unfold ">>"; induction x; simpl; reflexivity.
    all: k_solve.
  * specialize (H1  u rho); apply ksat_comp in H1.
    exists (@eval _ _  _ (I u) rho t); split.
    2: eapply ksat_ext. 4: eapply H1. 
    all: k_solve.
    intros. induction x; cbn; reflexivity.
  * specialize (H1 u rho H4 H5); destruct H1 as [j (wj, IH)].
    eapply ksat_shift. 3: eapply H3. all: k_solve.
    intros; destruct H1.
    rewrite <- H1; eauto.
    eapply in_map_iff in H1; destruct H1 as [psh (eq, elA1)]; rewrite <- eq; erewrite <- ksat_shift; eauto.
  * specialize (H1 u rho H2 H3); eauto. 
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
    | Pp : Preds
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
                                                      | Pp => False
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
                                                      | Pp => False
                                                      | Q => True
                                                      end
                              | cons _ b _ (nil _) =>  match pr with 
                                                      | Pp => True
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
        remember P as PP.
        induction PP; induction u0; induction v0; cbn; eauto; unfold in_dom in a0.
        all : dependent destruction vv; destruct h.
        dependent destruction vv.
        simpl in H; eauto.
        all : dependent destruction vv. eauto.
        all: simpl in H; eauto.
      - unfold in_dom; intros; induction u0; simpl in *; eauto. 
        dependent destruction vv; induction h; destruct vv; destruct P; eauto.
        destruct x; eauto.
        apply In_inv in H0; simpl in H0; destruct H0.
        discriminate H0.
        apply In_inv in H0; simpl in H0; eauto.
    Defined.

  Definition A (alpha: t term 1): form :=  atom Q alpha.
  Definition B (alpha: t term 1): form := quant Ex (atom Pp alpha).

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

Context {Σf : funcs_signature}.
Context {Σp : preds_signature}.

#[local] Existing Instance falsity_on.
Program Instance C_Σf: funcs_signature :=
  {|
    syms := sum (syms)  (nat*nat);
    ar_syms := fun f => (match f with 
              | inl f => ar_syms f
              | inr (_, _) => 0 end)
  |}.

Lemma ar_syms_eq (f: @syms Σf):
  @ar_syms Σf f = @ar_syms C_Σf (inl f).
Proof.
  eauto.
Defined.

Inductive term_c_bounded : nat-> @term C_Σf -> Prop :=
| bounded_var : forall (n x : nat), term_c_bounded n (var x)
| bounded_c   : forall (n k c: nat), k<n -> term_c_bounded n (@func C_Σf (inr (k, c)) (nil _) )
| bounded_f   : forall (n:nat)f (vv: (t term (@ar_syms C_Σf (inl f)))), 
                (forall (trm: term),  In trm vv -> term_c_bounded n trm) -> term_c_bounded n (@func C_Σf (inl f) vv).

Inductive c_bounded : nat -> @form C_Σf _ _ _-> Prop :=
| bounded_falsity : forall (n:nat), c_bounded n falsity 
| bounded_p : forall (n : nat)(P: preds)(vv: (t term (ar_preds P))), (forall (trm: term),  In trm vv -> term_c_bounded n trm) -> c_bounded n (atom P vv)
| bounded_bin: forall (n: nat)(phi psi: @form C_Σf _ _ _)(conn : full_logic_sym), (c_bounded n phi) ->(c_bounded n psi) -> c_bounded n (@bin C_Σf _ _ _  conn phi psi)
| bounded_quant: forall (n: nat)(phi: form)(q : full_logic_quant), (c_bounded n phi) -> c_bounded n (@quant C_Σf _ _ _ q phi).

Definition th_c_bounded (n: nat)(Gamma: (@form C_Σf _ _ _)-> Prop):=
  (forall psi: form, Gamma psi -> c_bounded n psi).

Lemma c_bound_p_term:
forall (n: nat)(P: preds)(vv: (t term (ar_preds P))),
c_bounded n (atom P vv) <-> Forall (term_c_bounded n) vv.
Proof.
  intros; split; intros.
  + dependent induction H.
    eapply Forall_forall; eapply H.
  + eapply bounded_p. eapply Forall_forall; eauto.
Qed.

Lemma c_bound_conn:
forall (n: nat)(phi psi: @form C_Σf _ _ _)(conn : full_logic_sym),
  c_bounded n (@bin C_Σf _ _ _  conn phi psi) <-> (c_bounded n phi /\ c_bounded n psi).
Proof.
intros; split; intros.
+ dependent destruction H; split; eauto.
+ destruct H; eapply bounded_bin; eauto.
Qed.

Lemma c_bound_quant:
forall (n: nat)(phi: @form C_Σf _ _ _)(q : full_logic_quant),
  c_bounded n (@quant C_Σf _ _ _ q phi) <-> (c_bounded n phi).
Proof.
intros; split; intros.
+ dependent destruction H; eauto.
+ eapply bounded_quant; eauto.
Qed.

Lemma term_c_bound_mon :
  forall (n m: nat)(trm : term), n <= m -> term_c_bounded n trm -> term_c_bounded m trm.
Proof.
  intros.
  induction H0.
  * eauto using bounded_var.
  * eapply bounded_c. eapply (Nat.lt_le_trans k n m); eauto.
  * eapply bounded_f. intros. eapply H1; eauto.
Qed.  

Lemma c_bound_mon :
  forall (n m: nat)(phi: form),
  n <= m -> c_bounded n phi -> c_bounded m phi.
Proof.
  intros. induction phi using form_ind_falsity.
  + eapply bounded_falsity.
  + dependent destruction H0. eapply bounded_p.
    intros. eapply term_c_bound_mon; eauto.
  + dependent destruction H0. eapply bounded_bin; [eapply IHphi1 | eapply IHphi2]; eauto.
  + dependent destruction H0. eapply bounded_quant ; eauto.
Qed.

Lemma th_c_bound_mon :
  forall (n m: nat)(Gamma: (@form C_Σf _ _ _)-> Prop),
  n <= m -> th_c_bounded n Gamma -> th_c_bounded m Gamma.
Proof.
  unfold th_c_bounded. intros. 
  eapply c_bound_mon; eauto.
Qed.


Lemma term_c_bound_eval: 
  forall (n: nat)(trm: term)(rho:  nat -> term),
  (forall x : nat, term_c_bounded n (rho x) )->
  term_c_bounded n trm ->
  term_c_bounded n (trm`[rho]).
Proof.
  intros. induction H0.
  + cbn; eauto.
  + cbn; eapply bounded_c; eauto.
  + unfold subst_term. eapply bounded_f; cbn.
    intros.
    eapply vector_in_map in H2.
    destruct H2. destruct H2.
    rewrite <- H3.
    eapply H1; eauto.
Qed.

Lemma c_bound_eval : 
  forall (n: nat)(phi: form)(rho:  nat -> term),
  (forall x : nat, term_c_bounded n (rho x)) ->
  c_bounded n phi ->
  c_bounded n (phi[rho]).
Proof.
  intros. generalize rho H. induction H0; intros.
  + eapply bounded_falsity.
  + eapply bounded_p.
    intros. eapply vector_in_map in H2.
    destruct H2. destruct H2. rewrite <- H3.
    eapply term_c_bound_eval; eauto.
  + cbn. eapply bounded_bin; eauto.
  + eapply bounded_quant. eapply IHc_bounded; eauto.
    intros; induction x.
    * cbn; eapply bounded_var.
    * unfold up. unfold ">>". cbn.
      eapply term_c_bound_eval; eauto.
      intros. eapply bounded_var.
Qed.  

Lemma term_c_bound_eval': 
  forall (n: nat)(trm: term)(j: term),
  term_c_bounded n j ->
  term_c_bounded n trm ->
  term_c_bounded n (trm`[j..]).
Proof.
  unfold scons. 
  intros. eapply term_c_bound_eval; eauto.
  destruct x.
  + eauto.
  + eapply bounded_var.
Qed.

Lemma c_bound_eval': 
  forall (n: nat)(phi: form)(j: term),
  term_c_bounded n j ->
  c_bounded n phi ->
  c_bounded n (phi[j..]).
Proof.
  intros. eapply c_bound_eval; eauto.
  intros. unfold scons.
  destruct x.
  + eauto.
  + eapply bounded_var.
Qed.  

 (* Lemma c_bound_subst_quant: 
    forall (n : nat)(phi: form)(rho: nat -> term)(j: term)(q: full_logic_quant),
    term_c_bounded n j ->
    c_bounded n ((quant q phi)[rho]) <-> c_bounded n phi[j.:rho].
  Proof.
    induction phi using form_ind_falsity; intros; split; intros.
    * eapply bounded_falsity.
    * eapply bounded_quant. eapply H0.
    * eapply bounded_p.    
      dependent destruction trm.
      ** intros; eapply bounded_var.
      ** destruct f; admit. 
  Admitted.  
      
  Definition c_closed (phi: @form C_Σf _ _ _):= c_bounded 0 phi.  

  Definition th_c_closed (Gamma: ( @form C_Σf _ _ _) -> Prop):=
    (forall (psi: @form C_Σf _ _ _), Gamma psi -> c_closed psi).
*) 


(* -------------------------------------------------------------------------------------- *)
Section Translations_Σf_C_Σf.

Arguments form _ {_ _ _}.  
Arguments theory _ {_ _ _}.

Fixpoint term_to_C_Σf_term (trm : @term Σf): @term C_Σf :=
match trm with 
| var n => @var C_Σf n
| func f vv => @func  C_Σf (inl f) (map (term_to_C_Σf_term) vv)
end.

Fixpoint form_to_C_Σf_form (phi: form Σf): form C_Σf:=
  match phi with
  | falsity => falsity
  | @atom _ _ _ falsity_on P vv => @atom C_Σf Σp _ falsity_on P (map term_to_C_Σf_term vv) 
  | @bin _ _ _ falsity_on bb phi psi => @bin C_Σf Σp _ falsity_on bb (form_to_C_Σf_form phi) (form_to_C_Σf_form psi)
  | @quant _ _ _ falsity_on qq phi => @quant C_Σf Σp _ falsity_on qq (form_to_C_Σf_form phi) 
end.

Definition theory_to_C_Σf_theory (T: theory Σf): theory C_Σf :=
  fun phi => (exists phi': form Σf, form_to_C_Σf_form phi' = phi).

Fixpoint C_closed_term_to_Σf_term (t: @term C_Σf) : @term Σf.
Proof.
  refine (match t with 
  | @var _ n => @var Σf n
  | @func _ (inl f) vv => @func Σf f (map C_closed_term_to_Σf_term vv)
  | @func _ (inr f) vv =>  @var Σf 0
  end).
Defined.

Fixpoint C_closed_form_to_Σf_form (phi: form C_Σf) : form Σf.
Proof.
  refine (match phi with 
  | falsity => falsity
  | @atom _ _ _ falsity_on P vv => @atom Σf _ _ falsity_on P (map C_closed_term_to_Σf_term vv) 
  | @bin _ _ _ falsity_on bb phi psi => @bin Σf _ _ falsity_on bb (C_closed_form_to_Σf_form phi) (C_closed_form_to_Σf_form psi)
  | @quant _ _ _ falsity_on qq phi => @quant Σf _ _ falsity_on qq (C_closed_form_to_Σf_form phi) 
  end).
Defined.

Fixpoint term_count_C (trm: @term C_Σf): nat :=
match trm with 
|  @var _ n => 0
|  @func _ (inl f) vv => (fold_left add 0 (map term_count_C vv))
|  @func _ (inr (k, c)) _  => 1
end.

Fixpoint form_count_C (phi: form C_Σf): nat :=
match phi with
  | falsity => 0
  | @atom _ _ _ falsity_on P vv => (fold_left add 0 (map term_count_C vv)) 
  | @bin _ _ _ falsity_on bb phi psi => (form_count_C phi) + (form_count_C psi)
  | @quant _ _ _ falsity_on qq phi => (form_count_C phi)
end.

Fixpoint term_shift_n (n: nat)(trm: @term C_Σf):=
match n with 
| 0    => trm
| S n  => term_shift_n n (trm `[↑])
end.

Fixpoint form_shift_n (n: nat)(phi: form C_Σf):=
match n with 
| 0    => phi
| S n  => form_shift_n n (phi[↑])
end.

Definition prepare_form (phi: form C_Σf) :=
  form_shift_n (form_count_C phi) phi.

#[local] Notation "[ ]" := (nil _) (format "[ ]").
#[local] Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Definition subst_const_n_var (n: nat)(trm: @term C_Σf): (nat)*(@term C_Σf):=
match trm with 
  | @func _ (inr (k, c)) _  => (S n, (@var C_Σf n))
  |  _ => (n, trm)
end.

Definition subst_const_n_var' (rho: nat -> @term C_Σf)(n: nat)(trm: @term C_Σf): (nat -> @term C_Σf)*(nat)*(@term C_Σf):=
match trm with 
  | @func _ (inr (k, c)) (nil _)  => ( (@func _ (inr (k, c)) (nil _)).:rho , S n, (@var C_Σf n))
  |  _ => (rho, n, trm)
end.

Definition temp_subst {len : nat}(n_ww : nat * (t (@term C_Σf) len))(trm: (@term C_Σf)): (nat)*(t (@term C_Σf) (S len)) :=
  let (n, ww ):= n_ww in 
  let (n', trm_sub) := (subst_const_n_var n trm) in (n', (shiftin trm_sub ww )).

Definition temp_subst' (rho:  nat -> @term C_Σf){len : nat}(n_ww : nat * (t (@term C_Σf) len))(trm: (@term C_Σf)): (nat -> @term C_Σf)*nat*(t (@term C_Σf) (S len)) :=
  let (n, ww ):= n_ww in 
  let (n', trm_sub) := (subst_const_n_var' rho n trm) in (n', (shiftin trm_sub ww )).

Fixpoint temp_fold_left_subs {len_ww}(n_ww : nat * (t (@term C_Σf) len_ww)) {len_vv} (vv: t (@term C_Σf) len_vv)
: nat * t (@term C_Σf) (len_vv + len_ww). 
Proof. 
  refine(
  match vv in t _ mm with
    | [] => n_ww
    | aa :: vv => _
  end).
  assert (n + S len_ww = S n + len_ww).
  rewrite Nat.add_succ_comm. reflexivity.
  rewrite <- H.
  exact (temp_fold_left_subs (S len_ww) (temp_subst n_ww aa) _ vv).
Defined.

Fixpoint temp_fold_left_subs' (rho:  nat -> @term C_Σf){len_ww}(n_ww : nat * (t (@term C_Σf) len_ww)) {len_vv} (vv: t (@term C_Σf) len_vv)
: (nat -> @term C_Σf)*nat* t (@term C_Σf) (len_vv + len_ww). 
Proof. 
  refine(   
  match vv in t _ mm with
    | [] =>  let (nn, ww):= n_ww in (rho, nn, _)
    | aa :: vv => let (nn, ww):= n_ww in 
                  let (rho'_n', ww') := temp_subst' rho n_ww aa in 
                  let (rho', n') := rho'_n' in _
  end).
  exact ww.
  assert (n + S len_ww = S n + len_ww).
  rewrite Nat.add_succ_comm. reflexivity.
  rewrite <- H.
  exact (temp_fold_left_subs'  rho' (S len_ww) (n' , ww') _ vv). 
Defined.

Definition fold_left_subs {len_vv}(n: nat)(vv: t (@term C_Σf) len_vv) := 
@temp_fold_left_subs 0 (n,(nil _)) _ vv.

Definition fold_left_subs' {len_vv}(rho:  nat -> @term C_Σf)(n: nat)(vv: t (@term C_Σf) len_vv) := 
@temp_fold_left_subs' rho 0 (n,(nil _)) _ vv.

Fixpoint C_term_to_C_Σf_closed_term (n: nat)(trm:  @term C_Σf): (nat)*(@term C_Σf).
Proof.
  refine( match trm with 
  |  @var _ m => (n,(@var C_Σf m))
  |  @func _ (inl f) vv => let (n',vv') := fold_left_subs n vv in 
                          (n', (@func _ ) (inl f) _)
  |  @func _ (inr (k, c)) _  =>  subst_const_n_var n trm
  end  ).
  all: simpl in *.
  rewrite plus_n_O.
  exact vv'.
Defined.

Fixpoint C_term_to_C_Σf_closed_term' (rho:  nat -> @term C_Σf)(n: nat)(trm:  @term C_Σf): (nat -> @term C_Σf)*(nat)*(@term C_Σf).
Proof.
  refine( match trm with 
  |  @var _ m => (rho, n,(@var C_Σf m))
  |  @func _ (inl f) vv => let (rho'_n',vv') := fold_left_subs' rho n vv in 
                           let (rho', n') := rho'_n' in 
                          (rho', n', (@func _ ) (inl f) _)
  |  @func _ (inr (k, c)) _  =>  subst_const_n_var' rho n trm
  end  ).
  all: simpl in *.
  rewrite plus_n_O.
  exact vv'.
Defined.

Definition C_term_to_Σf_term (n: nat)(trm: @term C_Σf): (@term Σf) :=
  let (n', trm'):= C_term_to_C_Σf_closed_term n trm in 
   C_closed_term_to_Σf_term trm'.

Definition C_term_to_Σf_term' (rho:  nat -> @term C_Σf)(n: nat)(trm: @term C_Σf):  (nat -> @term C_Σf)*(@term Σf) :=
  let (rho'_n', trm'):= C_term_to_C_Σf_closed_term' rho n trm in 
  let (rho', n') := rho'_n' in (rho', C_closed_term_to_Σf_term trm').

Fixpoint C_form_to_C_Σf_closed_form (n: nat)(phi: form C_Σf): (nat)*(form C_Σf).
Proof.
  refine(  match phi with 
  |  @falsity _ _ _ => (n, @falsity C_Σf _ _)
  |  @atom _ _ _ falsity_on P vv => let (n', vv'):= fold_left_subs n vv in
                                    (n', @atom C_Σf Σp _ falsity_on P _) 
  |  @bin _ _ _ falsity_on bb phi psi => let (n' , phi'):= (C_form_to_C_Σf_closed_form n  phi) in
                                        let (n'', psi'):= (C_form_to_C_Σf_closed_form n' phi) in
                                        (n'', @bin C_Σf Σp _ falsity_on bb phi' psi')
  | @quant _ _ _ falsity_on qq phi => let (n' , phi'):= (C_form_to_C_Σf_closed_form n  phi) in 
                                        (n', @quant C_Σf Σp _ falsity_on qq phi') 
  end).
  rewrite plus_n_O.
  exact vv'.
Defined.

Fixpoint C_form_to_C_Σf_closed_form' (rho:  nat -> @term C_Σf)(n: nat)(phi: form C_Σf): (nat -> @term C_Σf)*(nat)*(form C_Σf).
Proof.
  refine(  match phi with 
  |  @falsity _ _ _ => (rho, n, @falsity C_Σf _ _)
  |  @atom _ _ _ falsity_on P vv => let (n', vv'):= fold_left_subs' rho n vv in
                                    (n', @atom C_Σf Σp _ falsity_on P _) 
  |  @bin _ _ _ falsity_on bb phi psi => let (rho'_n' , phi'):= (C_form_to_C_Σf_closed_form' rho n  phi) in
                                         let (rho', n') := rho'_n' in 
                                         let (n'', psi'):= (C_form_to_C_Σf_closed_form' rho' n' phi) in
                                        (n'', @bin C_Σf Σp _ falsity_on bb phi' psi')
  | @quant _ _ _ falsity_on qq phi => let (rho'_n' , phi'):= (C_form_to_C_Σf_closed_form' rho n  phi) in 
                                      let (rho', n') := rho'_n' in 
                                      (rho', n', @quant C_Σf Σp _ falsity_on qq phi') 
  end).
  rewrite plus_n_O.
  exact vv'.
Defined.

Definition C_form_to_Σf_form (phi: form C_Σf) :=
  let (n, phi'):= C_form_to_C_Σf_closed_form 0 (prepare_form phi) in 
  C_closed_form_to_Σf_form phi'.

Definition C_form_to_Σf_form' (rho:  nat -> @term C_Σf)(phi: form C_Σf) :=
  let (rho'_n, phi'):= C_form_to_C_Σf_closed_form' rho 0 (prepare_form phi) in 
  let (rho', n) := rho'_n in 
  (rho', C_closed_form_to_Σf_form phi').

Definition C_form_to_Σf_form_rho (rho:  nat -> @term C_Σf)(phi: form C_Σf) :=
  let (rho', _):= C_form_to_Σf_form' rho phi in rho'.

(*TO GET EASIER LIFE HERE, I HAD TO PUT DEFINED EVERYWHERE*)  

Lemma sanity_translation (rho rho':  nat -> @term C_Σf)(phi: form C_Σf)(phi': form Σf): 
  (rho', phi') = C_form_to_Σf_form' rho phi ->
  phi[rho] = (form_to_C_Σf_form phi')[rho'].
Proof.
  induction phi using form_ind_falsity;
  intros; simpl; cbn in H.  (*with (f:= falsity_on).*)
  + injection H; intros.
    rewrite H0.
    simpl. reflexivity. 
  + unfold C_form_to_Σf_form' in H.
    dependent destruction H.
   admit.
Admitted.

Lemma term_sanity_translation1 (trm : term Σf):
  C_term_to_Σf_term 0 (term_to_C_Σf_term trm) = trm.
Proof.
  induction trm; cbn.
  + reflexivity.
  + admit.
Admitted.

Lemma term_zero_const (trm : term Σf):
term_count_C (term_to_C_Σf_term trm) = 0.
Proof.
  induction trm; cbn.
  + reflexivity.
  + erewrite map_map. erewrite map_ext_in.
    2: intros;eapply IH; eauto.
    induction v0.
    * cbn. reflexivity.
    * cbn. eapply IHv0.
      intros. eapply IH. 
      eapply In_cons_tl; eauto.
Defined.

Lemma zero_const (phi : form Σf):
form_count_C (form_to_C_Σf_form phi) = 0.
Proof.
  induction phi using form_ind_falsity.
  + cbn. reflexivity.
  + unfold form_to_C_Σf_form. 
    unfold form_count_C.
    erewrite map_map. erewrite map_ext.
    2: intros; eapply term_zero_const.
    induction t.
    * cbn. reflexivity.
    * cbn. eapply IHt.
  + cbn.
    rewrite IHphi1.
    rewrite IHphi2.
    eauto.
  + cbn. eapply IHphi.
Defined.

Lemma sanity_translation1 (psi : form Σf):
 C_form_to_Σf_form (form_to_C_Σf_form psi) = psi.
Proof.
  induction psi using form_ind_falsity.
  + cbn. reflexivity.
  + cbn. unfold C_form_to_Σf_form.
    destruct C_form_to_C_Σf_closed_form eqn:H.
    unfold prepare_form in H.
    pose proof zero_const.
    (*unfold atom. 
    Search map.
    erewrite map_.
    2: eapply 
  unfold C_form_to_Σf_form.
  rewrite term_sanity_translation1.*)
  admit.
  + cbn. unfold C_form_to_Σf_form.
    destruct C_form_to_C_Σf_closed_form eqn:H.
    cbn in H.
    rewrite zero_const in H. rewrite zero_const in H. 
    simpl in H.
    remember H as H1.
   (* destruct (C_form_to_C_Σf_closed_form 0 (form_to_C_Σf_form psi1)) in H.
    destruct 
    unfold C_form_to_C_Σf_closed_form in H .
    cbn in H.
    unfold C_closed_form_to_Σf_form.
  
  rewrite <- IHpsi1. cbn.  *)
Admitted.

Lemma translation_spec phi:
  C_form_to_Σf_form' (fun x : nat => $ x) (form_to_C_Σf_form phi) = ((fun x : nat => $ x), phi).
Admitted.

Lemma term_to_C_Σf_term_closed:
  forall (trm: term  Σf),
  term_c_bounded 0 (term_to_C_Σf_term trm).
Proof.
  intros. 
  induction trm.
  + eapply bounded_var.
  + intros. fold term_to_C_Σf_term. cbn. constructor.
    Print Forall_map.
    (*
    intros. 
    erewrite Forall_map in IH. 
    unfold term_c_bounded.*)
  admit.
Admitted.

Lemma form_to_C_Σf_form_closed:
  forall (phi: form  Σf),
  c_bounded 0 (form_to_C_Σf_form phi).
Proof.
  intros. 
  induction phi using form_ind_falsity.
  + eapply bounded_falsity. 
  + intros. eapply bounded_p.
   admit.
  + intros. eapply bounded_bin; eauto.  
  + intros. eapply bounded_quant; eauto.
Admitted.  

Lemma form_to_C_Σf_form_bounded (n: nat)(phi: form  Σf):
  c_bounded n (form_to_C_Σf_form phi).
Proof.
  eapply c_bound_mon.
  2: eapply form_to_C_Σf_form_closed.
  eapply Nat.le_0_l.
Qed.

Lemma theory_to_C_Σf_theory_closed:
  forall (T : theory Σf),
  th_c_bounded 0 (theory_to_C_Σf_theory T). 
Proof.
  unfold th_c_bounded; intros.
  unfold theory_to_C_Σf_theory in H.
  destruct H as (phi', H).
  rewrite <- H.
  eapply form_to_C_Σf_form_closed.
Qed.

Lemma theory_to_C_Σf_theory_bounded (n: nat)(Gamma : theory Σf):
  th_c_bounded n (theory_to_C_Σf_theory Gamma).
Proof.
  eapply th_c_bound_mon.
  2: eapply theory_to_C_Σf_theory_closed. 
  eapply Nat.le_0_l.
Qed.

  (*scan a formula, 
    count how many constants (count), 
    shift it up of count 
    substitute each x with x_i and increase the counter
    
    the one wit the prime at the same time build the evaluation rho*)  
End Translations_Σf_C_Σf.

Print theory.
Arguments theory _ {_ _ _}.
Arguments form _ {_ _ _}. 
Search theory.

Definition prv_th {sigma:  funcs_signature}(T : theory sigma)(phi: form sigma) :=
  exists (Gamma : list (form sigma)), (forall psi:(form sigma), 
  List.In psi Gamma-> T psi) /\ Gamma ⊢I phi.

(*Definition prv_inf_ext (T: theory sigma)(phi: @form Σf _ _ _ ) :=
  exists (Gamma_fin : list form), (forall (psi:form), List.In psi Gamma_fin -> Gamma psi) /\ Gamma_fin ⊢I (form_to_C_Σf_form phi).*)

Notation "T ⊢ phi" := (prv_th T phi) (at level 55).  
(*Notation "A ⊢* phi" := (prv_inf_ext A phi) (at level 55).*)

Lemma Weak A B phi:
    A ⊢ phi -> (forall psi, A psi -> B psi) -> B ⊢ phi.
Proof.
  unfold "⊢" in *; intros.
  destruct H as (L, (H1, H2)).
  exists L; split.
  intros. eapply H0. eapply H1. eauto.
  eauto.   
Qed.
 
Definition consistent {sigma:  funcs_signature} (A: theory sigma):= (A ⊢ ⊥) -> False.  

Lemma consistent_imp_not_Gamma_bot{sigma:  funcs_signature}: 
  forall (T: theory sigma),
  consistent T -> T falsity -> False.
Proof.
  intros.
  unfold consistent in H.
  unfold prv_th in H.
  eapply H.
  exists [falsity]; split.
  intros. simpl in H1; destruct H1; [rewrite <- H1 | ]; eauto.
  eapply Ctx; eauto.
Qed.

Class n_saturated (n:nat)(Gamma: theory C_Σf) :=
  { 
    consist        : consistent Gamma;
    c_bound phi    : Gamma phi -> c_bounded (S n) phi;
    der_closed phi : Gamma ⊢ phi -> Gamma phi;
    prime phi psi  : Gamma ⊢ (@bin C_Σf Σp _ falsity_on Disj phi psi) -> ((Gamma phi) \/ (Gamma psi));
    ex_closed phi  : Gamma ⊢ (@quant C_Σf Σp _ falsity_on Ex phi) -> exists m c, m<=n /\ Gamma (phi[(@func C_Σf (inr (m, c)) (nil _) )..]);
  }.

About "⊑".  
(*
Definition th_incl {sigma: funcs_signature}(T1 T2: theory sigma) :=
  forall phi: form sigma, T1 phi -> T2 phi. 

Notation "A ⊑ B" := (th_incl A B) (at level 20).  


#[local] Hint Unfold consistent th_incl : core.
*)
Theorem WeakList {sigma: funcs_signature} A B phi :
  A ⊢I phi -> A <<= B -> B ⊢I phi.
Proof.
  intros H. revert B.
  induction H; intros B HB; try unshelve (solve [econstructor; auto with datatypes]); try now econstructor.
Qed.

(*ENUMERATIONS!!!*)
Variable enum_disj: nat -> nat -> form C_Σf*form C_Σf.

Definition enum_disj_1: nat -> nat -> form C_Σf:=
  fun N n => let  (phi, psi):= enum_disj N n in phi.
Definition enum_disj_2: nat -> nat -> form C_Σf:=
  fun N n => let  (phi, psi):= enum_disj N n in psi.

Hypothesis c_bound_enum_disj_1: forall N n,
                              c_bounded N (enum_disj_1 N n).

Hypothesis c_bound_enum_disj_2: forall N n,
                              c_bounded N (enum_disj_2 N n).

Hypothesis H_enum_disj: forall phi psi, forall N n,
                        c_bounded N phi ->  c_bounded N psi ->
                        exists m, m>=n /\ 
                        (phi = enum_disj_1 N m /\ psi = enum_disj_2 N m).

Variable enum_ex : nat -> nat -> form C_Σf.

Hypothesis c_bound_ex:  forall N n,
                              c_bounded N (enum_ex (N) n).

Hypothesis H_enum_ex : forall phi, forall N n, c_bounded N phi -> exists m, m>=n /\ enum_ex N m = (phi).


Definition Even n := exists m, n = 2*m.
Definition Odd n := exists m, n = 2*m+1.

Section Union. (*COPIED FROM TARSKI CONSTRUCTIONS, could not use it directly because of the connectives*)
  Arguments theory {_ _ _ _}.
  Definition econsistent T T' := T' ⊢ ⊥ -> T ⊢ ⊥.
  Variable f : nat -> theory.
  Hypothesis econsistent_f : forall n, econsistent (f n) (f (S n)).
  Hypothesis f_le : forall m n, m <= n -> f m ⊑ f n. (*Does this hold?*)

  Definition union (f : nat -> theory) := fun t => exists n, f n t.
  Lemma union_f phi :
    union f ⊢ phi -> exists n, f n ⊢ phi.
  Proof.
    intros (A & HA1 & HA2). enough (exists n, A ⊏ f n) as [n H] by now exists n, A.
    clear HA2; induction A.
    - exists 0; eauto with contains_theory.
    - destruct IHA as [n Hn]; destruct (HA1 a0) as [m Hm]; eauto with contains_theory.
      exists (max n m); intros ? []; subst.
      + eapply f_le; [apply PeanoNat.Nat.le_max_r | eauto with contains_theory]. 
      + eapply f_le; [apply PeanoNat.Nat.le_max_l | eauto with contains_theory].
  Qed.

  Lemma union_sub n :
    f n ⊑ union f.
  Proof.
    intros ? ?; exists n; eauto with contains_theory.
  Qed.

  Lemma union_econsistent :
    econsistent (f 0) (union f).
  Proof.
    intros [n H] % union_f. induction n; unfold econsistent in *; eauto.
  Qed.

  Lemma union_closed :
    (forall n, closed_T (f n)) -> closed_T (union f).
  Proof.
    intros f_closed phi [m H]. now eapply f_closed with (n := m) (phi := phi).
  Qed.
End Union.

(** LEMMA 

!!! FIX  enum_const 
!!! FIX  phi = (enum_ex n)[(enum_const k)..] *)

Definition Gamma_succ (G_k : theory C_Σf)(A: form C_Σf)(N k : nat) (*everything N bounded*): theory C_Σf:=
  (fun (phi : form C_Σf) => 
  (G_k phi) 
  \/ 
  (exists n, (k = 2*n) /\ (G_k ⊢ (quant Ex (enum_ex (S N) n)) /\ phi = (enum_ex (S N) n)[(func C_Σf (inr (N, k)) (nil _))..]    ))
  \/ 
  (exists n, (k = 2*n +1) /\ (G_k ⊢ (bin Disj (enum_disj_1 (S N) n) (enum_disj_2 (S N) n))) /\ phi = (enum_disj_1 (S N) n) /\ 
      (((extend G_k (enum_disj_1 (S N) n)) ⊢ (A) ) -> False))
  \/ 
  (exists n, (k = 2*n +1) /\ (G_k ⊢ (bin Disj (enum_disj_1 (S N) n) (enum_disj_2 (S N) n))) /\ phi = (enum_disj_2 (S N) n) /\ 
      ((extend G_k (enum_disj_1 (S N) n)) ⊢ (A) ))).

Fixpoint saturated_from_Gamma_0_fix (G_0: theory C_Σf)(A: form C_Σf)(N n: nat): theory C_Σf :=
  match n with
  | 0 => G_0
  | S n => Gamma_succ (saturated_from_Gamma_0_fix G_0 A N n) A N n
  end.

Definition saturated_from_Gamma_0 (G_0: theory C_Σf)(A: form C_Σf)(N: nat):= 
  union (saturated_from_Gamma_0_fix (G_0) A N).

Lemma union_sub' n :
    forall(G_0: theory C_Σf)(A: form C_Σf)(N: nat),
    (saturated_from_Gamma_0_fix (G_0) A N n) ⊑ saturated_from_Gamma_0 G_0 A N.
Proof.
  intros ? ?; exists n; eauto.
Qed.

Lemma saturated_from_Gamma_incl_G_0 (G_0: theory C_Σf)(A: form C_Σf)(N: nat):
  G_0  ⊑ saturated_from_Gamma_0 G_0 A N. 
Proof. 
  apply union_sub' with (n := 0).
Qed.

Lemma saturated_from_Gamma_incl_mon_S (G_0: theory C_Σf)(A: form C_Σf)(N : nat): 
  forall (n : nat),
    saturated_from_Gamma_0_fix G_0 A N n  ⊑ saturated_from_Gamma_0_fix G_0 A N (S n).
Proof.
  intros; unfold "⊑" in *; intros; eauto.
  simpl in *. unfold Gamma_succ. left. eauto.
Qed.

Lemma saturated_from_Gamma_incl_mon (G_0: theory C_Σf)(A: form C_Σf)(N : nat): 
  forall (n m : nat),
    n <=m -> saturated_from_Gamma_0_fix G_0 A N n ⊑ saturated_from_Gamma_0_fix G_0 A N m.
Proof.
  intros n m ll.
  induction ll;unfold "⊑"; eauto.
  intros. 
  eapply saturated_from_Gamma_incl_mon_S.
  eapply IHll; eauto. 
Qed.

Arguments prv {_ _ _}.
Arguments form {_ _ _} _.

Lemma prv_ind_intu_on :
  forall P : (list (form falsity_on) -> (form falsity_on) -> Prop),
    (forall (A : list (form falsity_on)) (phi psi : form falsity_on),
        prv intu (phi :: A) psi -> P (phi :: A) psi -> P A (phi → psi)) ->
    (forall (A : list (form falsity_on)) (phi psi : form falsity_on),
        prv intu A (phi → psi) -> P A (phi → psi) -> prv intu A phi -> P A phi -> P A psi) ->
    (forall (A : list (form falsity_on)) (phi : form falsity_on),
        prv intu (List.map (subst_form ↑) A) phi -> P (List.map (subst_form ↑) A) phi -> P A (∀ phi)) ->
    (forall  (A : list (form falsity_on)) (t : term) (phi : form falsity_on),
        prv intu A (∀ phi) -> P A (∀ phi) -> P A phi[t..]) ->
    (forall  (A : list (form falsity_on)) (t : term) (phi : form falsity_on),
        prv intu A phi[t..] -> P A phi[t..] -> P A (∃ phi)) ->
    (forall  (A : list (form falsity_on)) (phi psi : form falsity_on),
        prv intu A (∃ phi) -> P A (∃ phi) -> prv intu (phi :: [p[↑] | p ∈ A]) psi[↑] -> P (phi :: [p[↑] | p ∈ A]) psi[↑] -> P A psi) ->
    (forall  (A : list (form falsity_on)) (phi : form falsity_on), prv intu A ⊥ -> P A ⊥ -> P A phi) ->
    (forall  (A : list (form falsity_on)) (phi : form falsity_on), phi el A -> P A phi) ->
    (forall  (A : list (form falsity_on)) (phi psi : form falsity_on),
        prv intu A phi -> P A phi -> prv intu A psi -> P A psi -> P A (phi ∧ psi)) ->
    (forall  (A : list (form falsity_on)) (phi psi : form falsity_on),
        prv intu A (phi ∧ psi) -> P A (phi ∧ psi) -> P A phi) ->
    (forall  (A : list (form falsity_on)) (phi psi : form falsity_on),
        prv intu A (phi ∧ psi) -> P A (phi ∧ psi) -> P A psi) ->
    (forall  (A : list (form falsity_on)) (phi psi : form falsity_on),
        prv intu A phi -> P A phi -> P A (phi ∨ psi)) ->
    (forall  (A : list (form falsity_on)) (phi psi : form falsity_on),
        prv intu A psi -> P A psi -> P A (phi ∨ psi)) ->
    (forall  (A : list (form falsity_on)) (phi psi theta : form falsity_on),
        prv intu A (phi ∨ psi) ->
        P A (phi ∨ psi) ->
        prv intu (phi :: A) theta ->
        P (phi :: A) theta -> prv intu (psi :: A) theta -> P (psi :: A) theta -> P A theta) ->
    forall (l : list (form falsity_on)) (f14 : form falsity_on), prv intu l f14 -> P l f14.
Proof.
  intros.
  remember intu as temp.
  specialize (@prv_ind_full _ _ (fun lable => match lable with intu => P | _ => (fun _ _ => True) end));
  intros H';
  apply H' with (p := intu); clear H'. 
  all: intros; try destruct p; trivial;
  try eapply prv_intu_peirce in H14; 
  try eapply prv_intu_peirce in H16; 
  try eapply prv_intu_peirce in H18; 
  intuition eauto 2.
  rewrite Heqtemp in H13; eauto.
Qed.

Arguments form _ {_ _ _}.

Lemma prv_ext (T: theory Σf)(A: form Σf):
    T ⊢ A <-> theory_to_C_Σf_theory T  ⊢ form_to_C_Σf_form A.
Proof.
  admit.
  (*
  unfold "⊢".  
  intros; destruct H as (G, (H1, H)). 
  exists (List.map form_to_C_Σf_form G). split.
  + intros.
    unfold theory_to_C_Σf_theory.
    exists (C_form_to_Σf_form psi).
    eapply sanity_translation1.
  + (*rewrite <- List.Forall_map.*)

    (*eapply prv_ind_intu_on with (P:= fun G A => [form_to_C_Σf_form p | p ∈ G] ⊢I form_to_C_Σf_form A)*)
    (* THIS DOES NOT WORK!!!! *)
    remember intu as temp.
       eapply prv_ind_intu_on; eauto; intros; trivial. 
      - eapply II; eauto.
      - eapply IE; eauto.
      - eapply AllI; eauto.
      - eapply AllE; eauto.
      - eapply ExI; eauto.
      - eapply ExE; eauto.
      - eapply Exp; eauto.
      - eapply Ctx; eauto.
      - eapply CI; eauto.
      - eapply CE1; eauto.
      - eapply CE2; eauto.
      - eapply DI1; eauto.
      - eapply DI2; eauto.
      - eapply DE; eauto.
      - admit.
    *)
Admitted.

Lemma n_saturated_c_bound (G_0: theory C_Σf)(A: form C_Σf)(N : nat)(phi : form C_Σf):
  th_c_bounded N G_0 -> c_bounded N A ->  (G_0 ⊢ A -> False) ->
  forall n: nat, saturated_from_Gamma_0_fix G_0 A N n phi -> c_bounded (S N) phi.
Proof.
  intros.
  induction n; cbn in *.
  + eapply c_bound_mon.
    2: now eapply H. eapply Nat.le_succ_diag_r.
  + destruct H2 as [H2| [H3 | [H4 | H5]]].
    * eapply IHn; eauto.
    * destruct H3 as (k, (ev_k, (H3, Hpsi))).
      rewrite Hpsi.
      eapply c_bound_eval'.
      - eapply bounded_c; eauto.
      - eapply c_bound_ex.
    * destruct H4 as (k, (od_k, (HDisj, (Hpsi , H4)))).
      rewrite Hpsi.
      eapply c_bound_enum_disj_1.
    * destruct H5 as (k, (od_k, (HDisj, (Hpsi , H4)))).
      rewrite Hpsi.
      eapply c_bound_enum_disj_2.
Qed.

Lemma saturated_c_bound (G_0: theory C_Σf)(A: form C_Σf)(N : nat)(phi : form C_Σf):
  th_c_bounded N G_0 -> c_bounded N A ->  (G_0 ⊢ A -> False) ->
  saturated_from_Gamma_0 G_0 A N phi -> c_bounded (S N) phi.
Proof.
  intros GB AB HA H.
  unfold saturated_from_Gamma_0 in H.
  destruct H as (n, H).
  eapply n_saturated_c_bound; eauto.
Qed.

Lemma n_saturated_not_proves (G_0: theory C_Σf)(A': form C_Σf)(N : nat):
  (th_c_bounded N G_0) -> (c_bounded N A') ->
  (G_0 ⊢ A' -> False) ->
 forall n : nat, ((saturated_from_Gamma_0_fix G_0 A' N n  ⊢ A') -> False).
Proof.
  intros.
  induction n.
  + simpl. eauto.
  + cbn in H2.
    destruct H2 as (Delta, (Delta_incl, HD)). 
    unfold Gamma_succ in Delta_incl.
    admit.
Admitted.

Lemma saturated_not_proves (G_0: theory C_Σf)(A: form C_Σf)(N : nat):
   (th_c_bounded N G_0) -> (c_bounded N A) ->
   (G_0 ⊢ A -> False) ->
  ((saturated_from_Gamma_0 G_0 A N ⊢ A) -> False).
Proof.
  intros GB AB HA.
  intros [n H] % union_f. 
  2: eapply saturated_from_Gamma_incl_mon. 
  eapply n_saturated_not_proves; eauto.
Qed.

Lemma saturated_consistent (G_0: theory C_Σf)(A: form C_Σf)(N : nat):
  th_c_bounded N G_0 -> c_bounded N A ->  (G_0 ⊢ A -> False) ->
  consistent (saturated_from_Gamma_0 G_0 A N).
Proof.
  unfold consistent.
  intros.
  eapply saturated_not_proves; eauto.
  destruct H2 as (Delta, (Delta_incl, HD)). 
  exists Delta; split; eauto.
  eapply Exp; eauto.
Qed.

Lemma n_saturated_consistent (G_0: theory C_Σf)(A: form C_Σf)(N : nat):
  (th_c_bounded N G_0) -> (c_bounded N A) -> (G_0 ⊢ A -> False) ->
  forall n : nat, (th_c_bounded (S N) (saturated_from_Gamma_0_fix G_0 A N n)).
Proof.
  intros.
  induction n.
  + cbn. eapply th_c_bound_mon. 2: eauto.
    eapply Nat.le_succ_diag_r.
  + unfold th_c_bounded; intros.
    eapply n_saturated_c_bound; eauto. 
Qed.

Lemma saturated_iff (G_0: theory C_Σf)(A: form C_Σf)(N : nat):
  (th_c_bounded N G_0) -> (c_bounded N A) -> (G_0 ⊢ A -> False) ->
  forall (phi: form C_Σf),
  (saturated_from_Gamma_0 G_0 A N ⊢ phi -> saturated_from_Gamma_0 G_0 A N phi).
Proof.
Admitted.

Lemma saturated_prime (G_0: theory C_Σf)(A: form C_Σf)(N : nat)(phi psi : form C_Σf):
saturated_from_Gamma_0 G_0 A N ⊢ phi ∨ psi -> 
(saturated_from_Gamma_0 G_0 A N phi \/ saturated_from_Gamma_0 G_0 A N psi).
Proof.
Admitted. 

Lemma saturated_ex_closed (G_0: theory C_Σf)(A: form C_Σf)(N : nat)(phi: form C_Σf):
saturated_from_Gamma_0 G_0 A N ⊢ ∃ phi -> 
exists m c : nat, m <= N /\ saturated_from_Gamma_0 G_0 A N phi [(func (inr (m, c)) (nil term))..].
Proof.
Admitted. 

Lemma saturation_lemma (Gamma : theory C_Σf)(A: form C_Σf)(N: nat):
  th_c_bounded N Gamma -> c_bounded N A ->  (Gamma ⊢ A -> False) ->
  exists (Delta:  theory C_Σf), (Gamma ⊑ Delta /\  n_saturated N Delta /\ ((Delta ⊢ A) -> False) ).
Proof.
  intros.
  exists (saturated_from_Gamma_0 Gamma A N).
  split. eapply saturated_from_Gamma_incl_G_0.
  split. 2: eapply saturated_not_proves; eauto.
  eapply Build_n_saturated.
  + eapply saturated_consistent; eauto.
  + intros. eapply saturated_c_bound; eauto.
  + intros. eapply saturated_iff; eauto.
  + intros. eapply saturated_prime; eauto.
  + intros. eapply saturated_ex_closed; eauto. 
Qed.

Lemma Lindenbaum_lemma: 
  forall (Gamma : theory Σf)(A : form Σf)(N: nat),
  (Gamma ⊢ A -> False)  ->
  exists (Delta:  theory C_Σf), 
  ( theory_to_C_Σf_theory Gamma ⊑ Delta /\  
    n_saturated N Delta /\ 
    ((Delta ⊢ form_to_C_Σf_form A) -> False) ).
Proof.
  intros.
  eapply saturation_lemma.
  + eapply theory_to_C_Σf_theory_bounded.
  + eapply form_to_C_Σf_form_bounded.
  + intros. eapply H.
    eapply prv_ext; eauto.
Qed.  

(*CANONICAL FRAME*)
Class canonical_nodes:= 
{
  c_n_th : theory C_Σf;
  c_n_nat : nat;
  c_n_s : n_saturated c_n_nat c_n_th
}.
(*
Definition canonical_nodes := { G_n :  (theory C_Σf )*nat | let (Gamma, n) := G_n in 
  n_saturated n Gamma }. *)

Definition c_set: canonical_nodes -> (theory C_Σf) := 
  fun (G_n : canonical_nodes) => let (Gamma, n, H):= G_n in Gamma.

Definition c_nat: canonical_nodes -> nat := 
  fun (G_n : canonical_nodes) => let (Gamma, n, H):= G_n in n.   
                                  
Definition c_incl (Gamma Delta: canonical_nodes): Prop :=
  (c_set Gamma) ⊑ (c_set Delta) /\ (c_nat Gamma <= c_nat Delta).

Definition in_c_world (Gamma: canonical_nodes) (j: @term C_Σf): Prop :=
  term_c_bounded (S(c_nat Gamma)) j.

Lemma consistent_canonical_set (G_n: canonical_nodes):
  consistent (c_set G_n).
Proof.
  destruct G_n as (Gamma, n, satu). simpl. eauto using consist.
Qed.

Lemma iff_der_closed: 
  forall (G_n : canonical_nodes)(phi: form C_Σf), 
  (c_set G_n) ⊢ phi <-> (c_set G_n) phi.
Proof.
  intros; split; intros.
  destruct G_n as (Gamma, n, satu).
  + eapply der_closed; eauto.
  + unfold "⊢"; exists [phi]; split.
    ++ intros; simpl in H0; destruct H0; [rewrite <- H0|]; eauto.
    ++ eapply Ctx; eauto.
Qed.

Lemma n_saturated_nodes: 
forall (G_n : canonical_nodes),
n_saturated (c_nat G_n) (c_set G_n).
Proof.
intros.
destruct G_n as (Gamma, n, H). simpl.
eauto.
Qed.

Existing Instance Σf.
Context {HF : eq_dec Σf} {XHF : eq_dec C_Σf} {HP : eq_dec preds}.

Program Instance canonical_model_frm : kframe :=
    {|
      domain := (@term C_Σf);
      nodes := canonical_nodes;
      reachable := c_incl;
      world := in_c_world;
    |}.
  Next Obligation.
    unfold c_incl.
    split; eauto.
    unfold "⊑". eauto.
  Qed.
  Next Obligation.
    unfold c_incl in *.
    split. destruct H. destruct H0. 
    + unfold "⊑" in *. eauto.
    + transitivity (c_nat v0); now eauto using H, H0.
  Qed.
  Next Obligation.
    unfold c_incl in H; destruct H as (H1, H2).
    unfold in_c_world in *.
    dependent induction H0.
      * eauto using bounded_var.
      * eapply bounded_c. 
        eapply Nat.lt_le_trans.
        eapply H.
        eapply le_n_S.
        eapply H2. 
      * eapply bounded_f. intros. eapply term_c_bound_mon.
        2: eapply H. 
        eapply le_n_S. all: eauto. 
Qed.

Definition I_Gamma (Gamma: canonical_nodes): interp (@term C_Σf):=
{|
  i_func := fun (f: Σf)(vv: t (@term C_Σf) (ar_syms f)) => @func C_Σf (inl f) vv;
  i_atom := fun P (vv: t (@term C_Σf) (ar_preds P)) =>  
            (prv_th (c_set Gamma) (@atom C_Σf Σp _ falsity_on P vv));
|}.

 #[refine] Instance canonical_model : (@kmodel Σf Σp canonical_model_frm) := 
{|
   I:= fun Gamma =>  I_Gamma Gamma
|}.
Proof.
  + intros. reflexivity.
  + intros. unfold in_dom in *.
    unfold world in *; simpl in *; unfold in_c_world in *. 
    eapply bounded_f; eapply vv_in_dom.
  + intros. unfold i_atom in *; simpl in *.
    unfold c_incl in reach. eapply Weak; eauto.
    eapply reach.
  + intros. unfold in_dom in *.
    unfold world in *; simpl in *. unfold in_c_world in *.
    eapply iff_der_closed in H.
    eapply c_bound in H.
    Unshelve. 2: eapply n_saturated_nodes.
    eapply c_bound_p_term in H.
    eapply Forall_forall; eauto.
Defined.

Lemma good_var (G_n: canonical_nodes):
  good G_n (fun x : nat => $ x).
Proof.
  unfold good.
  intros. 
  enough (in_c_world G_n $ n). eapply H.
  unfold in_c_world. eapply bounded_var.
Qed.

Theorem Impl_inv' {sigma: funcs_signature} A phi psi:
    (A ⊢I phi → psi) <-> ((phi :: A) ⊢I psi).
Proof.
  split; intros.
  + eapply IE. 
    eapply WeakList. eapply H. eauto.
    eapply WeakList.
    enough ([phi] ⊢I phi). exact H0.
    eapply Ctx; eauto.
    eauto.
  + eapply II; eauto.
Qed.

Print "⋄".
Lemma Impl_inv {sigma: funcs_signature}{HS: eq_dec sigma} T phi psi:
  (T ⊢ phi → psi) <-> (T⋄phi  ⊢ psi ).
Proof.
  split; intros.
  + destruct H as (A, (HA, H)). 
    exists (phi::A); intros; split.
    intros. simpl in H0. destruct H0.
    * rewrite <- H0. right. reflexivity. 
    * left. eapply HA; eauto.
    * eapply Impl_inv'; eauto. 
  + eapply prv_T_impl.
    eapply H.
Qed.

Lemma All_inv {sigma: funcs_signature}{HS: eq_dec sigma} T phi N:
  th_c_bounded N T -> c_bounded N phi ->
  ( T ⊢ ∀ phi  <-> T  ⊢ phi[(@func C_Σf (inr (N, 0)) (nil term))..] ). 
Proof.
  intros. split; intros; destruct H1 as (A, (HA, HH)).
  +  exists A; split; eauto; eapply AllE; eauto.
  + unfold "⊢". admit.
Admitted.  

Axiom DNE : forall P:Prop, ((P -> False)-> False) -> P.  

Axiom EM:  forall (A: Prop), A \/ (A -> False).

(*
Lemma base_case_truth:
forall (G_n : nodes)(rho : nat -> @term C_Σf)(P0 : Σp)(vv : t term (ar_preds P0)),
  (c_set G_n ⊢ (atom P0 (map (subst_term rho) (map term_to_C_Σf_term t))) <-> 
  (c_set G_n ⊢ atom P0 (map (eval rho) t))).
Proof.
  intros. cbn.
  erewrite map_map.
  enough (@i_atom _ _ _ (I G_n) P0 (map (@eval _ _ _ (I G_n) rho) vv) <->
  c_set G_n ⊢ atom P0 (map (subst_term rho) (map term_to_C_Σf_term vv))).
  eapply H.
  split; intros.
  cbn in H. erewrite map_map. 
  Search eval.
  (*
  erewrite eval_comp.
  eapply H. *)
  admit.
  unfold i_atom.
  intuition.
  unfold i_atom. unfold I.
Admitted.  *)

Lemma asimpl_test_1 {sigma: funcs_signature} phi t rho :
    phi[up rho][t..] = phi[t.:rho].
Proof. 
  asimpl. reflexivity.
Qed.

Print eval.

Lemma truth_lemma_rho:
  forall (G_n : nodes)(phi: form Σf)(rho : nat -> @term C_Σf), 
  (forall n: nat, term_c_bounded (S(c_nat G_n)) (rho n)) ->
  ((c_set G_n) ((form_to_C_Σf_form phi)[rho])) <->
  @ksat Σf Σp canonical_model_frm canonical_model falsity_on G_n rho phi.
Proof.
  intros G_n phi; revert G_n.
  apply (form_ind_falsity (P:= fun phi => forall G_n  (rho : nat -> term), (forall n : nat, term_c_bounded (S(c_nat G_n)) (rho n)) -> c_set G_n (form_to_C_Σf_form phi) [rho] <-> rho ⊩( G_n, canonical_model) phi)); intros.  
  + split; intros; cbn.
    * eapply consist. eapply (iff_der_closed G_n); eauto.
      Unshelve. 2: eapply G_n.
    * cbn in H0; eauto.
  + erewrite <- iff_der_closed; cbn in *.
    erewrite map_map; erewrite map_ext. 
    split; intros; eapply H0. 
    intros; induction a0; cbn.
    * reflexivity.
    * cbn. f_equal.
      erewrite map_map.
      erewrite map_ext_in.
      2: eapply IH. reflexivity. (*I DO NOT KNOW HOW TO PUT THIS OUTSIDEEE GRR*)
  + cbn. destruct b0; split; intros.
    * eapply iff_der_closed in H2. split; destruct H2 as (Delta, (Delta_sub, HH)).
      - eapply CE1 in HH. 
        eapply H.
        eapply H1.
        eapply iff_der_closed.
        exists Delta.
        split. eapply Delta_sub.
        eapply HH.
      - eapply CE2 in HH. 
        eapply H0.
        eapply H1.
        eapply iff_der_closed.
        exists Delta.
        split. eapply Delta_sub.
        eapply HH.
    * eapply iff_der_closed.
      destruct H2.
      specialize (H G_n rho H1). eapply H in H2.
      specialize (H0 G_n rho H1). eapply H0 in H3.
      eapply iff_der_closed in H2.
      eapply iff_der_closed in H3.
      destruct H2 as (Delta1, (Delta_sub1, HH1)).
      destruct H3 as (Delta2, (Delta_sub2, HH2)).
      exists (Delta1 ++ Delta2). split.
      intros.  eapply in_app_or in H2; destruct H2.
      eapply Delta_sub1; eauto.
      eapply Delta_sub2; eauto.
      cbn.  eapply CI; eapply WeakList; eauto.
    * eapply iff_der_closed in H2. eapply prime in H2. destruct H2.
      - left. eapply H. eapply H1. eapply H2.
      - right. eapply H0. eapply H1. eapply H2.
    * eapply iff_der_closed.
      cbn. destruct H2.
      - eapply H in H2; eauto. eapply iff_der_closed in H2. 
        destruct H2 as (Delta, (Delta_sub, HH)).
        exists Delta; split; eauto.
        eapply DI1; eauto.
      - eapply H0 in H2; eauto. eapply iff_der_closed in H2. 
        destruct H2 as (Delta, (Delta_sub, HH)).
        exists Delta; split; eauto.
        eapply DI2; eauto.
    * eapply iff_der_closed in H2.
      eapply H0. 
      intros;  eapply term_c_bound_mon. 2: eapply H1.
      eapply le_n_S; eapply H3.
      eapply iff_der_closed.
      eapply H in H4. eapply iff_der_closed in H4.
      destruct H2 as (Delta1, (Delta_sub1, HH1)).
      destruct H4 as (Delta2, (Delta_sub2, HH2)).
      exists (Delta1 ++ Delta2).
      - split.
        intros.  
        eapply in_app_or in H2; destruct H2.
        eapply H3. eapply Delta_sub1; eauto.
        eapply Delta_sub2; eauto.
        eapply IE.
        eapply WeakList. eauto. eauto.
        eapply WeakList. eauto. eauto.
      - intros. eapply term_c_bound_mon.
        2: eapply H1. eapply le_n_S; eapply H3. 
    * eapply iff_der_closed.
      eapply DNE; intros.
      erewrite Impl_inv in H3.
      pose proof saturation_lemma.
      specialize (H4 ( c_set G_n ⋄ (form_to_C_Σf_form f1) [rho]) ((form_to_C_Σf_form f2) [rho]) (S (c_nat G_n))).
      assert (th_c_bounded (S (c_nat G_n)) (c_set G_n ⋄ (form_to_C_Σf_form f1) [rho])).
      unfold th_c_bounded. intros.
      destruct H5. eapply c_bound; eauto.
      rewrite H5. eapply c_bound_eval.
      intros. induction x; eauto. 
      eapply form_to_C_Σf_form_bounded.
      assert (c_bounded (S (c_nat G_n)) (form_to_C_Σf_form f2) [rho]).
      eapply c_bound_eval; eauto.
      eapply form_to_C_Σf_form_bounded.
      assert ((c_set G_n ⋄ (form_to_C_Σf_form f1) [rho] ⊢ (form_to_C_Σf_form f2) [rho] -> False)).
      cbn. eapply H3.
      specialize (H4 H5 H6 H7).
      destruct H4 as (Delta, (Delta_inc, (Delta_sat, HH))).
      assert ((forall n : nat, term_c_bounded (S (c_nat (Build_canonical_nodes Delta_sat))) (rho n))).
      intros. eapply term_c_bound_mon; cbn. 2: eauto.
      eapply le_n_S; eauto.  
      specialize (H0 (Build_canonical_nodes Delta_sat) rho H4).
      erewrite <- iff_der_closed in H0. cbn in H0.
      erewrite H0 in HH.
      eapply HH. 
      eapply H2.
      - unfold c_incl; split; cbn; eauto.
        transitivity (c_set G_n ⋄ (form_to_C_Σf_form f1) [rho]); eauto.
        left; eauto.
      - eapply H; eauto. eapply Delta_inc. right. reflexivity.  
  + destruct q; cbn; split.
    * intros H1 G_n' G_incl j Hin.
      eapply H. 
      intros. induction n; cbn; eauto.
      eapply term_c_bound_mon. 2: eapply H0.
      eapply le_n_S; eapply G_incl.
      eapply iff_der_closed in H1.
      destruct H1 as (Delta, (Delta_sub, HH)).
      eapply iff_der_closed.
      exists Delta. split.
      intros. eapply G_incl. eapply Delta_sub; eauto.
      eapply (@AllE _ _ _ _ _ j) in HH.
      asimpl in HH; eauto.
    * intros. 
      rewrite <- iff_der_closed.
      eapply DNE; intros.
      pose proof (saturation_lemma).
      specialize (H3  (c_set G_n) ( (∀ (form_to_C_Σf_form f2)) [rho]) (S (c_nat G_n))).
      assert (th_c_bounded (S (c_nat G_n)) (c_set G_n) ).
      unfold th_c_bounded; intros; eapply c_bound; eauto.
      assert (c_bounded (S (c_nat G_n)) (∀ (form_to_C_Σf_form f2)) [rho]).
      eapply c_bound_eval; eauto.
      eapply bounded_quant; eapply form_to_C_Σf_form_bounded.
      specialize (H3 H4 H5 H2).
      destruct H3 as (Delta, (Delta_inc, (Delta_sat, HH))).
      eapply HH. cbn.
      assert (Delta = c_set (Build_canonical_nodes Delta_sat)). eauto.
      rewrite H3.
      eapply (@All_inv _ _ _ _ (S (c_nat G_n))).
      admit. 
      admit.
      eapply iff_der_closed. asimpl.
      eapply H.
      cbn. admit.
      eapply H1; eauto.
      unfold c_incl; split; cbn; eauto using Delta_inc.
      unfold in_c_world.
      eapply bounded_c. cbn. eauto. 
      Unshelve. exact (c_nat G_n) . all: eapply n_saturated_nodes.
    * intros; eapply iff_der_closed in H1. cbn in H1.
      eapply (@ex_closed (c_nat G_n) _ _ ) in H1.
      destruct H1 as (m, (c, (ineq_mc, H1))).
      eapply iff_der_closed in H1.
      exists ((@func C_Σf (inr (m, c)) (nil term))). split.
      cbn. unfold in_c_world. eapply bounded_c.
      eapply Arith_base.le_lt_n_Sm_stt; eauto. 
      eapply H.
      intros n. induction n.
      unfold in_c_world. eapply bounded_c.
      eapply Arith_base.le_lt_n_Sm_stt; eauto.  
      cbn. eapply H0.
      eapply iff_der_closed.
      asimpl in H1; eauto.
    * intros; eapply iff_der_closed. 
      cbn in H1. 
      destruct H1 as (j, (j_incl, HH)).
      eapply H in HH.
      eapply iff_der_closed in HH.
      destruct HH as (Delta, (Delta_sub, HH)).
      exists Delta; split; eauto.
      cbn.
      eapply ExI.
      asimpl; eauto.
      intros n. induction n; cbn; eauto.
Admitted.

Existing Instance C_Σf.

Definition kvalid_theo {sigma: funcs_signature}(T : theory sigma)(phi: form sigma) :=
  forall (M: kmodel) (u: nodes) (rho: nat -> domain),
    good u rho -> (forall psi, T psi -> @ksat sigma _ _ M _ u rho psi) ->
    @ksat sigma _ _ M _ u rho phi.

Notation "T '⊩' phi" := (kvalid_theo T phi) (at level 20). 

Theorem completeness: 
forall (T: theory Σf)(phi : form Σf),
(T ⊩ phi -> T ⊢ phi).
Proof.
  intros T phi H.
  eapply DNE; intros.
  pose proof (Lindenbaum_lemma 0 H0).
  destruct H1 as (Delta, (Hinc, (Hsat, H1))).
  eapply H1.
  eapply (iff_der_closed (Build_canonical_nodes Hsat) (form_to_C_Σf_form phi)); simpl.
  pose proof (truth_lemma_rho).
  specialize (H2 (Build_canonical_nodes Hsat) (phi) (fun x => var x)); simpl in H2.
  rewrite <- subst_var.
  eapply H2. 
  intros. eapply bounded_var.
  eapply H.
  eapply good_var.
  intros.
  eapply truth_lemma_rho.
  intros. eapply bounded_var.
  eapply iff_der_closed.
  cbn. rewrite subst_var.
  unfold  "⊢".
  exists [form_to_C_Σf_form psi]; split.
  intros. simpl in H4; destruct H4.
  rewrite <- H4. eapply Hinc. 
  unfold  theory_to_C_Σf_theory.
  unfold "∈ ". exists psi. reflexivity. eauto.  
  eapply Ctx. eauto.
Qed.
End Completeness.
