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

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
From Undecidability Require Import FOL.Syntax.Core.
Import FullSyntax.
Export FullSyntax.

Lemma boh:
  forall (A B: Prop), (A <-> B)-> ((A -> False) <-> (B -> False)).
Proof.
  intros.
  split; intros.
  1, 2:eapply H0; eapply H; eapply H1.
Qed.

Lemma boh2: 
  forall (A B: Prop), (A \/ B) -> (A -> False) -> B.
Proof.
  intros. destruct H. apply H0 in H; eauto. eauto.
Qed.

Lemma boh3: 
  forall (A B C: Prop), ((A /\ B) -> C) <->(A -> B -> C).
Proof.
  split; intros; eapply H;
  eauto; destruct H0; eauto.
Qed.

Lemma forall_not_exists_not : 
  forall (X: Type) (A: X -> Prop), 
    (forall x: X, A x) -> ((exists x: X, A x -> False) -> False).
Proof.
    intros.
    destruct H0.
    specialize (H0 (H x)).
    apply H0.
Qed.

Lemma existsl_not_forall_not : 
  forall (X: Type) (A: X -> Prop), 
    (exists x: X, A x) ->((forall x: X, A x -> False) -> False).
Proof.
  intros.
  destruct H.
  specialize (H0 x H); eauto.
Qed.

Definition WEM :=
  forall P: Prop, (P -> False) \/ ((P -> False) -> False).

Definition DNS :=
  forall (X: Type) (A: X -> Prop),
  forall x: X, ((A x -> False) -> False) -> (((forall x: X, A x ) -> False) -> False).


Lemma question :
  forall (X: Type)(A: X -> Prop),
  WEM ->
  (((exists x, A x) -> False) -> False) -> exists x, ((A x -> False) -> False) .
Proof.
  intros.
  unfold WEM in H.
  


Lemma WEM_implies_DNS : 
  WEM -> DNS.
Proof.
  unfold DNS.
  intros.
  unfold WEM in H.
  pose proof (H (exists x: X, (A x -> A x))).
  destruct H2.
  * eapply H0. intros. eapply H2. exists x. intros. auto.
  * eapply H0. intros. eapply   
  eapply H1.
  intros.

  apply (H1 (H2 x)).
Qed.



Locate prv.

Section intu_ind.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.



  Lemma prv_ind_full :
  forall P : falsity_flag -> list (form _) -> (form _) -> Prop,
    (forall (ff : falsity_flag) (A : list form) (phi psi : form),
        (phi :: A) ⊢I psi -> P ff (phi :: A) psi -> P ff A (phi → psi)) ->
    (forall (ff : falsity_flag)(A : list form) (phi psi : form),
        A ⊢I phi → psi -> P ff A (phi → psi) -> A ⊢I phi -> P ff A phi -> P ff A psi) ->
    (forall (ff : falsity_flag) (A : list form) (phi : form),
        (map (subst_form ↑) A) ⊢I phi -> P ff (map (subst_form ↑) A) phi -> P ff A (∀ phi)) ->
    (forall (ff : falsity_flag) (A : list form) (t : term) (phi : form),
        A ⊢I ∀ phi -> P ff A (∀ phi) -> P ff A phi[t..]) ->
    (forall (ff : falsity_flag) (A : list form) (t : term) (phi : form),
        A ⊢I phi[t..] -> P ff A phi[t..] -> P ff A (∃ phi)) ->
    (forall (ff : falsity_flag) (A : list form) (phi psi : form),
        A ⊢I ∃ phi ->
              P ff A (∃ phi) ->
              (phi :: [p[↑] | p ∈ A]) ⊢I psi[↑] -> P ff (phi :: [p[↑] | p ∈ A]) psi[↑] -> P ff A psi) ->
    (forall  (A : list form) (phi : form), A ⊢I ⊥ -> P falsity_on A ⊥ -> P falsity_on A phi) ->
    (forall (ff : falsity_flag) (A : list form) (phi : form), phi el A -> P ff A phi) ->
    (forall (ff : falsity_flag) (A : list form) (phi psi : form),
        A ⊢I phi -> P ff A phi -> A ⊢I psi -> P ff A psi -> P ff A (phi ∧ psi)) ->
    (forall (ff : falsity_flag) (A : list form) (phi psi : form),
        A ⊢I phi ∧ psi -> P ff A (phi ∧ psi) -> P ff A phi) ->
    (forall (ff : falsity_flag) (A : list form) (phi psi : form),
        A ⊢I phi ∧ psi -> P ff A (phi ∧ psi) -> P ff A psi) ->
    (forall (ff : falsity_flag) (A : list form) (phi psi : form),
        A ⊢I phi -> P ff A phi -> P ff A (phi ∨ psi)) ->
    (forall (ff : falsity_flag) (A : list form) (phi psi : form),
        A ⊢I psi -> P ff A psi -> P ff A (phi ∨ psi)) ->
    (forall (ff : falsity_flag) (A : list form) (phi psi theta : form),
        A ⊢I phi ∨ psi ->
        P ff A (phi ∨ psi) ->
        (phi :: A) ⊢I theta ->
        P ff (phi :: A) theta -> (psi :: A) ⊢I theta -> P ff (psi :: A) theta -> P ff A theta) ->
    forall (ff: falsity_flag) (l : list form) (f14 : form), l ⊢I f14 -> P ff l f14.
Proof.
  intros. specialize (@prv_ind _ _ (fun ff => match ff with falsity_on => P | _ => fun _ _ _ => True end)). intros H'.
  apply H' with (ff := falsity_on); clear H'. all: intros; try destruct ff; trivial. all: intuition eauto 2.
Qed.


Inductive my_prv : forall (ff : falsity_flag) (p : peirce), list form -> form -> Prop :=
  | II {ff} {p} A phi psi : my_prv _ (phi::A)  psi -> my_prv _ A  (phi → psi)
  | Exp {p} A phi : my_prv p A falsity -> my_prv p A phi
  | Pc {ff} A phi psi : my_prv class A (((phi → psi) → phi) → phi).


Lemma my_prv_ind' {ff: falsity_flag}:
  match ff with 
  | falsity_on => (forall P: list (form falsity_on ) -> form falsity_on -> Prop,
                  (forall (A : list (form falsity_on)) (phi psi : (form falsity_on)),
                      @my_prv falsity_on intu (phi::A)  psi -> P (phi::A)  psi -> P A (phi → psi)) ->
                  (forall (A : list (form falsity_on)) (phi  : (form falsity_on)),
                      @my_prv falsity_on intu A falsity -> P A falsity -> P A phi) ->
                   forall (l : list form) (fin_form : form falsity_on), my_prv intu l fin_form -> P l fin_form)
  | falsity_off => (forall P: list (form _ ) -> form _ -> Prop,
                  (forall (A : list (form _)) (phi psi : (form _)),
                      @my_prv ff intu (phi::A)  psi -> P (phi::A)  psi -> P A (phi → psi)) ->
                  forall (l : list form) (fin_form : form ), my_prv intu l fin_form -> P l fin_form)
                  end.
Proof.
  destruct ff. intros. 

  specialize (my_prv_ind' (fun ff => match ff with 
                                      | falsity_on =>  (fun p => match p with 
                                                        | intu => P intu 
                                                        | _ => fun  _ _ => True end)
                                      | falsity_off =>            => fun  _ _ _=> True end)). 
  specialize (@my_prv falsity_on intu).

 














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

(*
instead of stating this with "if x is not free in psi", I will state it with "if psi is a colsed formula" 


    Lemma k_bounded_eval_t n t (M: kmodel)(u : nodes)(rho sigma: nat -> my_KripkeCompleteness.domain):
      (forall k, n > k -> rho k = sigma k) -> bounded_t n t -> eval (I u) rho t = eval (I u) sigma t.
    Proof.
      intros H. induction 1; cbn; auto.
      f_equal. now apply Vector.map_ext_in.
    Qed.

    Lemma ksat_closed (M: kmodel)(u : nodes)(rho sigma: nat -> my_KripkeCompleteness.domain)(psi: form) :
      closed psi -> good u rho -> good u sigma -> ksat u rho psi <-> ksat u sigma psi.
    Proof.
      intros H gdr gds; 
      induction psi; split; intros.
      1, 2: simpl in H0. 1, 2: eapply H0.
      1, 2: simpl in H0. simpl. 1, 2: eapply H0.
      erewrite ksat_ext.
      1, 4: erewrite <-ksat_comp.
      1, 3: erewrite bounded_0_subst.
      all: eauto using good_shift, good_mon, reach_tran.

      induction psi; eauto; try tauto; rewrite <- bounded_0_subst.
      * eapply  
    Qed.



    Lemma forall_gen (M: kmodel)(rho: nat -> my_KripkeCompleteness.domain)(phi psi: form):
        forall u : nodes, closed psi -> good u rho ->
        ksat u rho (bin Impl (bin Disj (quant All  phi) (psi)) (quant All (bin Disj phi (psi)))).
    Proof.
      cbn; intros.
      destruct H2.
      + left. eapply H2; eauto.
      +  right. eapply ksat_ext. eauto using good_shift, good_mon, reach_tran.
      2: erewrite <-ksat_comp. 
      2: erewrite bounded_0_subst. 2: eapply ksat_mon. 4: eapply H2.
      all: eauto using reach_tran, good_mon, H.
      intros. unfold ">>".
      Print eval. induction x; simpl. Locate eval.
      
      let ρ := up in 1.
      all:
      
      eapply ksat_ext. 3: eapply ksat_mon. 5: eapply H2. 
        all: eauto using good_shift, good_mon, reach_tran.
        intros.  
    Qed.
    


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
*)