Require Export Basics.
Require Import List.
Require Import Relation_Operators.
Require Import Autosubst.Autosubst.
Require Import Lia.

(* I again used the autosubst library *)

Module System_F.

  Ltac smash := repeat split; eauto.

  Open Scope list_scope.

  #[export] Hint Resolve Operators_Properties.clos_rst_is_equiv : core.
  #[export] Hint Resolve Operators_Properties.clos_rt_is_preorder : core.

  (* I referenced this document for dealing with two-leveled de Bruijn indices: *)
  (* https://www.ps.uni-saarland.de/autosubst/doc/Ssr.SystemF_CBV.html *)

  Inductive tipe :=
  | Unit
  | Arrow (t1 : tipe) (t2 : tipe)
  | TVar (v : var)
  | All (t : {bind tipe}).

  Notation " T '→' S " := (Arrow T S) (at level 99, right associativity).
  (* Notation " T '∀' S " := (Forall T S) (at level 97). *)

  Inductive expr :=
  | EApp (e1 : expr) (e2 : expr)
  | EAbs (t : tipe) (e : {bind expr})
  | TApp (e : expr) (t : tipe)
  | TAbs (e : {bind tipe in expr})
  | Var (x : var)
  | Null.

  (* Let Autosubst take care of substitution *)
  #[export] Instance Ids_type : Ids tipe. derive. Defined.
  #[export] Instance Rename_type : Rename tipe. derive. Defined.
  #[export] Instance Subst_type : Subst tipe. derive. Defined.
  #[export] Instance SubstLemmas_type : SubstLemmas tipe. derive. Qed.
  #[export] Instance HSubst_expr : HSubst tipe expr. derive. Defined.
  #[export] Instance Ids_expr : Ids expr. derive. Defined.
  #[export] Instance Rename_expr : Rename expr. derive. Defined.
  #[export] Instance Subst_expr : Subst expr. derive. Defined.
  #[export] Instance HSubstLemmas_expr : HSubstLemmas tipe expr. derive. Qed.
  (* This line needs to come before the next one *)
  #[export] Instance SubstHSubstComp_type_expr : SubstHSubstComp tipe expr. derive. Qed.
  #[export] Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

  Inductive value : expr -> Prop :=
  | value_eabs e t : value (EAbs e t)
  | value_tabs e : value (TAbs e)
  | value_null : value Null.
  #[export] Hint Constructors value : core.

  (** Small step CBV beta reduction.  *)
  Reserved Notation " e '⇒' f " (at level 50).
  Inductive step : expr -> expr -> Prop :=
  | cbv_efun e1 e2 e1' : e1 ⇒ e1' -> (EApp e1 e2) ⇒ (EApp e1' e2)
  | cbv_earg t e e2 e2' : e2 ⇒ e2' -> (EApp (EAbs t e) e2) ⇒ (EApp (EAbs t e) e2')
  | cbv_esub t e v : value v -> EApp (EAbs t e) v ⇒ (e.[v/])
  | cbv_tfun e e' t : e ⇒ e' -> (TApp e t) ⇒ (TApp e' t)
  | cbv_tsub e t : TApp (TAbs e) t ⇒ e.|[t/]
  where " e '⇒' f " := (step e f).
  #[export] Hint Constructors step : core.

  (** Multi-step relation *)
  Definition multistep := clos_refl_trans_n1 _ step.
  #[export] Hint Constructors clos_refl_trans_n1 : core.
  Notation "e '⇒*' f" := (multistep e f) (at level 20).

  Lemma multistep_trans : forall e e' e'', e ⇒* e' -> e' ⇒* e'' -> e ⇒* e''.
  Proof.
    intros. induction H0.
    - auto.
    - apply rtn1_trans with (y := y); auto.
  Qed.
  #[export] Hint Resolve multistep_trans : core.

  Lemma multistep_refl : forall e, e ⇒* e.
  Proof. intros. apply rtn1_refl. Qed.
  #[export] Hint Resolve multistep_refl : core.

  Lemma multistep_once : forall e e', e ⇒ e' -> e ⇒* e'.
  Proof. intros. apply rtn1_trans with (y := e); eauto. Qed.
  #[export] Hint Resolve multistep_once : core.

  Definition beta_equiv := clos_refl_sym_trans _ step.
  #[export] Hint Constructors clos_refl_sym_trans: core.
  Notation "e '≡' f" := (beta_equiv e f) (at level 20).

  Lemma multistep_implies_beta : forall e e', e ⇒* e' -> e ≡ e'.
  Proof. intros. unfold beta_equiv. induction H; eauto. Qed.

  (* The free expression variable context is a stack, with the head being the most recently bound variable *)
  Definition ev_context : Type := List.list tipe.

  (** Since we're using de Bruijn indices, the type context just limits how many type variables you can have *)
  Definition tv_context : Type := nat.

  Definition lookup : ev_context -> nat -> option tipe := @nth_error tipe.

  (* A type is well-formed if it contains only FTV from the TV context *)
  Inductive well_formed_tipe : tv_context -> tipe -> Prop :=
  | unit_well_formed_tipe Δ : well_formed_tipe Δ Unit
  | tvar_well_formed_tipe Δ (X : var) : PeanoNat.Nat.le X Δ -> well_formed_tipe Δ (TVar X)
  | arrow_well_formed_tipe Δ t1 t2 : well_formed_tipe Δ t1 -> well_formed_tipe Δ t2 -> well_formed_tipe Δ (Arrow t1 t2)
  | forall_well_formed_tipe Δ t : well_formed_tipe (S Δ) t -> well_formed_tipe Δ (All t).

  (* A context is well-formed if every type in it is well-formed *)
  Inductive well_formed_ctxt : tv_context -> ev_context -> Prop :=
  | nil_well_formed_ctxt Δ : well_formed_ctxt Δ nil
  | cons_well_formed_ctxt Δ t Γ : well_formed_ctxt Δ Γ -> well_formed_ctxt Δ (t :: Γ).

  Reserved Notation " Δ ';' Γ '⊢' e ':::' t " (at level 96).
  Inductive typing : tv_context -> ev_context -> expr -> tipe -> Prop :=
  | arrow_intro Δ Γ e t1 t2 : well_formed_tipe Δ t1 -> Δ;(t1 :: Γ) ⊢ e ::: t2 -> Δ;Γ ⊢ (EAbs t1 e) ::: (t1 → t2)
  | arrow_elim Δ Γ e1 e2 t1 t2 : Δ;Γ ⊢ e1 ::: (t1 → t2) -> Δ;Γ ⊢ e2 ::: t1 -> Δ;Γ ⊢ (EApp e1 e2) ::: t2
  | all_intro Δ Γ e t : (S Δ);Γ ⊢ e ::: t -> Δ;Γ ⊢ (TAbs e) ::: (All t)
  | all_elim Δ Γ e t1 t2 : Δ;Γ ⊢ e ::: (All t1) -> Δ;Γ ⊢ (TApp e t2) ::: t1.[t2/]
  | unit_intro Δ Γ : Δ;Γ ⊢ Null ::: Unit
  | axiom_rule Δ Γ n t : well_formed_tipe Δ t -> lookup Γ n = Some t -> Δ;Γ ⊢ (Var n) ::: t
  where " Δ ';' Γ '⊢' e ':::' t " := (typing Δ Γ e t).
  #[export] Hint Constructors typing : core.

  Notation "∙;∙ '⊢' e ':::' t " := (0;nil ⊢ e ::: t) (at level 99).

  Notation expr_rel := (Relation_Definitions.relation expr).

  Definition triple : Type := (tipe * tipe) * expr_rel.

  Definition Rel t1 t2 (R : expr_rel) : Prop := forall v1 v2, R v1 v2 -> value v1 /\ value v2 /\ (∙;∙ ⊢ v1 ::: t1) /\ (∙;∙ ⊢ v2 ::: t2).

  Definition pi1_ρ := fun ρ : var -> triple => fun n => fst (fst (ρ n)).

  Definition pi2_ρ := fun ρ : var -> triple => fun n => snd (fst (ρ n)).

  (* Lemma good_prepend t1 t2 R (g : sig good_rel_map) : Rel t1 t2 R -> let ρ' := (((t1, t2), R) .: (proj1_sig g)) in { ρ' : var -> triple | good_rel_map ρ' }. *)
  (* Proof. *)
  (*   intros. unfold good_rel_map. destruct g as [m Ev]. exists m. destruct n; try subst ρ'; try simpl in ρ'; unfold good_rel_map in Ev; apply Ev. *)
  (* Qed. *)

  Fixpoint V ρ t v1 v2 {struct t} : Prop :=
    let E ρ t e1 e2 := exists v1 v2, (0;nil ⊢ v1 ::: t.[pi1_ρ ρ]) /\ (0;nil ⊢ v2 ::: t.[pi2_ρ ρ]) /\ e1 ⇒* v1 /\ e2 ⇒* v2 /\ V ρ t v1 v2 in
    match t with
    | Unit => v1 = Null /\ v2 = Null
    | TVar n => snd (ρ n) v1 v2
    | Arrow t1 t2 => exists (e1 e2 : {bind expr}), v1 = EAbs t1.[pi1_ρ ρ] e1 /\ v2 = EAbs t1.[pi2_ρ ρ] e2 /\ (forall v1' v2', V ρ t1 v1' v2' -> E ρ t2 (e1.[v1'/]) (e2.[v2'/]))
    | All t0 => exists e1 e2 : expr, v1 = TAbs e1 /\ v2 = TAbs e2 /\ forall t1 t2 R, forall (evidence : Rel t1 t2 R), E (((t1, t2), R) .: ρ) t0 (e1.|[t1/]) (e2.|[t2/])
    end.

  (* Definition E ρ t e1 e2 := ((0;nil ⊢ e1 ::: t.[pi1_ρ ρ]) /\ (0;nil ⊢ e2 ::: t.[pi2_ρ ρ]) /\ exists v1 v2, e1 ⇒* v1 /\ e2 ⇒* v2 /\ V ρ t v1 v2). *)
  Definition E ρ t e1 e2 := exists v1 v2, (∙;∙ ⊢ v1 ::: t.[pi1_ρ ρ]) /\ (∙;∙ ⊢ v2 ::: t.[pi2_ρ ρ]) /\ e1 ⇒* v1 /\ e2 ⇒* v2 /\ V ρ t v1 v2.

  Lemma app_fun_steps_steps : forall e e' e'', e ⇒* e' -> (EApp e e'') ⇒* (EApp e' e'').
  Proof. intros. induction H; eauto. Qed.
  #[export] Hint Resolve app_fun_steps_steps : core.

  Lemma app_arg_steps_steps : forall e e' e'' t, e' ⇒* e'' -> (EApp (EAbs t e) e') ⇒* (EApp (EAbs t e) e'').
  Proof. intros. induction H; eauto. Qed.
  #[export] Hint Resolve app_arg_steps_steps : core.

  Lemma tapp_fun_steps_steps :  forall e e' t, e ⇒* e' -> (TApp e t) ⇒* (TApp e' t).
  Proof. intros. induction H; eauto. Qed.
  #[export] Hint Resolve tapp_fun_steps_steps : core.

  (* This is the expression Λ X. λ x:X. x *)
  Example polymorphic_identity : expr :=
    TAbs (EAbs (TVar 0) (Var 0)).

  Definition parallel_subst : Type := nat -> expr.

  Inductive good_exp_maps : ev_context -> (var -> triple) -> parallel_subst -> parallel_subst -> Prop :=
  | nil_good_exp_map ρ γ1 γ2 : good_exp_maps nil ρ γ1 γ2
  | cons_good_exp_map ρ t Γ γ1 γ2 v1 v2 : good_exp_maps Γ ρ γ1 γ2 -> V ρ t v1 v2 -> good_exp_maps (t :: Γ) ρ (v1 .: γ1) (v2 .: γ2).
  #[export] Hint Constructors good_exp_maps : core.

  Inductive good_rel_map : tv_context -> (var -> triple) -> Prop :=
  | Z_good_rel_map ρ : good_rel_map 0 ρ
  | S_good_rel_map n ρ t1 t2 R: good_rel_map n ρ -> Rel t1 t2 R -> good_rel_map (S n) ((t1, t2, R) .: ρ).
  #[export] Hint Constructors good_rel_map : core.

  Definition semantically_related (Δ : tv_context) Γ e1 e2 t :=
    (Δ;Γ ⊢ e1 ::: t) /\ (Δ;Γ ⊢ e2 ::: t) /\
    forall ρ γ1 γ2, good_rel_map Δ ρ -> good_exp_maps Γ ρ γ1 γ2 ->
               E ρ t ((e1.[γ1]).|[pi1_ρ ρ]) ((e2.[γ2]).|[pi2_ρ ρ]).
  Notation "Δ ';' Γ ⊨ e '~' f ':::' t" := (semantically_related Δ Γ e f t) (at level 96).

  Lemma autosubst_help : forall e γ v, e.[up γ].[v/] = e.[v .: γ].
  Proof. intros. autosubst. Qed.

  Lemma closed_terms_invariant_γ : forall e t γ, (0;nil ⊢ e ::: t) -> e.[γ] = e.
  Proof.
    intros. simpl. generalize dependent γ. induction H; intros.
    - simpl. rewrite IHtyping. reflexivity.
    - simpl. rewrite (IHtyping1 γ), (IHtyping2 γ). reflexivity.
    - simpl. rewrite (IHtyping (γ >>| ren (+1))). reflexivity.
    - simpl. rewrite IHtyping. reflexivity.
    - reflexivity.
    - admit.
  Admitted.

  (* https://cs.au.dk/~birke/papers/AnIntroductionToLogicalRelations.pdf *)
  Lemma compositionality : forall Δ t t' ρ,
      well_formed_tipe Δ t' -> well_formed_tipe (S Δ) t -> good_rel_map Δ ρ ->
      forall v1 v2, V ρ t.[t'/] v1 v2 <-> V (((t'.[pi1_ρ ρ], t'.[pi2_ρ ρ]), V ρ t') .: ρ) t v1 v2.
  Proof.
    intros. induction t'; split.
    -


  (** Fundamental theorem of logical relations for System F : Parametricity *)
  Theorem parametricity : forall Δ Γ e t, Δ;Γ ⊢ e ::: t -> Δ;Γ ⊨ e ~ e ::: t.
  Proof.
    intros. unfold semantically_related. unfold E. smash. intros ρ γ1 γ2. remember (pi1_ρ ρ) as ρ1. remember (pi2_ρ ρ) as ρ2. generalize dependent γ2. generalize dependent γ1. induction H; intros.
    (* EAbs *)
    - simpl. exists (EAbs t1.[ρ1] e.[up γ1].|[ρ1]), (EAbs t1.[ρ2] e.[up γ2].|[ρ2]). smash.
      + apply arrow_intro.

  (** Strong normalization of CBV STLC *)
  Theorem strong_normalization : forall e t, ∅ ⊢ e ::: t -> exists v, value v /\ e ⇒* v.
  Proof.
    intros. apply (fundamental_theorem nil e t) in H. unfold semant_typing in H. specialize H with (@ids expr Ids_expr). rewrite subst_id in H. destruct H. apply subst_empty. exists x. split; destruct H; (try apply (V_implies_value t); auto).
  Qed.

End System_F.