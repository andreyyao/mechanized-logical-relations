Require Export Basics.
Require Import List.
Require Import Relation_Operators.
Require Import Autosubst.Autosubst.
Require Import Lia.

(* I again used the autosubst library *)

Module System_F.

  Ltac smash := repeat split; eauto.

  Open Scope list_scope.

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

  (** Small step CBV beta reduction *)
  Reserved Notation " e '⇒' f " (at level 50).
  Inductive step : expr -> expr -> Prop :=
  | cbv_efun e1 e2 e1' : e1 ⇒ e1' -> (EApp e1 e2) ⇒ (EApp e1' e2)
  | cbv_earg t e e2 e2' : e2 ⇒ e2' -> (EApp (EAbs t e) e2) ⇒ (EApp (EAbs t e) e2')
  | cbv_esub t e v : EApp (EAbs t e) v ⇒ (e.[v/])
  | cbv_tfun e e' t : e ⇒ e' -> (TApp e t) ⇒ (TApp e' t)
  | cbv_tsub e t : TApp (TAbs e) t ⇒ e (* e.|[t/] *)
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

  Definition beta_equiv := clos_refl_sym_trans_n1 _ step.
  #[export] Hint Constructors clos_refl_sym_trans_n1: core.
  Notation "e '≡' f" := (beta_equiv e f) (at level 20).

  Lemma multistep_implies_beta : forall e e', e ⇒* e' -> e ≡ e'.
  Proof. intros. unfold beta_equiv. induction H; eauto. Qed.

  (* The type of binary relations on expressions *)
  Definition rel : Type := Relation_Definitions.relation expr.

  (* A compatible relation is a binary relation that respects beta equivalence *)
  Definition compatible (R : rel) : Prop :=
    forall e1 e2 e1' e2', e1 ≡ e2 -> e1' ≡ e2' -> R e1 e2 -> R e1' e2'.

  (* A dependent sum of relation with a proof of compatibility *)
  Definition compat_rel : Type := sig compatible.

  Lemma equiv_rel_compatible : compat_rel.
  Proof. exists beta_equiv. unfold compatible. intros. eauto. Qed.

  Fixpoint V (ρ : var -> compat_rel) t v1 v2 {struct t} : Prop :=
    let E ρ t e1 e2 : Prop := exists v1 v2, e1 ⇒* v1 /\ e2 ⇒* v2 /\ V ρ t v1 v2 in
    match t with
    | TVar n => proj1_sig (ρ n) v1 v2
    | Unit => v1 = Null /\ v2 = Null
    | Arrow t1 t2 => exists (e1 e2 : {bind expr}), v1 = EAbs t1 e1 /\ v2 = EAbs t1 e2 /\ (forall v1' v2', V ρ t1 v1' v2' -> E ρ t2 (e1.[v1'/]) (e2.[v2'/]))
    | All t => exists (e1 e2 : {bind expr}), v1 = TAbs e1 /\ v2 = TAbs e2 /\ (forall R, E (R .: ρ) t e1 e2)
    end.

  Definition E ρ t e1 e2 : Prop := exists v1 v2, e1 ⇒* v1 /\ e2 ⇒* v2 /\ V ρ t v1 v2.

  Lemma V_implies_E : forall ρ t v1 v2, V ρ t v1 v2 -> E ρ t v1 v2.
  Proof. intros. unfold E. eauto. Qed.
  #[export] Hint Resolve V_implies_E : core.

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

  Lemma app_fun_steps_steps : forall e e' e'', e ⇒* e' -> (EApp e e'') ⇒* (EApp e' e'').
  Proof.
    intros. induction H.
    - apply rtn1_refl.
    - apply rtn1_trans with (y := (EApp y e'')); auto.
  Qed.
  #[export] Hint Resolve app_fun_steps_steps : core.

  Lemma app_arg_steps_steps : forall e e' e'' t, e' ⇒* e'' -> (EApp (EAbs t e) e') ⇒* (EApp (EAbs t e) e'').
  Proof.
    intros. induction H.
    - apply rtn1_refl.
    - apply rtn1_trans with (y := (EApp (EAbs t e) y)); auto.
  Qed.
  #[export] Hint Resolve app_arg_steps_steps : core.

  (* This is the expression Λ X. λ x:X. x *)
  Example polymorphic_identity : expr :=
    TAbs (EAbs (TVar 0) (Var 0)).

  Example polymorphic_identity_related_to_itself :
    forall ρ, V ρ (All (Arrow (TVar 0) (TVar 0))) polymorphic_identity polymorphic_identity.
  Proof.
    intros. unfold V. exists (EAbs (TVar 0) (Var 0)), (EAbs (TVar 0) (Var 0)). smash. intros. exists (EAbs (TVar 0) (Var 0)), (EAbs (TVar 0) (Var 0)). smash. exists (Var 0), (Var 0). smash.
  Qed.

  Definition parallel_subst : Type := var -> expr.

  Inductive sem_rel_expr_substs : (var -> compat_rel) -> ev_context -> parallel_subst -> parallel_subst -> Prop :=
  | nil_sem_rel_expr_substs ρ : sem_rel_expr_substs ρ nil ids ids
  | cons_sem_rel_expr_substs ρ t Γ γ1 γ2 e1 e2 : sem_rel_expr_substs ρ Γ γ1 γ2 -> E ρ t e1 e2 -> sem_rel_expr_substs ρ (t :: Γ) (e1 .: γ1) (e2 .: γ2).
  #[export] Hint Constructors sem_rel_expr_substs : core.

  Definition semantically_related (Δ : tv_context) Γ e1 e2 t :=
    forall ρ γ1 γ2, sem_rel_expr_substs ρ Γ γ1 γ2 -> E ρ t e1 .[γ1] e2.[γ2].
  Notation "Δ ';' Γ ⊨ e '~' f ':::' t" := (semantically_related Δ Γ e f t) (at level 96).

  Lemma autosubst_help : forall e γ v, e.[up γ].[v/] = e.[v .: γ].
  Proof. intros. autosubst. Qed.

  (** Fundamental theorem of logical relations for System F : Parametricity *)
  Theorem parametricity : forall Δ Γ e t, Δ;Γ ⊢ e ::: t -> Δ;Γ ⊨ e ~ e ::: t.
  Proof.
    intros. unfold semantically_related. unfold E. induction H; intros; simpl.
    - exists (EAbs t1 e.[up γ1]), (EAbs t1 e.[up γ2]). repeat split; (try apply rtn1_refl). exists e.[up γ1], e.[up γ2]. smash. intros. specialize (IHtyping ρ (v1' .: γ1) (v2' .: γ2)). repeat rewrite autosubst_help. auto.
    - destruct (IHtyping1 ρ γ1 γ2 H1) as [f1 [f2 [Sfun1 [Sfun2 Vfun]]]]. destruct (IHtyping2 ρ γ1 γ2 H1) as [arg1 [arg2 [Sarg1 [Sarg2 Varg]]]]. clear IHtyping1. clear IHtyping2. inversion Vfun. rename x into e3. destruct H2 as [e4 [Eq1 [Eq2]]]. subst. specialize (H2 arg1 arg2 Varg). destruct H2 as [v1 [v2 [Sapp1 [Sapp2 Vapp]]]]. exists v1, v2. smash.
      + apply multistep_trans with (e' := e3.[arg1/]); eauto. apply multistep_trans with (e' := EApp (EAbs t1 e3) e2.[γ1]); eauto.
      + apply multistep_trans with (e' := e4.[arg2/]); eauto. apply multistep_trans with (e' := EApp (EAbs t1 e4) e2.[γ2]); eauto.
    - exists (TAbs e.[γ1 >>| ren (+1)]), (TAbs e.[γ2 >>| ren (+1)]). smash. exists (e.[γ1 >>| ren (+1)]), (e.[γ2 >>| ren (+1)]). smash. intros. specialize (IHtyping ρ (γ1 >>| ren (+1)) (γ2 >>| ren (+1))). admit.
    - destruct (IHtyping ρ γ1 γ2 H0) as [v1 [v2 [S1 [S2 Vall]]]]. inversion Vall as [e1 [e2 [Eq1 [Eq2]]]]. subst. specialize (H1 equiv_rel_compatible).

  (** Strong normalization of CBV STLC *)
  Theorem strong_normalization : forall e t, ∅ ⊢ e ::: t -> exists v, value v /\ e ⇒* v.
  Proof.
    intros. apply (fundamental_theorem nil e t) in H. unfold semant_typing in H. specialize H with (@ids expr Ids_expr). rewrite subst_id in H. destruct H. apply subst_empty. exists x. split; destruct H; (try apply (V_implies_value t); auto).
  Qed.

End System_F.