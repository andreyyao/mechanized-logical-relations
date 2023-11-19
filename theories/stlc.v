Require Export Basics.
Require Import List.
Require Import Relation_Operators.
Require Import Autosubst.Autosubst.
Require Import Lia.

(* Some of the stuff about autosubst was taken from https://gist.github.com/tmoux/5027a9b9f6b5aee291d569e5f144b350 *)

Module STLC.

  Open Scope nat_scope.
  Open Scope list_scope.

  Inductive tipe :=
  | Unit : tipe
  | Arrow : tipe -> tipe -> tipe
  | Prod : tipe -> tipe -> tipe.

  Notation " T '→' S " := (Arrow T S) (at level 99, right associativity).
  Notation " T '×' S " := (Prod T S) (at level 98, left associativity).

  Inductive expr :=
  | Pair (e1 : expr) (e2 : expr)
  | App (e1 : expr) (e2 : expr)
  | Abs (e : {bind expr})
  | Pi1 (e : expr)
  | Pi2 (e : expr)
  | Var (x : var)
  | Null.

  #[export] Instance Ids_expr : Ids expr. derive. Defined.
  #[export] Instance Rename_expr : Rename expr. derive. Defined.
  #[export] Instance Subst_expr : Subst expr. derive. Defined.
  #[export] Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

  (* The context is a stack, with the head being the most recently bound variable *)
  Definition context : Type := List.list tipe.

  Definition lookup : context -> nat -> option tipe := @nth_error tipe.

  (* Empty context *)
  Notation "∅" := nil (at level 97).

  (* Lemma lookup_cons_equal : forall Γ t t' n, lookup Γ n = Some t -> lookup (t' :: Γ) n = Some t. *)
  (* Proof. *)
  (*   intros. *)

  Inductive typing : context -> expr -> tipe -> Prop :=
  | prod_intro Γ e1 e2 t1 t2 : typing Γ e1 t1 -> typing Γ e2 t2 -> typing Γ (Pair e1 e2) (t1 × t2)
  | prod_elim1 Γ e t1 t2 : typing Γ e (t1 × t2)  -> typing Γ (Pi1 e) t1
  | prod_elim2 Γ e t1 t2 : typing Γ e (t1 × t2)  -> typing Γ (Pi2 e) t2
  | arrow_intro Γ e t1 t2 : typing (t1 :: Γ) e t2 -> typing Γ (Abs e) (t1 → t2)
  | arrow_elim Γ e1 e2 t1 t2 : typing Γ e1 (t1 → t2) -> typing Γ e2 t1 -> typing Γ (App e1 e2) t2
  | unit_intro Γ : typing Γ Null Unit
  | axiom_rule Γ n t : lookup Γ n = Some t -> typing Γ (Var n) t.
  #[export] Hint Constructors typing : core.
  Notation " Γ '⊢' e ':::' t " := (typing Γ e t) (at level 99).

  Inductive value : expr -> Prop :=
  | value_pair v1 v2 : value v1 -> value v2 -> value (Pair v1 v2)
  | value_abs e : value (Abs e)
  | value_null : value Null.
  #[export] Hint Constructors value : core.

  (** Small step CBV beta reduction *)
  Inductive cbv_once : expr -> expr -> Prop :=
  | cbv_pair1 e1 e2 e1' : cbv_once e1 e1' -> cbv_once (Pair e1 e2) (Pair e1' e2)
  | cbv_pair2 e1 e2 e2' : cbv_once e2 e2' -> cbv_once (Pair e1 e2) (Pair e1 e2')
  | cbv_pi1 e e' : cbv_once e e' -> cbv_once (Pi1 e) (Pi1 e')
  | cbv_pi2 e e' : cbv_once e e' -> cbv_once (Pi2 e) (Pi2 e')
  | cbv_val_pi1 v1 v2 : cbv_once (Pi1 (Pair v1 v2)) v1
  | cbv_val_pi2 v1 v2 : cbv_once (Pi2 (Pair v1 v2)) v2
  | cbv_fun e1 e2 e1' : cbv_once e1 e1' -> cbv_once (App e1 e2) (App e1' e2)
  | cbv_arg e e2 e2' : cbv_once e2 e2' -> cbv_once (App (Abs e) e2) (App (Abs e) e2')
  | cbv_sub e v : value v -> cbv_once (App (Abs e) v) (e.[v .: ids]).
  #[export] Hint Constructors cbv_once : core.

  Notation " e '⇒' f " := (cbv_once e f) (at level 21).

  (** Multi-step relation *)
  Definition cbv_multi := clos_refl_trans_n1 _ cbv_once.
  #[export] Hint Constructors clos_refl_trans_n1 : core.
  Notation "e '⇒*' f" := (cbv_multi e f) (at level 20).

  Lemma cbv_multi_trans : forall e e' e'', e ⇒* e' -> e' ⇒* e'' -> e ⇒* e''.
  Proof.
    intros. induction H0.
    - auto.
    - apply rtn1_trans with (y := y); auto.
  Qed.

  Lemma pair_steps_steps_steps :
    forall e1 e2 e1' e2', e1 ⇒* e1' -> e2 ⇒* e2' -> (Pair e1 e2) ⇒* (Pair e1' e2').
  Proof.
    intros e1 e2 e1' e2'. intros H1 H2. induction H1; induction H2.
    - apply rtn1_refl.
    - eapply rtn1_trans. instantiate (1 := Pair e1 y).
      + apply cbv_pair2. auto.
      + apply IHclos_refl_trans_n1.
    - eapply rtn1_trans. instantiate (1 := Pair y e2).
      + apply cbv_pair1. auto.
      + apply IHclos_refl_trans_n1.
    - eapply rtn1_trans. instantiate (1 := Pair y z0).
      + apply cbv_pair1. auto.
      + apply IHclos_refl_trans_n1.
  Qed.

  Lemma pi1_steps_steps : forall e e', e ⇒* e' -> Pi1 e ⇒* Pi1 e'.
  Proof.
    intros e e' H. induction H.
    - apply rtn1_refl.
    - apply rtn1_trans with (y := Pi1 y); auto.
  Qed.

  Lemma pi2_steps_steps : forall e e', e ⇒* e' -> Pi2 e ⇒* Pi2 e'.
  Proof.
    intros e e' H. induction H.
    - apply rtn1_refl.
    - apply rtn1_trans with (y := Pi2 y); auto.
  Qed.

  Lemma app_fun_steps_steps : forall e e' e'', e ⇒* e' -> (App e e'') ⇒* (App e' e'').
  Proof.
    intros. induction H.
    - apply rtn1_refl.
    - apply rtn1_trans with (y := (App y e'')); auto.
  Qed.

  Lemma app_arg_steps_steps : forall e e' e'', e' ⇒* e'' -> (App (Abs e) e') ⇒* (App (Abs e) e'').
  Proof.
    intros. induction H.
    - apply rtn1_refl.
    - apply rtn1_trans with (y := (App (Abs e) y)); auto.
  Qed.

  Fixpoint V t v {struct t} : Prop :=
    let E t e : Prop := exists v, (cbv_multi e v) /\ (V t v) in
    match t with
    | Unit => v = Null
    | Prod t1 t2 => exists v1 v2 : expr, v = Pair v1 v2 /\ V t1 v1 /\ V t2 v2
    | Arrow t1 t2 => exists (e: {bind expr}), ((v = Abs e) /\ (forall (v': expr), V t1 v' -> E t2 (e .[v' .: ids])))
    end.

  Definition E t e := exists v, (cbv_multi e v) /\ (V t v).

  Lemma V_implies_value : forall t v, V t v -> value v.
  Proof.
    induction t; intros; inversion H.
    - apply value_null.
    - destruct H0. subst v. apply value_abs.
    - destruct H0 as [v2 [Eq [V1 V2]]]. subst v. apply value_pair; eauto.
  Qed.

  (* Taken from line 239 of https://gist.github.com/tmoux/5027a9b9f6b5aee291d569e5f144b350#file-stlc-v-L8 *)
  Inductive valid_subst : context -> (var -> expr) -> Prop :=
  | subst_empty : valid_subst nil ids
  | subst_cons Γ γ v t : valid_subst Γ γ -> V t v -> valid_subst (t :: Γ) (v .: γ).
  #[export] Hint Constructors valid_subst : core.

  (* Taken from line 244 of https://gist.github.com/tmoux/5027a9b9f6b5aee291d569e5f144b350#file-stlc-v-L8 *)
  Lemma valid_subst_implies_V :
    forall Γ γ, valid_subst Γ γ -> forall n t, lookup Γ n = Some t -> V t (γ n).
  Proof.
    intros Γ γ H. induction H; intros.
    - destruct n; simpl in *; inversion H.
    - induction n; simpl.
      + inversion H1. subst t. auto.
      + inversion H1. apply IHvalid_subst. auto.
  Qed.

  Definition semant_typing Γ e t : Prop :=
    forall γ, valid_subst Γ γ -> E t (e .[γ]).

  Notation " Γ '⊨' e ':::' t " := (semant_typing Γ e t) (at level 99).

  (** Fundamental theorem of logical relations *)
  Theorem fundamental_theorem : forall Γ e t, Γ ⊢ e ::: t -> Γ ⊨ e ::: t.
  Proof.
    intros Γ e t H. induction H; unfold semant_typing; intros γ VS; unfold E; simpl.
    (* pair *)
    - unfold semant_typing in IHtyping1, IHtyping2. remember (IHtyping1 γ VS) as E1. remember (IHtyping2 γ VS) as E2. unfold E in E1, E2. destruct E1, E2. destruct a, a0. eexists (Pair x x0). split. apply pair_steps_steps_steps; auto. eauto.
    (* pi1 *)
    - unfold semant_typing in IHtyping. remember (IHtyping γ VS) as E1. unfold E in E1. destruct E1. destruct a. inversion v. destruct H0 as [v2 [Eq [V1 V2]]]. exists x0. split; auto. eapply rtn1_trans. instantiate (1 := Pi1 (Pair x0 v2)). apply cbv_val_pi1. subst x. apply pi1_steps_steps. auto.
    (* pi2 *)
    - unfold semant_typing in IHtyping. remember (IHtyping γ VS) as E1. unfold E in E1. destruct E1. destruct a. inversion v. destruct H0 as [v2 [Eq [V1 V2]]]. exists v2. split; auto. eapply rtn1_trans. instantiate (1 := Pi2 (Pair x0 v2)). apply cbv_val_pi2. subst x. apply pi2_steps_steps. auto.
    (* abs *)
    - unfold semant_typing in IHtyping. exists (Abs e.[up γ]). split.
      + apply rtn1_refl.
      + exists (e.[up γ]). split; auto. intros. Search "subst". specialize (IHtyping (v' .: γ)). assert (valid_subst (t1 :: Γ) (v' .: γ)) as lemma. { apply subst_cons; auto. } apply IHtyping in lemma. unfold E in lemma. autosubst.
    (* app *)
    - unfold semant_typing in IHtyping1, IHtyping2. remember (IHtyping1 γ VS) as E1. remember (IHtyping2 γ VS) as E2. unfold E in E1, E2. destruct E1 as [v_fun [S1 V1]]. destruct E2 as [v_arg [S2 V2]]. inversion V1. destruct H1. subst v_fun. specialize (H2 v_arg). remember (H2 V2). destruct e as [v [Sv Vv]]. exists v. split.
      + apply cbv_multi_trans with (e' := App (Abs x) v_arg).
        * apply cbv_multi_trans with (e' := App (Abs x) (e2.[γ])).
          -- apply app_fun_steps_steps; auto.
          -- apply app_arg_steps_steps; auto.
        * apply cbv_multi_trans with (e' := x.[v_arg/]).
          -- apply Operators_Properties.clos_rtn1_step. apply cbv_sub. apply (V_implies_value t1). auto.
          -- auto.
      + auto.
    (* null *)
    - exists Null. split; auto. apply rtn1_refl.
    (* var *)
    - esplit. remember (valid_subst_implies_V Γ γ VS) as Valid. apply (Valid n t) in H. instantiate (1 := γ n). split.
      + apply rtn1_refl.
      + assumption.
  Qed.

  (** Strong normalization of CBV STLC *)
  Theorem strong_normalization : forall e t, ∅ ⊢ e ::: t -> exists v, value v /\ e ⇒* v.
  Proof.
    intros. apply (fundamental_theorem nil e t) in H. unfold semant_typing in H. Print SubstLemmas_expr. specialize H with (@ids expr Ids_expr). rewrite subst_id in H. destruct H. apply subst_empty. exists x. split; destruct H. apply (V_implies_value t). auto. auto.
  Qed.

End STLC.