Require Export Basics.
Require Import List.
Require Import Relation_Operators.
Require Import Autosubst.Autosubst.
Require Import Lia.
From Equations Require Import Equations.
From Equations.Type Require Import Subterm.
From Equations.Type Require Import NoConfusion.

Module StepIndex.

  Ltac smash := repeat split; eauto.

  Open Scope list_scope.
  Open Scope nat_scope.

  (* Some of the stuff about de Bruijn and the `autosubst` library was taken from https://gist.github.com/tmoux/5027a9b9f6b5aee291d569e5f144b350 *)
  Inductive tipe :=
  | Unit
  | TVar (X : var)
  | Prod (t1 : tipe) (t2 : tipe)
  | Arrow (t1 : tipe) (t2 : tipe)
  | Recur (t : {bind tipe}).

  Notation " T '→' S " := (Arrow T S) (at level 98, right associativity).
  Notation " T '×' S " := (Prod T S) (at level 97, left associativity).
  Notation " 'μ' T " := (Recur T) (at level 99).

  Inductive expr :=
  | Null
  | Var (x : var)
  | Pair (e1 : expr) (e2 : expr)
  | Pi1 (e : expr)
  | Pi2 (e : expr)
  | Abs (e : {bind expr})
  | App (e1 : expr) (e2 : expr)
  | Roll (e : expr)
  | Unroll (e : expr).

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

  (* The context is a stack, with the head being the most recently bound variable *)
  Definition context : Type := List.list tipe.

  Definition lookup : context -> nat -> option tipe := @nth_error tipe.
  #[export] Hint Unfold lookup : core.

  Reserved Notation " Γ '⊢' e ':::' t " (at level 99).
  Inductive typing : context -> expr -> tipe -> Prop :=
  | unit_intro Γ : Γ ⊢ Null ::: Unit
  | axiom_rule Γ n t : lookup Γ n = Some t -> Γ ⊢ (Var n) ::: t
  | prod_intro Γ e1 e2 t1 t2 : typing Γ e1 t1 -> typing Γ e2 t2 -> typing Γ (Pair e1 e2) (t1 × t2)
  | prod_elim1 Γ e t1 t2 : Γ ⊢ e ::: (t1 × t2) -> Γ ⊢ (Pi1 e) ::: t1
  | prod_elim2 Γ e t1 t2 : Γ ⊢ e ::: (t1 × t2) -> Γ ⊢ (Pi2 e) ::: t2
  | arrow_intro Γ e t1 t2 : (t1 :: Γ) ⊢ e ::: t2 -> Γ ⊢ (Abs e) ::: (t1 → t2)
  | arrow_elim Γ e1 e2 t1 t2 : Γ ⊢ e1 ::: (t1 → t2) -> Γ ⊢ e2 ::: t1 -> Γ ⊢ (App e1 e2) ::: t2
  | recur_intro Γ e t : Γ ⊢ e ::: t.[μ t/] -> Γ ⊢ Roll e ::: μ t
  | recur_elim Γ e t : Γ ⊢ e ::: (μ t) -> Γ ⊢ Unroll e ::: t.[μ t/]
  where " Γ '⊢' e ':::' t " := (typing Γ e t).
  #[export] Hint Constructors typing : core.

  Inductive value : expr -> Prop :=
  | value_null : value Null
  | value_pair v1 v2 : value v1 -> value v2 -> value (Pair v1 v2)
  | value_abs e : value (Abs e)
  | value_roll v : value v -> value (Roll v).
  #[export] Hint Constructors value : core.

  (** Small step CBV beta reduction *)
  Reserved Notation " e '⇒' f " (at level 50).
  Inductive cbv_once : expr -> expr -> Prop :=
  | cbv_pair1 e1 e2 e1' : e1 ⇒ e1' -> (Pair e1 e2) ⇒ (Pair e1' e2)
  | cbv_pair2 e1 e2 e2' : e2 ⇒ e2' -> (Pair e1 e2) ⇒ (Pair e1 e2')
  | cbv_pi1 e e' : e ⇒ e' -> (Pi1 e) ⇒ (Pi1 e')
  | cbv_pi2 e e' : e ⇒ e' -> (Pi2 e) ⇒ (Pi2 e')
  | cbv_val_pi1 v1 v2 : (Pi1 (Pair v1 v2)) ⇒ v1
  | cbv_val_pi2 v1 v2 : (Pi2 (Pair v1 v2)) ⇒ v2
  | cbv_fun e1 e2 e1' : e1 ⇒ e1' -> (App e1 e2) ⇒ (App e1' e2)
  | cbv_arg e e2 e2' : e2 ⇒ e2' -> (App (Abs e) e2) ⇒ (App (Abs e) e2')
  | cbv_sub e v : value v -> (App (Abs e) v) ⇒ (e.[v/])
  | cbv_roll e e' : e ⇒ e' -> Roll e ⇒ Roll e'
  | cbv_unroll e e' : e ⇒ e' -> Unroll e ⇒ Unroll e'
  | cbv_val_unroll v : value v -> Unroll (Roll v) ⇒ v
  where " e '⇒' f " := (cbv_once e f).
  #[export] Hint Constructors cbv_once : core.

  (** Multi-step relation *)
  Definition cbv_multi := clos_refl_trans_n1 _ cbv_once.
  #[export] Hint Constructors clos_refl_trans_n1 : core.
   #[export] Hint Constructors clos_refl_trans : core.
  Notation "e '⇒*' f" := (cbv_multi e f) (at level 20).

    (* Definition of SA and Omega combinator are taken from https://www.cs.uoregon.edu/research/summerschool/summer23/_lectures/Logical_Relations_Notes.pdf *)
  Example SA := Abs (App (Unroll (Var 0)) (Var 0)).
  Example Ω := App SA (Roll SA).

  (* The self-application operator can be typed with any type. We choose the unit type here, but it could be some other type *)
  Example SA_typed : nil ⊢ SA ::: (μ (TVar 0) → Unit) → Unit.
  Proof.
    unfold SA. apply arrow_intro. apply (arrow_elim ((μ TVar 0 → Unit) :: nil) (Unroll (Var 0)) (Var 0) (μ (TVar 0) → Unit) Unit); eauto. apply (recur_elim ((μ TVar 0 → Unit) :: nil) (Var 0) ((TVar 0) → Unit)). eauto.
  Qed.

  Example omega_typed : nil ⊢ Ω ::: Unit.
  Proof.
    intros. unfold Ω. apply (arrow_elim nil SA (Roll SA) (μ (TVar 0) → Unit) Unit). apply SA_typed. apply recur_intro. simpl. apply SA_typed.
  Qed.

  (** Infinite ∞ loop!!! *)
  Example omega_steps_to_itself : exists e, Ω ⇒ e /\ e ⇒* Ω.
  Proof.
    unfold Ω. unfold SA. exists (App (Unroll (Var 0)) (Var 0)).[(Roll (Abs (App (Unroll (Var 0)) (Var 0))))/]; split; eauto. simpl. apply Operators_Properties.clos_rt_rtn1_iff. apply rt_trans with (y := (App (Abs (App (Unroll (Var 0)) (Var 0))) (Roll (Abs (App (Unroll (Var 0)) (Var 0)))))); eauto.
  Qed.

  Lemma pair_steps_steps_steps :
    forall e1 e2 e1' e2', e1 ⇒* e1' -> e2 ⇒* e2' -> (Pair e1 e2) ⇒* (Pair e1' e2').
  Proof.
    intros e1 e2 e1' e2'. intros H1 H2. induction H1; induction H2.
    - apply rtn1_refl.
    - apply rtn1_trans with (y := Pair e1 y); eauto.
    - apply rtn1_trans with (y := Pair y e2); eauto.
    - apply rtn1_trans with (y := Pair y z0); eauto.
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

  Derive NoConfusion NoConfusionHom for tipe.
  Derive Subterm for tipe.

  Equations V (k : nat) (t : tipe) (v : expr) by wf : Prop :=
    V k Unit v := v = Null;
    V k (Prod t1 t2) v := exists v1 v2 : expr, v = Pair v1 v2 /\ V k t1 v1 /\ V k t2 v2;
    V k (Arrow t1 t2) v :=
      let E (k : nat) (t : tipe) (e : expr) : Prop := forall v, e ⇒* v -> V k t v in
      exists e: {bind expr}, v = Abs e /\ forall j v', j < k -> V j t1 v' -> E j t2 e.[v'/];
    V k (Recur t) v := exists v', v = Roll v' /\ forall j, j < k -> V j t.[Recur t/] v';
    V k (TVar _) v := True.



  (* Program Fixpoint V k t v {measure (fuel k t)}: Prop := *)
  (*   let E k t e := forall v, e ⇒* v -> V k t v in *)
  (*   match t with *)
  (*   | Unit => v = Null *)
  (*   | Prod t1 t2 => exists v1 v2 : expr, v = Pair v1 v2 /\ V k t1 v1 /\ V k t2 v2 *)
  (*   | Arrow t1 t2 => exists e: {bind expr}, v = Abs e /\ forall j v', j < k -> V j t1 v' -> E j t2 e.[v'/] *)
  (*   | Recur t => exists v', v = Roll v' /\ forall j, j < k -> V j t.[Recur t/] v' *)
  (*   | TVar _ => True *)
  (*   end. *)



  Lemma monotonicity : forall n n' t e, n < n' -> V n' t e -> V n t e.
  Proof.
    intros n n' t. generalize dependent n. generalize dependent n'. induction t.
    - destruct n'; destruct n; subst; eauto.
    - destruct n'; destruct n; eauto.
    - destruct n'; destruct n; eauto; try lia; intros; destruct H0 as [v1 [v2 [Eq [V1 V2]]]]. subst.
        assert (V (S n') t1 v1) as VS1. { assumption. }
        assert (V (S n') t2 v2) as VS2. { assumption. }
        assert (0 < S n') as Triv. { lia. }
        specialize (IHt1 (S n') 0 v1 Triv VS1).
        specialize (IHt2 (S n') 0 v2 Triv VS2).
        exists v1, v2. smash.
        assert (V (S n') t1 v1) as VS1. { assumption. }
        assert (V (S n') t2 v2) as VS2. { assumption. }
        assert (S n < S n') as Triv. { lia. }
        specialize (IHt1 (S n') (S n) v1 Triv VS1).
        specialize (IHt2 (S n') (S n) v2 Triv VS2).
        exists v1, v2. smash.
    - induction n'; induction n; try lia.
      + intros. destruct H0 as [e' [Eq Hyp]]. subst. simpl. exists e'. smash.
      + intros. apply PeanoNat.Nat.succ_lt_mono in H. simpl. destruct H0 as [e' [Eq Hyp]]. subst. exists e'. smash. intros.


        assert (S n = n' \/ S n < n') as Dich. { lia. } destruct Dich. subst. Search "lt". destruct H0 as [e' [Eq Hyp]]. subst.

         assert (n < S n') as IEq. { lia. }. specialize (IHn e IEq H0).

  Next Obligation. now constructor.

  (* Definition E ρ k t e := forall v, e ⇒* v -> V ρ k t v. *)

  Equations? V (ρ : expr -> Prop) (k : nat) (t : tipe) (v : expr) : Prop by wf (k lt) tipe_subterm :=
    V ρ k Unit v := v = Null;
    V ρ k (Prod t1 t2) v := exists v1 v2 : expr, v = Pair v1 v2 /\ V ρ k t1 v1 /\ V ρ k t2 v2;
    V ρ k (Arrow t1 t2) v := exists e: {bind expr}, v = Abs e /\ forall j v', j < k -> V ρ j t1 v' -> (forall v'', e.[v'/] ⇒* v'' -> V ρ k t2 v'');
    V ρ k (Recur t) v := exists v', v = Roll v' /\ forall j, j < k -> V ρ j t.[Recur t/] v';
    V ρ k (TVar t) v := ρ v.

  Lemma V_implies_value : forall t v, V t v -> value v.
  Proof.
    induction t; intros; inversion H.
    - apply value_null.
    - destruct H0. subst v. eauto.
    - destruct H0 as [v2 [Eq [V1 V2]]]. subst v. eauto.
    - destruct H0. destruct H0. apply IHt1 in H1. subst. eauto.
    - destruct H0. destruct H0. apply IHt2 in H1. subst. eauto.
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
    intros Γ e t H. induction H; unfold semant_typing in *; intros γ VS; unfold E; simpl.
    (* pair *)
    - remember (IHtyping1 γ VS) as E1. remember (IHtyping2 γ VS) as E2. unfold E in E1, E2. destruct E1, E2. destruct a, a0. eexists (Pair x x0). split. apply pair_steps_steps_steps; auto. eauto.
    (* pi1 *)
    - remember (IHtyping γ VS) as E1. unfold E in E1. destruct E1. destruct a. inversion v. destruct H0 as [v2 [Eq [V1 V2]]]. exists x0. split; auto. eapply rtn1_trans. instantiate (1 := Pi1 (Pair x0 v2)). apply cbv_val_pi1. subst x. apply pi1_steps_steps. auto.
    (* pi2 *)
    - remember (IHtyping γ VS) as E1. unfold E in E1. destruct E1. destruct a. inversion v. destruct H0 as [v2 [Eq [V1 V2]]]. exists v2. split; auto. eapply rtn1_trans. instantiate (1 := Pi2 (Pair x0 v2)). apply cbv_val_pi2. subst x. apply pi2_steps_steps. auto.
    (* abs *)
    - exists (Abs e.[up γ]). split.
      + apply rtn1_refl.
      + exists (e.[up γ]). split; auto. intros. specialize (IHtyping (v' .: γ)). assert (valid_subst (t1 :: Γ) (v' .: γ)) as lemma. { apply subst_cons; auto. } apply IHtyping in lemma. unfold E in lemma. autosubst.
    (* app *)
    - remember (IHtyping1 γ VS) as E1. remember (IHtyping2 γ VS) as E2. unfold E in E1, E2. destruct E1 as [v_fun [S1 V1]]. destruct E2 as [v_arg [S2 V2]]. inversion V1. destruct H1. subst v_fun. specialize (H2 v_arg). remember (H2 V2). destruct e as [v [Sv Vv]]. exists v. split.
      + apply cbv_multi_trans with (e' := App (Abs x) v_arg).
        * apply cbv_multi_trans with (e' := App (Abs x) (e2.[γ])).
          -- apply app_fun_steps_steps; auto.
          -- apply app_arg_steps_steps; auto.
        * apply cbv_multi_trans with (e' := x.[v_arg/]).
          -- apply Operators_Properties.clos_rtn1_step. apply cbv_sub. apply (V_implies_value t1). auto.
          -- auto.
      + auto.
    (* inl *)
    - remember (IHtyping γ VS). unfold E in e0. destruct e0 as [v [S V1]]. exists (Inl v). split; eauto using inl_steps_steps.
    (* inr *)
    - remember (IHtyping γ VS). unfold E in e0. destruct e0 as [v [S V2]]. exists (Inr v). split; eauto using inr_steps_steps.
    (* case *)
    - remember (IHtyping1 γ VS). unfold E in e0. destruct e0 as [v [S Vsum]]. inversion Vsum; destruct H2; destruct H2; subst.
      + specialize (IHtyping2 (x .: γ)). apply subst_cons with (v := x) (t := t1) in VS as Hehe; try assumption. apply IHtyping2 in Hehe. unfold E in Hehe. destruct Hehe as [v [S' Vv]]. exists v. split; try assumption. apply cbv_multi_trans with (e' := Case (Inl x) e1.[up γ] e2.[up γ]). apply case_steps_steps. assumption. apply cbv_multi_trans with (e' := e1.[x .: γ]); auto. apply rtn1_trans with (y := Case (Inl x) e1.[up γ] e2.[up γ]); eauto. assert (e1.[up γ].[x/] = e1.[x .: γ]) as AS. { autosubst. } rewrite <- AS. eauto.
      + specialize (IHtyping3 (x .: γ)). apply subst_cons with (v := x) (t := t2) in VS as Hehe; try assumption. apply IHtyping3 in Hehe. unfold E in Hehe. destruct Hehe as [v [S' Vv]]. exists v. split; try assumption. apply cbv_multi_trans with (e' := Case (Inr x) e1.[up γ] e2.[up γ]). apply case_steps_steps. assumption. apply cbv_multi_trans with (e' := e2.[x .: γ]); auto. apply rtn1_trans with (y := Case (Inr x) e1.[up γ] e2.[up γ]); eauto. assert (e2.[up γ].[x/] = e2.[x .: γ]) as AS. { autosubst. } rewrite <- AS. eauto.
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
    intros. apply (fundamental_theorem nil e t) in H. unfold semant_typing in H. specialize H with (@ids expr Ids_expr). rewrite subst_id in H. destruct H. apply subst_empty. exists x. split; destruct H; (try apply (V_implies_value t); auto).
  Qed.

End StepIndex.