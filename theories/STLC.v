Require Export Basics.

Module STLC.

  (* name is the countably infinite set of names *)
  Definition name := nat.

  Inductive tipe :=
  | unit: tipe
  | arrow: tipe -> tipe -> tipe.

  Inductive expr :=
  | null: expr (* This is of unit type *)
  | var: name -> expr
  | app: expr -> expr -> expr
  | abs: name -> expr -> expr.

  (* A context is a mapping from variable names to types or undefined *)
  Definition context := name -> option tipe.

  Definition empty_context : context := fun n => None.

  Definition context_update (c: context) n t := fun m => if Nat.eqb m n then c m else Some t.
  Notation "X , Y ::: Z" := (context_update X Y Z) (at level 100).

  Notation "∅" := empty_context.

  Inductive type_checks : context -> expr -> tipe -> Prop :=
  | unit_intro: type_checks ∅ null unit
  | axiom_rule Γ (n: name) (t: tipe) (H: Γ n = Some t) : type_checks Γ (var n) t
  | weakening Γ e t n t_var (H: Γ n = None) : type_checks Γ e t -> type_checks (Γ, n ::: t_var) e t
  | arrow_elim Γ e1 e2 t_arg t_bod : type_checks Γ e1 (arrow t_arg t_bod) -> type_checks Γ e2 t_arg -> type_checks Γ (app e1 e2) t_bod
  | arrow_intro Γ n e t_arg t_bod : type_checks (Γ, n ::: t_arg) e t_bod -> type_checks Γ (abs n e) (arrow t_arg t_bod).

  Notation " C ⊢ E ::: T " := (type_checks C E T) (at level 99).

  (* Substituition *)
  Fixpoint substitute e1 n e2 : expr :=
    match e1 with
    | null => null
    | var n' => if Nat.eqb n n' then e2 else e1
    | app e e' => app (substitute e n e2) (substitute e' n e2)
    | abs n' e => if Nat.eqb n n' then e1 else abs n' (substitute e n e2)
    end.

  (* The type of little gamma *)
  Definition substitution_maps : Type := name -> option expr.

  Fixpoint parallel_subst e γ : expr :=
    match e with
    | null => null
    | var n =>
        match (γ n) with
        | Some e' => e'
        | None => e
        end
    | app e e' => app (parallel_subst e γ) (parallel_subst e' γ)
    | abs n e =>
        let γ' := fun m => if Nat.eqb m n then None else γ m in
        abs n (parallel_subst e γ')
    end.

  Inductive is_value : expr -> Prop :=
  | null_is_value : is_value null
  | abs_is_value n e : is_value (abs n e).

  (* Small-step operational semantics *)
  Inductive cbv_once : expr -> expr -> Prop :=
  | app_cbv_once n e_bod v_arg (H: is_value v_arg): cbv_once (app (abs n e_bod) v_arg) (substitute e_bod n v_arg)
  | fun_cbv_once e e' e_arg : cbv_once e e' -> cbv_once (app e e_arg) (app e' e_arg)
  | arg_cbv_once v e e' (H: is_value v) : cbv_once (app v e) (app v e').

  (* Multi-step with the kleene star, aka reflexive and transitive closure of cbv_once *)
  Inductive cbv_multi : expr -> expr -> Prop :=
  | base_cbv_multi e1 e2 : cbv_once e1 e2 -> cbv_multi e1 e2
  | refl_cbv_multi e : cbv_multi e e
  | trans_cbv_multi e1 e2 e3 : cbv_multi e1 e2 -> cbv_multi e2 e3 -> cbv_multi e1 e3.

  (* Inductive *)
  (*   normal_form : expr -> Prop := *)
  (* | neutral_normal_form e : neutral_form e -> normal_form e *)
  (* | abs_normal_form n e : normal_form e -> normal_form (abs n e) *)
  (* with *)
  (*   neutral_form : expr -> Prop := *)
  (* | var_neutral_form n : neutral_form (var n) *)
  (* | app_neutral_form e1 e2 : neutral_form e1 -> normal_form e2 -> neutral_form (app e1 e2). *)

  (* Inductive *)
  (*   V : tipe -> expr -> Prop := *)
  (* | V_unit t : V t null *)
  (* | V_arrow t1 t2 n e (H: forall v, V t1 v -> E t2 (app e v)) : V (arrow t1 t2) (abs n e) *)
  (* with *)
  (*   E : tipe -> expr -> Prop := *)
  (* | E_t t e v (H: is_value v) : cbv_multi e v -> V t v -> E t v. *)

  Fixpoint
    V t v {struct t} : Prop :=
    let E t e : Prop := exists v, (cbv_multi e v) /\ (V t v) in
    match t with
    | unit => v = null
    | arrow t1 t2 => exists (n: name) (e: expr), ((v = abs n e) /\ (forall (v': expr), V t1 v' -> E t2 (substitute e n v')))
    end.

  Definition type_checks_parallel_subst Γ γ : Prop :=
    forall (n: name), forall t, Γ n = Some t -> exists v, (γ n = Some v) /\ (V t v).

  (* Notation " C ⊨ G " := (type_checks_parallel_subst C G) (at level 99). *)

  Definition type_checks_semantically Γ e t : Prop :=
    forall γ, (type_checks_parallel_subst Γ γ) -> (exists v, (cbv_multi (parallel_subst e γ) v) /\ (V t v)).

  Notation " C ⊨ E ::: T " := (type_checks_semantically C E T) (at level 99).

  Lemma type_check_parallel_subst_update : forall Γ γ n t,
       type_checks_parallel_subst (Γ, n ::: t) γ -> type_checks_parallel_subst Γ γ.
  Proof.
    unfold type_checks_parallel_subst. intros. specialize H with (n := n0) (t := t0).
    unfold context_update in H. destruct (Nat.eqb n0 n).
    - inversion H0. auto.
    - admit.
  Admitted.

  Lemma cbv_multi_under_fun : forall e1 e1' e2,
      cbv_multi e1 e1' -> cbv_multi (app e1 e2) (app e1' e2).
  Proof.
    intros. induction H.
    - apply base_cbv_multi, fun_cbv_once. auto.
    - apply refl_cbv_multi.
    - apply (trans_cbv_multi (app e1 e2) (app e0 e2) (app e3 e2)); auto.
  Qed.

  Lemma cbv_multi_under_arg : forall n e1 e e',
      cbv_multi e e' -> cbv_multi (app (abs n e1) e) (app (abs n e1) e').
  Proof.
    intros. induction H.
    - apply base_cbv_multi, arg_cbv_once. apply abs_is_value.
    - apply refl_cbv_multi.
    - apply (trans_cbv_multi (app (abs n e1) e0) (app (abs n e1) e2) (app (abs n e1) e3)); auto.
  Qed.

  (* Fundamental theorem of logical relations *)
  Theorem fundamental_theorem : forall Γ e t, ( Γ ⊢ e ::: t ) -> ( Γ ⊨ e ::: t ).
  Proof.
    intros. unfold type_checks_semantically. induction H.
    - intros. eexists null. split.
      + simpl. apply refl_cbv_multi.
      + reflexivity.
    - intros. simpl. unfold type_checks_parallel_subst in H0. destruct (H0 n t).
      + apply H.
      + simpl. destruct H1. rewrite H1. eexists x. split.
        * apply refl_cbv_multi.
        * auto.
    - intros. specialize IHtype_checks with (γ := γ). simpl in H1. apply type_check_parallel_subst_update in H1. auto.
    - simpl. intros. specialize (IHtype_checks1 γ H1). specialize (IHtype_checks2 γ H1).
      destruct IHtype_checks1, IHtype_checks2. destruct H2, H3. inversion H4. destruct H6.
      destruct H6. rewrite H6 in H2. specialize (H7 x0). apply H7 in H5 as H8. clear H7. destruct H8. destruct H7. exists x3. split.
      + apply (trans_cbv_multi (app (parallel_subst e1 γ) (parallel_subst e2 γ)) (app ((abs x1 x2)) (parallel_subst e2 γ))).
        * apply cbv_multi_under_fun. auto.
        * apply trans_cbv_multi with (e2 := (substitute x2 x1 x0)).
          -- assert (cbv_multi (app (abs x1 x2) (parallel_subst e2 γ)) (app (abs x1 x2) x0)) as Hyp. { apply cbv_multi_under_arg with (e' := x0). auto. } apply trans_cbv_multi with (e2 := (app (abs x1 x2) x0)).
             ++ auto.
             ++ apply base_cbv_multi. apply app_cbv_once. unfold V in H5. destruct t_arg.
                ** subst x0. apply null_is_value.
                ** destruct H5. destruct H5. destruct H5. subst x0. apply abs_is_value.
          -- auto.
      + auto.
    - intros. specialize (IHtype_checks γ). eexists (parallel_subst (abs n e) γ).
      split.
      + apply refl_cbv_multi.
      + simpl (parallel_subst (abs n e) γ). simpl. eexists n. eexists (parallel_subst e (fun m : nat => if Nat.eqb m n then None else γ m)). split.
        * reflexivity.
        * intros. esplit.
  Admitted.
End STLC.