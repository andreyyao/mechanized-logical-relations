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

  Definition context_update (c: context) n t := fun m => if Nat.eqb m n then Some t else c m.
  Notation "X , Y ::: Z" := (context_update X Y Z) (at level 3).

  Notation "∅" := empty_context.

  Inductive typing_derivation : context -> expr -> tipe -> Prop :=
  | unit_intro: typing_derivation ∅ null unit
  | axiom_rule Γ (n: name) (t: tipe) (H: Γ n = Some t) : typing_derivation Γ (var n) t
  | weakening Γ e t n t_var (H: Γ n = None) : typing_derivation Γ e t -> typing_derivation (Γ, n ::: t_var) e t
  | arrow_elim Γ e1 e2 t_arg t_bod : typing_derivation Γ e1 (arrow t_arg t_bod) -> typing_derivation Γ e2 t_arg -> typing_derivation Γ (app e1 e2) t_bod
  | arrow_intro Γ n e t_arg t_bod : typing_derivation (Γ, n ::: t_arg) e t_bod -> typing_derivation Γ (abs n e) (arrow t_arg t_bod).

  (* Substituition *)
  Fixpoint substitute e1 n e2 : expr :=
    match e1 with
    | null => null
    | var n' => if Nat.eqb n n' then e2 else e1
    | app e e' => app (substitute e n e2) (substitute e' n e2)
    | abs n' e => if Nat.eqb n n' then e1 else abs n' (substitute e n e2)
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

  Program Fixpoint
    V (t : tipe) : expr -> Prop :=
    match t with
    | unit => fun v => true
    | arrow t1 t2 => fun v => exists e.
    end
    and
    E (t : tipe) : expr -> bool :=

End STLC.