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
  | null_value : is_value null
  | abs_value n e : is_value (abs n e).

  (* Small-step operational semantics *)
  Inductive cbv_step : expr -> expr -> Prop :=
  | app_cbv n e_bod v_arg (H: is_value v_arg): cbv_step (app (abs n e_bod) v_arg) (substitute e_bod n v_arg)
  | fun_cbv e e' e_arg : cbv_step e e' -> cbv_step (app e e_arg) (app e' e_arg)
  | arg_cbv v e e' (H: is_value v) : cbv_step (app v e) (app v e').

End STLC.