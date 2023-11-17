Require Export Basics.
Require Import List.

(* https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf *)
Module DeBruijn.

  Open Scope nat_scope.
  Open Scope list_scope.

  Inductive tipe :=
  | Unit : tipe
  | Arrow : tipe -> tipe -> tipe
  | Prod : tipe -> tipe -> tipe.

  Inductive expr :=
  | Pair (e1 : expr) (e2 : expr)
  | App (e1 : expr) (e2 : expr)
  | Abs (e : expr)
  | Pi1 (e : expr)
  | Pi2 (e : expr)
  | Var (n : nat)
  | Null.

  (* The context is a stack, with the head being the most recently bound variable *)
  Definition context : Type := List.list tipe.

  (* Empty context *)
  Notation "∅" := nil (at level 100). Print List.

  (** Shift indices above cutoff `c` in `e` by amount `i`  *)
  Fixpoint shift i c e :=
    match e with
    | Pair e1 e2 => Pair (shift i c e1) (shift i c e2)
    | App e1 e2 => App (shift i c e1) (shift i c e2)
    | Abs e => Abs (shift i (S c) e)
    | Pi1 e => Pi1 (shift i c e)
    | Pi2 e => Pi2 (shift i c e)
    | Var n => Var (if Nat.ltb n c then n else n + i)
    | Null => Null
    end.

  (** Shifts the index down by one. This is same as `shift -1 c e` *)
  Fixpoint downshift_help c e :=
    match e with
    | Pair e1 e2 => Pair (downshift_help c e1) (downshift_help c e2)
    | App e1 e2 => App (downshift_help c e1) (downshift_help c e2)
    | Abs e => Abs (downshift_help (S c) e)
    | Pi1 e => Pi1 (downshift_help c e)
    | Pi2 e => Pi2 (downshift_help c e)
    | Var n => Var (if Nat.ltb n c then n else n - 1)
    | Null => Null
    end.

  (** shift -1 0 e *)
  Definition downshift := downshift_help 0.

  (** e[m ↦ e'] *)
  Fixpoint substitute expr m e' :=
    match expr with
    | Pair e1 e2 => Pair (substitute e1 m e') (substitute e2 m e')
    | App e1 e2 => App (substitute e1 m e') (substitute e2 m e')
    | Abs e => Abs (substitute e (m + 1) (shift 1 0 e'))
    | Pi1 e => Pi1 (substitute e m e')
    | Pi2 e => Pi2 (substitute e m e')
    | Var n => if Nat.eqb n m then e' else expr
    | Null => Null
    end.

  Notation " E [ N ↦ F ] " := (substitute E N F) (at level 100).

  Inductive typing : context -> expr -> tipe -> Prop :=
  | prod_intro c e1 e2 t1 t2 : typing c e1 t1 -> typing c e2 t2 -> typing c (Pair e1 e2) (Prod t1 t2)
  | prod_elim1 c e t1 t2 : typing c e (Prod t1 t2)  -> typing c (Pi1 e) t1
  | prod_elim2 c e t1 t2 : typing c e (Prod t1 t2)  -> typing c (Pi2 e) t2
  | arrow_intro c e t1 t2 : typing (t1 :: c) e t2 -> typing c e (Arrow t1 t2)
  | arrow_elim c e1 e2 t1 t2 : typing c e1 (Arrow t1 t2) -> typing c e2 t1 -> typing c (App e1 e2) t2
  | unit_intro c : typing c Null Unit
  | axiom_rule c n t : nth_error c n = Some t -> typing c (Var n) t.

  Inductive is_value : expr -> Prop :=
  | value_pair v1 v2 : is_value v1 -> is_value v2 -> is_value (Pair v1 v2)
  | value_abs e : is_value (Abs e)
  | value_null : is_value Null.

  (** Small step CBV beta reduction *)
  Inductive cbv_once : expr -> expr -> Prop :=
  | cbv_pair1 e1 e2 e1' : cbv_once e1 e1' -> cbv_once (Pair e1 e2) (Pair e1' e2)
  | cbv_pair2 e1 e2 e2' : cbv_once e2 e2' -> cbv_once (Pair e1 e2) (Pair e1 e2')
  | cbv_pi1 e e' : cbv_once e e' -> cbv_once (Pi1 e) (Pi1 e')
  | cbv_pi2 e e' : cbv_once e e' -> cbv_once (Pi2 e) (Pi2 e')
  | cbv_val_pi1 v1 v2 : is_value v1 -> is_value v2 -> cbv_once (Pi1 (Pair v1 v2)) v1
  | cbv_val_pi2 v1 v2 : is_value v1 -> is_value v2 -> cbv_once (Pi2 (Pair v1 v2)) v2
  | cbv_fun e1 e2 e1' : cbv_once e1 e1' -> cbv_once (App e1 e2) (App e1' e2)
  | cbv_arg e e2 e2' : cbv_once e2 e2' -> cbv_once (App (Abs e) e2) (App (Abs e) e2')
  | cbv_sub e v : cbv_once (App (Abs e) v) (downshift (e [0 ↦ (shift 1 0 v)])).

  Notation " e → f " := (cbv_once e f) (at level 101).

  Inductive cbv_multi : expr -> expr -> Prop :=
  | cbv_multi_refl e : cbv_multi e e
  | cbv_multi_more e e' e'' : cbv_multi e e' -> cbv_once e' e'' -> cbv_multi e e''.

  Notation "e →* f" := (cbv_multi e f) (at level 20).

End DeBruijn.