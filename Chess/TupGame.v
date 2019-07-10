Require Import List Util.ListMonad.
Import ListNotations.

Require Import Util.AssocList.
Require Import Util.Class.
Require Import Chess.Tuple.
Require Import Util.Color.
Require Import Util.Hierarchy.

Definition TableBase : Type := AssocList tuple nat.

Definition white_step_tup : list tuple -> TableBase -> list tuple :=
  fun ts base => rm_dups (
    do t <- ts;
    do m <- reverse_moves t;
    do_let s := t_standardizer (exec_rev_move m t);
    match lookup s base with
    | None => ret s
    | Some x => []
    end).

Definition white_step_tb : nat -> list tuple -> TableBase -> TableBase :=
  fun n ts base => base ++ map (fun t => (t,n)) ts.

Definition black_step_tup : list tuple -> TableBase -> list tuple :=
  fun ts base => rm_dups (
    do t <- ts;
    do m <- reverse_moves t;
    do_let s := t_standardizer (exec_rev_move m t);
    match forwards s with
    | None => []
    | Some ts' => if dec2 (forall x, In x (map t_standardizer ts') -> isSome (lookup (t_standardizer x) base)) then ret s else []
    end).

Definition black_step_tb : nat -> list tuple -> TableBase -> TableBase :=
 fun n ts base => base ++ map (fun t => (t,n)) ts.

Definition tb0 := map (fun t => (t,0)) standard_checkmates.
Definition t0 := standard_checkmates.

Definition t1 := white_step_tup t0 tb0.
Definition tb1 := white_step_tb 1 t1 tb0.

Definition t2 := black_step_tup t1 tb1.
Definition tb2 := black_step_tb 2 t2 tb1.

Definition t3 := white_step_tup t2 tb2.
Definition tb3 := white_step_tb 3 t3 tb2.

Definition t4 := black_step_tup t3 tb3.
Definition tb4 := black_step_tb 4 t4 tb3.

Definition t5 := white_step_tup t4 tb4.
Definition tb5 := white_step_tb 5 t5 tb4.

Definition t6 := black_step_tup t5 tb5.
Definition tb6 := black_step_tb 6 t6 tb5.

Definition t7 := white_step_tup t6 tb6.
Definition tb7 := white_step_tb 7 t7 tb6.

Definition t8 := black_step_tup t7 tb7.
Definition tb8 := black_step_tb 8 t8 tb7.

Definition t9 := white_step_tup t8 tb8.
Definition tb9 := white_step_tb 9 t9 tb8.

Definition t10 := black_step_tup t9 tb9.
Definition tb10 := black_step_tb 10 t10 tb9.

Definition t11 := white_step_tup t10 tb10.
Definition tb11 := white_step_tb 11 t11 tb10.

Definition t12 := black_step_tup t11 tb11.
Definition tb12 := black_step_tb 12 t12 tb11.

Definition t13 := white_step_tup t12 tb12.
Definition tb13 := white_step_tb 13 t13 tb12.

Definition t14 := black_step_tup t13 tb13.
Definition tb14 := black_step_tb 14 t14 tb13.

Definition t15 := white_step_tup t14 tb14.
Definition tb15 := white_step_tb 15 t15 tb14.

Inductive Result :=
  | Mate : nat -> Result
  | Draw : Result.

Print TableBase.

Definition getResult : option tuple -> TableBase -> Result :=
  fun o tb => match o with
              | None => Draw
              | Some t => match lookup (t_standardizer t) tb with
                          | None => Draw
                          | Some n => Mate n
                          end
              end.

Definition foo : AssocList tuple (Result * AssocList Move Result) :=
  do t <- standard_legals;
  match lookup t tb15 with
  | None => ret (t,(Draw, map  (fun m => (m, getResult (exec_move m t) tb15)) (moves t)))
  | Some n => ret (t,(Mate n, map (fun m => (m, getResult (exec_move m t) tb15)) (moves t)))
  end.

Require Import Chess.Chess.
Require Import Util.GroupAction.

Definition table := Eval native_compute in foo.

Definition query : tuple -> option (Result * AssocList Move Result) :=
  fun t => let s := standardizer (wk t) (bk t) (wr t) in
    match lookup (t_standardizer t) table with
    | None => None
    | Some (r,ps) => Some (r,map (fun '(m,r) => (s # m, r)) ps)
    end.

Compute query (White, (B,R3), (D,R4), (B,R1)).

Require Import Extraction ExtrHaskellBasic ExtrHaskellNatInt.
Extraction Language Haskell.
Extraction "base" query.
