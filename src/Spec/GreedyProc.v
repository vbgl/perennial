From Armada.Spec Require Import Proc.
From Transitions Require Import Relations.
Require Import List.

Global Set Implicit Arguments.
Global Generalizable All Variables.
Global Set Printing Projections.
Import RelationNotations.

Section GreedyProc.
  Variable Op : Type -> Type.
  Context `(sem: Dynamics Op OpState).
  Notation proc := (proc Op).
  Notation thread_pool := (thread_pool Op).
  Notation exec_step := (exec_step sem).
  Notation exec_pool_hd := (exec_pool_hd sem).
  Notation exec_pool := (exec_pool sem).
  Fixpoint greedy_exec_pool (ps: list {T & proc T}) : relation State State thread_pool :=
    match ps with
    | nil => none
    | existT _ T p :: ps' =>
      (exec_pool_hd p ps')
    end.

  Inductive greedy_exec_pool_alt (ps1: thread_pool) (σ1: State) (ret: Return State thread_pool) : Prop :=
    | step_atomic_valid {T} (e1 e2: proc T) ps2 efs σ2 t1 :
       ps1 = existT _ _ e1 :: t1 ->
       ps2 = existT _ _ e2 :: t1 ++ efs ->
       ret = Val σ2 ps2 ->
       exec_step e1 σ1 (Val σ2 (e2, efs)) ->
       greedy_exec_pool_alt ps1 σ1 ret
    | step_atomic_error {T} (e1: proc T) t1 :
       ps1 = existT _ _ e1 :: t1 ->
       ret = Err ->
       exec_step e1 σ1 Err ->
       greedy_exec_pool_alt ps1 σ1 ret.

  Lemma greedy_exec_pool_equiv_alt_val ps1 σ1 σ2 ps2:
    greedy_exec_pool ps1 σ1 (Val σ2 ps2) <-> greedy_exec_pool_alt ps1 σ1 (Val σ2 ps2).
  Admitted.
  Lemma greedy_exec_pool_equiv_alt_err ps1 σ1:
    greedy_exec_pool ps1 σ1 Err <-> greedy_exec_pool_alt ps1 σ1 Err.
  Admitted.
  Definition greedy_exec_partial {T} (p: proc T) :=
    bind_star (greedy_exec_pool) ((existT _ T p) :: nil).

  Definition greedy_exec_halt {T} (p: proc T) : relation State State unit :=
    greedy_exec_partial p;; pure tt.

  (* A complete execution is one in which the first thread is a value *)
  Definition greedy_exec {T} (p: proc T) : relation State State {T: Type & T} :=
    ps <- greedy_exec_partial p;
    match ps with
    | existT _ _ (Ret v) :: _ => pure (existT _ _ v)
    | _ => @none _ _ {T: Type & T}
    end.
  Theorem greedy_exec_subrelation_exec ps1 σ1 r:
    greedy_exec_pool ps1 σ1 r -> exec_pool ps1 σ1 r.
  Admitted. 
End GreedyProc.