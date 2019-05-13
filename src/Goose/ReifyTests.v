From stdpp Require Import base countable.
From Tactical Require Import ProofAutomation.

From RecordUpdate Require Import RecordUpdate RecordSet.
From Transitions Require Import Relations.

From Armada Require Import Helpers.RecordZoom.
From Armada Require Import Spec.Proc.
From Armada Require Import Spec.GreedyProc.
From Armada Require Import Spec.InjectOp.
From Armada Require Import Spec.SemanticsHelpers.
From Armada Require Import Spec.LockDefs.
From Armada Require Import Spec.Layer.
From Armada.Goose Require Import base Machine Filesys Heap GoZeroValues GoLayer Globals Reify.

(* DataOp Reification Tests *)
Theorem testNewLock : reify (DataOp (Data.NewLock)) = RTerm.ZoomFS (RTerm.ZoomDS (RTerm.AllocPtr Ptr.Lock ())).
  vm_compute; reflexivity.
Qed.

Theorem testPtrDeref : reify (DataOp (Data.PtrDeref 4 3)) = RTerm.Error gs gs nat.
Admitted.

Theorem testPtrStore : reify (DataOp (Data.PtrStore 5 4 3 Begin)) = RTerm.Error gs gs ().
Admitted.

Theorem testSlideAppend : reify (DataOp (Data.SliceAppend (slice.mk nat 5 4 3) 2)) = RTerm.Error gs gs (slice.t nat).
Admitted.

Theorem testNewMap : reify (DataOp (Data.NewMap nat)) =
  RTerm.ZoomFS
      (RTerm.ZoomDS
         (RTerm.AllocPtr (Ptr.Map nat)
            {|
            gmap.gmap_car := {|
                             pmap.pmap_car := pmap.PLeaf;
                             pmap.pmap_prf := I |};
            gmap.gmap_prf := I |})).
  vm_compute; reflexivity.
Qed.

Theorem testMapAlter : reify (DataOp (@Data.MapAlter _ nat 3(*map*) 3 (fun x => x) Begin)) = RTerm.Error gs gs ().
Admitted.

Theorem testMapLookup : reify (DataOp (Data.MapLookup 2 3)) = RTerm.Error gs gs (option nat).
Admitted.

Theorem testMapStartIter : reify (DataOp (Data.MapStartIter 2)) = RTerm.Error gs gs (list (uint64 * nat)).
Admitted.

Theorem testMapEndIter : reify (DataOp (@Data.MapEndIter _ nat 3)) = RTerm.Error gs gs ().
Admitted.

Theorem testLockAcquire : reify (DataOp (Data.LockAcquire 0 Reader)) = RTerm.Error gs gs ().
Admitted.

Theorem testLockRelease : reify (DataOp (Data.LockRelease 0 Reader)) = RTerm.Error gs gs ().
Admitted.

Theorem testUint64Get : reify (DataOp (Data.Uint64Get (slice.mk unit 1 2 3) Begin)) = RTerm.Error gs gs ().
Admitted.

Theorem testUint64Put : reify (DataOp (Data.Uint64Put (slice.mk unit 1 2 3) 4 Begin)) = RTerm.Error gs gs ().
Admitted.

Theorem testBytesToString : reify (DataOp (Data.BytesToString (slice.mk unit 1 2 3))) = RTerm.Error gs gs string.
Admitted.

Theorem testStringToBytes : reify (DataOp (Data.StringToBytes "a")) =
  RTerm.ZoomFS
    (RTerm.ZoomDS
       (RTerm.AndThenDS
          (RTerm.AllocPtr (Ptr.Heap ()) [()])
          (λ x : nat,
             RTerm.Pure ds
               {|
               slice.ptr := x;
               slice.offset := 0;
               slice.length := 1 |}))).
vm_compute; reflexivity.
Qed.

Theorem testRandomUint64 : reify (DataOp (Data.RandomUint64)) =
  RTerm.ZoomFS
    (RTerm.ZoomDS
       (RTerm.NotImpl
          (such_that
             (λ (_ : ds) (_ : nat), True)))).
vm_compute; reflexivity.
Qed.