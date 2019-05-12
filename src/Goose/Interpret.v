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
From Armada.Goose Require Import base Machine Filesys Heap GoZeroValues GoLayer Globals.
From Armada.Goose.Examples Require Import UnitTests.
From Armada.Goose Require Import Reify.

Fixpoint interpret_ds (T : Type) (r : RTerm.t ds ds T) (X : ds*ptrMap) : Output (ds*ptrMap) T :=
  match r with
  | RTerm.Pure ds t => Success X t
  | RTerm.Reads f => Success X (f (fst X))
  | RTerm.ReadSome f =>
      let t' := f (fst X) in match t' with
                        | Some t => Success X t
                        | None => Error
                        end
  | RTerm.ReadNone f =>
      let t' := f (fst X) in match t' with
                        | Some t => Error
                        | None => Success X tt
                        end
  | RTerm.AndThenDS r f =>
    let o := interpret_ds r X in
    match o with
    | Success b t => let r' := f t in let o' := interpret_ds r' b in o'
    | Error => Error
    | NotImpl => NotImpl
    end
  | RTerm.AllocPtr _ prm => 
    let p := snd X
                 in let f := @set ds (DynMap goModel.(@Ptr) Data.ptrModel) Data.allocs _ (updDyn p (Unlocked, prm))
                        in Success (f (fst X), (snd X) + 1) p
  | RTerm.UpdAllocs p pm =>
    let f := @set Data.State _ Data.allocs _ (updDyn p pm)
                        in Success (f (fst X), snd X) tt
  | RTerm.DelAllocs p =>
    let f := @set Data.State _ Data.allocs _ (deleteDyn p)
                        in Success (f (fst X), snd X) tt
  | _ => NotImpl
  end.

Fixpoint interpret_fs (T : Type) (r : RTerm.t fs fs T) (X : fs*ptrMap) : Output (fs*ptrMap) T :=
  match r with
  | RTerm.Pure fs t => Success X t
  | RTerm.Puts f => Success (f (fst X), snd X) tt
  | RTerm.AndThenFS r f =>
    let o := interpret_fs r X in
    match o with
    | Success b t => let r' := f t in let o' := interpret_fs r' b in o'
    | Error => Error
    | NotImpl => NotImpl
    end
  | RTerm.ZoomDS r => let (f, pm) := X in
                      let d := FS.heap f in
                      match (interpret_ds r (d, pm)) with
                      | Success (d', pm') t => Success (f <| FS.heap := d' |>, pm') t
                      | Error => Error
                      | NotImpl => NotImpl
                      end
  | _ => NotImpl
  end.

Fixpoint interpret_gb (T : Type) (r : RTerm.t gb gb T) (X : gb*ptrMap) : Output (gb*ptrMap) T :=
  match r with
  | RTerm.ReadsGB f => Success X (f (fst X))
  | RTerm.ReadSomeGB f =>
      let t' := f (fst X) in match t' with
                        | Some t => Success X t
                        | None => Error
                        end
  | RTerm.AndThenGB r f =>
    let o := interpret_gb r X in
    match o with
    | Success b t => let r' := f t in let o' := interpret_gb r' b in o'
    | Error => Error
    | NotImpl => NotImpl
    end
  | _ => NotImpl
  end.
    
Fixpoint interpret_gs (T : Type) (r : RTerm.t gs gs T) (X : gs*ptrMap) : Output (gs*ptrMap) T :=
  match r with
  | RTerm.Pure gs t => Success X t
  | RTerm.AndThenGS r f =>
      let o := interpret_gs r X in
      match o with
      | Success b t => let r' := f t in let o' := interpret_gs r' b in o'
      | Error => Error
      | NotImpl => NotImpl
      end
  | RTerm.ZoomFS r => let (g, pm) := X in
                      let f := Go.fs g in
                      match (interpret_fs r (f, pm)) with
                      | Success (f', pm') t => Success (g <| Go.fs := f' |>, pm') t
                      | Error => Error
                      | NotImpl => NotImpl
                      end
  | RTerm.ZoomGB r => let (g, pm) := X in
                      let b := Go.maillocks g in
                      match (interpret_gb r (b, pm)) with
                      | Success (b', pm') t => Success (g <| Go.maillocks := b' |>, pm') t
                      | Error => Error
                      | NotImpl => NotImpl
                      end
  | RTerm.Error _ _ _ => (Error)
  | RTerm.NotImpl _ => NotImpl
  | _ => NotImpl
  end.

Fixpoint interpret_nat (T : Type) (r : RTerm.t nat nat T) (X : nat*ptrMap) : Output (nat*ptrMap) T :=
  match r with
  | _ => NotImpl
  end.

Fixpoint interpret_es (T : Type) (r : RTerm.t es es T) (X : es*ptrMap) : Output (es*ptrMap) T :=
  match r with
  | RTerm.Ret t => Success X t
  | RTerm.CallGS r => let (e, pm) := X in
                    let (thr, g) := e in
                    match (interpret_gs r (g, pm)) with
                    | Success (g', pm') t => Success ((thr, g'), pm') t
                    | Error => Error                                                  
                    | NotImpl => NotImpl                                                  
                    end
  | RTerm.BindES r f =>
      let o := interpret_es r X in
      match o with
      | Success e t => let r' := f t in let o' := interpret_es r' e in o'
      | Error => Error
      | NotImpl => NotImpl
      end
  | RTerm.FstLiftES r => let (e, pm) := X in
                    let (thr, g) := e in
                    match (interpret_nat r (thr, pm)) with
                    | Success (thr', pm') t => Success ((thr', g), pm') t
                    | Error => Error                                                  
                    | NotImpl => NotImpl                                                  
                    end
  | _ => NotImpl
  end.

    
Definition interpret (T : Type) (r: RTerm.t es es T) : es -> Output es T :=
  fun a => match interpret_es r (a, ptrMap_null) with
           | Success x t => Success (fst x) t
           | Error => Error
           | NotImpl => NotImpl
           end.
  
(* Prove Interpreter *)
Theorem interpret_ok : forall T (r: RTerm.t es es T) (a : es),
    match (interpret r a) with
    | NotImpl => True
    | Error => rtermDenote r a Err
    | Success b t => rtermDenote r a (Val b t)
    end.
Proof.
  intros.
  destruct (interpret r a) eqn:H; eauto; unfold interpret in H.
  all: destruct (interpret_es r (a, ptrMap_null)) eqn:Hes; try discriminate; unfold interpret_es in Hes.
  invert r.
  - (* discriminate should work but won't *) unfold es in H1. admit.
Admitted.

(* Tests *)    
Definition literalCast {model:GoModel} : proc uint64 :=
  let x := 2 in
  Ret (x + 2).

Definition usePtr {model:GoModel} : proc unit :=
  p <- Data.newPtr uint64;
  _ <- Data.writePtr p 1;
  x <- Data.readPtr p;
  Data.writePtr p x.

Module Table.
  (* A Table provides access to an immutable copy of data on the filesystem,
     along with an index for fast random access. *)
  Record t {model:GoModel} := mk {
    Index: Map uint64;
    File: File;
  }.
  Arguments mk {model}.
  Global Instance t_zero {model:GoModel} : HasGoZero t := mk (zeroValue _) (zeroValue _).
End Table.

(* CreateTable creates a new, empty table. *)
Definition CreateTable {model:GoModel} (p:string) : proc Table.t :=
  index <- Data.newMap uint64;
  let! (f, _) <- FS.create "db" p;
  _ <- FS.close f;
  f2 <- FS.open "db" p;
  Ret {| Table.Index := index;
         Table.File := f2; |}.
     
Ltac test e :=
  let t := refl e in
  let e' := eval cbv [rtermDenote] in (rtermDenote t) in
  unify e e'.
