From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement.
Require Import AtomicPairAPI AtomicPair.ImplShadow ExMach.WeakestPre ExMach.RefinementAdequacy.
Require Import AtomicPair.Helpers.
Unset Implicit Arguments.

Existing Instance from_exist_left_sep_later.

Set Default Proof Using "Type".
Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, stagedG Σ, !@cfgG (AtomicPair.Op) (AtomicPair.l) Σ}.
  Import ExMach.

  Definition ptr_map (ptr_val : nat) (pcurr: nat * nat) (pother: nat * nat) :=
    (ptr_addr d↦ ptr_val ∗
     (read_addrs ptr_val).1 d↦ pcurr.1 ∗
     (read_addrs ptr_val).2 d↦ pcurr.2 ∗
     (write_addrs ptr_val).1 d↦ pother.1 ∗
     (write_addrs ptr_val).2 d↦ pother.2)%I.

  Definition ExecLockInv :=
    fun (params: nat * ((nat * nat) * (nat * nat))) =>
      let '(ptr_val, (pcurr, pother)) := params in
            (source_state pcurr ∗
            ptr_map ptr_val pcurr pother)%I.

  Definition ExecInner := (∃ params, ExecLockInv params)%I.

  (* Post-crash, pre recovery we know the ptr mapping is in a good state w.r.t the
     abstract state, and the lock must have been reset 0 *)

  Definition CrashInner := (ExecInner ∗ lock_addr m↦ 0)%I.

  Definition lN : namespace := (nroot.@"lock").
  Definition lN' : namespace := (nroot.@"lock'").
  Definition iN : namespace := (nroot.@"inner").

  Definition ExecInv :=
    (source_ctx ∗ ∃ γlock, is_staged_lock lN lN' γlock lock_addr ExecLockInv)%I.
  Definition CrashInv := (source_ctx ∗ inv iN CrashInner)%I.

  Lemma read_of_swap ptr_val :
    (read_addrs (swap_ptr ptr_val)) = write_addrs ptr_val.
  Proof. destruct ptr_val => //=. Qed.

  Lemma write_of_swap ptr_val :
    (write_addrs (swap_ptr ptr_val)) = read_addrs ptr_val.
  Proof. destruct ptr_val => //=. Qed.

  Tactic Notation "open_step_close" open_constr(new_val) :=
    wp_bind;
    iMod (staged_inv_open with "[$]") as "(HEL&Hclose)"; [ set_solver |];
    iDestruct "HEL" as ">(Hsource&Hread&H1&H2&H3&H4)";
    try wp_step;
    iSpecialize ("Hclose" $! new_val);
    try (iMod ("Hclose" with "[$]") as "HEL"; iModIntro).

  Lemma write_refinement {T} j K `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} p:
    {{{ j ⤇ K (Call (AtomicPair.Write p)) ∗ Registered ∗ ExecInv }}}
      write p
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γlock) "#Hlockinv".
    wp_bind.
    iApply (wp_staged_lock with "Hlockinv").
    iIntros (x) "!> (Hlocked&HEL)".
    wp_bind.
    iMod (staged_inv_open with "[$]") as "(HEL&Hclose)".
    { set_solver+. }
    rewrite /ExecLockInv.
    destruct x as (ptr_val&pcurr&pother).
    iDestruct "HEL" as ">(Hsource&Hread&H1&H2&H3&H4)".
    wp_step.
    iMod("Hclose" $! (_, (_, _)) with "[$]") as "HEL".
    iModIntro.

    open_step_close (_, (pcurr, (fst p, snd pother))).
    open_step_close (_, (pcurr, (fst p, snd p))).

    open_step_close (swap_ptr ptr_val, (p, pcurr)).
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }
    iMod("Hclose" with "[Hsource Hread H1 H2 H3 H4]") as "HEL".
    { iFrame. simpl. rewrite ?read_of_swap ?write_of_swap; iFrame. }

    iModIntro.
    iApply (wp_staged_unlock with "[Hlockinv HEL Hlocked]").
    { iFrame "Hlockinv". iFrame. }
    iIntros "!> ?". by iApply "HΦ"; iFrame.
  Qed.

  Lemma read_refinement {T} j K `{LanguageCtx AtomicPair.Op (nat*nat) T AtomicPair.l K}:
    {{{ j ⤇ K (Call (AtomicPair.Read)) ∗ Registered ∗ ExecInv }}}
      read
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γlock) "#Hlockinv".
    wp_bind.
    iApply (wp_staged_lock with "Hlockinv").
    iIntros (x) "!> (Hlocked&HEL)".
    wp_bind.
    iMod (staged_inv_open with "[$]") as "(HEL&Hclose)".
    { set_solver+. }
    rewrite /ExecLockInv.
    destruct x as (ptr_val&pcurr&pother).
    iDestruct "HEL" as ">(Hsource&Hread&H1&H2&H3&H4)".
    wp_step.
    iMod("Hclose" $! (_, (_, _)) with "[$]") as "HEL".
    iModIntro.

    do 3 open_step_close (_, (_, (_, _))).
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }
    iMod("Hclose" with "[$]") as "HEL".

    iApply (wp_staged_unlock with "[Hlockinv HEL Hlocked]").
    { iFrame "Hlockinv". iFrame. }
    iIntros "!> ?".
    iApply fupd_intro_mask; first by set_solver.
    wp_ret. iApply "HΦ"; iFrame.
    destruct pcurr; eauto.
  Qed.

  Lemma init_mem_split:
    (([∗ map] i↦v ∈ init_zero, i m↦ v) -∗ lock_addr m↦ 0)%I.
  Proof.
    iIntros "Hmem".
    rewrite (big_opM_delete _ _ 0 0); last first.
    { rewrite /ExMach.mem_state. apply init_zero_lookup_lt_zero. rewrite /size. lia. }
    iDestruct "Hmem" as "(?&_)".
    iFrame.
  Qed.

  Lemma init_disk_split:
    (([∗ map] i↦v ∈ init_zero, i d↦ v)
       -∗ ptr_addr d↦ 0 ∗ copy0_fst d↦ 0 ∗ copy0_snd d↦ 0
          ∗ copy1_fst d↦ 0 ∗ copy1_snd d↦ 0)%I.
  Proof.
    iIntros "Hdisk".
    iPoseProof (disk_ptr_iter_split_aux O 4 with "Hdisk") as "H".
    { rewrite /size. lia. }
    iDestruct "H" as "($&_)".
  Qed.

End refinement_triples.

Module sRT <: exmach_refinement_type.

Definition Σ : gFunctors := #[Adequacy.exmachΣ; @cfgΣ AtomicPair.Op AtomicPair.l; lockΣ; stagedΣ].

Definition init_absr σ1a σ1c :=
  ExMach.l.(initP) σ1c ∧ AtomicPair.l.(initP) σ1a.

  Definition OpT := AtomicPair.Op.
  Definition Λa := AtomicPair.l.

  Definition impl := ImplShadow.impl.
  Existing Instance subG_cfgPreG.

  Instance CFG : @cfgPreG AtomicPair.Op AtomicPair.l Σ. apply _. Qed.
  Instance HEX : ExMach.Adequacy.exmachPreG Σ. apply _. Qed.
  Instance INV : Adequacy.invPreG Σ. apply _. Qed.
  Instance REG : inG Σ (csumR countingR (authR (optionUR (exclR unitC)))). apply _. Qed.

  Definition exec_inv := fun H1 H2 => (@ExecInv Σ H2 _ _ H1)%I.
  Definition exec_inner :=
    fun (H1: @cfgG OpT Λa Σ) (H2: exmachG Σ) => (lock_addr m↦ 0 ∗ @ExecInner Σ H2 H1)%I.

  Definition crash_param := fun (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ) => unit.
  Definition crash_inv := fun H1 H2 (_ : crash_param _ _) => @CrashInv Σ H2 H1.
  Definition crash_starter :=
    fun H1 H2 (_ : crash_param H1 H2) => (True%I : iProp Σ).
  Definition crash_inner := fun H1 H2 => (@CrashInner Σ H2 H1)%I.
  Definition E := nclose sourceN.

  Definition recv: proc ExMach.Op unit := Ret tt.

End sRT.

Module sRD := exmach_refinement_definitions sRT.

Module sRO : exmach_refinement_obligations sRT.

  Module eRD := exmach_refinement_definitions sRT.
  Import sRT.
  Import sRD.

  Lemma einv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _},
      Persistent (exec_inv H1 H2).
  Proof. apply _. Qed.

  Lemma cinv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _} P,
      Persistent (crash_inv H1 H2 P).
  Proof. apply _. Qed.

  Lemma nameIncl: nclose sourceN ⊆ E.
  Proof. solve_ndisj. Qed.

  Lemma recsingle: recover impl = rec_singleton recv.
  Proof. trivial. Qed.

  Lemma refinement_op_triples: refinement_op_triples_type.
  Proof.
    red. intros. iIntros "(?&?&HDB)". destruct op.
    - iApply (write_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
    - iApply (read_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
  Qed.

  Lemma exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx.
  Proof. iIntros (??) "(?&?)"; eauto. Qed.

  Lemma recv_triple: recv_triple_type.
  Proof.
    red. intros. iIntros "((#Hctx&#Hinv)&_)".
    wp_ret. iInv "Hinv" as "(Hcase&>?)" "_".
    iDestruct "Hcase" as ((ptr_val&(pcurr&pother))) ">(?&Hcase&?)".
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iExists pcurr, pcurr. iFrame.
    iSplitL "".
    { iPureIntro; econstructor. }
    iClear "Hctx Hinv".
    iIntros (???) "(#Hctx&Hstate)".
    iModIntro. iFrame. iExists (ptr_val, (pcurr, pother)).
    iFrame.
  Qed.

  Lemma init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → ExMach.state_wf σ1c.
  Proof.
    intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf.
  Qed.

  Lemma init_exec_inner : init_exec_inner_type.
  Proof.
    red. intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
    iIntros "(Hmem&Hdisk&#?&Hstate)".
    iPoseProof (init_mem_split with "Hmem") as "?".
    iPoseProof (init_disk_split with "Hdisk") as "(?&?&?&?&?)".
    iModIntro. iFrame. iExists (_, ((_, _), (_, _))); iFrame. simpl. iFrame.
  Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iDestruct "Hinv" as (γlock) "#Hlock".
    iMod (staged_lock_crack with "Hlock") as
        ((?&(?&?)&(?&?))) ">(?&?&?&?&?&?)"; first by set_solver+.
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iModIntro. iExists (_, (_, _)). iFrame.
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iFrame.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iInv "Hinv" as "(Hopen&_)" "_".
    iDestruct "Hopen" as ((?&(?&?))) ">?".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iModIntro. iExists (_, (_, _)). iFrame.
  Qed.

  Lemma crash_inner_inv : crash_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG) "(Hinv&Hmem)".
    iDestruct "Hinv" as ((?&(?&?))) "(?&?&?)".
    iMod (@inv_alloc Σ (exm_invG) iN _ CrashInner with "[-]").
    { iNext. iExists (_, (_, _)); iFrame. }
    iModIntro. iFrame. iExists tt. iFrame "Hsrc".
  Qed.

  Lemma exec_inner_inv : exec_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG) "Hinv".
    iDestruct "Hinv" as "(Hmem&Hinv)".
    iDestruct "Hinv" as ((?&(?&?))) "Hinv".
    iMod (@staged_lock_init Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ _ _ _ _ lN lN'
                    lock_addr (ExecLockInv) _ (_, (_, _)) with "[$] [$]") as (γlock) "H".
    iModIntro. iFrame "Hsrc". iExists _. iFrame.
  Qed.

  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "? (?&H)".
    iDestruct "H" as (?) "Hlock".
    iMod (staged_lock_crack with "Hlock") as
        ((?&(?&?)&(?&?))) ">(?&?&?&?&?&?)"; first by set_solver+.
    iApply fupd_mask_weaken; first by solve_ndisj.
    iExists _, _; iFrame.
    iSplitL "".
    { iPureIntro. econstructor. }
    iFrame. iIntros (????) "(?&?&Hmem)".
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iFrame. iExists (_, (_, _)). iFrame; eauto.
  Qed.

End sRO.

Module sR := exmach_refinement sRT sRO.
Import sR.

Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq AtomicPair.Op T) :
  sRT.init_absr σ1a σ1c →
  wf_client_seq es →
  ¬ proc_exec_seq AtomicPair.l es (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c res, proc_exec_seq ExMach.l (compile_proc_seq ImplShadow.impl es)
                                      (rec_singleton recv) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq AtomicPair.l es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof. apply sR.R.crash_refinement_seq. Qed.
