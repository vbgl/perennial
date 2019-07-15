From iris.algebra Require Import gmap auth agree gset coPset excl.
From iris.base_logic.lib Require Export fancy_updates.
From stdpp Require Export namespaces.
From iris.base_logic.lib Require Import wsat invariants saved_prop.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Class stagedG (Σ : gFunctors) : Set := WsatG {
  staging_auth_inG :> inG Σ (authR (optionUR (exclR positiveC)));
}.

Definition stagedΣ : gFunctors := #[GFunctor (authR (optionUR (exclR positiveC)))].
Instance subG_stagedΣ {Σ} : subG stagedΣ Σ → stagedG Σ.
Proof. solve_inG. Qed.

Definition staged_inv `{!invG Σ, !stagedG Σ} `{Countable A} (N: namespace) (γ: gname)
           (Φ: A → iProp Σ) : iProp Σ :=
  (inv N (∃ a, own γ (● Excl' (encode a)) ∗ Φ a))%I.

Definition staged_value `{!stagedG Σ} `{Countable A} (N: namespace) γ (a: A)
  : iProp Σ := own γ (◯ Excl' (encode a)).

Section inv.
Context `{!invG Σ, !stagedG Σ}.
Context `{Countable A}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types Φ : A → iProp Σ.
Implicit Types P Q R : iProp Σ.

(* TODO *)
(*
Global Instance staged_contractive N γ : Contractive (staged_inv N γ).
Proof. rewrite /staged_inv. solve_contractive. Qed.
*)

Global Instance staged_ne N γ :
  Proper (pointwise_relation A (dist n) ==> dist n) (staged_inv N γ).
Proof. intros. solve_proper. Qed.

Global Instance staged_proper N γ :
  Proper (pointwise_relation A (⊣⊢) ==> (⊣⊢)) (staged_inv N γ).
Proof.
  intros Φ1 Φ2 HΦ. apply equiv_dist=> n.
  apply staged_ne=> x. apply equiv_dist, HΦ.
Qed.

Global Instance staged_persistent N γ (Φ : A → iProp Σ) : Persistent (staged_inv N γ Φ).
Proof. rewrite /staged_inv. apply _. Qed.

Lemma staged_inv_iff N γ Φ1 Φ2 :
  ▷ □ (∀ x, Φ1 x ↔ Φ2 x) -∗ staged_inv N γ Φ1 -∗ staged_inv N γ Φ2.
Proof.
  iIntros "#HPQ". iApply inv_iff. iNext. iAlways. iSplit.
  - iIntros "H". iDestruct "H" as (?) "(?&?)". iExists _. iFrame.
    by iApply "HPQ".
  - iIntros "H". iDestruct "H" as (?) "(?&?)". iExists _. iFrame.
    by iApply "HPQ".
Qed.

Lemma staged_inv_alloc N E Φ x:
  ▷ (Φ x) ={E}=∗ ∃ γ, staged_inv N γ Φ ∗ staged_value N γ x.
Proof.
  iMod (own_alloc (● (Excl' (encode x)) ⋅ ◯ (Excl' (encode x)))) as (γ) "[H1 H2]".
  { apply auth_both_valid_2; [econstructor | reflexivity]. }
  iIntros "HP".
  iMod (inv_alloc N E _ with "[HP H1]") as "HI"; last first.
  { iModIntro. iExists γ. iSplitL "HI".
    - iApply "HI".
    - by iFrame.
  }
  iNext. iExists x. by iFrame.
Qed.

Lemma staged_inv_open' `{Inhabited A} E N γ Φ x:
  ↑N ⊆ E → staged_inv N γ Φ ∗ staged_value N γ x
           ={E,E∖↑N}=∗ ▷ (Φ x) ∗ (∀ x', ▷ Φ x' ={E∖↑N,E}=∗ staged_value N γ x').
Proof.
  iIntros (?) "(#Hinv&Hval)".
  iInv N as "H" "HC".
  iDestruct "H" as (a) "(>Hγ&HΦ)".
  iDestruct (own_valid_2 with "Hγ Hval") as "#H".
  iDestruct "H" as %[Henc%Excl_included%leibniz_equiv _]%auth_both_valid.
  apply encode_inj in Henc; subst.
  iFrame.
  iModIntro. iIntros (a'). iIntros "HΦ'".
  iMod (own_update_2 _ _ _ (● Excl' (encode a') ⋅ ◯ Excl' (encode a')) with "Hγ Hval") as "[Hγ' Hγ]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  iMod ("HC" with "[HΦ' Hγ']").
  * iNext. iExists _. by iFrame.
  * iModIntro. by iFrame.
Qed.

Lemma staged_inv_weak_open E N γ Φ:
  ↑N ⊆ E → staged_inv N γ Φ ={E,E∖↑N}=∗ ▷ (∃ x, Φ x).
Proof.
  iIntros (?) "#Hinv".
  iInv N as "H" "HC".
  iModIntro. iNext. iDestruct "H" as (?) "(?&?)". iExists _. by iFrame.
Qed.

Global Instance into_inv_staged_inv1 N γ Φ : IntoInv (staged_inv N γ Φ) N := {}.

Definition staged_inv_exact N Φ (x: A) :=
  (∃ γ, staged_inv N γ Φ ∗ staged_value N γ x)%I.

Lemma staged_inv_open `{Inhabited A} E N Φ x:
  ↑N ⊆ E → staged_inv_exact N Φ x
           ={E,E∖↑N}=∗ ▷ (Φ x) ∗ (∀ x', ▷ Φ x' ={E∖↑N,E}=∗ staged_inv_exact N Φ x').
Proof.
  iIntros (?) "H". iDestruct "H" as (?) "(#?&?)".
  iMod (staged_inv_open' with "[$]") as "($&H)"; auto.
  iModIntro. iIntros (x') "?". iMod ("H" with "[$]").
  iModIntro. iExists _. by iFrame.
Qed.

(*
Global Instance into_acc_inv E N Φ x :
  IntoAcc (staged_inv_exact N Φ x)
          (↑N ⊆ E) True (fupd E (E∖↑N)) (fupd (E∖↑N) E)
          (λ x, Φ x)%I (λ x, ▷ Φ x)%I (λ x, None)%I.
Proof.
  rewrite /IntoAcc /accessor.
  iIntros (?) "(#Hinv&Hvalue) _". iMod (staged_inv_open with "[Hvalue]") as "($&?)"; first done.
  { by iFrame. }
  simpl default.
  { auto.
Qed.

Lemma inv_open_timeless E N P `{!Timeless P} :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ P ∗ (P ={E∖↑N,E}=∗ True).
Proof.
  iIntros (?) "Hinv". iMod (inv_open with "Hinv") as "[>HP Hclose]"; auto.
  iIntros "!> {$HP} HP". iApply "Hclose"; auto.
Qed.
*)

End inv.
