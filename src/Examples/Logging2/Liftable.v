From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct.
Require Import ExMach.WeakestPre ExMach.RefinementAdequacy.
Require Import Equality.
Set Default Proof Using "All".
Unset Implicit Arguments.


Notation "l ↦[ t ] v " := (mapsto (hG := t) l 1 v)
  (at level 20, t at level 50, format "l  ↦[ t ]  v") : bi_scope.

Section liftable.

  Context `{Σ : gFunctors}.
  Context `{L : Type}.
  Context `{V : Type}.
  Context `{!EqDecision L}.
  Context `{!Countable L}.

  Definition heapT := @gen_heapG L V Σ _ _.

  Lemma mapsto_disjoint h (a0 a1 : L) (v0 v1 : V) :
    ( mapsto (Σ := Σ) (hG := h) a0 1 v0 -∗
      mapsto (Σ := Σ) (hG := h) a1 1 v1 -∗
      ⌜ a0 ≠ a1 ⌝ )%I.
  Proof.
    iIntros "Ha0 Ha1".
    destruct (decide (a0 = a1)); auto; subst.
    iDestruct (mapsto_valid_2 with "Ha0 Ha1") as %Ha.
    exfalso.
    apply Ha; simpl.
    auto.
  Qed.

  Lemma big_sepM_disjoint h (m0 m1 : gmap L V) :
    ( ( [∗ map] a↦v ∈ m0, mapsto (Σ := Σ) (hG := h) a 1 v ) -∗
      ( [∗ map] a↦v ∈ m1, mapsto (Σ := Σ) (hG := h) a 1 v ) -∗
      ⌜ m0 ##ₘ m1 ⌝ )%I.
  Proof.
    iIntros "H0 H1".
    iIntros (i).
    unfold option_relation.
    destruct (m0 !! i) eqn:H0; destruct (m1 !! i) eqn:H1; try solve [ iPureIntro; auto ].
    iDestruct (big_sepM_lookup with "H0") as "H0"; eauto.
    iDestruct (big_sepM_lookup with "H1") as "H1"; eauto.
    iDestruct (mapsto_disjoint with "H0 H1") as %Hc.
    congruence.
  Qed.

  Class Liftable (P : heapT -> iProp Σ) := liftable :
    ( ∀ h1, P h1 -∗
      ∃ (m : gmap L V), ([∗ map] a ↦ v ∈ m, mapsto (Σ := Σ) (hG := h1) a 1 v) ∗
           ∀ h2, ([∗ map] a ↦ v ∈ m, mapsto (Σ := Σ) (hG := h2) a 1 v) -∗ P h2
    )%I.

  Global Instance star_liftable `{Liftable P} `{Liftable Q} : Liftable (fun h => P h ∗ Q h)%I.
  Proof.
    unfold Liftable in *.
    iIntros (?) "[Hp Hq]".
    iDestruct (H with "Hp") as (mp) "[Hpm Hpi]".
    iDestruct (H0 with "Hq") as (mq) "[Hqm Hqi]".
    iExists (mp ∪ mq).
    iDestruct (big_sepM_disjoint with "[$Hpm] [$Hqm]") as %?.
    iDestruct (big_sepM_union with "[$Hpm $Hqm]") as "Hm"; eauto.
    iFrame.
    iIntros (h2) "Hm".
    rewrite big_sepM_union; eauto.
    iDestruct "Hm" as "[Hpm Hqm]".
    iDestruct ("Hpi" with "Hpm") as "Hp".
    iDestruct ("Hqi" with "Hqm") as "Hq".
    iFrame.
  Qed.

  Global Instance pure_liftable P : Liftable (fun h => ⌜ P ⌝)%I.
  Proof.
    unfold Liftable in *.
    iIntros (?) "%".
    iExists ∅.
    rewrite big_sepM_empty.
    iSplit; try done.
    iIntros (h2) "Hm".
    iPureIntro. auto.
  Qed.

  Global Instance exists_liftable T P :
    (forall x, Liftable (P x)) ->
    Liftable (fun h => ∃ (x : T), P x h)%I.
  Proof.
    unfold Liftable in *.
    iIntros (H h) "H".
    iDestruct "H" as (x) "H".
    iDestruct (H with "H") as (m) "(Hm & Hx)".
    iExists _. iFrame.
    iIntros (h2) "Hm".
    iDestruct ("Hx" with "Hm") as "Hp".
    iExists _. iFrame.
  Qed.

  Global Instance map_liftable `{EqDecision LM} `{Countable LM} `(m : gmap LM VM) P :
    (forall a v, Liftable (P a v)) ->
    Liftable (fun h => [∗ map] a ↦ v ∈ m, (P a v h))%I.
  Proof.
    intros.
    unfold Liftable.
    iIntros (?) "Hm".
    iInduction m as [|i x m] "IH" using map_ind.
    - iExists ∅.
      repeat rewrite big_sepM_empty.
      iFrame.
      iIntros.
      repeat rewrite big_sepM_empty.
      done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hx Hm]"; auto.
      iDestruct ("IH" with "Hm") as (m0) "[Hm0 Hr0]".
      specialize (H0 i x).
      unfold Liftable in H0.
      iPoseProof H0 as "Hlift".
      iDestruct ("Hlift" with "Hx") as (m1) "[Hm1 Hr1]".
      iExists (m0 ∪ m1).
      iDestruct (big_sepM_disjoint with "[$Hm0] [$Hm1]") as %?.
      rewrite big_sepM_union; auto. iFrame.
      iIntros (h2) "Hh2".
      rewrite big_sepM_union; auto.
      iDestruct ("Hh2") as "[Hm0 Hm1]".
      iDestruct ("Hr0" with "Hm0") as "Hr0".
      iDestruct ("Hr1" with "Hm1") as "Hr1".
      rewrite big_sepM_insert; auto.
      iFrame.
  Qed.

  Global Instance mapsto_liftable :
    Liftable (fun h => a ↦[h] v)%I.
  Proof.
    intros; unfold Liftable.
    iIntros (h1) "Ha".
    iExists (<[a:=v]> ∅).
    rewrite big_sepM_insert.
    iFrame.
    rewrite big_sepM_empty.
    iSplitL. done.
    iIntros (h2) "Hh2".
    rewrite big_sepM_insert.
    iDestruct "Hh2" as "[Ha Hemp]".
    rewrite big_sepM_empty.
    iFrame.
    apply lookup_empty.
    apply lookup_empty.
  Qed.

  Global Instance emp_liftable : Liftable (fun h => emp)%I.
  Proof.
    intros; unfold Liftable.
    iIntros (h1) "H".
    iExists ∅.
    rewrite big_sepM_empty; iFrame.
    iIntros (h2) "Hm".
    rewrite big_sepM_empty; iFrame.
  Qed.

  Lemma list_liftable' `(l : list V) off P :
    (forall a v, Liftable (P a v)) ->
    Liftable (fun h => [∗ list] a ↦ v ∈ l, (P (off + a) v h))%I.
  Proof.
    intros.
    generalize dependent off.
    induction l; intros.
    - apply emp_liftable.
    - unfold Liftable in *.
      iIntros (h1) "[Ha Hl]".
      iDestruct (H with "Ha") as (ma0) "[Ha Hm0]".
      setoid_rewrite <- plus_n_Sm.
      setoid_rewrite <- plus_Sn_m.
      iDestruct (IHl with "Hl") as (ml) "[Hl Hml]".
      iExists (ma0 ∪ ml).
      iDestruct (big_sepM_disjoint with "[$Ha] [$Hl]") as %?.
      rewrite big_sepM_union; auto; iFrame.
      iIntros (h2) "Hh2".
      rewrite big_sepM_union; auto.
      iDestruct "Hh2" as "[Ha Hl]".
      iDestruct ("Hm0" with "Ha") as "Ha".
      iDestruct ("Hml" with "Hl") as "Hl".
      simpl.
      setoid_rewrite <- plus_n_Sm.
      setoid_rewrite <- plus_Sn_m.
      iFrame.
  Qed.

  Global Instance list_liftable `(l : list V) P :
    (forall a v, Liftable (P a v)) ->
    Liftable (fun h => [∗ list] a ↦ v ∈ l, (P a v h))%I.
  Proof.
    intros.
    apply (list_liftable' l 0 P) in H.
    simpl in H.
    auto.
  Qed.

End liftable.