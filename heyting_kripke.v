Require Import Morphisms Setoid List.
Require Import structure filter nj_strong_complete.
Import ListNotations NJ.


Module kripke_heyting.

Class Kripke : Type := {
  worlds: Type;
  wle :> Leq worlds;
  wle_refl :> Reflexive leq;
  wle_trans : Transitive leq;
  aforces : worlds -> atom -> Prop;
  aforces_mon : forall w w', w <= w' -> forall P, aforces w P -> aforces w' P
  }.

Reserved Notation "w [- A" (at level 90).

Fixpoint forcing `{Kripke} (w : worlds) (A : prop) : Prop := match A with
  | Atomic A => aforces w A
  | And A B => and (w [- A) (w [- B)
  | Or A B => or (w [- A) (w [- B)
  | Impl A B => forall w', wle w w' -> w' [- A -> w' [- B
  | pfalse => False
  | ptrue => True
  end
where "w [- A" := (forcing w A).

Lemma forcing_mon `{Kripke} : forall w A, w [- A ->
 forall w', wle w w' -> w' [- A.
Proof.
induction A;simpl;intros.
- apply aforces_mon with w;assumption.
- destruct H0;split;auto.
- destruct H0;auto.
- apply H0. eapply wle_trans;eauto.
  assumption.
- assumption.
- split.
Defined.

Lemma NJ_sound_kripke `{Kripke} : forall Gamma A, Gamma |- A ->
  forall w, (forall P, In P Gamma -> w [- P) -> w [- A.
Proof.
induction 1;simpl;intros.
- split.
- split;auto.
- apply IHNJ. intros ? [[]|?]. assumption. apply forcing_mon with w.
  auto. assumption.
- left;auto.
- right;auto.
- simpl in IHNJ1. apply IHNJ1 with w. assumption. apply wle_refl.
  auto.
- destruct IHNJ1 with w. assumption.
  apply IHNJ2. intros ? [[]|?];auto.
  apply IHNJ3. intros ? [[]|?];auto.
- apply IHNJ;auto.
- apply IHNJ;auto.
- apply H1. assumption.
- destruct IHNJ with w. assumption.
Defined.

Section VarSec.

Variable (K : Kripke).

Definition Omega : Type := sigT (fun H : set (@worlds K) =>
 forall k k', wle k k' -> H k -> H k').

Global Instance Omega_eq : Equiv Omega := fun x y => x.1 == y.1.

Global Instance Omega_leq : Leq Omega := fun x y => x.1 <= y.1.

Instance Omega_setoid : Setoid Omega.
Proof.
constructor.
split; reflexivity.
split. apply H. apply H.
split. eapply transitivity. apply H. apply H0.
eapply transitivity. apply H0. apply H.
Defined.

Instance Omega_order : Order Omega.
Proof.
split. apply _.
split;
apply set_order;auto. symmetry;assumption. symmetry;assumption.
split. intro;apply set_order.
red. unfold leq;unfold Omega_leq. intros ? ? ?.
apply transitivity.
red. unfold equiv,Omega_eq,leq,Omega_leq. intros ? ?.
apply antisymmetry. apply _.
Defined.

Global Instance Omega_meet : Meet Omega.
Proof.
intros x y. exists (fun a => x.1 a /\ y.1 a).
intros ??? [? ?];split. eapply x.2;eauto. eapply y.2;eauto.
Defined.

Global Instance Omega_join : Join Omega.
Proof.
intros x y. exists (fun a => x.1 a \/ y.1 a).
intros ??? [?|?];[left|right]. eapply x.2;eauto. eapply y.2;eauto.
Defined.

Global Instance Omega_top : Top Omega.
Proof.
exists (fun _ => True). auto.
Defined.

Global Instance Omega_bot : Bot Omega.
Proof.
exists (fun _ => False). auto.
Defined.

Global Instance Omega_imply : Imply Omega.
Proof.
intros x y.
exists (fun a => exists z : Omega, meet x z <= y /\ z.1 a).
intros. destruct H0 as [z [H0 H0']].
exists z. split. assumption. eapply z.2;eauto.
Defined.

Global Instance Omega_heyting : Heyting Omega.
Proof.
split.
split.
split; (split;[apply _| | |]).
intros ? ? ? ?. apply H.
intros ? ? ? ?. apply H.
split. apply H;auto. apply H0;auto.
left;assumption. right;assumption.
intros ??? ? ? ? [?|?]. apply H;auto. apply H0;auto.
split.
intros ? ? [].
split;intros ? ? ?.
destruct H0. apply H in H0. destruct H0 as [? [? ?]].
apply H0. split;assumption.
exists a. split. intros ? [??];apply H;split;assumption.
assumption.
Defined.

Definition aeval : atom -> Omega.
Proof.
intros A.
exists (fun k => aforces k A).
intros ???;apply aforces_mon. assumption.
Defined.

Lemma Omega_embed : worlds -> Omega.
Proof.
intros X. exists (leq X).
intros ????. eapply wle_trans;eauto.
Defined.

Lemma validity : forall A k, k [- A <-> (interp _ aeval A).1 k.
Proof.
induction A;simpl;intros.
- reflexivity.
- split. intros X. split. apply IHA1. apply X. apply IHA2. apply X.
  unfold incl. intros. destruct H. apply IHA1 in H. apply IHA2 in H0.
  auto.

- split. intros X. destruct X.
  left;apply IHA1;assumption.
  right;apply IHA2;assumption.
  unfold incl. intros [?|?].
  apply IHA1 in H. left;assumption.
  apply IHA2 in H. right;assumption.

- unfold incl. split. intros X.
  exists (Omega_embed k). split.
  intros ? [? ?]. apply IHA2. apply IHA1 in H. apply X.
  assumption. assumption.
  apply wle_refl.

  intros [z [H H0]].
  intros. apply IHA2. apply H. split.
  apply IHA1;assumption. eapply z.2;eauto.

- split. intros [].
  intros [].

- split;split.
Defined.

End VarSec.
End kripke_heyting. Import kripke_heyting.



Section Heyting_Kripke.

Variable T : Type.
Context `{Heyting T}.
Variable aeval : atom -> T.

Record World :=
 { world_set : set T
 ; world_prime : IsPrimeFilter world_set
 ; world_proper : exists x, ~ world_set x }.

Existing Instance world_prime.

Instance K : Kripke.
Proof.
split with World (fun x y => (world_set x) <= (world_set y))
 (fun (w : World) a => world_set w (aeval a)).
intro. red. reflexivity.
intros ???. unfold leq. apply transitivity.
intros. apply H0. assumption.
Defined.

Lemma equivalence : forall A w, w [- A <-> world_set w (interp _ aeval A).
Proof.
induction A;intros;simpl.
- reflexivity.

- split;intros.
  apply filter_meet;[apply IHA1|apply IHA2];tauto.
  apply filter_equiv in H0.
  split;[apply IHA1|apply IHA2];tauto.

- split;intros.
  apply filter_join. destruct H0;[apply IHA1 in H0|apply IHA2 in H0];tauto.
  apply primefilter_or in H0.
  destruct H0;[apply IHA1 in H0|apply IHA2 in H0];tauto.

- split.
  intros.
  apply PEM;intro.
  assert (~ gen_filter (fun x => world_set w x \/ (interp _ aeval A1 = x))
     (interp T aeval A2)).
  intro Hgen. apply H1. eapply prop_4_12;[ | | | apply Hgen]. apply _.
  change (IsFilter (world_set w)). apply _.
  intros. reflexivity.
  apply (@exists_prime_not_incl _ _ _ _ _ _ _ _ _ _ _ _) in H2.
  destruct H2 as [F' [HF' [Hsub Hneg]]].
  apply Hneg.
  apply (IHA2 (Build_World F' HF' (ex_intro (fun x => ~ F' x) _ Hneg))).
  apply H0.
  simpl. eapply transitivity;[|apply Hsub].
  eapply transitivity;[|apply gen_filter_sub].
  intros ??. tauto.
  apply IHA1. simpl.
  apply Hsub. apply gen_filter_sub. right. reflexivity.

  intros Hw F' Hsub HA1.
  apply IHA1 in HA1;apply IHA2.
  apply Hsub in Hw.
  red in Hw.
  apply filter_up with
   (meet (interp T aeval A1 __> interp T aeval A2) (interp T aeval A1)).
  apply filter_meet;assumption.
  apply heyting_imply. reflexivity.

- split. intros [].
  intros. destruct (world_proper w).
  apply H1. apply filter_up with bot. assumption. apply bounded_bot.

- split;auto.
  intros _. apply filter_top.
Defined.

End Heyting_Kripke.
