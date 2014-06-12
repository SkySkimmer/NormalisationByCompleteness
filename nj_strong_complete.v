Global Generalizable All Variables.

Require Export Morphisms Setoid.
Require Export List.
Export ListNotations.

Require Export structure.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation "( x ; y )" := (existT _ x y).

Definition in_app_or : forall {A : Type} (l m : list A) (a : A),
       In a (l ++ m) -> In a l \/ In a m
 := fun (A : Type) (l m : list A) (a : A) =>
list_ind (fun l0 : list A => In a (l0 ++ m) -> In a l0 \/ In a m)
  (fun H : In a m => or_intror H)
  (fun (a0 : A) (y : list A) (H : In a (y ++ m) -> In a y \/ In a m)
     (H0 : a0 = a \/ In a (y ++ m)) =>
   or_ind (fun H1 : a0 = a => or_introl (or_introl H1))
     (fun H1 : In a (y ++ m) =>
      or_ind (fun H2 : In a y => or_introl (or_intror H2))
        (fun H2 : In a m => or_intror H2) (H H1)) H0) l.

Definition in_or_app : forall {A : Type} (l m : list A) (a : A),
       In a l \/ In a m -> In a (l ++ m)
 := fun (A : Type) (l m : list A) (a : A) =>
list_ind (fun l0 : list A => In a l0 \/ In a m -> In a (l0 ++ m))
  (fun H : False \/ In a m =>
   or_ind (fun H0 : False => False_ind (In a m) H0) (fun H0 : In a m => H0) H)
  (fun (H : A) (y : list A) (H0 : In a y \/ In a m -> In a (y ++ m))
     (H1 : (H = a \/ In a y) \/ In a m) =>
   or_ind
     (fun H2 : H = a \/ In a y =>
      or_ind (fun H3 : H = a => or_introl H3)
        (fun H3 : In a y => or_intror (H0 (or_introl H3))) H2)
     (fun H2 : In a m => or_intror (H0 (or_intror H2))) H1) l.

Definition in_app_iff : forall {A : Type} (l l' : list A) (a : A),
       In a (l ++ l') <-> In a l \/ In a l' := 
fun (A : Type) (l l' : list A) (a : A) =>
conj (fun H : In a (l ++ l') => in_app_or l l' a H)
  (fun H : In a l \/ In a l' => in_or_app l l' a H).



Class EqDec (A : Type) := eqdec : forall x y : A, {x=y}+{~x=y}.

Lemma app_insert_find : forall A : Type,
forall P Q (x : A) P' Q', P++Q = P'++x::Q' ->
(sig (fun P0 => P = P'++x::P0 /\ Q' = P0++Q ))+
(sig (fun Q0 => P' = P++Q0 /\ Q=Q0++x::Q')).
Proof.
induction P;intros.
simpl in H. right. exists P'. simpl. split; auto.
destruct P'. simpl in H;simpl. left. exists P. injection H;intros;subst;auto.
simpl in H. injection H;intros.
apply IHP in H0. destruct H0 as [[P0 H0]|[Q0 H0]];destruct H0.
left. exists P0. simpl. split;auto. subst. auto.
right;exists Q0. subst;split;auto. 
Defined.

Lemma In_find : forall A {Hdec : EqDec A}, forall (x : A) l, In x l ->
sigT (fun l1 => sigT (fun l2 => l = l1++x::l2)).
Proof.
induction l. intros [].
intros. simpl in H.
destruct (Hdec a x). exists nil;exists l. simpl. f_equal;assumption.
assert (In x l). destruct H;auto. destruct n;auto.
apply IHl in H0. exists (a::(projT1 H0)). exists (projT1 (projT2 H0)).
simpl. f_equal.
destruct H0 as [l1 [l2 H0]]. simpl;auto.
Defined.

Axiom atom : Type.
Hypothesis atom_ne : exists a : atom, True.
Hypothesis atom_dec : EqDec atom.

Inductive prop : Type :=
  | Atomic : atom -> prop
  | And : Meet prop
  | Or : Join prop
  | Impl : Imply prop
  | pfalse : Bot prop
  | ptrue : Top prop
.

Existing Instance And.
Existing Instance Or.
Existing Instance Impl.
Existing Instance pfalse.
Existing Instance ptrue.

Definition neg (p : prop) : prop := p __> bot.

Global Instance prop_dec : EqDec prop.
Proof.
red. induction x;destruct y;try solve [right;discriminate].
- destruct (atom_dec a a0). left;f_equal;assumption. right;injection;assumption.
- destruct (IHx1 y1);[destruct (IHx2 y2)|];
  solve [left;f_equal;assumption|right;injection;auto].
- destruct (IHx1 y1);[destruct (IHx2 y2)|];
  solve [left;f_equal;assumption|right;injection;auto].
- destruct (IHx1 y1);[destruct (IHx2 y2)|];
  solve [left;f_equal;assumption|right;injection;auto].
- left;reflexivity.
- left;reflexivity.
Defined.

Section interpSec.

Context (A : Type) `{H : Heyting A}.
Variable (aEval : atom -> A).

Fixpoint interp (p : prop) : A := match p with
  | Atomic a => aEval a
  | And p q => meet (interp p) (interp q)
  | Or p q => join (interp p) (interp q)
  | Impl p q => imply (interp p) (interp q)
  | pfalse => bot
  | ptrue => top
 end.

End interpSec.

Definition context := list prop.
Hint Unfold context.

Definition sub_ctx (G G' : context) := (forall A, In A G -> In A G').
Hint Unfold sub_ctx.

Module NJ.

Reserved Notation "G |- A" (at level 90).
Inductive NJ : context -> prop -> Prop :=
  | NJ_top : forall Gamma, Gamma |- ptrue
  | NJ_inconj : forall Gamma A B, Gamma |- A -> Gamma |- B -> Gamma |- meet A B
  | NJ_inmp : forall Gamma A B, A::Gamma |- B -> Gamma |- A __> B
  | NJ_indisjl : forall Gamma A B, Gamma |- A -> Gamma |- join A B
  | NJ_indisjr : forall Gamma A B, Gamma |- B -> Gamma |- join A B
  | NJ_exmp : forall Gamma A B, Gamma |- A __> B -> Gamma |- A -> Gamma |- B
  | NJ_exdisj : forall Gamma A B, Gamma |- join A B ->
     forall C, A::Gamma |- C -> B::Gamma |- C -> Gamma |- C
  | NJ_exconjl : forall Gamma A B, Gamma |- meet A B -> Gamma |- A
  | NJ_exconjr : forall Gamma A B, Gamma |- meet A B -> Gamma |- B
  | NJ_ax : forall Gamma A {H : In A Gamma}, Gamma |- A  
  | NJ_bot : forall Gamma, Gamma |- pfalse -> forall A, Gamma |- A
where "G |- A" := (NJ G A).


Inductive cf : context -> prop -> Prop :=
  | ne_cf : forall G A, ne G A -> cf G A
  | cf_top : forall Gamma, cf Gamma ptrue
  | cf_inconj : forall Gamma A B, cf Gamma A -> cf Gamma B -> cf Gamma (And A B)
  | cf_inmp : forall Gamma A B, cf (A::Gamma) B -> cf Gamma (Impl A B)
  | cf_indisjl : forall Gamma A B, cf Gamma A -> cf Gamma (Or A B)
  | cf_indisjr : forall Gamma A B, cf Gamma B -> cf Gamma (Or A B)
with ne : context -> prop -> Prop :=
  | ne_exmp : forall Gamma A B, ne Gamma (Impl A B) -> cf Gamma A
     -> ne Gamma B
  | ne_exdisj : forall Gamma A B, ne Gamma (Or A B) ->
     forall C, cf (A::Gamma) C -> cf (B::Gamma) C -> ne Gamma C
  | ne_exconjl : forall Gamma A B, ne Gamma (And A B) -> ne Gamma A
  | ne_exconjr : forall Gamma A B, ne Gamma (And A B) -> ne Gamma B
  | ne_ax : forall Gamma A (H : In A Gamma), ne Gamma A
  | ne_bot : forall Gamma, ne Gamma pfalse -> forall A, ne Gamma A
.

Lemma NJ_generalise : forall Gamma Sigma, (forall A, In A Gamma -> In A Sigma)
 -> forall A, Gamma |- A -> Sigma |- A.
Proof.
intros ? ? Hsub ? d;revert Gamma A d Sigma Hsub.
induction 1;intros.
- constructor.
- constructor;auto.
- constructor. apply IHd. intros.
  simpl;destruct H;auto.
- apply NJ_indisjl. auto.
- apply NJ_indisjr. auto.
- apply NJ_exmp with A;auto.
- apply NJ_exdisj with A B;auto.
  apply IHd2. intros ? [?|?];simpl;auto.
  apply IHd3. intros ? [?|?];simpl;auto.
- apply NJ_exconjl with B. auto.
- apply NJ_exconjr with A. auto.
- apply NJ_ax;auto.
- apply NJ_bot;auto.
Defined.

Lemma cf_NJ : forall G A, cf G A -> G |- A
with ne_NJ : forall G A, ne G A -> G |- A.
Proof.
intros G A d;destruct d.
apply ne_NJ. assumption.
apply NJ_top.
apply NJ_inconj;apply cf_NJ;assumption.
apply NJ_inmp;apply cf_NJ;assumption.
apply NJ_indisjl;apply cf_NJ;assumption.
apply NJ_indisjr;apply cf_NJ;assumption.
intros G A d;destruct d.
apply NJ_exmp with A;[apply ne_NJ|apply cf_NJ];assumption.
apply NJ_exdisj with A B;[apply ne_NJ|apply cf_NJ|apply cf_NJ];assumption.
apply NJ_exconjl with B;apply ne_NJ;assumption.
apply NJ_exconjr with A;apply ne_NJ;assumption.
apply NJ_ax;assumption.
apply NJ_bot;apply ne_NJ;assumption.
Defined.

Lemma cf_gen : forall G A, cf G A -> forall G', sub_ctx G G' -> cf G' A
with ne_gen : forall G A, ne G A -> forall G', sub_ctx G G' -> ne G' A.
Proof.
intros ?? d;destruct d;intros.
apply ne_cf. apply ne_gen with G;assumption.
apply cf_top.
apply cf_inconj;apply cf_gen with Gamma;assumption.
apply cf_inmp;apply cf_gen with (A::Gamma);try assumption.
intros ? [?|?];[left|right];auto.
apply cf_indisjl;apply cf_gen with Gamma;assumption.
apply cf_indisjr;apply cf_gen with Gamma;assumption.
intros ?? d;destruct d;intros.
apply ne_exmp with A;[apply ne_gen with Gamma|apply cf_gen with Gamma];
assumption.
apply ne_exdisj with A B;[apply ne_gen with Gamma|
apply cf_gen with (A::Gamma)|apply cf_gen with (B::Gamma)];try assumption;
(intros ? [?|?];[left|right];auto).
apply ne_exconjl with B;apply ne_gen with Gamma;assumption.
apply ne_exconjr with A;apply ne_gen with Gamma;assumption.
apply ne_ax. apply H0. assumption.
apply ne_bot. apply ne_gen with Gamma;assumption.
Defined.

Fixpoint replace_atom_prop (a : atom) (b : prop) (f : prop) : prop :=
 match f with
  | Atomic x => if atom_dec a x then b else Atomic x
  | And x y => And (replace_atom_prop a b x) (replace_atom_prop a b y)
  | Or x y => Or (replace_atom_prop a b x) (replace_atom_prop a b y)
  | Impl x y => Impl (replace_atom_prop a b x) (replace_atom_prop a b y)
  | pfalse => pfalse
  | ptrue => ptrue
  end.

Definition replace_atom_ctx (a : atom) (b : prop) : context -> context
 := map (replace_atom_prop a b).

Lemma replace_atom_nj (a : atom) (b : prop) : forall G A, G |- A ->
replace_atom_ctx a b G |- replace_atom_prop a b A.
Proof.
intros ?? H;induction H;simpl.
- apply NJ_top.
- apply NJ_inconj;assumption.
- apply NJ_inmp;assumption.
- apply NJ_indisjl;assumption.
- apply NJ_indisjr;assumption.
- eapply NJ_exmp;[|apply IHNJ2]. apply IHNJ1.
- simpl in IHNJ1. eapply NJ_exdisj;[apply IHNJ1| |];assumption.
- eapply NJ_exconjl. apply IHNJ.
- eapply NJ_exconjr. apply IHNJ.
- apply NJ_ax. apply in_map. assumption.
- simpl in IHNJ. apply NJ_bot. assumption.
Defined.


Lemma NJ_strong_weakening : forall G A, G |- A ->
forall D, (forall B, In B G -> D |- B) -> D |- A.
Proof.
induction 1;intros;try solve [constructor;auto].
- constructor. apply IHNJ.
  simpl;intros ? [?|?]. apply NJ_ax;left;auto.
  apply NJ_generalise with D. simpl;auto. auto.
- apply NJ_indisjr. auto.
- apply NJ_exmp with A;auto.
- apply NJ_exdisj with A B;auto.
  apply IHNJ2. intros. destruct H3 as [?|H3].
  constructor;red;auto.
  apply NJ_generalise with D. simpl;auto.
  auto.
  apply IHNJ3. intros. destruct H3 as [?|H3].
  constructor;red;auto.
  apply NJ_generalise with D. simpl;auto.
  auto.
- apply NJ_exconjl with B. auto.
- apply NJ_exconjr with A. auto.
- auto.
- apply NJ_bot. auto.
Defined.

Lemma cf_str : forall G A, cf G A -> forall G', (forall A, In A G -> ne G' A)
-> cf G' A
with ne_str : forall G A, ne G A -> forall G', (forall A, In A G -> ne G' A)
-> ne G' A.
Proof.
intros ?? d;destruct d;intros.
apply ne_cf. apply ne_str with G;assumption.
apply cf_top.
apply cf_inconj;apply cf_str with Gamma;assumption.
apply cf_inmp;apply cf_str with (A::Gamma);try assumption.
intros ? [?|?]. apply ne_ax. left;assumption.
apply ne_gen with G'. apply H. assumption. intro;apply (@or_intror _ _).
apply cf_indisjl;apply cf_str with Gamma;assumption.
apply cf_indisjr;apply cf_str with Gamma;assumption.
intros ?? d;destruct d;intros.
apply ne_exmp with A;[apply ne_str with Gamma|apply cf_str with Gamma];
assumption.
apply ne_exdisj with A B;[apply ne_str with Gamma|
apply cf_str with (A::Gamma)|apply cf_str with (B::Gamma)];try assumption;
(intros ? [?|?];[apply ne_ax;left;assumption|
apply ne_gen with G';[apply H1;assumption|intro;apply or_intror]]).
apply ne_exconjl with B;apply ne_str with Gamma;assumption.
apply ne_exconjr with A;apply ne_str with Gamma;assumption.
apply H0;assumption.
apply ne_bot. apply ne_str with Gamma;assumption.
Defined.

Section NJ_sound_heyting.

Context (T : Type) `{Heyt : Heyting T} (eval : atom -> T).

Lemma NJ_sound_heyting : forall Gamma A, Gamma |- A ->
 fold_right meet top (map (interp _ eval) Gamma) <= interp _ eval A.
Proof.
induction 1;simpl in *;intros.
- apply bounded_top.
- apply meet_glb;assumption.
- apply heyting_imply. simpl in IHNJ.
  eapply transitivity;[|apply IHNJ].
  eapply order_proper. apply (@meet_comm T _ _ ). apply _.
  reflexivity. reflexivity.
- eapply transitivity;[|apply join_ub_l]. assumption.
- eapply transitivity;[|apply join_ub_r]. assumption.
- apply heyting_imply in IHNJ1.
  eapply transitivity;[|apply IHNJ1].
  apply meet_glb. apply reflexivity.
  assumption.
- apply (join_lub _ _ (interp T eval C) IHNJ2) in IHNJ3.
  clear IHNJ2.
  apply transitivity with
 (meet (join (interp T eval A) (interp T eval B))
       (fold_right meet top (map (interp T eval) Gamma))).
  apply meet_glb. assumption. apply reflexivity.
  eapply order_proper;[|reflexivity|apply IHNJ3].
  symmetry. apply meet_distrib_r.
- eapply transitivity. apply IHNJ. apply meet_lb_l.
- eapply transitivity. apply IHNJ. apply meet_lb_r.
- induction Gamma. destruct H.
  simpl. destruct H. destruct H.
  apply meet_lb_l.
  eapply transitivity. apply meet_lb_r. auto.
- apply transitivity with bot. assumption. apply Heyt.
Defined.

End NJ_sound_heyting.

Module NJ_complete.

Definition extract (A : prop) : set context :=
fun G => cf G A.

Notation "|_ A _|" := (extract A) (only parsing).
Notation "⌊ A ⌋" := (extract A). (* u230A and u230B *)

Definition Omega_aux (H : set context) (P : prop -> Prop) : Prop
 := forall G, H G <-> forall A, P A -> |_ A _| G.

Definition Omega : Type
 := sigT (fun H : set context => sigT (fun P : prop -> Prop => Omega_aux H P)).

Definition Omega_set : Omega -> set context := fun omega => projT1 omega.
Coercion Omega_set : Omega >-> set.
Hint Unfold Omega_set.

Lemma Omega_inter : forall P : Omega -> Prop, Omega.
Proof.
intros. exists (fun G => forall omega, P omega -> omega.1 G).
exists (fun A => exists omega, P omega /\ omega .2 .1 A).
red.
split;intros. destruct H0 as [omega [H0 H1]]. apply (omega .2 .2).
 apply H. assumption.
 assumption.
apply (omega .2 .2). intros.
apply H. exists omega. split. assumption. assumption.
Defined.

Instance Omega_eq : Equiv Omega
 := fun H K => Omega_set H == K.

Instance Omega_setoid : Setoid Omega.
Proof.
constructor.
split; reflexivity.
split. apply H. apply H.
split. eapply transitivity. apply H. apply H0.
eapply transitivity. apply H0. apply H.
Defined.

Lemma Omega_sub : forall omega : Omega, forall A : prop, omega .2 .1 A
-> sub omega (extract A).
Proof.
intros ? ? H G HG.
apply (omega .2 .2). assumption. assumption.
Defined.

Lemma Omega_weakening : forall omega : Omega,
forall G, omega.1 G -> forall G', (forall p, In p G -> In p G')
 -> omega.1 G'.
Proof.
intros.
destruct omega as [omega [P HP]]. simpl.
apply HP. intros.
assert (|_ A _| G). apply HP. assumption. assumption.
apply cf_gen with G;assumption.
Defined.

Instance Omega_leq : Leq Omega := fun X Y => X.1 <= Y.1.

Instance Omega_order : @Order Omega _ (<=).
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

Instance Omega_meet : Meet Omega.
Proof.
intros X Y. exists (fun G => X.1 G /\ Y.1 G).
destruct X as [X [P HP]];destruct Y as [Y [Q HQ]].
exists (fun A => P A \/ Q A). split.
intros H ? [H' | H'].
 simpl in H. apply HP. apply H. apply H'.
 simpl in H. apply HQ. apply H. apply H'.
intros H. split;simpl.
 apply HP;intros;apply H. left;assumption.
 apply HQ;intros;apply H. right;assumption.
Defined.

Lemma Omega_meet_lattice : @MeetSemiLattice Omega _ (<=) _.
Proof.
split. apply _.
repeat intro. hnf in H. apply H.
repeat intro. hnf in H. apply H.
repeat intro. split;
auto.
Defined.

Lemma Omega_extract : prop -> Omega.
Proof.
intro A. exists (extract A).
exists (fun B => A=B). split. intros ? _ []. assumption.
intros. apply H. reflexivity.
Defined.

Instance Omega_top : Top Omega := Omega_extract top.
Instance Omega_bot : Bot Omega := Omega_extract bot.

Lemma Omega_top_pr : forall omega : Omega, omega <= top.
Proof.
intros ? G _.
apply cf_top.
Defined.

Lemma cf_bot_all : forall G, cf G pfalse -> forall B, cf G B.
Proof.
assert (forall G A, cf G A -> pfalse = A -> forall B, cf G B).
intros ?? d;destruct d;intros X C;try discriminate X.
destruct X. apply ne_cf;apply ne_bot;assumption.
intros ??;apply H with pfalse. assumption. reflexivity.
Defined.

Lemma Omega_bot_pr : forall omega : Omega, bot <= omega.
Proof.
intros ? G H.
destruct omega as [E [P HP]].
apply HP. intros.
apply cf_bot_all. assumption.
Defined.

Lemma Omega_extract_incl : forall A : prop, (Omega_extract A).1 [A].
Proof.
intros. unfold Omega_extract. simpl. apply ne_cf;apply ne_ax.
left;auto.
Defined.

Instance Omega_join : Join Omega.
Proof.
intros X Y.
apply (Omega_inter (fun omega => sub X omega /\ sub Y omega)).
Defined.

Lemma Omega_join_pr : forall (a b : Omega) G, (join a b).1 G <->
  forall D : prop, sub a (extract D) -> sub b (extract D) -> (extract D) G.
Proof.
split;intros.
hnf in H. simpl in H. apply (H (Omega_extract D)).
split;assumption.
intros omega [H0 H1].
apply (omega .2 .2). intros.
apply H.
 transitivity (Omega_set omega). assumption.
 apply Omega_sub. assumption.
 transitivity (Omega_set omega). assumption.
 apply Omega_sub. assumption.
Defined.

Instance Omega_imply : Imply Omega := fun X Y =>
  Omega_inter (fun omega => forall Z : Omega, (meet X Z) <= Y -> Z <= omega).

Lemma Omega_imply_pr : forall (a b : Omega) G, (a __> b).1 G <->
  forall D : prop, (forall c : Omega, meet a c <= b -> sub c (extract D))
    -> (extract D) G.
Proof.
split;intros.
apply (H (Omega_extract D)).
assumption.
intros ? ?. apply (omega .2 .2). intros. apply H.
intros. transitivity (Omega_set omega). apply H0. assumption.
apply Omega_sub. assumption.
Defined.

Lemma Omega_join_lattice : @JoinSemiLattice Omega _ (<=) _.
Proof.
split.
apply _.
intros ? ? ? ? ? [H0 _]. apply H0. assumption.
intros ? ? ? ? ? [_ H1]. apply H1. assumption.
intros ? ? ? ? ? ? ?. apply H1;split;assumption.
Defined.

Lemma Omega_imply_left : forall X Y Z, meet X Y <= Z -> X <= Y __> Z.
Proof.
intros ? ? ? ? G ?.
intros d ?. apply H1 with X.
intros ? ?;apply H;split;destruct H2;auto.
assumption.
Defined.

Lemma cf_imply_passes_right : forall G D A, cf (G++D) A ->
 cf D (fold_right imply A G).
Proof.
induction G;intros ? ? d.
assumption.
simpl. apply cf_inmp. apply IHG.
eapply cf_gen. apply d.
red;intros. apply in_app_iff;apply in_app_iff in H. simpl. simpl in H.
tauto.
Defined.

(* CUT *)
Lemma cf_kleene : forall G A B, cf G (A __> B) -> cf (A::G) B.
Proof.
intros. inversion H.
apply ne_cf. apply ne_exmp with A. apply ne_gen with G. assumption.
intro;apply or_intror. apply ne_cf;apply ne_ax;left;reflexivity.
assumption.
Defined.


Lemma cf_imply_passes_left : forall G D A, cf D (fold_right imply A G)
 -> cf (G++D) A.
Proof.
induction G;intros.
assumption.
simpl in H. apply cf_kleene in H. apply IHG in H.
eapply cf_gen. apply H.
simpl;intros ? H0. apply in_app_iff in H0.
simpl;destruct H0;[right;apply in_app_iff;auto|
destruct H0;[auto|right;apply in_app_iff;auto]].
Defined.

Lemma Omega_imply_right : forall X Y Z, X <= Y __> Z -> meet X Y <= Z.
Proof.
intros ? ? ? ? G [HG0 HG1].
apply (Z .2 .2).
intros C HC.
pose (H0 := H _ HG0);clearbody H0.
pose (H1 := match (Omega_imply_pr _ _ _) with | conj H _ => H end H0
  (fold_right imply C G));clearbody H1.
assert (HD: |_ fold_right imply C G _| G). apply H1.
intros E ? D HD. assert (Z.1 (G++D)). apply H2.
split.
apply Omega_weakening with G. assumption.
 intros;apply in_app_iff;auto.
apply Omega_weakening with D. assumption.
 intros;apply in_app_iff;auto.
apply (match Z.2.2 (G++D) with | conj H _ => H end) with C in H3.
apply cf_imply_passes_right in H3.
assumption. assumption.
apply cf_imply_passes_left in HD.
eapply cf_gen. apply HD. intros ? H2;apply in_app_iff in H2;tauto.
Defined.

Instance Omega_heyting : @Heyting Omega _ _ _ _ _ _ _.
Proof.
split;[split;[split| |]|].
apply Omega_meet_lattice.
apply Omega_join_lattice.
apply Omega_top_pr.
apply Omega_bot_pr.
split. apply Omega_imply_right. apply Omega_imply_left.
Defined.

Definition Omega_interp : prop -> Omega
 := interp Omega (fun a : atom => Omega_extract (Atomic a)).

Notation "[| A |]" := (Omega_interp A).

Definition closure (A : prop) : Omega
 := Omega_inter (fun omega => omega.1 [A]).

Lemma closure_pr : forall A G, (closure A).1 G <->
  forall D, (extract D) [A] -> (extract D) G.
Proof.
split;intros.
red in H;red in H. simpl in H.
apply (H (Omega_extract D)). assumption.
intros ? ?. apply (omega.2.2). intros B ?. apply H.
apply (omega.2.2). assumption. assumption.
Defined.

Lemma Omega_strong_weakening : forall (omega : Omega) G, omega.1 G ->
  forall G', (forall p, In p G -> ne G' p) -> omega.1 G'.
Proof.
intros.
apply omega.2.2. intros.
apply cf_str with G.
apply omega.2.2. assumption. assumption.
assumption.
Defined.

Lemma cl_sub_pr : forall A (omega : Omega), omega.1 [A] ->
 sub (closure A) omega.
Proof.
intros ? ? ? G ?.
apply H0. assumption.
Defined.

Lemma Omega_imply_monotonous : forall A A' B B' : Omega,
  A <= A' -> B <= B' -> A' __> B <= A __> B'.
Proof.
intros ? ? ? ? ? ? G ?.
intros ? ?. apply H1. intros.
apply H2. intros ? [? ?]. apply H0. apply H3. split;auto.
Defined.

Lemma cl_extract : forall A, sub (closure A) (extract A).
Proof.
intros A G H. hnf in H;simpl in H. change ((Omega_extract A).1 G). apply H.
apply Omega_extract_incl.
Defined.

Lemma Omega_key_cl (A : prop) :  sub (closure A) (Omega_interp A)
with Omega_key_ex (A : prop) : sub (Omega_interp A) (extract A).
Proof.
destruct A.
(* atom *)
  intros G ?. hnf in H;simpl in H. apply H.
  apply Omega_extract_incl.

(* and *)
  simpl. intros G;unfold incl;intros ?.
  split.
  apply Omega_key_cl. intros ? ?. apply H.
  apply Omega_strong_weakening with [A1]. assumption.
  intros ? [[]|[]].
  apply ne_exconjl with A2. apply ne_ax. left;auto.
  apply Omega_key_cl. intros ? ?. apply H.
  apply Omega_strong_weakening with [A2]. assumption.
  intros ? [[]|[]].
  apply ne_exconjr with A1. apply ne_ax. left;auto.

(* or *)
  intros G H. apply H. clear G H.
  simpl;red. intros omega [? ?].
  apply (omega.2.2). intros C ?.
  assert ((extract C) [A1]).
    apply (omega.2.2);try assumption.
    apply H. apply Omega_key_cl. intros ?;auto.
  assert ((extract C) [A2]).
    apply (omega.2.2);try assumption.
    apply H0. apply Omega_key_cl. intros ?;auto.
  apply ne_cf;apply ne_exdisj with A1 A2.
  apply ne_ax;left;auto.
  apply cf_gen with [A1];auto.
    red;intros. simpl in H4;simpl. tauto.
  apply cf_gen with [A2];auto.
    red;intros. simpl in H4;simpl. tauto.

(* imply *)
  change ((closure (Impl A1 A2)) <= (Omega_interp A1 __> Omega_interp A2)).
  apply Omega_imply_left.
  intros G ?.
  apply Omega_key_cl. destruct H. apply Omega_key_ex in H0.
  apply closure_pr. intros ? H1.
  apply cf_gen with (G++G);[ |
  intros ? H2;apply in_app_or in H2;tauto].
  apply cf_imply_passes_left.
  change ((Omega_extract (fold_right imply D G)).1 G).
  apply H. apply cf_imply_passes_right.
  apply cf_str with [A2].
  assumption.
  intros _ [[]|[]]. apply ne_exmp with A1.
  apply ne_ax. apply in_app_iff. right;left;reflexivity.
  apply cf_gen with G. assumption.
  red;intros. apply in_app_iff;left;assumption.

(* false *)
  intros G ?. apply H.
  red;simpl. apply ne_cf;apply ne_ax;simpl;auto.

(* true *)
  intros ? _. hnf. apply cf_top.

destruct A.
(* atom *)
   intros ?;auto.

(* and *)
  intros G ?. destruct H. apply Omega_key_ex in H;apply Omega_key_ex in H0.
  apply cf_inconj;assumption.

(* or *)
  intros G ?. simpl in H. apply (H (Omega_extract (Or A1 A2))).
  clear G H. split.
  intros G ?. apply Omega_key_ex in H. apply cf_indisjl;assumption.
  intros G ?. apply Omega_key_ex in H. apply cf_indisjr;assumption.

(* imply *)
  apply (sub_trans _ ((closure A1) __> (Omega_extract A2)) _).
  change [| Impl A1 A2 |] with ([|A1|] __> [|A2|]).
  apply Omega_imply_monotonous.
  apply Omega_key_cl. apply Omega_key_ex.
  intros G ?.
  apply (match Omega_imply_pr _ _ _ with | conj H _ => H end H (A1 __> A2)).
  intros o ?. intros S ?.
  assert ((meet (closure A1) o).1 (A1::S)).
  split. unfold closure. simpl. red;intros. apply Omega_weakening with [A1].
  assumption. simpl;left;tauto.
  apply Omega_weakening with S. assumption. simpl;auto.
  apply H0 in H2.
  apply cf_inmp. assumption.

(* false *)
  intros ? H;apply H.

(* true *)
  intros ? H;apply H.
Defined.

Lemma fold_right_closure_interp : forall G,
 sub (fold_right meet top (map closure G))
     (fold_right meet top (map Omega_interp G)).
Proof.
induction G. simpl. reflexivity.
simpl. red;unfold incl. intros ?[??].
split. apply Omega_key_cl. assumption.
apply IHG. assumption.
Defined.

Lemma context_closure : forall G G', (forall x, In x G -> In x G')
-> (fold_right meet top (map closure G)).1 G'.
Proof.
induction G;simpl;unfold incl;intros.
apply cf_top.
split. intros. apply Omega_weakening with [a]. assumption.
intros;apply H. left;destruct H1 as [?|[]]. assumption.
apply IHG. intros;apply H;right;assumption.
Defined.

Lemma Omega_complete : forall {G A},
 fold_right meet top (map Omega_interp G) <= Omega_interp A -> cf G A.
Proof.
intros. change (extract A G). apply Omega_key_ex.
apply H. apply fold_right_closure_interp. apply context_closure. auto.
Defined.

Lemma Omega_sound : forall {G A}, G |- A ->
  fold_right meet top (map Omega_interp G) <= Omega_interp A.
Proof.
eapply NJ_sound_heyting. apply _.
Defined.

Lemma cf_complete : forall G A, (forall T `{Heyting T} eval,
fold_right meet top (map (interp _ eval) G) <= interp _ eval A) -> cf G A.
Proof.
intros.
apply Omega_complete. eapply H. apply _.
Defined.

Lemma remove_cuts : forall {G A}, G |- A -> cf G A.
Proof.
intros. apply Omega_complete. apply Omega_sound. assumption.
Defined.

Definition reduction : forall {G A}, G |- A -> G |- A
 := fun G A d => cf_NJ _ _ (remove_cuts d).

(*
Goal forall (G : context) (A B : prop) (d : (A::G) |- B) (d' : G |- A),
 exists k, k =
 NJ_sound_heyting Omega (fun a => Omega_extract (Atomic a)) 
 G B (NJ_exmp G A B (NJ_inmp G A B d) d').
econstructor.
simpl. unfold reflexivity.
unfold transitivity. unfold sub_trans.
*)

Axiom A B : atom.

Definition test : NJ [Atomic A] (Atomic A).
apply NJ_exmp with (Atomic A).
apply NJ_inmp. apply NJ_ax. right;left;reflexivity.
apply NJ_ax;left;reflexivity.
Defined.

Eval compute in (reduction test).

Definition test' : NJ [Atomic A] (Atomic A).
apply NJ_exmp with (Atomic A).
apply NJ_exdisj with (Atomic A) (Atomic A).
apply NJ_exmp with (meet (Atomic A) (Atomic A)).
apply NJ_inmp.
apply NJ_indisjl. apply NJ_exconjr with (Atomic A).
apply NJ_ax;simpl;auto.
apply NJ_inconj;apply NJ_ax;simpl;auto.
apply NJ_inmp;apply NJ_ax;right;left;auto.
apply NJ_inmp;apply NJ_ax;simpl;auto.
apply NJ_ax;simpl;auto.
Defined.

Eval compute in (reduction test').

Definition test0 : NJ [Atomic A; Atomic A] (Atomic A).
apply NJ_exmp with (Atomic A).
apply NJ_exconjl with (Atomic A).
apply NJ_inconj. apply NJ_inmp. apply NJ_ax. right;left;reflexivity.
apply NJ_ax. left;reflexivity.
apply NJ_ax. right;left;reflexivity.
Defined.

Eval compute in (reduction test0).

Definition test1 : NJ [Atomic A ⊔ Atomic B] (Atomic A ⊔ Atomic B).
apply NJ_ax;left;reflexivity.
Defined.

Eval compute in (Omega_sound test1).

Eval compute in (reduction test1).
Eval compute in (reduction (reduction test1)).

Definition test2 : NJ [meet (Atomic A) (Atomic B)] (meet (Atomic A) (Atomic B)).
Proof.
apply NJ_ax;simpl;auto.
Defined.

Eval compute in (reduction test2).
Eval compute in (reduction (reduction test2)).

Definition test3 : NJ [imply (Atomic A) (Atomic B)]
 (imply (Atomic A) (Atomic B)).
Proof.
apply NJ_ax;simpl;auto.
Defined.

Eval compute in (reduction test3).
Eval compute in (reduction (reduction test3)).

End NJ_complete.

End NJ.
