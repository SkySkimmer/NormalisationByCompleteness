(*
In this file we define Heyting algebras using typeclasses for concise use
*)
Global Generalizable All Variables.

Require Import Morphisms Setoid.
Require Import List.
Import ListNotations.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation "( x ; y )" := (existT _ x y).

(*
various things pulled from math-classes
https://github.com/math-classes/math-classes.git
*)
(* Equality *)
Class Equiv A := equiv: relation A.

(* Revert to transparency to allow conversions during unification. *)
Typeclasses Transparent Equiv.

(* We use this virtually everywhere, and so use "=" for it: *)
Infix "==" := equiv (at level 70) : type_scope.
Notation "(==)" := equiv (only parsing) : mc_scope.
Notation "( x ==)" := (equiv x) (only parsing) : mc_scope.
Notation "(== x )" := (fun y => equiv y x) (only parsing) : mc_scope.

Delimit Scope mc_scope with mc. 
Global Open Scope mc_scope.

Ltac auto_symm := match goal with
                    [ H: ?R ?x ?y |- ?R ?y ?x] => apply (symmetry H)
                  end.
Ltac auto_trans := match goal with
                    [ H: ?R ?x ?y, I: ?R ?y ?z |- ?R ?x ?z] =>
                         apply (transitivity H I)
                  end.
Hint Extern 2 (?x == ?x) => reflexivity.
Hint Extern 2 (?x == ?y) => auto_symm.
Hint Extern 2 (?x == ?y) => auto_trans.

Class SgOp A := sg_op: A -> A -> A.
Class MonUnit A := mon_unit: A.
Typeclasses Transparent SgOp MonUnit.

Class Meet A := meet: A -> A -> A.
Class Join A := join: A -> A -> A.
Class Top A := top: A.
Class Bot A := bot: A.
Typeclasses Transparent Meet Join Top Bot.

Class Leq A := leq: relation A.
Typeclasses Transparent Leq.

Instance meet_is_sg_op `{f : Meet A} : SgOp A := f.
Instance join_is_sg_op `{f : Join A} : SgOp A := f.
Instance top_is_mon_unit `{s : Top A} : MonUnit A := s.
Instance bottom_is_mon_unit `{s : Bot A} : MonUnit A := s.

Infix "&" := sg_op (at level 50, left associativity) : mc_scope.
Notation "(&)" := sg_op (only parsing) : mc_scope.
Notation "( x &)" := (sg_op x) (only parsing) : mc_scope.
Notation "(& x )" := (fun y => y & x) (only parsing) : mc_scope.

Notation "⊤" := top : mc_scope.
Notation "⊥" := bot : mc_scope.

Infix "⊓" := meet (at level 50, no associativity) : mc_scope.
Notation "(⊓)" := meet (only parsing) : mc_scope.
Notation "( X ⊓)" := (meet X) (only parsing) : mc_scope.
Notation "(⊓ X )" := (fun Y => Y ⊓ X) (only parsing) : mc_scope.

Infix "⊔" := join (at level 50, no associativity) : mc_scope.
Notation "(⊔)" := join (only parsing) : mc_scope.
Notation "( X ⊔)" := (join X) (only parsing) : mc_scope.
Notation "(⊔ X )" := (fun Y => Y ⊔ X) (only parsing) : mc_scope.

Infix "<=" := leq : mc_scope.
Notation "(<=)" := leq (only parsing) : mc_scope.
Notation "( x <=)" := (leq x) (only parsing) : mc_scope.
Notation "(<= x )" := (fun y => y <= x) (only parsing) : mc_scope.

Class LeftIdentity {A} `{Equiv B} (op : A -> B -> B) (x : A): Prop
 := left_identity: forall y, op x y == y.
Class RightIdentity `{Equiv A} {B} (op : A -> B -> A) (y : B): Prop
 := right_identity: forall x, op x y == x.

Class Commutative `{Equiv B} `(f : A -> A -> B) : Prop
 := commutativity: forall x y, f x y == f y x.

Class HeteroAssociative {A B C AB BC} `{Equiv ABC}
     (fA_BC: A -> BC -> ABC) (fBC: B -> C -> BC)
     (fAB_C: AB -> C -> ABC) (fAB : A -> B -> AB): Prop
   := associativity : forall x y z, fA_BC x (fBC y z) == fAB_C (fAB x y) z.
Class Associative `{Equiv A} f
 := simple_associativity:> HeteroAssociative f f f f.

Class AntiSymmetric `{Ae : Equiv A} (R : relation A) : Prop
 := antisymmetry: forall x y, R x y -> R y x -> x == y.
Arguments antisymmetry {A Ae} _ {AntiSymmetric} _ _ _ _.

Class Setoid A {Ae : Equiv A} : Prop := setoid_eq :> Equivalence (@equiv A Ae).

Section setoid_morphisms.
  Context {A B} {Ae : Equiv A} {Be : Equiv B} (f : A -> B).

  Class Setoid_Morphism :=
    { setoidmor_a : Setoid A
    ; setoidmor_b : Setoid B
    ; sm_proper :> Proper ((==) ==> (==)) f }. 

End setoid_morphisms.

Section upper_classes.

  Context A {Ae : Equiv A}.

  Class Magma {Aop: SgOp A} : Prop :=
    { mag_setoid :> Setoid A
    ; mag_op_proper :> Proper ((==) ==> (==) ==> (==)) (&) }.

  Class SemiGroup {Aop : SgOp A} : Prop :=
    { sg_mag :> Magma
    ; sg_assoc :> Associative (&) }.

  Class Monoid {Aop : SgOp A} {Aunit : MonUnit A} : Prop :=
    { monoid_semigroup :> SemiGroup
    ; monoid_left_id :> LeftIdentity (&) mon_unit
    ; monoid_right_id :> RightIdentity (&) mon_unit }.

End upper_classes.

Lemma fold_right_app_assoc `{Monoid A} : forall l l',
 fold_right (&) mon_unit (l++l') ==
  (fold_right (&) mon_unit l) & (fold_right (&) mon_unit l').
Proof.
induction l;intros;simpl.
symmetry. apply left_identity.
eapply transitivity. apply mag_op_proper. apply _.
reflexivity. apply IHl.
apply associativity.
Defined.


Class Order A `{Ae : Equiv A} `{Aleq : Leq A} : Prop :=
  { order_setoid : Setoid A
   (* Making this ^ a subclass makes instance search slow *)
  ; order_proper:> Proper ((==) ==> (==) ==> iff) (<=)
  ; order_preorder:> PreOrder (<=)
  ; order_antisym:> AntiSymmetric (<=) }.


Class MeetSemiLattice A `{Ae : Equiv A} `{Aleq : Leq A} `{Ameet : Meet A}
 : Prop :=
  { meet_sl_order :> Order A
  ; meet_lb_l : forall x y, x ⊓ y <= x
  ; meet_lb_r : forall x y, x ⊓ y <= y
  ; meet_glb : forall x y z, z <= x -> z <= y -> z <= x ⊓ y }.

Lemma meet_left `{MeetSemiLattice A} : forall a b, a <= b ->
forall c d, meet b c <= d -> meet a c <= d.
Proof.
intros. eapply transitivity;[|apply H1].
apply meet_glb. eapply transitivity. apply meet_lb_l. assumption.
apply meet_lb_r. 
Defined.

Lemma meet_right `{MeetSemiLattice A} : forall a b, a <= b ->
forall c d, meet c b <= d -> meet c a <= d.
Proof.
intros. eapply transitivity;[|apply H1].
apply meet_glb. apply meet_lb_l.
 eapply transitivity. apply meet_lb_r. assumption.
Defined.

Lemma meet_mono_l `{MeetSemiLattice A} : forall a b, a <= b ->
forall c, meet a c <= meet b c.
Proof.
intros. apply meet_left with b. assumption. reflexivity.
Defined.

Lemma meet_mono_r `{MeetSemiLattice A} : forall a b, a <= b ->
forall c, meet c a <= meet c b.
Proof.
intros. apply meet_right with b. assumption. reflexivity.
Defined.

Class JoinSemiLattice A `{Ae : Equiv A} `{Aleq : Leq A} `{Ajoin : Join A}
 : Prop :=
  { join_sl_order :> Order A
  ; join_ub_l : forall x y, x <= x ⊔ y
  ; join_ub_r : forall x y, y <= x ⊔ y
  ; join_lub : forall x y z, x <= z -> y <= z -> x ⊔ y <= z }.

Lemma join_left `{JoinSemiLattice A} : forall a b, b <= a ->
forall c d, d <= join b c -> d <= join a c.
Proof.
intros. eapply transitivity;[apply H1|].
apply join_lub. eapply transitivity. apply H0. apply join_ub_l.
apply join_ub_r.
Defined.

Lemma join_right `{JoinSemiLattice A} : forall a b, b <= a ->
forall c d, d <= join c b -> d <= join c a.
Proof.
intros. eapply transitivity;[apply H1|].
apply join_lub. apply join_ub_l.
 eapply transitivity. apply H0. apply join_ub_r.
Defined.

Lemma join_mono_l `{JoinSemiLattice A} : forall a b, a <= b ->
forall c, join a c <= join b c.
Proof.
intros. apply join_left with a. assumption. reflexivity.
Defined.

Lemma join_mono_r `{JoinSemiLattice A} : forall a b, a <= b ->
forall c, join c a <= join c b.
Proof.
intros. apply join_right with a. assumption. reflexivity.
Defined.

Class Lattice A `{Ae : Equiv A} `{Aleq : Leq A}
 `{Ameet : Meet A} `{Ajoin : Join A}
 : Prop :=
  { lattice_meet :> MeetSemiLattice A
  ; lattice_join :> JoinSemiLattice A }.

Class BoundedLattice A `{Ae : Equiv A} `{Aleq : Leq A}
 `{Ameet : Meet A} `{Ajoin : Join A} `{Atop : Top A} `{Abot : Bot A} : Prop :=
  { bounded_lattice_lattice :> Lattice A
  ; bounded_top : forall x, x <= top
  ; bounded_bot : forall x, bot <= x }.

Instance meet_assoc (A : Type) `{Hmeet : MeetSemiLattice A}
 : Associative meet.
Proof.
hnf. intros.
apply (antisymmetry (<=)).
apply meet_glb;[ apply meet_glb|].
apply meet_lb_l.
eapply transitivity. apply meet_lb_r. apply meet_lb_l.
eapply transitivity. apply meet_lb_r. apply meet_lb_r.
apply meet_glb;[ |apply meet_glb].
eapply transitivity. apply meet_lb_l. apply meet_lb_l.
eapply transitivity. apply meet_lb_l. apply meet_lb_r.
apply meet_lb_r.
Defined.

Instance meet_comm (A : Type) `{Hmeet : MeetSemiLattice A}
 : Commutative meet.
Proof.
red;intros.
apply (antisymmetry (<=));
apply meet_glb;first [apply meet_lb_l|apply meet_lb_r].
Defined.

Definition rrev {A : Type} (R : relation A) : relation A := fun a b => R b a.

Instance rrev_order {A : Type} `{Order A} : @Order A _ (rrev (<=)).
Proof.
constructor.
apply H.
assert (Setoid A);[apply H|].
repeat red. unfold leq. unfold rrev. split;apply H;auto.
constructor. apply H.
hnf. unfold leq,rrev. intros;eapply transitivity;eauto.
red. intros;apply (antisymmetry (<=));assumption.
Defined.

Lemma meet_rev_join {A : Type} `{H : MeetSemiLattice A} :
 @JoinSemiLattice A _ (rrev leq) meet.
Proof.
constructor;[apply rrev_order| | |];unfold join,leq,rrev;apply H.
Defined.

Lemma join_rev_meet {A : Type} `{H : JoinSemiLattice A} :
 @MeetSemiLattice A _ (rrev leq) join.
Proof.
constructor;[apply rrev_order| | |];unfold meet,rrev;apply H.
Defined.

Instance join_assoc (A : Type) `{H : JoinSemiLattice A}
 : Associative join.
Proof.
apply (@meet_assoc A _ (rrev (<=)) join join_rev_meet).
Defined.

Instance join_comm (A : Type) `{H : JoinSemiLattice A}
 : Commutative join.
Proof.
apply (@meet_comm A _ (rrev (<=)) join join_rev_meet).
Defined.

Lemma order_refl `{Order A} : forall x y, x == y -> x <= y.
Proof.
intros. eapply order_proper. apply H0. apply H. apply H.
Defined.

Instance meet_monoid (A : Type) `{BoundedLattice A} : @Monoid A _ meet top.
Proof.
constructor. constructor;try apply _. constructor. apply H.
unfold sg_op. hnf;red. assert (Hset : Setoid A). apply H.
intros x y H2 a b H3. apply (antisymmetry (<=)).
apply meet_glb. apply transitivity with x.
apply meet_lb_l. apply order_refl;assumption.
apply transitivity with a. apply meet_lb_r. apply order_refl;assumption.
apply meet_glb. apply transitivity with y.
apply meet_lb_l. apply order_refl. auto.
apply transitivity with b. apply meet_lb_r. apply order_refl;auto.

red;intros. apply (antisymmetry (<=)).
apply meet_lb_r.
apply meet_glb. apply H. reflexivity.
red;intros. apply (antisymmetry (<=)).
apply meet_lb_l.
apply meet_glb. reflexivity. apply H.
Defined.

Lemma bounded_lattice_rev (A : Type) `{Hl : BoundedLattice A}
 : @BoundedLattice A _ (rrev (<=)) join meet (@bot A _) (@top A _).
Proof.
constructor;[| apply Hl | apply Hl].
constructor. apply join_rev_meet. apply meet_rev_join.
Defined.

Instance join_monoid (A : Type) `{BoundedLattice A} : @Monoid A _ join bot.
Proof.
apply (@meet_monoid A _ _ _ _ _ _ (bounded_lattice_rev A)).
Defined.

Class Imply (A : Type) := imply : A -> A -> A.
Infix "__>" := imply (at level 65).

Class Heyting A `{Ae : Equiv A} `{Aleq : Leq A} `{Ame : Meet A} `{Ajo : Join A}
 `{Aimp : Imply A} `{Atop : Top A} `{Abot : Bot A} :=
  { heyting_lattice :> BoundedLattice A
  ; heyting_imply : forall a b c : A, a <= b __> c <-> meet a b <= c }.

Lemma meet_distrib_r `{Heyting A}
 : forall a b c : A, join (meet a c) (meet b c) == meet (join a b) c.
Proof.
intros;apply (antisymmetry (<=)).
- apply meet_glb.
   apply join_lub.
    eapply transitivity. apply meet_lb_l. apply join_ub_l.
    eapply transitivity. apply meet_lb_l. apply join_ub_r.
   apply join_lub;apply meet_lb_r.
- apply heyting_imply. apply join_lub;apply heyting_imply.
  apply join_ub_l. apply join_ub_r.
Defined.
(* Do we really need a heyting algebra here?
 yes (lattice non equivalent to distributive lattice) *)

Lemma join_distrib_aux `{Heyting A}
 : forall a b c : A, meet (join a b) (join a c) <= join a (meet b c).
Proof.
intros.
apply heyting_imply. apply join_lub;apply heyting_imply.
eapply transitivity. apply meet_lb_l. apply join_ub_l.
rewrite (@commutativity A _ _ meet);[|apply _].
apply heyting_imply. apply join_lub;apply heyting_imply.
eapply transitivity. apply meet_lb_l. apply join_ub_l.
rewrite commutativity. apply join_ub_r.
Defined.




Definition set (T : Type) := T -> Prop.

Instance sub {T : Type} : Leq (set T)
 := fun x y => forall z, x z -> y z.

Instance sub_trans {T} : Transitive (@sub T).
Proof.
red;intros;intro;auto.
Defined.

Instance setEq (T : Type) : Equiv (set T)
 := fun E F => sub E F /\ sub F E.

Instance set_setoid : forall T, Setoid (set T).
Proof.
constructor;split;intro; auto.
apply H.
apply H.
intros. apply H0. apply H. assumption.
intros;apply H;apply H0;assumption.
Defined.

Instance set_order : forall T, @Order (set T) _ (<=).
Proof.
constructor. apply _.
repeat intro. split;repeat intro. apply H0. apply H1. apply H. assumption.
apply H0;apply H1;apply H;assumption.
constructor;repeat intro. assumption.
apply H0;apply H;assumption.
repeat intro. split; assumption.
Defined.
