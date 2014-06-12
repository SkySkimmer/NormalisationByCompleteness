Require Import Morphisms Setoid List.
Require Import structure.

Import ListNotations.

Axiom PEM : forall P : Prop, ~ ~ P -> P.

Section Zorn.

Context `{Order T}.

Definition is_ub (P Q : set T) m := P m /\ forall x, Q x -> x <= m.

Definition is_chain (P : set T) := forall a b, P a -> P b -> (a <= b \/ b <= a).

Axiom Zorn : forall `{Order T}, forall P, (forall Q, sub Q P ->
 is_chain Q -> ex (is_ub P Q))
 -> exists m, P m /\ forall x, P x -> x <= m.

End Zorn.


Lemma Forall_inv : forall T P (a : T) l,
Forall P (a::l) -> (P a /\ Forall P l).
Proof.
intros ??.
assert (forall l, Forall P l -> match l with
 | nil => True | a::l => P a /\ Forall P l end).
intros. destruct H. split. split;assumption.
intros ??. apply H.
Defined.

Lemma Forall_app : forall T : Type, forall P (l1 l2 : list T),
Forall P (l1++l2) <-> (Forall P l1 /\ Forall P l2).
Proof.
induction l1;intros;split.
split. constructor. assumption.
intros. apply H.
simpl. intros. apply Forall_inv in H. destruct H.
apply IHl1 in H0. split. constructor;tauto. tauto.
intros. destruct H. apply Forall_inv in H. simpl;constructor.
tauto. apply IHl1;tauto.
Defined.


Section Filter_lattice.

Context {T : Type} `{BoundedLattice T}.

Class IsFilter (F : set T) := isfilter 
 { filter_equiv : forall a b, F (meet a b) <-> (F a /\ F b)
 ; filter_proper : Proper ((==) ==> (iff)) F
 ; filter_inhab : ex F }.

Lemma filter_meet `{IsFilter F} : forall a b, F a -> F b -> F (meet a b).
Proof.
intros. apply filter_equiv;split;assumption.
Defined.

Lemma filter_up `{IsFilter F} : forall a b, F a -> a <= b -> F b.
Proof.
intros.
assert (F (meet a b)). apply filter_proper with a.
eapply antisymmetry. apply H. apply meet_lb_l. apply meet_glb.
reflexivity. assumption.
assumption.
apply filter_equiv in H3. apply H3.
Defined.

Lemma filter_sufficient : forall F : set T,
(forall a b, F a -> F b -> F (meet a b)) -> (forall a b, F a -> a <= b -> F b)
 -> ex F -> IsFilter F.
Proof.
intros ??? Hex. split.
split;intros.
split;apply (H1 _ _ H2). apply meet_lb_l. apply meet_lb_r.
apply H0;apply H2.

hnf. split; intros H'; apply (H1 _ _ H'); apply order_refl. assumption.
apply (@symmetry _ Ae). apply H. assumption.

assumption.
Defined.

Lemma filter_join `{IsFilter F} : forall a b, (F a \/ F b) -> F (join a b).
Proof.
intros ?? [H'|H'];
apply (filter_up _ _ H').
apply join_ub_l. apply join_ub_r.
Defined.

Class IsPrimeFilter (F : set T) := isprimefilter
 { primefilter_filter :> IsFilter F
 ; primefilter_or : forall a b, F (join a b) -> (F a \/ F b) }.

Inductive gen_filter (F : set T) : set T :=
  | gen_filter_sub : sub F (gen_filter F)
  | gen_filter_meet : forall a b, gen_filter F a -> gen_filter F b
       -> gen_filter F (meet a b)
  | gen_filter_up : forall a b, gen_filter F a -> a <= b -> gen_filter F b
  | gen_filter_top : gen_filter F top
.

Global Instance gen_is_filter : forall F, IsFilter (gen_filter F).
Proof.
intros. apply filter_sufficient.
apply gen_filter_meet.
apply gen_filter_up.
exists top. apply gen_filter_top.
Defined.

Lemma gen_filter_least : forall F F', sub F F' ->
 IsFilter F' -> sub (gen_filter F) F'.
Proof.
intros ? ? Hsub Hf'.
red. unfold incl. intros ? Hg.
induction Hg.
apply Hsub. assumption.
apply filter_meet;assumption.
apply filter_up with a;assumption.
destruct (@filter_inhab F' _). apply filter_up with x. assumption.
apply bounded_top.
Defined.

Lemma filter_bot_whole `{IsFilter F} : F bot -> forall x, F x.
Proof.
intros. apply filter_up with bot;auto. apply bounded_bot.
Defined.

Lemma filter_fold_meet_incl `{IsFilter F} : forall l, Forall F l ->
F (fold_right meet top l).
Proof.
intros ? Hl;induction Hl.
- simpl. destruct (@filter_inhab F _).
  apply filter_up with x. assumption. apply bounded_top.

- simpl. apply filter_meet. assumption. assumption.
Defined.

Definition filter_top `{IsFilter F} : F top :=
 filter_fold_meet_incl nil (Forall_nil _).

Lemma gen_filter_list : forall F y, gen_filter F y ->
 exists l : list T, Forall F l /\ fold_right meet top l <= y.
Proof.
intros ?? F. induction F.
- exists [z]. split. constructor. assumption. constructor.
  simpl. apply meet_lb_l.

- destruct IHF1 as [l1 [H0 H1]];destruct IHF2 as [l2 [H2 H3]].
  exists (l1++l2). split.
  apply Forall_app. tauto.
  rewrite fold_right_app_assoc.
  unfold sg_op,mon_unit. fold top;fold meet.
  apply meet_right with b. assumption.
  apply meet_mono_l. assumption.

- destruct IHF as [l [H1 H2]]. exists l. split. assumption.
  apply transitivity with a. assumption. assumption.

- exists nil. split. constructor. reflexivity.
Defined.


End Filter_lattice.

(* we could define ideals,
 either independently of filters or as ideal (L : lattice) = filter (rev L)
But we would not use it. *)

Arguments IsFilter {T Ae Ameet} F.

Section Filter_heyting.

Context (T : Type) `{Heyt : Heyting T}.

Lemma prop_4_12 : forall F, IsFilter F -> forall a b P,
 (forall x, P x <-> (F x \/ a=x)) ->
 gen_filter P b -> F (a __> b).
Proof.
intros. induction H1.
- apply H0 in H1. destruct H1.
  apply filter_up with z. assumption.
  apply heyting_imply. apply meet_lb_l.
  destruct H1. apply filter_up with top. 
  apply filter_top.
  apply heyting_imply. apply meet_lb_r.

- apply filter_up with (meet (a __> a0) (a __> b)). apply filter_meet;assumption.
  apply heyting_imply. apply meet_glb.
  apply heyting_imply. apply meet_lb_l.
  apply heyting_imply. apply meet_lb_r.

- apply filter_up with (a __> a0). assumption.
  apply heyting_imply. apply transitivity with a0.
  apply heyting_imply. reflexivity.
  assumption.

- apply filter_up with top. apply filter_top.
  apply heyting_imply. apply meet_lb_l.
Defined.

(* NB: only needs distributive lattice, but w/e *)
(* needs PEM: must decide F x \/ F y *)

(*
based on http://www.math.waikato.ac.nz/~stokes/MATH511/511dyn13.pdf
(slides by Tim Stokes, University of Waikato, New Zealand)
*)

Lemma max_wrt_not_incl_prime_aux : forall F, IsFilter F -> forall a, ~ F a ->
(forall F', IsFilter F' -> sub F F' -> ~ F' a -> sub F' F) ->
forall x y, F (join x y) -> (F x \/ F y).
Proof.
intros.
apply PEM. intro.

apply H3. left.
pose (Gx := fun c => exists f, F f /\ meet x f <= c).
fold (set T) in Gx.
apply H1 with Gx.

apply filter_sufficient.
intros p q [f1 Hf1] [f2 Hf2]. exists (meet f1 f2).
split. apply filter_meet;tauto.
setoid_replace x with (meet x x).
setoid_replace (meet (meet x x) (meet f1 f2))
 with (meet (meet x f1) (meet x f2)).
apply meet_right with q. tauto.
apply meet_mono_l. tauto.
rewrite associativity. rewrite associativity.
apply mag_op_proper. apply _.
rewrite <-associativity. apply commutativity. reflexivity.
apply order_antisym. apply meet_glb; reflexivity. apply meet_lb_l.
intros p q [f Hf] ?. exists f. split. tauto. apply transitivity with p.
tauto. assumption.
destruct (@filter_inhab _ _ _ _ H). exists x0. exists x0. split. assumption.
apply meet_lb_r.

intros z;unfold incl;intros. exists z. split.
assumption. apply meet_lb_r.

intros [fx Hfx].
clear Gx.

apply H3. right.
pose (Gy := fun c => exists f, F f /\ meet y f <= c).
fold (set T) in Gy.
apply H1 with Gy.

apply filter_sufficient.
intros p q [f1 Hf1] [f2 Hf2]. exists (meet f1 f2).
split. apply filter_meet;tauto.
setoid_replace y with (meet y y).
setoid_replace (meet (meet y y) (meet f1 f2))
 with (meet (meet y f1) (meet y f2)).
apply meet_right with q. tauto.
apply meet_mono_l. tauto.
rewrite associativity. rewrite associativity.
apply mag_op_proper. apply _.
rewrite <-associativity. apply commutativity. reflexivity.
apply order_antisym. apply meet_glb; reflexivity. apply meet_lb_l.
intros p q [f Hf] ?. exists f. split. tauto. apply transitivity with p.
tauto. assumption.
destruct (@filter_inhab _ _ _ _ H). exists x0. exists x0. split. assumption.
apply meet_lb_r.

intros z;unfold incl;intros. exists z. split.
assumption. apply meet_lb_r.

intros [fy Hfy]. clear Gy.
apply H0.
apply filter_up with (meet (join x y) (meet fx fy)).
apply filter_meet. assumption. apply filter_meet;tauto.

rewrite <-meet_distrib_r. apply join_lub.
apply meet_right with fx. apply meet_lb_l. tauto.
apply meet_right with fy. apply meet_lb_r. tauto.

exists top. split. apply filter_top. apply meet_lb_l.
exists top. split. apply filter_top. apply meet_lb_l.
Qed.

Lemma max_wrt_not_incl_prime : forall F, IsFilter F -> forall a, ~ F a ->
(forall F', IsFilter F' -> sub F F' -> ~ F' a -> sub F' F) ->
IsPrimeFilter F.
Proof.
split. apply _. apply max_wrt_not_incl_prime_aux with a;assumption.
Defined.


Section Prime.

Variable F : set T.
Context {Hf : IsFilter F}.
Variables (a : T) (Ha : ~ F a).

Definition P : set (set T) := fun F' => IsFilter F' /\ sub F F' /\ ~ F' a.

Lemma P_F : P F.
Proof.
red;unfold sub;tauto.
Defined.

Lemma every_chain_has_upper_bound : forall G, sub G P ->
 is_chain G -> ex (is_ub P G).
Proof.
intros.

assert (~ ex G \/ ex G).
apply PEM. intro. apply H1.
left. intro. apply H1. right;assumption.
destruct H1 as [?|Hex].
exists F. red. split. apply P_F.
intros. destruct H1. exists x;assumption.

pose (G0 := fun z => exists g, G g /\ g z).
fold (set T) in G0.
assert (HG0 : IsFilter G0).
apply filter_sufficient.

- assert (Hsym : forall x y, forall gx : set T,
  G gx /\ gx x ->
  forall gy : set T, G gy /\ gy y -> gx <= gy ->
   exists g : set T, G g /\ g (x ⊓ y)).

  Focus 2.
  unfold G0. intros x y [gx Hgx] [gy Hgy].
  destruct H0 with gx gy;try tauto.
  apply Hsym with gx gy;assumption.
  eapply Hsym in H1;[| apply Hgy | apply Hgx].
  destruct H1 as [g [Hg H1]]. exists g. split. assumption.
  apply H in Hg. red in Hg.
  destruct Hg. apply @filter_proper in H2. apply H2 with (meet y x).
  apply commutativity. assumption.

  intros.
  exists gy. split. tauto.
  apply @filter_meet with Ae. apply H. tauto.
  apply H3;tauto.
  tauto.

- intros x y [gx Hgx] Hle.
  exists gx. split. tauto.
  eapply @filter_up. apply _. apply H. tauto.
  apply Hgx. assumption.

- exists top.
  destruct Hex as [x Hx]. exists x. split. assumption.
  assert (IsFilter x). apply H. assumption. apply filter_top.

- exists G0.
  split. split. assumption.
  split. intros ??. destruct Hex. exists x. split. assumption.
  apply H. assumption. assumption.
  intros [ga [Hga Hga']].
  apply H in Hga. red in Hga. tauto.
  intros g Hg ??.
  unfold incl in *.
  exists g. tauto. 
Defined.

Lemma exists_prime_not_incl : exists F', IsPrimeFilter F' /\ sub F F' /\ ~ F' a.
Proof.
destruct (Zorn _ every_chain_has_upper_bound) as [F' [HPF' Hmax]].
unfold P in HPF'.
exists F'. split;try tauto.
apply max_wrt_not_incl_prime with a;try tauto.
intros g Hg Hsub Hga.
apply Hmax. red. split. tauto. split;[|tauto].
apply transitivity with F';tauto.
Defined.

End Prime.

End Filter_heyting.





