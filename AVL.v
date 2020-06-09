(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite map library.  *)

(** * MMaps.AVL *)

(** This module implements maps using AVL trees.
    It follows the implementation from Ocaml's standard library.

    See the comments at the beginning of MSetAVL for more details.

    Note that we only prove here that the operations below preserve
    the binary search tree invariant ([Bst], a.k.a [Ok] predicate here),
    but *not* the AVL balancing invariant. Indeed, the former is enough
    to implement the desired interface [S], and ensure observational
    correctness. And proceeding this way is quite lighter. For the
    proofs of AVL balancing, see [MMaps.AVLproofs].
*)

From Coq Require Import Bool PeanoNat BinInt FunInd Int.
From Coq Require Import Orders OrdersFacts OrdersLists.
From MMaps Require Import Interface OrdList GenTree.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

(* For nicer extraction, we create inductive principles
   only when needed *)
Local Unset Elimination Schemes.

(** Notations and helper lemma about pairs *)

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

(** * The Raw functor

   Functor of pure functions + separate proofs of invariant
   preservation *)

Module MakeRaw (Import I:Int)(K: OrderedType) <: Raw.S K.

(** ** Generic trees instantiated with integer height *)

(** We reuse a generic definition of trees where the information
    parameter is a [Int.t]. Functions like mem or fold are also
    provided by this generic functor. *)

Include MMaps.GenTree.Ops K I.

Local Open Scope pair_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope Int_scope.
Local Notation int := I.t.

Section Elt.
Variable elt : Type.
Local Notation t := (tree elt).
Implicit Types l r m : t.
Implicit Types e : elt.

(** * Basic functions on trees: height and cardinal *)

Definition height (m : t) : int :=
  match m with
  | Leaf _ => 0
  | Node h _ _ _ _ => h
  end.

(** * Singleton set *)

Definition singleton x e := Node 1 (Leaf _) x e (Leaf _).

(** * Helper functions *)

(** [create l x r] creates a node, assuming [l] and [r]
    to be balanced and [|height l - height r| <= 2]. *)

Definition create l x e r :=
   Node (max (height l) (height r) + 1) l x e r.

(** [bal l x e r] acts as [create], but performs one step of
    rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

Definition assert_false := create.

Definition bal l x d r :=
  let hl := height l in
  let hr := height r in
  if (hr+2) <? hl then
    match l with
     | Leaf _ => assert_false l x d r
     | Node _ ll lx ld lr =>
       if (height lr) <=? (height ll) then
         create ll lx ld (create lr x d r)
       else
         match lr with
          | Leaf _ => assert_false l x d r
          | Node _ lrl lrx lrd lrr =>
              create (create ll lx ld lrl) lrx lrd (create lrr x d r)
         end
    end
  else
    if (hl+2) <? hr then
      match r with
       | Leaf _ => assert_false l x d r
       | Node _ rl rx rd rr =>
         if (height rl) <=? (height rr) then
            create (create l x d rl) rx rd rr
         else
           match rl with
            | Leaf _ => assert_false l x d r
            | Node _ rll rlx rld rlr =>
                create (create l x d rll) rlx rld (create rlr rx rd rr)
           end
      end
    else
      create l x d r.

(** * Insertion *)

Fixpoint add x d m :=
  match m with
    | Leaf _ => Node 1 (Leaf _) x d (Leaf _)
    | Node h l y d' r =>
      match K.compare x y with
        | Eq => Node h l y d r
        | Lt => bal (add x d l) y d' r
        | Gt => bal l y d' (add x d r)
      end
  end.

(** * Extraction of minimum binding

  Morally, [remove_min] is to be applied to a non-empty tree
  [t = Node l x e r h]. Since we can't deal here with [assert false]
  for [t=Leaf], we pre-unpack [t] (and forget about [h]).
*)

Fixpoint remove_min l x d r : t*(key*elt) :=
  match l with
    | Leaf _ => (r,(x,d))
    | Node lh ll lx ld lr =>
       let (l',m) := remove_min ll lx ld lr in
       (bal l' x d r, m)
  end.

(** * Appending two disjoint maps of similar heights

  [append t1 t2] builds the union of [t1] and [t2] assuming all keys
  of [t1] to be smaller than all keys of [t2], and
  [|height t1 - height t2| <= 2].

  This was named [merge] in the initial Set implementation.
*)

Definition append s1 s2 :=
  match s1,s2 with
    | Leaf _, _ => s2
    | _, Leaf _ => s1
    | _, Node h2 l2 x2 d2 r2 =>
      let '(s2',(x,d)) := remove_min l2 x2 d2 r2 in
      bal s1 x d s2'
  end.

(** * Deletion *)

Fixpoint remove x m := match m with
  | Leaf _ => Leaf _
  | Node h l y d r =>
      match K.compare x y with
         | Eq => append l r
         | Lt => bal (remove x l) y d r
         | Gt => bal l y d (remove x r)
      end
   end.

(** * join

    Same as [bal] but does not assume anything regarding heights of [l]
    and [r].
*)

Fixpoint join l : key -> elt -> t -> t :=
  match l with
    | Leaf _ => add
    | Node lh ll lx ld lr => fun x d =>
       fix join_aux (r:t) : t := match r with
          | Leaf _ => add x d l
          | Node rh rl rx rd rr =>
            if rh+2 <? lh then bal ll lx ld (join lr x d r)
            else if lh+2 <? rh then bal (join_aux rl) rx rd rr
            else create l x d r
          end
  end.

(** * Splitting

    [split x m] returns a triple [(l, o, r)] where
    - [l] is the set of elements of [m] that are [< x]
    - [r] is the set of elements of [m] that are [> x]
    - [o] is the result of [find x m].
*)

Record triple := mktriple { t_left:t; t_opt:option elt; t_right:t }.
Notation "〚 l , b , r 〛" := (mktriple l b r) (at level 9).

Fixpoint split x m : triple := match m with
  | Leaf _ => 〚 Leaf _, None, Leaf _ 〛
  | Node h l y d r =>
     match K.compare x y with
      | Lt => let (ll,o,rl) := split x l in 〚 ll, o, join rl y d r 〛
      | Eq => 〚 l, Some d, r 〛
      | Gt => let (rl,o,rr) := split x r in 〚 join l y d rl, o, rr 〛
     end
 end.

(** * Concatenation

   Same as [append] but does not assume anything about heights.
*)

Definition concat m1 m2 :=
   match m1, m2 with
      | Leaf _, _ => m2
      | _ , Leaf _ => m1
      | _, Node _ l2 x2 d2 r2 =>
            let (m2',xd) := remove_min l2 x2 d2 r2 in
            join m1 xd#1 xd#2 m2'
   end.

End Elt.
Notation "〚 l , b , r 〛" := (mktriple l b r) (at level 9).
Notation "t #l" := (t_left t) (at level 9, format "t '#l'").
Notation "t #o" := (t_opt t) (at level 9, format "t '#o'").
Notation "t #r" := (t_right t) (at level 9, format "t '#r'").

(** * Map with removal *)

Fixpoint mapo (elt elt' : Type)(f : key -> elt -> option elt')(m : t elt)
  : t elt' :=
  match m with
   | Leaf _ => Leaf _
   | Node _ l x d r =>
      match f x d with
       | Some d' => join (mapo f l) x d' (mapo f r)
       | None => concat (mapo f l) (mapo f r)
      end
  end.

(** * Generalized merge

  Suggestion by B. Gregoire: a [merge] function with specialized
  arguments that allows bypassing some tree traversal. Instead of one
  [f0] of type [key -> option elt -> option elt' -> option elt''],
  we ask here for:
  - [f] which is a specialisation of [f0] when first option isn't [None]
  - [mapl] treats a [tree elt] with [f0] when second option is [None]
  - [mapr] treats a [tree elt'] with [f0] when first option is [None]

  The idea is that [mapl] and [mapr] can be instantaneous (e.g.
  the identity or some constant function).
*)

Section GMerge.
Variable elt elt' elt'' : Type.
Variable f : key -> elt -> option elt' -> option elt''.
Variable mapl : t elt -> t elt''.
Variable mapr : t elt' -> t elt''.

Fixpoint gmerge m1 m2 :=
 match m1, m2 with
  | Leaf _, _ => mapr m2
  | _, Leaf _ => mapl m1
  | Node h1 l1 x1 d1 r1, _ =>
     let (l2',o2,r2') := split x1 m2 in
     match f x1 d1 o2 with
      | Some e => join (gmerge l1 l2') x1 e (gmerge r1 r2')
      | None => concat (gmerge l1 l2') (gmerge r1 r2')
     end
 end.

End GMerge.

(** * Merge

    The [merge] function of the Map interface can be implemented
    via [gmerge] and [mapo].
*)

Section Merge.
Variable elt elt' elt'' : Type.
Variable f : key -> option elt -> option elt' -> option elt''.

Definition merge : t elt -> t elt' -> t elt'' :=
 gmerge
   (fun k d o => f k (Some d) o)
   (mapo (fun k d => f k (Some d) None))
   (mapo (fun k d' => f k None (Some d'))).

End Merge.

(** * Correctness proofs *)

Include MMaps.GenTree.Props K I.
Import Ind.

Local Infix "∈" := In (at level 70).
Local Infix "==" := K.eq (at level 70).
Local Infix "<" := K.lt (at level 70).
Local Infix "<<" := Below (at level 70).
Local Infix ">>" := Above (at level 70).
Local Infix "<<<" := Apart (at level 70).

Functional Scheme bal_ind := Induction for bal Sort Prop.
Functional Scheme add_ind := Induction for add Sort Prop.
Functional Scheme remove_min_ind := Induction for remove_min Sort Prop.
Functional Scheme append_ind := Induction for append Sort Prop.
Functional Scheme remove_ind := Induction for remove Sort Prop.
Functional Scheme concat_ind := Induction for concat Sort Prop.
Functional Scheme split_ind := Induction for split Sort Prop.
Functional Scheme mapo_ind := Induction for mapo Sort Prop.
Functional Scheme gmerge_ind := Induction for gmerge Sort Prop.

(** * Automation and dedicated tactics. *)

Local Hint Constructors tree MapsTo In Bst Above Below.
Local Hint Unfold Apart Ok Bst_Ok.
Local Hint Immediate F.eq_sym.
Local Hint Resolve F.eq_refl F.eq_trans F.lt_trans.
Local Hint Resolve
 AboveLt Above_not_In Above_trans
 BelowGt Below_not_In Below_trans.

(* Function/Functional Scheme can't deal with internal fix.
   Let's do its job by hand: *)

Ltac join_tac l x d r :=
 revert x d r;
 induction l as [| lh ll _ lx ld lr Hlr];
   [ | intros x d r; induction r as [| rh rl Hrl rx rd rr _]; unfold join;
     [ | destruct (rh+2 <? lh) eqn:LT;
       [ match goal with |- context [ bal ?u ?v ?w ?z ] =>
           replace (bal u v w z)
           with (bal ll lx ld (join lr x d (Node rh rl rx rd rr))); [ | auto]
         end
       | destruct (lh+2 <? rh) eqn:LT';
         [ match goal with |- context [ bal ?u ?v ?w ?z ] =>
             replace (bal u v w z)
             with (bal (join (Node lh ll lx ld lr) x d rl) rx rd rr); [ | auto]
           end
         | ] ] ] ]; intros.

Ltac cleansplit :=
  simpl; cleanf; invok;
  match goal with
  | E:split _ _ = 〚 ?l, ?o, ?r 〛 |- _ =>
    change l with (〚l,o,r〛#l); rewrite <- ?E;
    change o with (〚l,o,r〛#o); rewrite <- ?E;
    change r with (〚l,o,r〛#r); rewrite <- ?E
  | _ => idtac
  end.

Section Elt.
Variable elt:Type.
Implicit Types m r : t elt.

(** * Helper functions *)

Global Instance create_ok l x e r `{!Ok l, !Ok r} :
 x >> l -> x << r -> Ok (create l x e r).
Proof.
 unfold create; auto.
Qed.

Lemma create_in l x e r y :
  y ∈ (create l x e r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 unfold create; split; [ inversion_clear 1 | ]; intuition.
Qed.

Global Instance bal_ok l x e r `{!Ok l, !Ok r} :
 x >> l -> x << r -> Ok (bal l x e r).
Proof.
 functional induction (bal l x e r); intros; cleanf;
 invok; invok; inv Above; inv Below;
 repeat apply create_ok; auto; unfold create; constructor; eauto.
Qed.

Lemma bal_in l x e r y :
 y ∈ (bal l x e r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 functional induction (bal l x e r); intros; cleanf;
 rewrite !create_in; intuition_in.
Qed.

Lemma bal_mapsto l x e r y e' :
 MapsTo y e' (bal l x e r) <-> MapsTo y e' (create l x e r).
Proof.
 functional induction (bal l x e r); intros; cleanf;
 unfold assert_false, create; intuition_in.
Qed.

Lemma bal_find l x e r y `{!Ok l, !Ok r} :
 x >> l -> x << r -> find y (bal l x e r) = find y (create l x e r).
Proof.
 functional induction (bal l x e r); intros; cleanf; trivial;
 invok; inv Above; inv Below;
 simpl; repeat case K.compare_spec; intuition; order.
Qed.

(** * Insertion *)

Lemma add_in m x y e :
 y ∈ (add x e m) <-> y == x \/ y ∈ m.
Proof.
 functional induction (add x e m); auto; intros; cleanf;
 rewrite ?bal_in; intuition_in. setoid_replace y with x; auto.
Qed.

Lemma add_lt m x e y : y >> m -> x < y -> y >> add x e m.
Proof.
 intros. apply above_alt. intros z. rewrite add_in. destruct 1; order.
Qed.

Lemma add_gt m x e y : y << m -> y < x -> y << add x e m.
Proof.
 intros. apply below_alt. intros z. rewrite add_in. destruct 1; order.
Qed.
Hint Resolve add_lt add_gt.

Global Instance add_ok m x e `{!Ok m} : Ok (add x e m).
Proof.
 functional induction (add x e m); intros; cleanf; invok; autok.
Qed.

Lemma add_spec1 m x e `{!Ok m} : find x (add x e m) = Some e.
Proof.
 functional induction (add x e m); simpl; intros; cleanf; trivial.
 - now rewrite F.compare_refl.
 - invok. rewrite bal_find; autok.
   simpl. case K.compare_spec; try order; auto.
 - invok. rewrite bal_find; autok.
   simpl. case K.compare_spec; try order; auto.
Qed.

Lemma add_spec2 m x y e `{!Ok m} : ~ x == y ->
 find y (add x e m) = find y m.
Proof.
 functional induction (add x e m); simpl; intros; cleanf; trivial.
 - case K.compare_spec; trivial; order.
 - case K.compare_spec; trivial; order.
 - invok. rewrite bal_find by autok. simpl. now rewrite IHt0.
 - invok. rewrite bal_find by autok. simpl. now rewrite IHt0.
Qed.

Lemma add_find m x y e `{!Ok m} :
 find y (add x e m) =
  match K.compare y x with Eq => Some e | _ => find y m end.
Proof.
 case K.compare_spec; intros E.
 - apply find_spec; autok. rewrite E. apply find_spec; autok.
   now apply add_spec1.
 - apply add_spec2; trivial; order.
 - apply add_spec2; trivial; order.
Qed.

(** * Extraction of minimum binding *)

Definition RemoveMin m res :=
 match m with
 | Leaf _ => False
 | Node h l x e r => remove_min l x e r = res
 end.

Lemma RemoveMin_step l x e r h m' p :
 RemoveMin (Node h l x e r) (m',p) ->
 (l = Leaf _ /\ m' = r /\ p = (x,e) \/
  exists m0, RemoveMin l (m0,p) /\ m' = bal m0 x e r).
Proof.
 simpl. destruct l as [|lh ll lx le lr]; simpl.
 - intros [= <- <-]. now left.
 - destruct (remove_min ll lx le lr) as (l',p').
   intros [= <- <-]. right. now exists l'.
Qed.

Lemma remove_min_mapsto m m' p : RemoveMin m (m',p) ->
 forall y e,
 MapsTo y e m <-> (y == p#1 /\ e = p#2) \/ MapsTo y e m'.
Proof.
 revert m'.
 induction m as [|h l IH x d r _]; [destruct 1|].
 intros m' R. apply RemoveMin_step in R.
 destruct R as [(->,(->,->))|[m0 (R,->)]]; intros y e; simpl.
 - intuition_in. subst. now constructor.
 - rewrite bal_mapsto. unfold create. specialize (IH _ R y e).
   intuition_in.
Qed.

Lemma remove_min_in m m' p : RemoveMin m (m',p) ->
 forall y, y ∈ m <-> y == p#1 \/ y ∈ m'.
Proof.
 revert m'.
 induction m as [|h l IH x e r _]; [destruct 1|].
 intros m' R y. apply RemoveMin_step in R.
 destruct R as [(->,(->,->))|[m0 (R,->)]].
 + intuition_in.
 + rewrite bal_in, In_node_iff, (IH _ R); intuition.
Qed.

Lemma remove_min_lt m m' p : RemoveMin m (m',p) ->
 forall y, y >> m -> y >> m'.
Proof.
 intros R y L. apply above_alt. intros z Hz.
 apply (AboveLt L).
 apply (remove_min_in R). now right.
Qed.
Hint Resolve remove_min_lt.

Lemma remove_min_gt m m' p `{!Ok m} : RemoveMin m (m',p) ->
 p#1 << m'.
Proof.
 revert m'.
 induction m as [|h l IH x e r _]; [destruct 1|].
 intros m' R. invok. apply RemoveMin_step in R.
 destruct R as [(_,(->,->))|[m0 (R,->)]]; auto.
 assert (p#1 << m0) by now apply IH.
 assert (In p#1 l) by (apply (remove_min_in R); now left).
 apply below_alt. intros z. rewrite bal_in.
 intuition_in; order.
Qed.

Global Instance remove_min_ok m m' p `{!Ok m} : RemoveMin m (m',p) -> Ok m'.
Proof.
 revert m'.
 induction m as [|h l IH x e r _]; [destruct 1|].
 intros m' R. invok. apply RemoveMin_step in R.
 destruct R as [(_,(->,->))|[m0 (R,->)]]; eauto with *.
Qed.

Lemma remove_min_find m m' p `{!Ok m} : RemoveMin m (m',p) ->
 forall y,
 find y m =
   match K.compare y p#1 with
    | Eq => Some p#2
    | Lt => None
    | Gt => find y m'
   end.
Proof.
 revert m'.
 induction m as [|h l IH x e r _]; [destruct 1|].
 intros m' R y. invok.
 apply RemoveMin_step in R.
 destruct R as [(->,(->,->))|[m0 (R,->)]]; auto.
 assert (Ok m0) by now apply remove_min_ok in R.
 assert (p#1 << m0) by now apply remove_min_gt in R.
 assert (x >> m0) by now apply (remove_min_lt R).
 assert (In p#1 l) by (apply (remove_min_in R); now left).
 simpl in *.
 rewrite (IH _ _ R), bal_find by trivial. clear IH. simpl.
 do 2 case K.compare_spec; trivial; try order.
Qed.

(** * Merging two trees *)

Ltac factor_remove_min m R := match goal with
 | h:int, H:remove_min ?l ?x ?e ?r = ?p |- _ =>
   assert (R:RemoveMin (Node h l x e r) p) by exact H;
   set (m:=Node h l x e r) in *; clearbody m; clear H l x e r
end.

Lemma append_in m1 m2 y :
  y ∈ (append m1 m2) <-> y ∈ m1 \/ y ∈ m2.
Proof.
 functional induction (append m1 m2); intros; try factornode m1.
 - intuition_in.
 - intuition_in.
 - factor_remove_min l R. rewrite bal_in, (remove_min_in R).
   simpl; intuition.
Qed.

Lemma append_mapsto m1 m2 y e :
 MapsTo y e (append m1 m2) <-> MapsTo y e m1 \/ MapsTo y e m2.
Proof.
 functional induction (append m1 m2); intros; try factornode m1.
 - intuition_in.
 - intuition_in.
 - factor_remove_min l R. rewrite bal_mapsto, (remove_min_mapsto R).
   simpl. unfold create; intuition_in. subst. now constructor.
Qed.

Global Instance append_ok m1 m2 `{!Ok m1, !Ok m2} : m1 <<< m2 ->
 Ok (append m1 m2).
Proof.
 functional induction (append m1 m2); intros B12; trivial.
 factornode m1. factor_remove_min l R.
 apply bal_ok; eauto with *.
 - apply above_alt. intros z Hz. apply B12; trivial.
   rewrite (remove_min_in R). now left.
 - now apply (remove_min_gt R).
Qed.

(** * Deletion *)

Lemma remove_in m x y `{!Ok m} :
 y ∈ remove x m <-> ~ y == x /\ y ∈ m.
Proof.
 functional induction (remove x m); simpl; intros; cleanf; invok;
  rewrite ?append_in, ?bal_in, ?IHt; intuition_in; order.
Qed.

Lemma remove_lt m x y `{!Ok m} : y >> m -> y >> remove x m.
Proof.
  intros. apply above_alt. intro. rewrite remove_in by trivial.
   destruct 1; order.
Qed.

Lemma remove_gt m x y `{!Ok m} : y << m -> y << remove x m.
Proof.
  intros. apply below_alt. intro. rewrite remove_in by trivial.
   destruct 1; order.
Qed.
Hint Resolve remove_gt remove_lt.

Global Instance remove_ok m x `{!Ok m} : Ok (remove x m).
Proof.
 functional induction (remove x m); simpl; intros; cleanf; invok; autok.
 apply append_ok; eauto.
Qed.

Lemma remove_spec1 m x `{!Ok m} : find x (remove x m) = None.
Proof.
 intros. apply not_find_iff; autok. rewrite remove_in; intuition.
Qed.

Lemma remove_spec2 m x y `{!Ok m} : ~ x == y ->
 find y (remove x m) = find y m.
Proof.
 functional induction (remove x m); simpl; intros; cleanf; invok; autok.
 - case K.compare_spec; intros; try order;
   rewrite find_mapsto_equiv; auto.
   + intros. rewrite append_mapsto; intuition; order.
   + apply append_ok; auto. red; intros; transitivity y0; order.
   + intros. rewrite append_mapsto; intuition; order.
   + apply append_ok; auto. now apply between with y0.
 - rewrite bal_find by autok. simpl. case K.compare_spec; auto.
 - rewrite bal_find by autok. simpl. case K.compare_spec; auto.
Qed.

(** * join *)

Lemma join_in l x d r y :
 y ∈ (join l x d r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 join_tac l x d r.
 - simpl join. rewrite add_in. intuition_in.
 - rewrite add_in. intuition_in.
 - rewrite bal_in, Hlr. clear Hlr Hrl. intuition_in.
 - rewrite bal_in, Hrl; clear Hlr Hrl; intuition_in.
 - apply create_in.
Qed.

Global Instance join_ok l x d r :
 Ok (create l x d r) -> Ok (join l x d r).
Proof.
  join_tac l x d r; unfold create in *;
  invok; invok; inv Above; inv Below; autok.
  - simpl. autok.
  - apply bal_ok; auto.
    apply below_alt. intro. rewrite join_in. intuition_in; order.
  - apply bal_ok; auto.
    apply above_alt. intro. rewrite join_in. intuition_in; order.
Qed.

Lemma join_find l x d r y :
 Ok (create l x d r) ->
 find y (join l x d r) = find y (create l x d r).
Proof.
 unfold create at 1.
 join_tac l x d r; trivial.
 - simpl in *. invok.
   rewrite add_find; trivial.
   case K.compare_spec; intros; trivial.
   apply not_find_iff; auto. intro. order.
 - clear Hlr. factornode l. simpl. invok.
   rewrite add_find by auto.
   case K.compare_spec; intros; trivial.
   apply not_find_iff; auto. intro. order.
 - clear Hrl LT. factornode r. invok; invok; inv Above; inv Below;
   rewrite bal_find; autok; simpl.
   + rewrite Hlr; auto; simpl.
     repeat (case K.compare_spec; trivial; try order).
   + apply below_alt. intro. rewrite join_in. intuition_in; order.
 - clear Hlr LT LT'. factornode l. invok; invok; inv Above; inv Below;
   rewrite bal_find; autok; simpl.
   + rewrite Hrl; auto; simpl.
     repeat (case K.compare_spec; trivial; try order).
   + apply above_alt. intro. rewrite join_in. intuition_in; order.
Qed.

(** * split *)

Lemma split_in_l0 m x y : y ∈ (split x m)#l -> y ∈ m.
Proof.
  functional induction (split x m); cleansplit;
  rewrite ?join_in; intuition.
Qed.

Lemma split_in_r0 m x y : y ∈ (split x m)#r -> y ∈ m.
Proof.
  functional induction (split x m); cleansplit;
  rewrite ?join_in; intuition.
Qed.

Lemma split_in_l m x y `{!Ok m} :
 (y ∈ (split x m)#l <-> y ∈ m /\ y < x).
Proof.
  functional induction (split x m); intros; cleansplit;
  rewrite ?join_in, ?IHt; intuition_in; order.
Qed.

Lemma split_in_r m x y `{!Ok m} :
 (y ∈ (split x m)#r <-> y ∈ m /\ x < y).
Proof.
  functional induction (split x m); intros; cleansplit;
  rewrite ?join_in, ?IHt; intuition_in; order.
Qed.

Lemma split_in_o m x : (split x m)#o = find x m.
Proof.
  functional induction (split x m); intros; cleansplit; auto.
Qed.

Lemma split_lt_l m x `{!Ok m} : x >> (split x m)#l.
Proof.
  apply above_alt. intro. rewrite split_in_l; intuition; order.
Qed.

Lemma split_lt_r m x y : y >> m -> y >> (split x m)#r.
Proof.
  intro. apply above_alt. intros z Hz. apply split_in_r0 in Hz. order.
Qed.

Lemma split_gt_r m x `{!Ok m} : x << (split x m)#r.
Proof.
  apply below_alt. intro. rewrite split_in_r; intuition; order.
Qed.

Lemma split_gt_l m x y : y << m -> y << (split x m)#l.
Proof.
  intro. apply below_alt. intros z Hz. apply split_in_l0 in Hz. order.
Qed.
Hint Resolve split_lt_l split_lt_r split_gt_l split_gt_r.

Global Instance split_ok_l m x `{!Ok m} : Ok (split x m)#l.
Proof.
  functional induction (split x m); intros; cleansplit; intuition.
Qed.

Global Instance split_ok_r m x `{!Ok m} : Ok (split x m)#r.
Proof.
  functional induction (split x m); intros; cleansplit; intuition.
Qed.

Lemma split_find m x y `{!Ok m} :
 find y m = match K.compare y x with
              | Eq => (split x m)#o
              | Lt => find y (split x m)#l
              | Gt => find y (split x m)#r
            end.
Proof.
 functional induction (split x m); intros; cleansplit.
 - now case K.compare.
 - repeat case K.compare_spec; trivial; order.
 - simpl in *. rewrite join_find, IHt0; autok.
   simpl. repeat case K.compare_spec; trivial; order.
 - rewrite join_find, IHt0; autok.
   simpl; repeat case K.compare_spec; trivial; order.
Qed.

(** * Concatenation *)

Lemma concat_in m1 m2 y :
 y ∈ (concat m1 m2) <-> y ∈ m1 \/ y ∈ m2.
Proof.
 functional induction (concat m1 m2); intros; try factornode m1.
 - intuition_in.
 - intuition_in.
 - factor_remove_min m2 R.
   rewrite join_in, (remove_min_in R); simpl; intuition.
Qed.

Global Instance concat_ok m1 m2 `{!Ok m1, !Ok m2} : m1 <<< m2 ->
 Ok (concat m1 m2).
Proof.
  functional induction (concat m1 m2); intros LT; auto;
  try factornode m1.
  factor_remove_min m2 R.
  apply join_ok, create_ok; auto.
  - now apply remove_min_ok in R.
  - apply above_alt. intros y Hy. apply LT; trivial.
    rewrite (remove_min_in R); now left.
  - now apply (remove_min_gt R).
Qed.

Definition oelse {A} (o1 o2:option A) :=
  match o1 with
  | Some x => Some x
  | None => o2
  end.

Lemma concat_find m1 m2 y `{!Ok m1, !Ok m2} : m1 <<< m2 ->
 find y (concat m1 m2) = oelse (find y m2) (find y m1).
Proof.
 functional induction (concat m1 m2); intros B; auto; try factornode m1.
 - destruct (find y m2); auto.
 - factor_remove_min m2 R.
   assert (xd#1 >> m1).
   { apply above_alt. intros z Hz. apply B; trivial.
     rewrite (remove_min_in R). now left. }
   rewrite join_find; simpl; auto.
   + rewrite (remove_min_find R y).
     case K.compare_spec; intros; auto.
     destruct (find y m2'); trivial.
     simpl. symmetry. apply not_find_iff; eauto.
   + apply create_ok; eauto with *. now apply (remove_min_gt R).
Qed.

End Elt.

Section Mapo.
Variable elt elt' : Type.
Variable f : key -> elt -> option elt'.

Lemma mapo_in m x :
 x ∈ (mapo f m) ->
 exists y d, K.eq y x /\ MapsTo x d m /\ f y d <> None.
Proof.
functional induction (mapo f m); simpl; auto; intro H.
- inv In.
- rewrite join_in in H; destruct H as [H|[H|H]].
  + exists x0, d. do 2 (split; auto). congruence.
  + destruct (IHt0 H) as (y & e & ? & ? & ?). exists y, e. auto.
  + destruct (IHt1 H) as (y & e & ? & ? & ?). exists y, e. auto.
- rewrite concat_in in H; destruct H as [H|H].
  + destruct (IHt0 H) as (y & e & ? & ? & ?). exists y, e. auto.
  + destruct (IHt1 H) as (y & e & ? & ? & ?). exists y, e. auto.
Qed.

Lemma mapo_lt m x : x >> m -> x >> mapo f m.
Proof.
  intros H. apply above_alt. intros y Hy.
  destruct (mapo_in Hy) as (y' & e & ? & ? & ?). order.
Qed.

Lemma mapo_gt m x : x << m -> x << mapo f m.
Proof.
  intros H. apply below_alt. intros y Hy.
  destruct (mapo_in Hy) as (y' & e & ? & ? & ?). order.
Qed.
Hint Resolve mapo_lt mapo_gt.

Global Instance mapo_ok m `{!Ok m} : Ok (mapo f m).
Proof.
functional induction (mapo f m); simpl; auto; invok.
- apply join_ok, create_ok; auto.
- apply concat_ok; auto. apply between with x; auto.
Qed.

Ltac nonify e :=
 replace e with (@None elt) by
  (symmetry; rewrite not_find_iff; auto; intro; order).

Definition obind {A B} (o:option A) (f:A->option B) :=
  match o with Some a => f a | None => None end.

Lemma mapo_find m x `{!Ok m} :
  exists y, K.eq y x /\
            find x (mapo f m) = obind (find x m) (f y).
Proof.
functional induction (mapo f m); simpl; auto; invok.
- now exists x.
- rewrite join_find; auto.
  + simpl. case K.compare_spec; simpl; intros.
    * now exists x0.
    * destruct IHt0 as (y' & ? & ?); auto.
      exists y'; split; trivial.
    * destruct IHt1 as (y' & ? & ?); auto.
      exists y'; split; trivial.
  + constructor; chok; auto using mapo_lt, mapo_gt with *.
- rewrite concat_find; autok.
  + destruct IHt1 as (y' & ? & ->); auto.
    destruct IHt0 as (y'' & ? & ->); auto.
    case K.compare_spec; simpl; intros.
    * nonify (find x r). nonify (find x l). simpl. now exists x0.
    * nonify (find x r). now exists y''.
    * nonify (find x l). exists y'. split; trivial.
      destruct (find x r); simpl; trivial.
      now destruct (f y' e).
  + apply between with x0; auto.
Qed.

End Mapo.

Section Gmerge.
Variable elt elt' elt'' : Type.
Variable f0 : key -> option elt -> option elt' -> option elt''.
Variable f : key -> elt -> option elt' -> option elt''.
Variable mapl : t elt -> t elt''.
Variable mapr : t elt' -> t elt''.
Hypothesis f0_f : forall x d o, f x d o = f0 x (Some d) o.
Hypothesis mapl_ok : forall m, Ok m -> Ok (mapl m).
Hypothesis mapr_ok : forall m', Ok m' -> Ok (mapr m').
Hypothesis mapl_f0 : forall x m, Ok m ->
 exists y, K.eq y x /\
           find x (mapl m) = obind (find x m) (fun d => f0 y (Some d) None).
Hypothesis mapr_f0 : forall x m, Ok m ->
 exists y, K.eq y x /\
           find x (mapr m) = obind (find x m) (fun d => f0 y None (Some d)).

Notation gmerge := (gmerge f mapl mapr).

Lemma gmerge_in m m' y `{!Ok m, !Ok m'} :
  y ∈ (gmerge m m') -> y ∈ m \/ y ∈ m'.
Proof.
  functional induction (gmerge m m'); intros H;
  try factornode m2; invok.
  - right. apply find_in.
    generalize (in_find H).
    destruct (@mapr_f0 y m2) as (y' & ? & ->); trivial.
    intros A B. rewrite B in A. now elim A.
  - left. apply find_in.
    generalize (in_find H).
    destruct (@mapl_f0 y m2) as (y' & ? & ->); trivial.
    intros A B. rewrite B in A. now elim A.
  - rewrite join_in in *. revert IHt2 IHt0 H. cleansplit.
    generalize (@split_ok_l _ m2 x1 _) (@split_ok_r _ m2 x1 _).
    rewrite split_in_r, split_in_l; intuition_in.
  - rewrite concat_in in *. revert IHt2 IHt0 H; cleansplit.
    generalize (@split_ok_l _ m2 x1 _) (@split_ok_r _ m2 x1 _).
    rewrite split_in_r, split_in_l; intuition_in.
Qed.

Lemma gmerge_lt m m' x `{!Ok m, !Ok m'} :
  x >> m -> x >> m' -> x >> gmerge m m'.
Proof.
  intros. apply above_alt. intros y Hy.
  apply gmerge_in in Hy; intuition_in; order.
Qed.

Lemma gmerge_gt m m' x `{!Ok m, !Ok m'} :
  x << m -> x << m' -> x << gmerge m m'.
Proof.
  intros. apply below_alt. intros y Hy.
  apply gmerge_in in Hy; intuition_in; order.
Qed.
Hint Resolve gmerge_lt gmerge_gt.
Hint Resolve split_ok_l split_ok_r split_lt_l split_gt_r.

Global Instance gmerge_ok m m' `{!Ok m, !Ok m'} : Ok (gmerge m m').
Proof.
  functional induction (gmerge m m'); auto; factornode m2; invok;
  (apply join_ok, create_ok || apply concat_ok);
  revert IHt2 IHt0; cleansplit; intuition.
  apply between with x1; auto.
Qed.

Lemma oelse_none_r {A} (o:option A) : oelse o None = o.
Proof. now destruct o. Qed.

Ltac nonify e :=
 let E := fresh "E" in
 let U := fresh "U" in
 assert (E : e = None);
   [ rewrite not_find_iff; autok; intro U;
     try apply gmerge_in in U; intuition_in; order
   | rewrite E; clear E ].

Lemma gmerge_find m m' x `{!Ok m, !Ok m'} :
 In x m \/ In x m' ->
 exists y, K.eq y x /\
           find x (gmerge m m') = f0 y (find x m) (find x m').
Proof.
  functional induction (gmerge m m'); intros H;
  try factornode m2; invok.
  - destruct H; [ intuition_in | ].
    destruct (@mapr_f0 x m2) as (y,(Hy,E)); trivial.
    exists y; split; trivial.
    rewrite E. simpl. apply in_find in H; trivial.
    destruct (find x m2); simpl; intuition.
  - destruct H; [ | intuition_in ].
    destruct (@mapl_f0 x m2) as (y,(Hy,E)); trivial.
    exists y; split; trivial.
    rewrite E. simpl. apply in_find in H; trivial.
    destruct (find x m2); simpl; intuition.
  - generalize (@split_ok_l _ m2 x1 _) (@split_ok_r _ m2 x1 _).
    rewrite (@split_find _ m2 x1 x); autok.
    rewrite e1 in *; simpl in *. intros.
    rewrite join_find by (cleansplit; constructor; autok).
    simpl. case K.compare_spec; intros.
    + exists x1. split; auto. now rewrite <- e3, f0_f.
    + apply IHt2; auto. clear IHt2 IHt0.
      cleansplit; rewrite split_in_l; trivial.
      intuition_in; order.
    + apply IHt0; auto. clear IHt2 IHt0.
      cleansplit; rewrite split_in_r; trivial.
      intuition_in; order.
  - generalize (@split_ok_l _ m2 x1 _) (@split_ok_r _ m2 x1 _).
    rewrite (@split_find _ m2 x1 x); autok.
    pose proof (@split_lt_l _ m2 x1 _).
    pose proof (@split_gt_r _ m2 x1 _).
    rewrite e1 in *; simpl in *. intros.
    rewrite concat_find by (try apply between with x1; autok).
    case K.compare_spec; intros.
    + clear IHt0 IHt2.
      exists x1. split; auto. rewrite <- f0_f, e2.
      nonify (find x (gmerge r1 r2')).
      nonify (find x (gmerge l1 l2')). trivial.
    + nonify (find x (gmerge r1 r2')).
      simpl. apply IHt2; auto. clear IHt2 IHt0.
      intuition_in; try order.
      right. cleansplit. now apply split_in_l.
    + nonify (find x (gmerge l1 l2')). simpl.
      rewrite oelse_none_r.
      apply IHt0; auto. clear IHt2 IHt0.
      intuition_in; try order.
      right. cleansplit. now apply split_in_r.
Qed.

End Gmerge.

Section Merge.
Variable elt elt' elt'' : Type.
Variable f : key -> option elt -> option elt' -> option elt''.

Global Instance merge_ok m m' `{!Ok m, !Ok m'} : Ok (merge f m m').
Proof.
unfold merge; intros.
apply gmerge_ok with f;
 auto using mapo_ok, mapo_find.
Qed.

Lemma merge_spec1 m m' x `{!Ok m, !Ok m'} :
 In0 x m \/ In0 x m' ->
 exists y, K.eq y x /\
           find x (merge f m m') = f y (find x m) (find x m').
Proof.
  rewrite !In_alt.
  unfold merge; intros.
  edestruct (gmerge_find (f0:=f)) as (y,(Hy,E));
    eauto using mapo_ok.
  - reflexivity.
  - intros. now apply mapo_find.
  - intros. now apply mapo_find.
Qed.

Lemma merge_spec2 m m' x `{!Ok m, !Ok m'} :
  In0 x (merge f m m') -> In0 x m \/ In0 x m'.
Proof.
rewrite !In_alt.
unfold merge; intros.
eapply gmerge_in with (f0:=f); try eassumption;
 auto using mapo_ok, mapo_find.
Qed.

End Merge.

Definition In := Ind.In0.
Definition Eqdom := Ind.Eqdom0.
Definition Equiv := Ind.Equiv0.
Definition Equivb := Ind.Equivb0.

End MakeRaw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we need
   to encapsulate everything into a type of binary search trees. *)

Module IntMake (I:Int)(K: OrderedType) <: Interface.S K.
 Module Raw := MakeRaw I K.
 Include Raw.Pack K Raw.
End IntMake.


Module IntMake_ord (I:Int)(K:OrderedType)(D:OrderedType) <: Sord K D.
  Module Import MapS := IntMake(I)(K).
  Module LO := MMaps.OrdList.Make_ord(K)(D).
  Module Import R := Raw.

  Definition t := MapS.t D.t.

  Definition cmp e e' :=
   match D.compare e e' with Eq => true | _ => false end.

  (** One step of comparison of bindings *)

  Definition compare_more x1 d1 (cont:R.enumeration D.t -> comparison) e2 :=
   match e2 with
    | R.End _ => Gt
    | R.More x2 d2 r2 e2 =>
       match K.compare x1 x2 with
        | Eq => match D.compare d1 d2 with
                   | Eq => cont (R.cons r2 e2)
                   | Lt => Lt
                   | Gt => Gt
                  end
        | Lt => Lt
        | Gt => Gt
       end
   end.

  (** Comparison of left tree, middle element, then right tree *)

  Fixpoint compare_cont s1 (cont:R.enumeration D.t -> comparison) e2 :=
   match s1 with
    | R.Leaf _ => cont e2
    | R.Node _ l1 x1 d1 r1 =>
       compare_cont l1 (compare_more x1 d1 (compare_cont r1 cont)) e2
   end.

  (** Initial continuation *)

  Definition compare_end (e2:R.enumeration D.t) :=
   match e2 with R.End _ => Eq | _ => Lt end.

  (** The complete comparison *)

  Definition compare m1 m2 :=
    compare_cont m1.(this) compare_end (R.cons m2.(this) (R.End _)).

  (** Correctness of this comparison *)

  Definition Cmp c :=
   match c with
    | Eq => LO.eq_list
    | Lt => LO.lt_list
    | Gt => flip LO.lt_list
   end.

  Lemma cons_Cmp c x1 x2 d1 d2 l1 l2 :
   K.eq x1 x2 -> D.eq d1 d2 ->
   Cmp c l1 l2 -> Cmp c ((x1,d1)::l1) ((x2,d2)::l2).
  Proof.
    destruct c; simpl; unfold flip; simpl; intuition.
  Qed.
  Hint Resolve cons_Cmp.

  Lemma compare_end_Cmp e2 :
   Cmp (compare_end e2) nil (R.flatten_e e2).
  Proof.
   destruct e2; simpl; auto.
  Qed.

  Lemma compare_more_Cmp x1 d1 cont x2 d2 r2 e2 l :
    Cmp (cont (R.cons r2 e2)) l (R.bindings r2 ++ R.flatten_e e2) ->
     Cmp (compare_more x1 d1 cont (R.More x2 d2 r2 e2)) ((x1,d1)::l)
       (R.flatten_e (R.More x2 d2 r2 e2)).
  Proof.
   simpl; case K.compare_spec; simpl;
   try case D.compare_spec; simpl; unfold flip; simpl; intuition.
  Qed.

  Lemma compare_cont_Cmp : forall s1 cont e2 l,
   (forall e, Cmp (cont e) l (R.flatten_e e)) ->
   Cmp (compare_cont s1 cont e2) (R.bindings s1 ++ l) (R.flatten_e e2).
  Proof.
    induction s1 as [|h1 l1 Hl1 x1 d1 r1 Hr1] using R.tree_ind;
    intros; auto.
    rewrite R.bindings_node_acc; simpl.
    apply Hl1; auto. clear e2. intros [|x2 d2 r2 e2].
    simpl; unfold flip; simpl; auto.
    apply compare_more_Cmp.
    rewrite <- Raw.cons_1; auto.
  Qed.

  Lemma compare_Cmp m1 m2 :
   Cmp (compare m1 m2) (bindings m1.(this)) (bindings m2.(this)).
  Proof.
    destruct m1 as (s1,H1), m2 as (s2,H2).
    unfold compare; simpl.
    rewrite <- (app_nil_r (R.bindings s1)).
    replace (R.bindings s2) with (R.flatten_e (R.cons s2 (R.End _))) by
    (rewrite R.cons_1; simpl; rewrite app_nil_r; auto).
    auto using compare_cont_Cmp, compare_end_Cmp.
  Qed.

  Definition eq (m1 m2 : t) :=
    LO.eq_list (bindings m1.(this)) (bindings m2.(this)).
  Definition lt (m1 m2 : t) :=
    LO.lt_list (bindings m1.(this)) (bindings m2.(this)).

  Lemma compare_spec m1 m2 : CompSpec eq lt m1 m2 (compare m1 m2).
  Proof.
    assert (H := compare_Cmp m1 m2).
    unfold Cmp in H.
    destruct (compare m1 m2); auto.
  Qed.

  (* Proofs about [eq] and [lt] *)

  Definition sbindings (m1 : t) :=
   @LO.MapS.Mkt _ _ (@R.bindings_spec2 _ m1 _).

  Definition seq (m1 m2 : t) := LO.eq (sbindings m1) (sbindings m2).
  Definition slt (m1 m2 : t) := LO.lt (sbindings m1) (sbindings m2).

  Lemma eq_seq : forall m1 m2, eq m1 m2 <-> seq m1 m2.
  Proof.
   unfold eq, seq, sbindings, bindings, LO.eq; intuition.
  Qed.

  Lemma lt_slt : forall m1 m2, lt m1 m2 <-> slt m1 m2.
  Proof.
   unfold lt, slt, sbindings, bindings, LO.lt; intuition.
  Qed.

  Lemma eq_spec m m' : eq m m' <-> MapS.Equivb cmp m m'.
  Proof.
  rewrite eq_seq; unfold seq.
  rewrite Equivb_Equivb, R.Equivb_alt, R.Equivb_bindings.
  apply LO.eq_spec.
  Qed.

  Instance eq_equiv : Equivalence eq.
  Proof.
    constructor; red; [intros x|intros x y| intros x y z];
    rewrite !eq_seq; apply LO.eq_equiv.
  Qed.

  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros m1 m2 H1 m1' m2' H2. rewrite !lt_slt. rewrite eq_seq in *.
    now apply LO.lt_compat.
  Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor; red; [intros x; red|intros x y z];
    rewrite !lt_slt; apply LO.lt_strorder.
  Qed.

End IntMake_ord.

(* For concrete use inside Coq, we propose an instantiation of [Int] by [Z]. *)

Module Make (K:OrderedType) <: S K := IntMake(Z_as_Int)(K).

Module Make_ord (K:OrderedType)(D:OrderedType) <: Sord K D
 := IntMake_ord(Z_as_Int)(K)(D).
