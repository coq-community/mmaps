(** * MSets.GenTree : maps via generic trees

    This module factorizes common parts in implementations
    of finite maps as AVL trees and as Red-Black trees. The nodes
    of the trees defined here include an generic information
    parameter, that will be the height in AVL trees and the color
    in Red-Black trees. Without more details here about these
    information parameters, trees here are not known to be
    well-balanced, but simply binary-search-trees.

    The operations we could define and prove correct here are the
    ones that do not modify the informations on the nodes :

     - empty is_empty
     - find mem
     - equal
     - fold cardinal bindings
     - map mapi
*)

From Coq Require Import Bool PeanoNat BinInt FunInd.
From Coq Require Import Orders OrdersFacts OrdersLists.
From MMaps Require Import Interface OrdList.

Local Open Scope list_scope.
Local Open Scope lazy_bool_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* For nicer extraction, we create induction principles
   only when needed *)
Local Unset Elimination Schemes.

Module Type InfoTyp.
 Parameter t : Set.
End InfoTyp.

(** * Ops : the pure functions *)

Module Type Ops (K:OrderedType)(Info:InfoTyp).

Definition key := K.t.
Hint Transparent key.

Section Elt.

Variable elt : Type.

(** * Trees *)

Inductive tree  : Type :=
| Leaf : tree
| Node : Info.t -> tree -> K.t -> elt -> tree -> tree.

Notation t := tree.

(** ** The empty map and emptyness test *)

Definition empty := Leaf.

Definition is_empty t :=
 match t with
 | Leaf => true
 | _ => false
 end.

(** ** Membership test *)

(** The [mem] function is deciding membership. It exploits the
    binary search tree invariant to achieve logarithmic complexity. *)

Fixpoint mem x t :=
 match t with
 | Leaf => false
 | Node _ l k _ r =>
   match K.compare x k with
     | Lt => mem x l
     | Eq => true
     | Gt => mem x r
   end
 end.

Fixpoint find x m : option elt :=
  match m with
    |  Leaf => None
    |  Node _ l y v r =>
       match K.compare x y with
         | Eq => Some v
         | Lt => find x l
         | Gt => find x r
       end
   end.

(** ** Minimal, maximal, arbitrary bindings *)

Fixpoint min_binding (t : tree) : option (key * elt) :=
 match t with
 | Leaf => None
 | Node _ Leaf x e r => Some (x,e)
 | Node _ l x e r => min_binding l
 end.

Fixpoint max_binding (t : tree) : option (key * elt) :=
  match t with
  | Leaf => None
  | Node _ l x e Leaf => Some (x,e)
  | Node _ l x e r => max_binding r
  end.

Definition choose := min_binding.

(** ** Iteration on elements *)

Fixpoint fold {A: Type} (f: key -> elt -> A -> A) (t: tree) (base: A) : A :=
  match t with
  | Leaf => base
  | Node _ l x e r => fold f r (f x e (fold f l base))
 end.

Fixpoint bindings_aux acc s :=
  match s with
   | Leaf => acc
   | Node _ l x e r => bindings_aux ((x,e) :: bindings_aux acc r) l
  end.

Definition bindings := bindings_aux nil.

Fixpoint rev_bindings_aux acc s :=
  match s with
   | Leaf => acc
   | Node _ l x e r => rev_bindings_aux ((x,e) :: rev_bindings_aux acc l) r
  end.

Definition rev_bindings := rev_bindings_aux nil.

Fixpoint cardinal (s : tree) : nat :=
  match s with
   | Leaf => 0
   | Node _ l _ _ r => S (cardinal l + cardinal r)
  end.

Fixpoint maxdepth s :=
 match s with
 | Leaf => 0
 | Node _ l _ _ r => S (max (maxdepth l) (maxdepth r))
 end.

Fixpoint mindepth s :=
 match s with
 | Leaf => 0
 | Node _ l _ _ r => S (min (mindepth l) (mindepth r))
 end.

(** ** Testing universal or existential properties. *)

(** We do not use the standard boolean operators of Coq,
    but lazy ones. *)

Fixpoint for_all (f:key->elt->bool) s := match s with
  | Leaf => true
  | Node _ l x e r => f x e &&& for_all f l &&& for_all f r
end.

Fixpoint exists_ (f:key->elt->bool) s := match s with
  | Leaf => false
  | Node _ l x e r => f x e ||| exists_ f l ||| exists_ f r
end.

(** ** Comparison of trees *)

(** The algorithm here has been suggested by Xavier Leroy,
    and transformed into c.p.s. by Benjamin Grégoire.
    The original ocaml code (with non-structural recursive calls)
    has also been formalized (thanks to Function+measure), see
    [ocaml_compare] in [MSetFullAVL]. The following code with
    continuations computes dramatically faster in Coq, and
    should be almost as efficient after extraction.
*)

(** * Comparison *)

Variable cmp : elt->elt->bool.

(** Enumeration of the elements of a tree. This corresponds
    to the "samefringe" notion in the litterature. *)

Inductive enumeration :=
 | End : enumeration
 | More : key -> elt -> tree -> enumeration -> enumeration.

(** [cons t e] adds the elements of tree [t] on the head of
    enumeration [e]. *)

Fixpoint cons s e : enumeration :=
 match s with
  | Leaf => e
  | Node _ l x v r => cons l (More x v r e)
 end.

(** One step of comparison of elements *)

Definition equal_more x1 v1 (cont:enumeration->bool) e2 :=
 match e2 with
 | End => false
 | More x2 v2 r2 e2 =>
     match K.compare x1 x2 with
      | Eq => cmp v1 v2 &&& cont (cons r2 e2)
      | _ => false
     end
 end.

(** Comparison of left tree, middle element, then right tree *)

Fixpoint equal_cont m1 (cont:enumeration->bool) e2 :=
 match m1 with
  | Leaf => cont e2
  | Node _ l1 x1 v1 r1 =>
     equal_cont l1 (equal_more x1 v1 (equal_cont r1 cont)) e2
  end.

(** Initial continuation *)

Definition equal_end e2 := match e2 with End => true | _ => false end.

(** The complete comparison *)

Definition equal m1 m2 := equal_cont m1 equal_end (cons m2 End).

End Elt.
Notation t := tree.

(** ** Map *)

Fixpoint map {elt elt'}(f : elt -> elt')(m : t elt) : t elt' :=
  match m with
   | Leaf _  => Leaf _
   | Node h l x d r => Node h (map f l) x (f d) (map f r)
  end.

(* ** Mapi *)

Fixpoint mapi (elt elt' : Type)(f : key -> elt -> elt')(m : t elt) : t elt' :=
  match m with
   | Leaf _ => Leaf _
   | Node h l x d r => Node h (mapi f l) x (f x d) (mapi f r)
  end.

End Ops.

(** * Props : correctness proofs of these generic operations *)

Module Type Props (K:OrderedType)(Info:InfoTyp)(Import M:Ops K Info).

Section Invariants.
Variable elt : Type.

(** ** Occurrence in a tree *)

Inductive MapsTo (x : key)(e : elt) : t elt -> Prop :=
  | MapsRoot : forall l r h y,
      K.eq x y -> MapsTo x e (Node h l y e r)
  | MapsLeft : forall l r h y e',
      MapsTo x e l -> MapsTo x e (Node h l y e' r)
  | MapsRight : forall l r h y e',
      MapsTo x e r -> MapsTo x e (Node h l y e' r).

Inductive In (x : key) : t elt -> Prop :=
  | InRoot : forall l r h y e,
      K.eq x y -> In x (Node h l y e r)
  | InLeft : forall l r h y e',
      In x l -> In x (Node h l y e' r)
  | InRight : forall l r h y e',
      In x r -> In x (Node h l y e' r).

Definition In0 k m := exists e:elt, MapsTo k e m.

Definition Equal (m m' : t elt) := forall k, find k m = find k m'.
Definition Eqdom (m m' : t elt) := forall k, In k m <-> In k m'.

(** ** Binary search trees *)

(** [Above x m] : [x] is strictly greater than any key in [m].
    [Below x m] : [x] is strictly smaller than any key in [m]. *)

Inductive Above (x:key) : t elt -> Prop :=
 | AbLeaf : Above x (Leaf _)
 | AbNode l r h y e : Above x l -> K.lt y x -> Above x r ->
   Above x (Node h l y e r).

Inductive Below (x:key) : t elt -> Prop :=
 | BeLeaf : Below x (Leaf _)
 | BeNode l r h y e : Below x l -> K.lt x y -> Below x r ->
   Below x (Node h l y e r).

(** [Apart] : all keys in [m1] are lower than all keys in [m2] *)

Definition Apart (m1 m2 : t elt) : Prop :=
  forall x1 x2, In x1 m1 -> In x2 m2 -> K.lt x1 x2.

(** [Bst t] : [t] is a binary search tree *)

Inductive Bst : t elt -> Prop :=
  | BSLeaf : Bst (Leaf _)
  | BSNode : forall h x e l r, Bst l -> Bst r ->
     Above x l -> Below x r -> Bst (Node h l x e r).

(** [Bst] is the (decidable) invariant our trees will have to satisfy. *)

Class Ok (m:t elt) : Prop := ok : Bst m.

End Invariants.

Module F := OrderedTypeFacts K.
Module O := KeyOrderedType K.
Module L := MMaps.OrdList.Raw K.

Local Infix "∈" := In (at level 70).
Local Infix "==" := K.eq (at level 70).
Local Infix "<" := K.lt (at level 70).
Local Infix "<<" := Below (at level 70).
Local Infix ">>" := Above (at level 70).
Local Infix "<<<" := Apart (at level 70).

Scheme tree_ind := Induction for tree Sort Prop.
Scheme MapsTo_ind := Induction for MapsTo Sort Prop.
Scheme In_ind := Induction for In Sort Prop.
Scheme Above_ind := Induction for Above Sort Prop.
Scheme Below_ind := Induction for Below Sort Prop.

Functional Scheme mem_ind := Induction for mem Sort Prop.
Functional Scheme find_ind := Induction for find Sort Prop.

(** * Automation and dedicated tactics. *)

Local Hint Constructors tree MapsTo In Bst Above Below.
Local Hint Unfold Apart Ok.
Local Hint Immediate F.eq_sym.
Local Hint Resolve F.eq_refl F.eq_trans F.lt_trans.

Tactic Notation "factornode" ident(s) :=
 try clear s;
 match goal with
   | |- context [Node ?h ?l ?x ?e ?r] =>
       set (s:=Node h l x e r) in *; clearbody s; clear l x e r; try clear h
   | _ : context [Node ?h ?l ?x ?e ?r] |- _ =>
       set (s:=Node h l x e r) in *; clearbody s; clear l x e r; try clear h
 end.

(** A tactic for cleaning hypothesis after use of functional induction. *)

Ltac cleanf :=
 match goal with
  | H : K.compare _ _ = Eq |- _ =>
    rewrite ?H; apply F.compare_eq in H; cleanf
  | H : K.compare _ _ = Lt |- _ =>
    rewrite ?H; apply F.compare_lt_iff in H; cleanf
  | H : K.compare _ _ = Gt |- _ =>
    rewrite ?H; apply F.compare_gt_iff in H; cleanf
  | _ => idtac
 end.


(** A tactic to repeat [inversion_clear] on all hyps of the
    form [(f (Node ...))] *)

Ltac inv f :=
  match goal with
     | H:f (Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ (Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ _ (Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ _ _ (Leaf _) |- _ => inversion_clear H; inv f
     | H:f (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ _ _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | _ => idtac
  end.

Ltac inv_all f :=
  match goal with
   | H: f _ |- _ => inversion_clear H; inv f
   | H: f _ _ |- _ => inversion_clear H; inv f
   | H: f _ _ _ |- _ => inversion_clear H; inv f
   | H: f _ _ _ _ |- _ => inversion_clear H; inv f
   | _ => idtac
  end.

Ltac intuition_in := repeat (intuition; inv In; inv MapsTo).

Arguments Equal {elt} m m'.
Arguments Eqdom {elt} m m'.

Global Instance Equal_equiv {elt} : Equivalence (@Equal elt).
Proof. split; congruence. Qed.
Global Instance Eqdom_equiv {elt} : Equivalence (@Eqdom elt).
Proof. firstorder. Qed.

(** * Basic results about [MapsTo], [In], [Above], [Below], [height] *)

(** Facts about [MapsTo] and [In]. *)

Lemma MapsRoot' {elt} x y e e' (l r:t elt) h :
 x == y -> e = e' -> MapsTo x e (Node h l y e' r).
Proof.
 intros; subst; auto.
Qed.

Lemma MapsTo_In {elt} k (e:elt) m : MapsTo k e m -> k ∈ m.
Proof.
 induction 1; auto.
Qed.
Local Hint Resolve MapsTo_In.

Lemma In_MapsTo {elt} k m : k ∈ m -> exists (e:elt), MapsTo k e m.
Proof.
 induction 1; try destruct IHIn as (e,He); exists e; auto.
Qed.

Lemma In_alt' {elt} k (m:t elt) : k ∈ m <-> exists e, MapsTo k e m.
Proof.
 split; [ apply In_MapsTo | intros (e,M); eapply MapsTo_In; eauto].
Qed.

Lemma In_alt {elt} k (m:t elt) : In0 k m <-> k ∈ m.
Proof.
 symmetry. apply In_alt'.
Qed.

Lemma MapsTo_1 {elt} m x y (e:elt) :
  x == y -> MapsTo x e m -> MapsTo y e m.
Proof.
 induction m; simpl; intuition_in; eauto.
Qed.
Hint Immediate MapsTo_1.

Global Instance MapsTo_compat {elt} :
  Proper (K.eq==>Logic.eq==>Logic.eq==>iff) (@MapsTo elt).
Proof.
 intros x x' Hx e e' He m m' Hm. subst.
 split; now apply MapsTo_1.
Qed.

Global Instance In_compat {elt} :
  Proper (K.eq==>Logic.eq==>iff) (@In elt).
Proof.
 intros x x' H m m' <-.
 induction m; simpl; intuition_in; eauto.
Qed.

Lemma In_leaf {elt} y : y ∈ (@Leaf elt) <-> False.
Proof.
 intuition_in.
Qed.

Lemma In_node_iff {elt} l x (e:elt) r h y :
  y ∈ (Node h l x e r) <-> y ∈ l \/ y == x \/ y ∈ r.
Proof.
 intuition_in.
Qed.

Lemma MapsTo_leaf {elt} y e : MapsTo y e (@Leaf elt) <-> False.
Proof.
 intuition_in.
Qed.

Lemma MapsTo_node_iff {elt} l x (e:elt) r h y v :
  MapsTo y v (Node h l x e r) <->
   MapsTo y v l \/ (y == x /\ v = e) \/ MapsTo y v r.
Proof.
 intuition_in. subst; auto.
Qed.

(** Results about [Above] and [Below] *)

Lemma above_alt {elt} (m:t elt) x :
  x >> m <-> forall y, y ∈ m -> y < x.
Proof.
 split.
 - induction 1; intuition_in; F.order.
 - induction m; constructor; auto.
Qed.

Global Instance Above_m {elt} :
  Proper (K.eq ==> Eqdom ==> iff) (@Above elt).
Proof.
 intros x x' Hx m m' Hm. rewrite !above_alt.
 split; intros H y.
 - rewrite <- Hx, <- (Hm y). auto.
 - rewrite Hx, (Hm y). auto.
Qed.

Lemma below_alt {elt} (m:t elt) x :
  x << m <-> forall y, y ∈ m -> x < y.
Proof.
 split.
 - induction 1; intuition_in; F.order.
 - induction m; constructor; auto.
Qed.

Global Instance Below_m {elt} :
  Proper (K.eq ==> Eqdom ==> iff) (@Below elt).
Proof.
 intros x x' Hx m m' Hm. rewrite !below_alt.
 split; intros H y.
 - rewrite <- Hx, <- (Hm y). auto.
 - rewrite Hx, (Hm y). auto.
Qed.

Lemma AboveLt {elt} (m:t elt) x y : x >> m -> y ∈ m -> y < x.
Proof.
 rewrite above_alt; intuition.
Qed.

Lemma BelowGt {elt} (m:t elt) x y : x << m -> y ∈ m -> x < y.
Proof.
 rewrite below_alt; intuition.
Qed.

Lemma Above_not_In {elt} (m:t elt) x : x >> m -> ~ x ∈ m.
Proof.
 induction 1; intuition_in; F.order.
Qed.

Lemma Below_not_In {elt} (m:t elt) x : x << m -> ~ x ∈ m.
Proof.
 induction 1; intuition_in; F.order.
Qed.

Lemma Above_trans {elt} (m:t elt) x y : x < y -> x >> m -> y >> m.
Proof.
 induction 2; constructor; trivial; F.order.
Qed.

Lemma Below_trans {elt} (m:t elt) x y : y < x -> x << m -> y << m.
Proof.
 induction 2; constructor; trivial; F.order.
Qed.

Local Hint Resolve
 AboveLt Above_not_In Above_trans
 BelowGt Below_not_In Below_trans.

(** Helper tactic concerning order of elements. *)

Ltac order := match goal with
 | U: _ >> ?m, V: _ ∈ ?m |- _ =>
   generalize (AboveLt U V); clear U; order
 | U: _ << ?m, V: _ ∈ ?m |- _ =>
   generalize (BelowGt U V); clear U; order
 | U: _ >> ?m, V: MapsTo _ _ ?m |- _ =>
   generalize (AboveLt U (MapsTo_In V)); clear U; order
 | U: _ << ?m, V: MapsTo _ _ ?m |- _ =>
   generalize (BelowGt U (MapsTo_In V)); clear U; order
 | _ => F.order
end.

Lemma between {elt} (m m':t elt) x :
  x >> m -> x << m' -> m <<< m'.
Proof.
 intros H H' y y' Hy Hy'. order.
Qed.

Lemma apart_node_l {elt} h l x v r (m:t elt) :
  (Node h l x v r) <<< m <-> l <<< m /\ x << m /\ r <<< m.
Proof.
 unfold "<<<". setoid_rewrite In_node_iff. rewrite below_alt.
 firstorder. setoid_replace x1 with x; firstorder.
Qed.

Lemma apart_node_r {elt} h l x v r (m:t elt) :
  m <<< (Node h l x v r) <-> m <<< l /\ x >> m /\ m <<< r.
Proof.
 unfold "<<<". setoid_rewrite In_node_iff. rewrite above_alt.
 firstorder. setoid_replace x2 with x; firstorder.
Qed.


(** Bst is decidable *)

Instance Bst_Ok {elt} (m : t elt) (B : Bst m) : Ok m := B.

Fixpoint above {elt} x (m : t elt) :=
 match m with
  | Leaf _ => true
  | Node _ l y _ r =>
     match K.compare x y with
      | Gt => above x l && above x r
      | _ => false
     end
 end.

Fixpoint below {elt} x (m : t elt) :=
 match m with
  | Leaf _ => true
  | Node _ l y _ r =>
     match K.compare x y with
      | Lt => below x l && below x r
      | _ => false
     end
 end.

Fixpoint isok {elt} (m : t elt) :=
 match m with
  | Leaf _ => true
  | Node _  l x _ r => isok l && isok r && above x l && below x r
 end.

Lemma above_iff {elt} x (m:t elt) :
  x >> m <-> above x m = true.
Proof.
 induction m as [|c l IHl y v r IHr]; simpl.
 - intuition.
 - case K.compare_spec.
   + split; intros; try easy. inv Above. order.
   + split; intros; try easy. inv Above. order.
   + rewrite andb_true_iff, <- IHl, <- IHr. clear IHl IHr.
     intuition; inv Above; auto.
Qed.

Lemma below_iff {elt} x (m:t elt) :
  x << m <-> below x m = true.
Proof.
 induction m as [|c l IHl y v r IHr]; simpl.
 - intuition.
 - case K.compare_spec.
   + split; intros; try easy. inv Below. order.
   + rewrite !andb_true_iff, <-IHl, <-IHr. clear IHl IHr.
     intuition; inv Below; auto.
   + split; intros; try easy. inv Below. order.
Qed.

Lemma isok_iff {elt} (m:t elt) : Ok m <-> isok m = true.
Proof.
 induction m as [|c l IHl y v r IHr]; simpl.
 - intuition_in.
 - rewrite !andb_true_iff, <- IHl, <-IHr, <- below_iff, <- above_iff.
   intuition; inv (@Ok elt); auto.
Qed.

Lemma isok_spec {elt} (m:t elt) : reflect (Ok m) (isok m).
Proof.
 apply iff_reflect, isok_iff.
Qed.

Instance isok_Ok {elt} (m:t elt) : isok m = true -> Ok m | 10.
Proof. apply isok_iff. Qed.

Section Elt.
Variable elt:Type.
Implicit Types m r : t elt.

(** * Membership *)

Lemma find_1 m x e `{!Ok m} : MapsTo x e m -> find x m = Some e.
Proof.
 functional induction (find x m); cleanf;
  intros; inv Ok; intuition_in; order.
Qed.

Lemma find_2 m x e : find x m = Some e -> MapsTo x e m.
Proof.
 functional induction (find x m); cleanf; subst; intros; auto.
 - discriminate.
 - injection H as ->. auto.
Qed.

Lemma find_spec m x e `{!Ok m} :
 find x m = Some e <-> MapsTo x e m.
Proof.
 split; auto using find_1, find_2.
Qed.

Lemma find_in m x : find x m <> None -> x ∈ m.
Proof.
 destruct (find x m) eqn:F; intros H.
 - apply MapsTo_In with e. now apply find_2.
 - now elim H.
Qed.

Lemma in_find m x `{!Ok m} : x ∈ m -> find x m <> None.
Proof.
 intros IN.
 destruct (In_MapsTo IN) as (d,Hd).
 now rewrite (find_1 Hd).
Qed.

Lemma find_in_iff m x `{!Ok m} :
 find x m <> None <-> x ∈ m.
Proof.
 split; auto using find_in, in_find.
Qed.

Lemma not_find_iff m x `{!Ok m} :
 find x m = None <-> ~ x ∈ m.
Proof.
 rewrite <- find_in_iff; trivial.
 destruct (find x m); split; try easy. now destruct 1.
Qed.

Lemma eq_option_alt (o o':option elt) :
 o=o' <-> (forall e, o=Some e <-> o'=Some e).
Proof.
split; intros.
- now subst.
- destruct o, o'; rewrite ?H; auto. symmetry; now apply H.
Qed.

Lemma find_mapsto_equiv m m' x `{!Ok m, !Ok m'} :
 find x m = find x m' <->
  (forall d, MapsTo x d m <-> MapsTo x d m').
Proof.
 rewrite eq_option_alt.
 split; intros H d. now rewrite <- 2 find_spec. now rewrite 2 find_spec.
Qed.

Lemma find_in_equiv m m' x `{!Ok m, !Ok m'} :
 find x m = find x m' ->
  (x ∈ m <-> x ∈ m').
Proof.
 intros E. split; intros; apply find_in; [ rewrite <- E | rewrite E ];
  apply in_find; auto.
Qed.

Lemma find_compat m x x' `{!Ok m} : x == x' -> find x m = find x' m.
Proof.
 intros E.
 destruct (find x' m) eqn:H.
 - apply find_1; trivial. rewrite E. now apply find_2.
 - rewrite not_find_iff in *; trivial. now rewrite E.
Qed.

Lemma mem_spec m x `{!Ok m} : mem x m = true <-> x ∈ m.
Proof.
 functional induction (mem x m); auto; intros; cleanf;
  inv Ok; intuition_in; try discriminate; order.
Qed.

(** * Empty map *)

Global Instance empty_ok : Ok (empty elt).
Proof.
 constructor.
Qed.

Lemma empty_spec x : find x (empty elt) = None.
Proof.
 reflexivity.
Qed.

(** * Emptyness test *)

Lemma is_empty_spec m : is_empty m = true <-> forall x, find x m = None.
Proof.
 destruct m as [|h r x e l]; simpl; split; try easy.
 intros H. specialize (H x). now rewrite F.compare_refl in H.
Qed.

(** * Elements *)

Notation eqk := (O.eqk (elt:= elt)).
Notation eqke := (O.eqke (elt:= elt)).
Notation ltk := (O.ltk (elt:= elt)).

Ltac red_eqke :=
  match goal with
  | |- context [ eqke (?x,?e) (?y,?e')] =>
    change (eqke (x,e) (y,e')) with (x==y /\ e=e')
  | H : context [ eqke (?x,?e) (?y,?e')] |- _ =>
    change (eqke (x,e) (y,e')) with (x==y /\ e=e') in H
  end.

Lemma bindings_aux_mapsto m acc x e :
 InA eqke (x,e) (bindings_aux acc m) <->
 MapsTo x e m \/ InA eqke (x,e) acc.
Proof.
 revert acc.
 induction m as [ | h l Hl y e' r Hr ]; intros acc; simpl; auto.
 - intuition_in.
 - rewrite Hl, InA_cons, Hr. red_eqke. intuition_in. subst; auto.
Qed.

Lemma bindings_mapsto m x e :
 InA eqke (x,e) (bindings m) <-> MapsTo x e m.
Proof.
 unfold bindings. rewrite bindings_aux_mapsto. rewrite InA_nil. intuition.
Qed.

Lemma bindings_in m x : L.PX.In x (bindings m) <-> x ∈ m.
Proof.
 unfold L.PX.In.
 rewrite In_alt'.
 split; intros (y,H); exists y.
 - now rewrite <- bindings_mapsto.
 - unfold L.PX.MapsTo; now rewrite bindings_mapsto.
Qed.

Lemma bindings_aux_sort m acc `{!Ok m} :
 sort ltk acc ->
 (forall x e y, InA eqke (x,e) acc -> y ∈ m -> y < x) ->
 sort ltk (bindings_aux acc m).
Proof.
 revert acc.
 induction m as [ | h l Hl y e r Hr ]; intros acc; simpl; intuition.
 inv Ok.
 apply Hl; auto.
 - constructor.
   + apply Hr; eauto.
   + clear Hl Hr.
     apply InA_InfA with (eqA:=eqke); auto with *.
     intros (y',e') Hy'.
     apply bindings_aux_mapsto in Hy'. compute. intuition; eauto.
 - clear Hl Hr. intros x e' y' Hx Hy'.
   inversion_clear Hx as [? ? Hx'|? ? Hx'].
   + compute in Hx'. destruct Hx'; simpl in *. order.
   + apply bindings_aux_mapsto in Hx'. intuition eauto.
Qed.

Lemma bindings_sort m `{!Ok m} : sort ltk (bindings m).
Proof.
 unfold bindings; apply bindings_aux_sort; auto. inversion 1.
Qed.
Hint Resolve bindings_sort.

Lemma bindings_nodup m `{!Ok m} : NoDupA eqk (bindings m).
Proof.
 intros; apply O.Sort_NoDupA; auto.
Qed.

Lemma bindings_aux_cardinal m acc :
 length acc + cardinal m = length (bindings_aux acc m).
Proof.
 revert acc. induction m; simpl; intuition.
 rewrite <- IHm1; simpl.
 rewrite <- IHm2. rewrite Nat.add_succ_r, <- Nat.add_assoc.
 f_equal. f_equal. apply Nat.add_comm.
Qed.

Lemma bindings_cardinal m : cardinal m = length (bindings m).
Proof.
 exact (bindings_aux_cardinal m nil).
Qed.

Lemma bindings_app :
 forall (s:t elt) acc, bindings_aux acc s = bindings s ++ acc.
Proof.
 induction s; simpl; intros; auto.
 rewrite IHs1, IHs2.
 unfold bindings; simpl.
 rewrite 2 IHs1, IHs2, !app_nil_r, !app_ass; auto.
Qed.

Lemma bindings_node_acc (t1 t2:t elt) x e z acc :
 bindings (Node z t1 x e t2) ++ acc =
 bindings t1 ++ (x,e) :: bindings t2 ++ acc.
Proof.
 unfold bindings; simpl; intros.
 rewrite !bindings_app, !app_nil_r, !app_ass; auto.
Qed.

Lemma bindings_node (t1 t2:t elt) x e z :
 bindings (Node z t1 x e t2) =
 bindings t1 ++ (x,e) :: bindings t2.
Proof.
 rewrite <- (app_nil_r (bindings _)), bindings_node_acc.
 now rewrite app_nil_r.
Qed.

Lemma rev_bindings_aux_rev m acc :
 rev_bindings_aux acc m = rev (bindings m) ++ acc.
Proof.
 revert acc. induction m; simpl; intros; auto.
 rewrite IHm2, IHm1, bindings_node, !rev_app_distr. simpl.
 now rewrite <- !app_assoc.
Qed.

Lemma rev_bindings_rev m : rev_bindings m = rev (bindings m).
Proof.
 unfold rev_bindings. rewrite rev_bindings_aux_rev. apply app_nil_r.
Qed.

Lemma in_bindings k v (m:t elt) : List.In (k,v) (bindings m) -> In k m.
Proof.
 intros IN. apply In_alt'; exists v.
 apply bindings_mapsto, In_InA; eauto with *.
Qed.

Lemma in_bindings_uniq k k' v v' (m:t elt) `{!Ok m}:
 List.In (k,v) (bindings m) ->
 List.In (k',v') (bindings m) ->
 K.eq k k' -> k = k' /\ v = v'.
Proof.
 induction m as [|c l IHl x e r IHr].
 - now cbn.
 - rewrite !bindings_node, !in_app_iff. simpl.
   inv Ok; change Bst with Ok in *.
   intros [INl|[[= <- <-]|INl]] [INr|[[= <- <-]|INr]] E; eauto;
   try apply in_bindings in INl; try apply in_bindings in INr; order.
Qed.

(** * Fold *)

Definition fold' {A} (f : key -> elt -> A -> A) m :=
  L.fold f (bindings m).

Lemma fold_equiv_aux {A} m (f : key -> elt -> A -> A) (a : A) acc :
 L.fold f (bindings_aux acc m) a = L.fold f acc (fold f m a).
Proof.
 revert a acc.
 induction m; simpl; trivial.
 intros. rewrite IHm1. simpl. apply IHm2.
Qed.

Lemma fold_equiv {A} m (f : key -> elt -> A -> A) (a : A) :
 fold f m a = fold' f m a.
Proof.
 unfold fold', bindings. now rewrite fold_equiv_aux.
Qed.

Lemma fold_spec m `{!Ok m} {A} (i:A)(f : key -> elt -> A -> A) :
 fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
Proof.
 rewrite fold_equiv. unfold fold'. now rewrite L.fold_spec.
Qed.

(** * Comparison *)

(** [flatten_e e] returns the list of bindings of the enumeration [e]
    i.e. the list of bindings actually compared *)

Fixpoint flatten_e (e : enumeration elt) : list (key*elt) := match e with
  | End _ => nil
  | More x e t r => (x,e) :: bindings t ++ flatten_e r
 end.

Lemma flatten_e_bindings :
 forall (l:t elt) r x d z e,
 bindings l ++ flatten_e (More x d r e) =
 bindings (Node z l x d r) ++ flatten_e e.
Proof.
 intros. now rewrite bindings_node, <- app_assoc.
Qed.

Lemma cons_1 : forall (s:t elt) e,
  flatten_e (cons s e) = bindings s ++ flatten_e e.
Proof.
  induction s; auto; intros.
  simpl flatten_e; rewrite IHs1; apply flatten_e_bindings; auto.
Qed.

(** Proof of correction for the comparison *)

Variable cmp : elt->elt->bool.

Definition IfEq b l1 l2 := L.equal cmp l1 l2 = b.

Lemma cons_IfEq : forall b x1 x2 d1 d2 l1 l2,
  x1 == x2 -> cmp d1 d2 = true ->
  IfEq b l1 l2 ->
    IfEq b ((x1,d1)::l1) ((x2,d2)::l2).
Proof.
 unfold IfEq; destruct b; simpl; intros; case K.compare_spec; simpl;
  try rewrite H0; auto; order.
Qed.

Lemma equal_end_IfEq : forall e2,
  IfEq (equal_end e2) nil (flatten_e e2).
Proof.
 destruct e2; red; auto.
Qed.

Lemma equal_more_IfEq :
 forall x1 d1 (cont:enumeration elt -> bool) x2 d2 r2 e2 l,
  IfEq (cont (cons r2 e2)) l (bindings r2 ++ flatten_e e2) ->
    IfEq (equal_more cmp x1 d1 cont (More x2 d2 r2 e2)) ((x1,d1)::l)
       (flatten_e (More x2 d2 r2 e2)).
Proof.
 unfold IfEq; simpl; intros; destruct K.compare; simpl; auto.
 rewrite <-andb_lazy_alt; f_equal; auto.
Qed.

Lemma equal_cont_IfEq : forall m1 cont e2 l,
  (forall e, IfEq (cont e) l (flatten_e e)) ->
  IfEq (equal_cont cmp m1 cont e2) (bindings m1 ++ l) (flatten_e e2).
Proof.
 induction m1 as [|h1 l1 Hl1 x1 d1 r1 Hr1]; intros; auto.
 rewrite bindings_node_acc; simpl.
 apply Hl1; auto.
 clear e2; intros [|x2 d2 r2 e2].
 simpl; red; auto.
 apply equal_more_IfEq.
 rewrite <- cons_1; auto.
Qed.

Lemma equal_IfEq : forall (m1 m2:t elt),
  IfEq (equal cmp m1 m2) (bindings m1) (bindings m2).
Proof.
 intros; unfold equal.
 rewrite <- (app_nil_r (bindings m1)).
 replace (bindings m2) with (flatten_e (cons m2 (End _)))
  by (rewrite cons_1; simpl; rewrite app_nil_r; auto).
 apply equal_cont_IfEq.
 intros.
 apply equal_end_IfEq; auto.
Qed.

Definition Equivb (m m' : t elt) :=
  Eqdom m m' /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

Lemma Equivb_bindings m m' :
 Equivb m m' <-> L.Equivb cmp (bindings m) (bindings m').
Proof.
unfold Equivb, L.Equivb; split; split; try red; intros.
do 2 rewrite bindings_in; firstorder.
destruct H.
apply (H2 k); rewrite <- bindings_mapsto; auto.
do 2 rewrite <- bindings_in; firstorder.
destruct H.
apply (H2 k); unfold L.PX.MapsTo; rewrite bindings_mapsto; auto.
Qed.

Lemma equal_Equivb m m' `{!Ok m, !Ok m'} :
  equal cmp m m' = true <-> Equivb m m'.
Proof.
 rewrite Equivb_bindings, <- equal_IfEq.
 split; [apply L.equal_2 | apply L.equal_1]; auto.
Qed.

End Elt.

Section Map.
Variable elt elt' : Type.
Variable f : elt -> elt'.

Lemma map_spec m x :
 find x (map f m) = option_map f (find x m).
Proof.
induction m; simpl; trivial. case K.compare_spec; auto.
Qed.

Lemma map_in m x : x ∈ (map f m) <-> x ∈ m.
Proof.
induction m; simpl; intuition_in.
Qed.

Global Instance map_ok m `{!Ok m} : Ok (map f m).
Proof.
induction m; simpl; auto.
intros; inv Ok; constructor; change Bst with Ok in *; auto with *.
- apply above_alt. intro. rewrite map_in. intros. order.
- apply below_alt. intro. rewrite map_in. intros. order.
Qed.

End Map.
Section Mapi.
Variable elt elt' : Type.
Variable f : key -> elt -> elt'.

Lemma mapi_spec m x :
  exists y:key,
    K.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).
Proof.
  induction m; simpl.
  - now exists x.
  - case K.compare_spec; simpl; auto. intros. now exists t0.
Qed.

Lemma mapi_in m x : x ∈ (mapi f m) <-> x ∈ m.
Proof.
induction m; simpl; intuition_in.
Qed.

Global Instance mapi_ok m `{!Ok m} : Ok (mapi f m).
Proof.
induction m; simpl; auto.
intros; inv Ok; constructor; change Bst with Ok; auto with *.
- apply above_alt. intro. rewrite mapi_in. intros. order.
- apply below_alt. intro. rewrite mapi_in. intros. order.
Qed.

End Mapi.

End Props.
