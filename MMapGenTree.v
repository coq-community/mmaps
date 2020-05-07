(** * MSetGenTree : maps via generic trees

    This module factorizes common parts in implementations
    of finite maps as AVL trees and as Red-Black trees. The nodes
    of the trees defined here include an generic information
    parameter, that will be the height in AVL trees and the color
    in Red-Black trees. Without more details here about these
    information parameters, trees here are not known to be
    well-balanced, but simply binary-search-trees.

    The operations we could define and prove correct here are the
    one that do not build non-empty trees, but only analyze them :

     - empty is_empty
     - find mem
     - equal
     - fold cardinal bindings
*)

Require Import Bool PeanoNat BinInt FunInd MMapInterface MMapList.
Require Import Orders OrdersFacts OrdersLists.
Local Open Scope list_scope.
Local Open Scope lazy_bool_scope.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

(* For nicer extraction, we create induction principles
   only when needed *)
Local Unset Elimination Schemes.

Module Type InfoTyp.
 Parameter t : Set.
End InfoTyp.

(** * Ops : the pure functions *)

Module Type Ops (X:OrderedType)(Info:InfoTyp).

Definition key := X.t.
Hint Transparent key.

Section Elt.

Variable elt : Type.

(** * Trees *)

Inductive tree  : Type :=
| Leaf : tree
| Node : Info.t -> tree -> X.t -> elt -> tree -> tree.

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
   match X.compare x k with
     | Lt => mem x l
     | Eq => true
     | Gt => mem x r
   end
 end.

Fixpoint find x m : option elt :=
  match m with
    |  Leaf => None
    |  Node _ l y v r =>
       match X.compare x y with
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
     match X.compare x1 x2 with
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
End Ops.

(** * Props : correctness proofs of these generic operations *)

Module Type Props (X:OrderedType)(Info:InfoTyp)(Import M:Ops X Info).

Section Invariants.
Variable elt : Type.

(** ** Occurrence in a tree *)

Inductive MapsTo (x : key)(e : elt) : t elt -> Prop :=
  | MapsRoot : forall l r h y,
      X.eq x y -> MapsTo x e (Node h l y e r)
  | MapsLeft : forall l r h y e',
      MapsTo x e l -> MapsTo x e (Node h l y e' r)
  | MapsRight : forall l r h y e',
      MapsTo x e r -> MapsTo x e (Node h l y e' r).

Inductive In (x : key) : t elt -> Prop :=
  | InRoot : forall l r h y e,
      X.eq x y -> In x (Node h l y e r)
  | InLeft : forall l r h y e',
      In x l -> In x (Node h l y e' r)
  | InRight : forall l r h y e',
      In x r -> In x (Node h l y e' r).

Definition In0 k m := exists e:elt, MapsTo k e m.

(** ** Binary search trees *)

(** [Above x m] : [x] is strictly greater than any key in [m].
    [Below x m] : [x] is strictly smaller than any key in [m]. *)

Inductive Above (x:key) : t elt -> Prop :=
 | AbLeaf : Above x (Leaf _)
 | AbNode l r h y e : Above x l -> X.lt y x -> Above x r ->
   Above x (Node h l y e r).

Inductive Below (x:key) : t elt -> Prop :=
 | BeLeaf : Below x (Leaf _)
 | BeNode l r h y e : Below x l -> X.lt x y -> Below x r ->
   Below x (Node h l y e r).

Definition Apart (m1 m2 : t elt) : Prop :=
  forall x1 x2, In x1 m1 -> In x2 m2 -> X.lt x1 x2.

(** Alternative statements, equivalent with [LtTree] and [GtTree] *)

Definition lt_tree x m := forall y, In y m -> X.lt y x.
Definition gt_tree x m := forall y, In y m -> X.lt x y.

(** [Bst t] : [t] is a binary search tree *)

Inductive Bst : t elt -> Prop :=
  | BSLeaf : Bst (Leaf _)
  | BSNode : forall h x e l r, Bst l -> Bst r ->
     Above x l -> Below x r -> Bst (Node h l x e r).

End Invariants.

Module MX := OrderedTypeFacts X.
Module PX := KeyOrderedType X.
Module L := MMapList.Raw X.

Local Infix "∈" := In (at level 70).
Local Infix "==" := X.eq (at level 70).
Local Infix "<" := X.lt (at level 70).
Local Infix "<<" := Below (at level 70).
Local Infix ">>" := Above (at level 70).
Local Infix "<<<" := Apart (at level 70).

Scheme tree_ind := Induction for tree Sort Prop.
Scheme Bst_ind := Induction for Bst Sort Prop.
Scheme MapsTo_ind := Induction for MapsTo Sort Prop.
Scheme In_ind := Induction for In Sort Prop.
Scheme Above_ind := Induction for Above Sort Prop.
Scheme Below_ind := Induction for Below Sort Prop.

Functional Scheme mem_ind := Induction for mem Sort Prop.
Functional Scheme find_ind := Induction for find Sort Prop.

(** * Automation and dedicated tactics. *)

Local Hint Constructors tree MapsTo In Bst Above Below.
Local Hint Unfold lt_tree gt_tree Apart.
Local Hint Immediate MX.eq_sym.
Local Hint Resolve MX.eq_refl MX.eq_trans MX.lt_trans.

Tactic Notation "factornode" ident(s) :=
 try clear s;
 match goal with
   | |- context [Node ?h ?l ?x ?e ?r] =>
       set (s:=Node h l x e r) in *; clearbody s; clear l x e r h
   | _ : context [Node ?h ?l ?x ?e ?r] |- _ =>
       set (s:=Node h l x e r) in *; clearbody s; clear l x e r h
 end.

(** A tactic for cleaning hypothesis after use of functional induction. *)

Ltac cleanf :=
 match goal with
  | H : X.compare _ _ = Eq |- _ =>
    rewrite ?H; apply MX.compare_eq in H; cleanf
  | H : X.compare _ _ = Lt |- _ =>
    rewrite ?H; apply MX.compare_lt_iff in H; cleanf
  | H : X.compare _ _ = Gt |- _ =>
    rewrite ?H; apply MX.compare_gt_iff in H; cleanf
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

(** * Basic results about [MapsTo], [In], [lt_tree], [gt_tree], [height] *)

(** Facts about [MapsTo] and [In]. *)

Lemma MapsTo_In {elt} k (e:elt) m : MapsTo k e m -> k ∈ m.
Proof.
 induction 1; auto.
Qed.
Local Hint Resolve MapsTo_In.

Lemma In_MapsTo {elt} k m : k ∈ m -> exists (e:elt), MapsTo k e m.
Proof.
 induction 1; try destruct IHIn as (e,He); exists e; auto.
Qed.

Lemma In_alt {elt} k (m:t elt) : In0 k m <-> k ∈ m.
Proof.
 split.
 intros (e,H); eauto.
 unfold In0; apply In_MapsTo; auto.
Qed.

Lemma MapsTo_1 {elt} m x y (e:elt) :
  x == y -> MapsTo x e m -> MapsTo y e m.
Proof.
 induction m; simpl; intuition_in; eauto.
Qed.
Hint Immediate MapsTo_1.

Instance MapsTo_compat {elt} :
  Proper (X.eq==>Logic.eq==>Logic.eq==>iff) (@MapsTo elt).
Proof.
 intros x x' Hx e e' He m m' Hm. subst.
 split; now apply MapsTo_1.
Qed.

Instance In_compat {elt} :
  Proper (X.eq==>Logic.eq==>iff) (@In elt).
Proof.
 intros x x' H m m' <-.
 induction m; simpl; intuition_in; eauto.
Qed.

Lemma In_node_iff {elt} l x (e:elt) r h y :
  y ∈ (Node h l x e r) <-> y ∈ l \/ y == x \/ y ∈ r.
Proof.
 intuition_in.
Qed.

(** Results about [Above] and [Below] *)

Lemma above {elt} (m:t elt) x :
  x >> m <-> forall y, y ∈ m -> y < x.
Proof.
 split.
 - induction 1; intuition_in; MX.order.
 - induction m; constructor; auto.
Qed.

Lemma below {elt} (m:t elt) x :
  x << m <-> forall y, y ∈ m -> x < y.
Proof.
 split.
 - induction 1; intuition_in; MX.order.
 - induction m; constructor; auto.
Qed.

Lemma AboveLt {elt} (m:t elt) x y : x >> m -> y ∈ m -> y < x.
Proof.
 rewrite above; intuition.
Qed.

Lemma BelowGt {elt} (m:t elt) x y : x << m -> y ∈ m -> x < y.
Proof.
 rewrite below; intuition.
Qed.

Lemma Above_not_In {elt} (m:t elt) x : x >> m -> ~ x ∈ m.
Proof.
 induction 1; intuition_in; MX.order.
Qed.

Lemma Below_not_In {elt} (m:t elt) x : x << m -> ~ x ∈ m.
Proof.
 induction 1; intuition_in; MX.order.
Qed.

Lemma Above_trans {elt} (m:t elt) x y : x < y -> x >> m -> y >> m.
Proof.
 induction 2; constructor; trivial; MX.order.
Qed.

Lemma Below_trans {elt} (m:t elt) x y : y < x -> x << m -> y << m.
Proof.
 induction 2; constructor; trivial; MX.order.
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
 | _ => MX.order
end.

Lemma between {elt} (m m':t elt) x :
  x >> m -> x << m' -> m <<< m'.
Proof.
 intros H H' y y' Hy Hy'. order.
Qed.

Section Elt.
Variable elt:Type.
Implicit Types m r : t elt.

(** * Membership *)

Lemma find_1 m x e : Bst m -> MapsTo x e m -> find x m = Some e.
Proof.
 functional induction (find x m); cleanf;
  intros; inv Bst; intuition_in; order.
Qed.

Lemma find_2 m x e : find x m = Some e -> MapsTo x e m.
Proof.
 functional induction (find x m); cleanf; subst; intros; auto.
 - discriminate.
 - injection H as ->. auto.
Qed.

Lemma find_spec m x e : Bst m ->
 (find x m = Some e <-> MapsTo x e m).
Proof.
 split; auto using find_1, find_2.
Qed.

Lemma find_in m x : find x m <> None -> x ∈ m.
Proof.
 destruct (find x m) eqn:F; intros H.
 - apply MapsTo_In with e. now apply find_2.
 - now elim H.
Qed.

Lemma in_find m x : Bst m -> x ∈ m -> find x m <> None.
Proof.
 intros H H'.
 destruct (In_MapsTo H') as (d,Hd).
 now rewrite (find_1 H Hd).
Qed.

Lemma find_in_iff m x : Bst m ->
 (find x m <> None <-> x ∈ m).
Proof.
 split; auto using find_in, in_find.
Qed.

Lemma not_find_iff m x : Bst m ->
 (find x m = None <-> ~ x ∈ m).
Proof.
 intros H. rewrite <- find_in_iff; trivial.
 destruct (find x m); split; try easy. now destruct 1.
Qed.

Lemma eq_option_alt (o o':option elt) :
 o=o' <-> (forall e, o=Some e <-> o'=Some e).
Proof.
split; intros.
- now subst.
- destruct o, o'; rewrite ?H; auto. symmetry; now apply H.
Qed.

Lemma find_mapsto_equiv : forall m m' x, Bst m -> Bst m' ->
 (find x m = find x m' <->
  (forall d, MapsTo x d m <-> MapsTo x d m')).
Proof.
 intros m m' x Hm Hm'. rewrite eq_option_alt.
 split; intros H d. now rewrite <- 2 find_spec. now rewrite 2 find_spec.
Qed.

Lemma find_in_equiv : forall m m' x, Bst m -> Bst m' ->
 find x m = find x m' ->
 (x ∈ m <-> x ∈ m').
Proof.
 split; intros; apply find_in; [ rewrite <- H1 | rewrite H1 ];
  apply in_find; auto.
Qed.

Lemma find_compat m x x' : Bst m -> X.eq x x' -> find x m = find x' m.
Proof.
  intros B E.
  destruct (find x' m) eqn:H.
  - apply find_1; trivial. rewrite E. now apply find_2.
  - rewrite not_find_iff in *; trivial. now rewrite E.
Qed.

Lemma mem_spec m x : Bst m -> mem x m = true <-> x ∈ m.
Proof.
 functional induction (mem x m); auto; intros; cleanf;
  inv Bst; intuition_in; try discriminate; order.
Qed.

(** * Empty map *)

Lemma empty_bst : Bst (empty elt).
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
 intros H. specialize (H x). now rewrite MX.compare_refl in H.
Qed.

(** * Elements *)

Notation eqk := (PX.eqk (elt:= elt)).
Notation eqke := (PX.eqke (elt:= elt)).
Notation ltk := (PX.ltk (elt:= elt)).

Lemma bindings_aux_mapsto : forall (s:t elt) acc x e,
 InA eqke (x,e) (bindings_aux acc s) <-> MapsTo x e s \/ InA eqke (x,e) acc.
Proof.
 induction s as [ | h l Hl x e r Hr ]; simpl; auto.
 intuition.
 inversion H0.
 intros.
 rewrite Hl.
 destruct (Hr acc x0 e0); clear Hl Hr.
 intuition; inversion_clear H3; intuition.
 compute in H0. destruct H0; simpl in *; subst; intuition.
Qed.

Lemma bindings_mapsto : forall (s:t elt) x e,
 InA eqke (x,e) (bindings s) <-> MapsTo x e s.
Proof.
 intros; generalize (bindings_aux_mapsto s nil x e); intuition.
 inversion_clear H0.
Qed.

Lemma bindings_in : forall (s:t elt) x, L.PX.In x (bindings s) <-> x ∈ s.
Proof.
 intros.
 unfold L.PX.In.
 rewrite <- In_alt; unfold In0.
 split; intros (y,H); exists y.
 - now rewrite <- bindings_mapsto.
 - unfold L.PX.MapsTo; now rewrite bindings_mapsto.
Qed.

Lemma bindings_aux_sort : forall (s:t elt) acc,
 Bst s -> sort ltk acc ->
 (forall x e y, InA eqke (x,e) acc -> y ∈ s -> y < x) ->
 sort ltk (bindings_aux acc s).
Proof.
 induction s as [ | h l Hl y e r Hr ]; simpl; intuition.
 inv Bst.
 apply Hl; auto.
 - constructor.
   + apply Hr; eauto.
   + clear Hl Hr.
     apply InA_InfA with (eqA:=eqke); auto with *.
     intros (y',e') Hy'.
     apply bindings_aux_mapsto in Hy'. compute. intuition; eauto.
 - clear Hl Hr. intros x e' y' Hx Hy'.
   inversion_clear Hx.
   + compute in H. destruct H; simpl in *. order.
   + apply bindings_aux_mapsto in H. intuition eauto.
Qed.

Lemma bindings_sort : forall s : t elt, Bst s -> sort ltk (bindings s).
Proof.
 intros; unfold bindings; apply bindings_aux_sort; auto.
 intros; inversion H0.
Qed.
Hint Resolve bindings_sort.

Lemma bindings_nodup : forall s : t elt, Bst s -> NoDupA eqk (bindings s).
Proof.
 intros; apply PX.Sort_NoDupA; auto.
Qed.

Lemma bindings_aux_cardinal m acc :
 (length acc + cardinal m)%nat = length (bindings_aux acc m).
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

Lemma bindings_node :
 forall (t1 t2:t elt) x e z l,
 bindings t1 ++ (x,e) :: bindings t2 ++ l =
 bindings (Node z t1 x e t2) ++ l.
Proof.
 unfold bindings; simpl; intros.
 rewrite !bindings_app, !app_nil_r, !app_ass; auto.
Qed.

(** * Fold *)

Definition fold' {A} (f : key -> elt -> A -> A)(s : t elt) :=
  L.fold f (bindings s).

Lemma fold_equiv_aux {A} (s : t elt) (f : key -> elt -> A -> A) (a : A) acc :
 L.fold f (bindings_aux acc s) a = L.fold f acc (fold f s a).
Proof.
 revert a acc.
 induction s; simpl; trivial.
 intros. rewrite IHs1. simpl. apply IHs2.
Qed.

Lemma fold_equiv {A} (s : t elt) (f : key -> elt -> A -> A) (a : A) :
 fold f s a = fold' f s a.
Proof.
 unfold fold', bindings. now rewrite fold_equiv_aux.
Qed.

Lemma fold_spec (s:t elt)(Hs:Bst s){A}(i:A)(f : key -> elt -> A -> A) :
 fold f s i = fold_left (fun a p => f (fst p) (snd p) a) (bindings s) i.
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
 intros; apply bindings_node.
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
  X.eq x1 x2 -> cmp d1 d2 = true ->
  IfEq b l1 l2 ->
    IfEq b ((x1,d1)::l1) ((x2,d2)::l2).
Proof.
 unfold IfEq; destruct b; simpl; intros; case X.compare_spec; simpl;
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
 unfold IfEq; simpl; intros; destruct X.compare; simpl; auto.
 rewrite <-andb_lazy_alt; f_equal; auto.
Qed.

Lemma equal_cont_IfEq : forall m1 cont e2 l,
  (forall e, IfEq (cont e) l (flatten_e e)) ->
  IfEq (equal_cont cmp m1 cont e2) (bindings m1 ++ l) (flatten_e e2).
Proof.
 induction m1 as [|h1 l1 Hl1 x1 d1 r1 Hr1]; intros; auto.
 rewrite <- bindings_node; simpl.
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

Definition Equivb m m' :=
  (forall k, In k m <-> In k m') /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

Lemma Equivb_bindings : forall s s',
 Equivb s s' <-> L.Equivb cmp (bindings s) (bindings s').
Proof.
unfold Equivb, L.Equivb; split; split; intros.
do 2 rewrite bindings_in; firstorder.
destruct H.
apply (H2 k); rewrite <- bindings_mapsto; auto.
do 2 rewrite <- bindings_in; firstorder.
destruct H.
apply (H2 k); unfold L.PX.MapsTo; rewrite bindings_mapsto; auto.
Qed.

Lemma equal_Equivb : forall (s s': t elt), Bst s -> Bst s' ->
  (equal cmp s s' = true <-> Equivb s s').
Proof.
 intros s s' B B'.
 rewrite Equivb_bindings, <- equal_IfEq.
 split; [apply L.equal_2|apply L.equal_1]; auto.
Qed.

End Elt.
End Props.
