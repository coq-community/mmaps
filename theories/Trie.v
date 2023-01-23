From Coq Require Import PArith OrdersEx.
From Coq Require List.
From MMaps Require Import Interface Comparisons.

(** * Extensional binary tries based on a canonical representation *)

(* Adapted from <https://www.cs.princeton.edu/~appel/papers/ptree.pdf> *)

(* Authors: Andrew W. Appel, Princeton University,
            Xavier Leroy, Collège de France and Inria.
            Andres Erbsen
   Copyright: Andrew W. Appel and Inria and Andres Erbsen.
   Original code licensed under BSD-3-Clause. *)

Definition option_bind {A B} (f : A -> option B) (o : option A) : option B :=
  match o with None => None | Some a => f a end.

(** Nonempty branches. Each constructor is of the form [NodeXYZ], where the
   bit [X] says whether there is a left subtree, [Y] whether there is a value
   at this node, and [Z] whether there is a right subtree. No [Node000] here! *)
Inductive branch (A : Type) : Type :=
| Node001:                  branch A -> branch A
| Node010:             A ->             branch A
| Node011:             A -> branch A -> branch A
| Node100: branch A ->                  branch A
| Node101: branch A ->      branch A -> branch A
| Node110: branch A -> A ->             branch A
| Node111: branch A -> A -> branch A -> branch A.
Arguments Node001 {A}. Arguments Node010 {A}. Arguments Node011 {A}.
Arguments Node100 {A}. Arguments Node101 {A}. Arguments Node110 {A}.
Arguments Node111 {A}.

Definition trie A := option (branch A).
Definition empty A : trie A := None.

(** Smart constructors and eliminators *)

Definition Node {A} (l : trie A) (o : option A) (r : trie A) : trie A :=
  match l,o,r with
  | None,    None,   None    => None
  | None,    None,   Some r' => Some (Node001 r')
  | None,    Some x, None    => Some (Node010 x)
  | None,    Some x, Some r' => Some (Node011 x r')
  | Some l', None,   None    => Some (Node100 l')
  | Some l', None,   Some r' => Some (Node101 l' r')
  | Some l', Some x, None    => Some (Node110 l' x)
  | Some l', Some x, Some r' => Some (Node111 l' x r')
  end.

Definition isBranch {A} (l : trie A) (o : option A) (r : trie A) :=
  match l, o, r with None, None, None => False | _, _, _ => True end.

Definition branch_case {A} (P : trie A -> Type) (f : forall l o r, isBranch l o r -> P (Node l o r)) (m : branch A) : P (Some m) :=
  match m with
  | Node001     r => f None     None     (Some r) I
  | Node010   x   => f None     (Some x) None     I
  | Node011   x r => f None     (Some x) (Some r) I
  | Node100 l     => f (Some l) None     None     I
  | Node101 l   r => f (Some l) None     (Some r) I
  | Node110 l x   => f (Some l) (Some x) None     I
  | Node111 l x r => f (Some l) (Some x) (Some r) I
  end.

Definition branch_map {A B} f : branch A -> B :=
  branch_case (fun _ => B) (fun l o r _ => f l o r).

Section Induction.
Context {A : Type} (P : trie A -> Type)
        (empty : P None)
        (node : forall l, P l -> forall o r, P r -> isBranch l o r -> P (Node l o r)).

Fixpoint trie_branch_ind' (m : branch A) : P (Some m) :=
  branch_case P ltac:(intros [] [] [] ?; apply node; auto) m.
Definition trie_branch_ind := Eval cbv [trie_branch_ind' branch_case] in trie_branch_ind'.

Definition trie_ind : forall m, P m := option_rect P trie_branch_ind empty.
End Induction.

Local Fixpoint get' {A} (p : positive) (m : branch A) : option A :=
  match p, m with
  | xH,   (Node010 x|Node011 x _|Node110 _ x|Node111 _ x _) => Some x
  | xO q, (Node100 m|Node101 m _|Node110 m _|Node111 m _ _) => get' q m
  | xI q, (Node001 m|Node011 _ m|Node101 _ m|Node111 _ _ m) => get' q m
  | _,_ => None
  end.

Definition get {A} p : trie A -> option A := option_bind (get' p).

Lemma get_empty {A} i : get i (empty A) = None.
Proof. trivial. Qed.

Lemma get_Node {A} i l (x : option A) r :
  get i (Node l x r) = match i with xI j => get j r | xO j => get j l | _ => x end.
Proof. case l, x, r; case i; trivial. Qed.

(** ** Extensionality property *)

Local Lemma get'_not_None {A} m : exists i, @get' A i m <> None.
Proof.
  induction m; try case IHm as [p H]; try case IHm1 as [p H];
    try ((exists xH + exists (xI p) + exists (xO p)); cbn; congruence).
Qed.

Lemma extensionality_empty {A} (m : trie A) (H : forall i, get i m = None) : m = None.
Proof. case m as [m|]; auto. case (get'_not_None m) as [i []]. apply H. Qed.

Lemma extensionality {A} : forall m1 m2, (forall i, @get A i m1 = get i m2) -> m1 = m2.
Proof.
  induction m1 using trie_ind; induction m2 using trie_ind; intros;
    eauto using eq_sym, extensionality_empty.
  f_equal; [apply IHm1_1| |apply IHm1_2]; try intros i;
    [>specialize (H1 (xO i)) | specialize (H1 xH) | specialize (H1 (xI i))];
    rewrite ?get_Node in H1; auto.
Qed.

(** Setters *)

Fixpoint singleton {A} (p : positive) (x : A) : branch A :=
  match p with
  | xH => Node010 x
  | xO q => Node100 (singleton q x)
  | xI q => Node001 (singleton q x)
  end.

Local Fixpoint set' {A} (p : positive) (x : A) (m : branch A) : branch A :=
  match p, m with
  | xH, Node001 r => Node011 x r
  | xH, Node010 _ => Node010 x
  | xH, Node011 _ r => Node011 x r
  | xH, Node100 l => Node110 l x
  | xH, Node101 l r => Node111 l x r
  | xH, Node110 l _ => Node110 l x
  | xH, Node111 l _ r => Node111 l x r
  | xO q, Node001 r => Node101 (singleton q x) r
  | xO q, Node010 y => Node110 (singleton q x) y
  | xO q, Node011 y r => Node111 (singleton q x) y r
  | xO q, Node100 l => Node100 (set' q x l)
  | xO q, Node101 l r => Node101 (set' q x l) r
  | xO q, Node110 l y => Node110 (set' q x l) y
  | xO q, Node111 l y r => Node111 (set' q x l) y r
  | xI q, Node001 r => Node001 (set' q x r)
  | xI q, Node010 y => Node011 y (singleton q x)
  | xI q, Node011 y r => Node011 y (set' q x r)
  | xI q, Node100 l => Node101 l (singleton q x)
  | xI q, Node101 l r => Node101 l (set' q x r)
  | xI q, Node110 l y => Node111 l y (singleton q x)
  | xI q, Node111 l y r => Node111 l y (set' q x r)
  end.

Definition set {A} (p : positive) (x : A) (m : trie A) : trie A :=
  Some match m with Some m' => set' p x m' | None => singleton p x end.

Lemma set_Node {A} (v : A) l o r p :
  set p v (Node l o r) =
    match p with
    | xH => Node l (Some v) r
    | xO q => Node (set q v l) o r
    | xI q => Node l o (set q v r)
    end.
Proof. case l, o, r, p; trivial. Qed.

Lemma set_None {A} x p : @set A p x None = set p x (Node None None None).
Proof. trivial. Qed.

Lemma get_set_same {A} : forall i x (m : trie A), get i (set i x m) = Some x.
Proof.
  induction i; induction m using trie_ind; intros;
    rewrite ?set_None, ?set_Node, ?get_Node; auto.
Qed.

Lemma get_set_diff {A} : forall i j x (m : trie A),
  i <> j -> get i (set j x m) = get i m.
Proof.
  induction i, j; induction m using trie_ind; intros;
    rewrite ?set_None, ?set_Node, ?get_Node; auto;
    try (apply IHi); congruence.
Qed.

Local Fixpoint remove'' {A} (p : positive) (m : branch A) : trie A :=
  match p with
  | xH => branch_map (fun l o r => Node l None r) m
  | xO p => branch_map (fun l o r => Node (option_bind (remove'' p) l) o r) m
  | xI p => branch_map (fun l o r => Node l o (option_bind (remove'' p) r)) m
  end.
Local Definition remove' {A} := Eval cbv [remove'' branch_map branch_case option_bind Node ] in @remove'' A.

Definition remove {A} (p : positive) : trie A -> trie A := option_bind (remove' p).

Lemma remove_Node {A} l o r p :
  @remove A p (Node l o r) =
    match p with
    | xH => Node l None r
    | xO q => Node (remove q l) o r
    | xI q => Node l o (remove q r)
    end.
Proof. case l, o, r, p; trivial. Qed.

Lemma get_remove_same {A} i (m: trie A) : get i (remove i m) = None.
Proof.
  revert i; induction m using trie_ind; case i as [];
    rewrite ?remove_Node, ?IHm1, ?IHm2, ?get_Node; trivial.
Qed.

Lemma get_remove_diff {A} i j (m : trie A) :
  i <> j -> get i (remove j m) = get i m.
Proof.
  revert i j; induction m using trie_ind; trivial; case i as [], j as []; intros;
    rewrite ?remove_Node, ?get_Node; try (apply IHm1||apply IHm2); try congruence.
Qed.

(** Bulk operations *)

Section MapFilter.
Context {A B : Type} (f : A -> option B).
Let Fixpoint map_filter'' (m : branch A) : trie B := branch_map (fun l o r =>
  Node (option_bind map_filter'' l) (option_bind f o) (option_bind map_filter'' r)) m.

Local Definition map_filter' :=
  Eval cbv [map_filter'' branch_map branch_case option_bind Node] in map_filter''.

Definition map_filter : trie A -> trie B := option_bind map_filter'.

Lemma map_filter_Node l o r :
  map_filter (Node l o r) = Node (map_filter l) (option_bind f o) (map_filter r).
Proof. case l, o, r; trivial. Qed.

Lemma get_map_filter m : forall i, get i (map_filter m) = option_bind f (get i m).
Proof.
  induction m using trie_ind; case i as [];
    rewrite ?map_filter_Node, ?get_Node, ?IHm1, ?IHm2; trivial.
Qed.
End MapFilter.

Section Combine.
Context {A B C : Type} (f : option A -> option B -> option C).

Local Notation combine'_l m := (map_filter (fun a => f (Some a) None) (Some m)).
Local Notation combine'_r m := (map_filter (fun b => f None (Some b)) (Some m)).

Let Fixpoint combine'' (m1 : branch A) (m2 : branch B) {struct m1} : trie C.
Proof. (* 49 cases *)
  case m1 as [ r1 | x1 | x1 r1 | l1 | l1 r1 | l1 x1 | l1 x1 r1 ];
  case m2 as [ r2 | x2 | x2 r2 | l2 | l2 r2 | l2 x2 | l2 x2 r2 ]; (apply Node;
   [ try (exact (combine'' l1 l2) || exact (combine'_l l1) || exact (combine'_r l2))
   | apply f; [ try exact (Some x1) | try exact (Some x2) ]
   | try (exact (combine'' r1 r2) || exact (combine'_l r1) || exact (combine'_r r2))
   ]; exact None).
Defined.
Local Definition combine' := Eval cbv [combine'' Node map_filter option_bind] in combine''.

Definition combine (m1 : trie A) (m2 : trie B) : trie C :=
  match m1, m2 with
  | None, None => None
  | None, Some m2 => combine'_r m2
  | Some m1, None => combine'_l m1
  | Some m1, Some m2 => combine' m1 m2
  end.

Context (f_None_None : f None None = None).

Lemma combine_Node_Node l1 o1 r1 l2 o2 r2 :
  combine (Node l1 o1 r1) (Node l2 o2 r2) = Node (combine l1 l2) (f o1 o2) (combine r1 r2).
Proof. case l1, o1, r1, l2, o2, r2; trivial; rewrite ?f_None_None; trivial. Qed.

Lemma get_combine : forall m1 m2 i, get i (combine m1 m2) = f (get i m1) (get i m2).
Proof.
  induction m1 using trie_ind; induction m2 using trie_ind; auto; case i as [];
  repeat (change (combine None) with (combine (Node None None None))
       || change (combine ?x None) with (combine x (Node None None None)));
  rewrite ?combine_Node_Node, ?get_Node, ?IHm2_1, ?IHm2_2, ?IHm1_1, ?IHm1_2; auto.
Qed.
End Combine.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Module TrieMap <: S PositiveOrderedTypeBits.

  Module E := PositiveOrderedTypeBits.

  Definition key := positive : Type.

  Definition eq_key {A} (p p':positive*A) := fst p = fst p'.
  Definition eq_key_elt {A} (p p':positive*A) := fst p = fst p' /\ snd p = snd p'.
  Definition lt_key {A} (x y:_*A) := E.lt (fst x) (fst y).

  Definition t := trie.

  Definition empty {A} : t A := empty A.

  Section A.
  Variable A:Type.

  Definition is_empty (m : trie A) := match m with None => true | _ => false end.

  Definition find (i : key) (m : t A) : option A := get i m.

  Definition mem (i : key) (m : t A) : bool := match get i m with Some _ => true | _ => false end.

  Definition add (i : key) (v : A) (m : t A) : t A := set i v m.

  Definition singleton x e := add x e None.

  Definition remove (i : key) (m : t A) : t A := remove i m.

  Parameter bindings : t A -> list (key*A).

  Definition cardinal : t A -> nat :=
    trie_ind (fun _ => nat) O (fun _ x o _ y _ => x+(match o with Some a => 1|_=> O end)+y).

  Definition MapsTo (i:key)(v:A)(m:t A) := get i m = Some v.

  Definition In (i:key)(m:t A) := exists v, get i m = Some v.

  Lemma MapsTo_compat : Proper (E.eq ==> eq ==> eq ==> iff) MapsTo.
  Proof.
   intros k k' Hk e e' He m m' Hm. red in Hk. now subst.
  Qed.

  Lemma find_spec m x e : find x m = Some e <-> MapsTo x e m.
  Proof. reflexivity. Qed.

  Lemma mem_find :
    forall m x, mem x m = match find x m with None => false | _ => true end.
  Proof.
   induction m; destruct x; simpl; auto.
  Qed.

  Lemma mem_spec : forall m x, mem x m = true <-> In x m.
  Proof.
   intros m x; split.
   - cbv [mem In]. case get eqn:?; eauto; discriminate.
   - cbv [mem In]; intros [v H].
     rewrite H. trivial.
  Qed.

  Theorem empty_spec: forall (i: key), find i empty = None.
  Proof. reflexivity. Qed.

  Lemma is_empty_spec m : is_empty m = true <-> forall k, find k m = None.
  Proof.
   split.
   - case m; simpl; intros b H; [discriminate|reflexivity].
   - intros H. erewrite (extensionality_empty m); trivial.
  Qed.

  Theorem add_spec1: forall (m: t A) (i: key) (x: A),
   find i (add i x m) = Some x.
  Proof. intros; apply get_set_same. Qed.

  Theorem add_spec2: forall (m: t A) (i j: key) (x: A),
    i <> j -> find j (add i x m) = find j m.
  Proof.
   intros; cbv [find add].
   rewrite get_set_diff; congruence.
  Qed.

  Theorem remove_spec1: forall (m: t A)(i: key),
    find i (remove i m) = None.
  Proof.
  Admitted.

  Theorem remove_spec2: forall (m: t A)(i j: key),
    i <> j -> find j (remove i m) = find j m.
  Proof.
  Admitted.

  Lemma bindings_spec1 m k e :
    InA eq_key_elt (k,e) (bindings m) <-> MapsTo k e m.
  Proof.
  Admitted.

  Lemma bindings_spec2 m : sort lt_key (bindings m).
  Proof.
  Admitted.

  Lemma bindings_spec2w m : NoDupA eq_key (bindings m).
  Proof.
  Admitted.

  Lemma bindings_nil m : bindings m = nil <-> is_empty m = true.
  Proof.
  Admitted.

  Theorem singleton_spec i x : bindings (singleton i x) = (i,x)::nil.
  Proof.
  Admitted.

  Lemma cardinal_spec m : cardinal m = length (bindings m).
  Proof.
  Admitted.

  Variable B : Type.

  Parameter mapi : (key -> A -> B) -> t A -> t B.

  Definition map : (A -> B) -> t A -> t B :=
    fun f => @map_filter A B (fun a => Some (f a)).

  End A.

  Lemma mapi_spec A B (f:key -> A -> B) (m : t A) :
    bindings (mapi f m) =
     List.map (fun '(k,e) => (k, f k e)) (bindings m).
  Proof.
  Admitted.

  Lemma map_spec A B (f:A -> B)(m : t A) :
    bindings (map f m) =
     List.map (fun '(k,e) => (k, f e)) (bindings m).
  Proof.
  Admitted.

  Parameter merge : forall {A B C}, (key -> option A -> option B -> option C) -> t A -> t B -> t C.

  Lemma merge_spec1 {A B C}(f:key->option A->option B->option C) :
    forall m m' x,
    In x m \/ In x m' ->
    exists y, E.eq y x /\
     find x (merge f m m') = f y (find x m) (find x m').
  Proof.
  Admitted.

  Lemma merge_spec2 {A B C}(f:key->option A->option B->option C) :
    forall m m' x, In x (merge f m m') -> In x m \/ In x m'.
  Proof.
  Admitted.

  Parameter fold : forall A B, (key -> A -> B -> B) -> t A -> B -> B.

  Lemma fold_spec : forall {A}(m:t A){B}(i : B) (f : key -> A -> B -> B),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
  Proof.
  Admitted.

  Definition equal {A} eqA ma mb :=
    @trie_ind bool (fun _ => bool) true (fun _ x o _ y _ => x&&(match o with Some a => a|_=> true end)&&y)%bool
     (@combine A A bool
        (fun a b =>
           match a, b with
           | None, None => Some true
           | Some a, Some b => Some (eqA a b)
           | _, _ => Some false end) ma mb).

  Definition Equal A (m m':t A) := forall y, find y m = find y m'.

  Definition Eqdom A (m m':t A) := forall k, In k m <-> In k m'.

  Definition Equiv A (R:A->A->Prop) m m' :=
    Eqdom m m' /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> R e e').

  Definition Equivb (A:Type)(cmp: A->A->bool) := Equiv (Cmp cmp).

  Lemma equal_1 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    Equivb cmp m m' -> equal cmp m m' = true.
  Proof.
  Admitted.

  Lemma equal_2 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    equal cmp m m' = true -> Equivb cmp m m'.
  Proof.
  Admitted.

  Lemma equal_spec : forall (A:Type)(cmp:A->A->bool)(m m':t A),
    equal cmp m m' = true <-> Equivb cmp m m'.
  Proof.
    split. apply equal_2. apply equal_1.
  Qed.

  Parameter compare : forall A, (A -> A -> comparison) -> t A -> t A -> comparison.

  Lemma compare_spec A (cmp : A -> A -> comparison) m1 m2 :
   compare cmp m1 m2 =
    list_compare (pair_compare E.compare cmp) (bindings m1) (bindings m2).
  Proof.
  Admitted.

  Parameter filter : forall A, (key -> A -> bool) -> t A -> t A.

  Parameter partition : forall A, (key -> A -> bool) -> t A -> t A * t A.

  Parameter for_all : forall A, (key -> A -> bool) -> t A -> bool.

  Parameter exists_ : forall A, (key->A->bool) -> t A -> bool.

  Lemma filter_spec A (f:key->A->bool) m :
   bindings (filter f m) = List.filter (fun '(k,e) => f k e) (bindings m).
  Proof.
  Admitted.

  Lemma partition_spec A (f:key->A->bool) m :
   prodmap (@bindings _) (partition f m) =
    List.partition (fun '(k,e) => f k e) (bindings m).
  Proof.
  Admitted.

  Lemma for_all_spec A (f:key->A->bool) m :
   for_all f m = List.forallb (fun '(k,e) => f k e) (bindings m).
  Proof.
  Admitted.

  Lemma exists_spec A (f:key->A->bool) m :
   exists_ f m = List.existsb (fun '(k,e) => f k e) (bindings m).
  Proof.
  Admitted.

End TrieMap.

Module TrieMapAdditionalFacts.
  Import TrieMap.

  Lemma MapsTo_1 {A} m x y e : x = y -> @MapsTo A x e m -> MapsTo y e m.
  Proof. congruence. Qed.
End TrieMapAdditionalFacts.
