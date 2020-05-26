
(** * MMaps.RBT *)

(** This module implements finite maps using Red-Black trees.
    This code is based on [MSetRBT.v], due initially to
    Andrew W. Appel, 2011. See initial comment at the beginning
    of [MSetRBT.v].

    Note that we only prove here that the operations below preserve
    the binary search tree invariant ([Bst], a.k.a [Ok] predicate here),
    but *not* the Red/Black balancing invariant. Indeed, the former
    is enough to implement the desired interface [S], and ensure
    observational correctness. And proceeding this way is much lighter.

    Of course, the Red/Black invariants are also meant to be preserved
    here (otherwise we could end with wrong complexities). It shouldn't
    be too hard to adapt the proofs of [MSetRBT.BalanceProps] to this
    file, but this remains to be done.
*)

From Coq Require Import Bool BinPos Pnat Setoid SetoidList PeanoNat.
From Coq Require Import Orders OrdersFacts OrdersLists.
From MMaps Require Import Interface OrdList GenTree.

Local Set Implicit Arguments.
Local Unset Strict Implicit.
Import ListNotations.

(* For nicer extraction, we create inductive principles
   only when needed *)
Local Unset Elimination Schemes.

(** Notations and helper lemma about pairs *)

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

(** The type of color annotation. *)

Inductive color := Red | Black.

Module Color.
 Definition t := color.
End Color.

(** * The Raw functor

   Functor of pure functions + separate proofs of invariant
   preservation *)

Module Raw (K: OrderedType).

(** ** Generic trees instantiated with Red/Black colors *)

(** We reuse a generic definition of trees where the information
    parameter is a [Color.t]. Functions like mem or fold are also
    provided by this generic functor. *)

Include MMaps.GenTree.Ops K Color.

Local Open Scope pair_scope.
Local Open Scope lazy_bool_scope.
Local Notation color := Color.t.
Local Arguments Leaf {elt}.
Local Notation Rd := (@Node _ Red).
Local Notation Bk := (@Node _ Black).

Section Elt.
Variable elt : Type.
Local Notation t := (tree elt).
Implicit Types l r m : t.
Implicit Types e : elt.

(** ** Basic tree *)

Definition singleton (k : key) (v : elt) : t :=
  Node Black Leaf k v Leaf.

(** ** Changing root color *)

Definition makeBlack m : t :=
 match m with
 | Leaf => Leaf
 | Node _ a x v b => Bk a x v b
 end.

Definition makeRed m : t :=
 match m with
 | Leaf => Leaf
 | Node _ a x v b => Rd a x v b
 end.

(** ** Balancing *)

(** We adapt when one side is not a true red-black tree.
    Both sides have the same black depth. *)

Definition lbal l k vk r :=
 match l with
 | Rd (Rd a x vx b) y vy c => Rd (Bk a x vx b) y vy (Bk c k vk r)
 | Rd a x vx (Rd b y vy c) => Rd (Bk a x vx b) y vy (Bk c k vk r)
 | _ => Bk l k vk r
 end.

Definition rbal l k vk r :=
 match r with
 | Rd (Rd b y vy c) z vz d => Rd (Bk l k vk b) y vy (Bk c z vz d)
 | Rd b y vy (Rd c z vz d) => Rd (Bk l k vk b) y vy (Bk c z vz d)
 | _ => Bk l k vk r
 end.

(** A variant of [rbal], with reverse pattern order. *)

Definition rbal' l k vk r :=
 match r with
 | Rd b y vy (Rd c z vz d) => Rd (Bk l k vk b) y vy (Bk c z vz d)
 | Rd (Rd b y vy c) z vz d => Rd (Bk l k vk b) y vy (Bk c z vz d)
 | _ => Bk l k vk r
 end.

(** Balancing with different black depth.
    One side is almost a red-black tree, while the other is
    a true red-black tree, but with black depth + 1.
    Used in deletion. *)

Definition lbalS l k vk r :=
 match l with
 | Rd a x vx b => Rd (Bk a x vx b) k vk r
 | _ =>
   match r with
   | Bk a y vy b => rbal' l k vk (Rd a y vy b)
   | Rd (Bk a y vy b) z vz c => Rd (Bk l k vk a) y vy (rbal' b z vz (makeRed c))
   | _ => Rd l k vk r (* impossible *)
   end
 end.

Definition rbalS l k vk r :=
 match r with
 | Rd b y vy c => Rd l k vk (Bk b y vy c)
 | _ =>
   match l with
   | Bk a x vx b => lbal (Rd a x vx b) k vk r
   | Rd a x vx (Bk b y vy c) => Rd (lbal (makeRed a) x vx b) y vy (Bk c k vk r)
   | _ => Rd l k vk r (* impossible *)
   end
 end.

(** ** Insertion *)

Fixpoint ins x vx s :=
 match s with
 | Leaf => Rd Leaf x vx Leaf
 | Node c l y vy r =>
   match K.compare x y with
   | Eq => Node c l y vx r
   | Lt =>
     match c with
     | Red => Rd (ins x vx l) y vy r
     | Black => lbal (ins x vx l) y vy r
     end
   | Gt =>
     match c with
     | Red => Rd l y vy (ins x vx r)
     | Black => rbal l y vy (ins x vx r)
     end
   end
 end.

Definition add x vx s := makeBlack (ins x vx s).

(** ** Deletion *)

Fixpoint append (l:t) : t -> t :=
 match l with
 | Leaf => fun r => r
 | Node lc ll lx lv lr =>
   fix append_l (r:t) : t :=
   match r with
   | Leaf => l
   | Node rc rl rx rv rr =>
     match lc, rc with
     | Red, Red =>
       let lrl := append lr rl in
       match lrl with
       | Rd lr' x v rl' => Rd (Rd ll lx lv lr') x v (Rd rl' rx rv rr)
       | _ => Rd ll lx lv (Rd lrl rx rv rr)
       end
     | Black, Black =>
       let lrl := append lr rl in
       match lrl with
       | Rd lr' x v rl' => Rd (Bk ll lx lv lr') x v (Bk rl' rx rv rr)
       | _ => lbalS ll lx lv (Bk lrl rx rv rr)
       end
     | Black, Red => Rd (append_l rl) rx rv rr
     | Red, Black => Rd ll lx lv (append lr r)
     end
   end
 end.

Fixpoint del x m : t :=
 match m with
 | Leaf => Leaf
 | Node _ a y v b =>
   match K.compare x y with
   | Eq => append a b
   | Lt =>
     match a with
     | Bk _ _ _ _ => lbalS (del x a) y v b
     | _ => Rd (del x a) y v b
     end
   | Gt =>
     match b with
     | Bk _ _ _ _ => rbalS a y v (del x b)
     | _ => Rd a y v (del x b)
     end
   end
 end.

Definition remove x m := makeBlack (del x m).

(** ** Tree-ification

    We rebuild a tree of size [if pred then n-1 else n] as soon
    as the list [l] has enough elements *)

Definition klist A := list (key * A).
Local Notation treeify_t := (klist elt -> t * klist elt).

Definition bogus : t * klist elt := (Leaf, nil).

Definition treeify_zero : treeify_t :=
 fun acc => (Leaf,acc).

Definition treeify_one : treeify_t :=
 fun acc => match acc with
 | (x,v)::acc => (Rd Leaf x v Leaf, acc)
 | _ => bogus
 end.

Definition treeify_cont (f g : treeify_t) : treeify_t :=
 fun acc =>
 match f acc with
 | (l, (x,v)::acc) =>
   match g acc with
   | (r, acc) => (Bk l x v r, acc)
   end
 | _ => bogus
 end.

Fixpoint treeify_aux (pred:bool)(n: positive) : treeify_t :=
 match n with
 | xH => if pred then treeify_zero else treeify_one
 | xO n => treeify_cont (treeify_aux pred n) (treeify_aux true n)
 | xI n => treeify_cont (treeify_aux false n) (treeify_aux pred n)
 end.

Fixpoint plength_aux (l:klist elt)(p:positive) := match l with
 | nil => p
 | _::l => plength_aux l (Pos.succ p)
end.

Definition plength (l:klist elt) := plength_aux l 1.

Definition treeify (l:klist elt) :=
 fst (treeify_aux true (plength l) l).

End Elt.

(** * Map with removal *)

Definition ocons {A B} (a:A) (o:option B) (l:list (A*B)) :=
 match o with
 | None => l
 | Some b => (a,b)::l
 end.

Section Mapo.
Variable elt elt' : Type.
Variable f : key -> elt -> option elt'.

Fixpoint mapoL (l : klist elt)(acc : klist elt') : klist elt' :=
  match l with
   | nil => acc
   | (k,v)::l => mapoL l (ocons k (f k v) acc)
  end.

Definition mapo (m : t elt) : t elt' :=
 treeify (mapoL (rev_bindings m) nil).

End Mapo.

(** * Merge *)

Section Merge.
Variable elt elt' elt'' : Type.
Variable f : key -> option elt -> option elt' -> option elt''.

Fixpoint mergeL (l1:klist elt) :
 klist elt' -> klist elt'' -> klist elt'' :=
 match l1 with
 | nil => mapoL (fun k v' => f k None (Some v'))
 | (x,vx)::l1' =>
    fix mergeL_l1 l2 acc :=
    match l2 with
    | nil => mapoL (fun k v => f k (Some v) None) l1 acc
    | (y,vy)::l2' =>
       match K.compare x y with
       | Eq => mergeL l1' l2' (ocons x (f x (Some vx) (Some vy)) acc)
       | Lt => mergeL_l1 l2' (ocons y (f y None (Some vy)) acc)
       | Gt => mergeL l1' l2 (ocons x (f x (Some vx) None) acc)
       end
    end
 end.

Definition merge (m1 : t elt) (m2 : t elt') : t elt'' :=
 treeify (mergeL (rev_bindings m1) (rev_bindings m2) nil).

End Merge.

(** * Correctness proofs *)

Include MMaps.GenTree.Props K Color.

Local Infix "∈" := In (at level 70).
Local Infix "==" := K.eq (at level 70).
Local Infix "<" := K.lt (at level 70).
Local Infix "<<" := Below (at level 70).
Local Infix ">>" := Above (at level 70).
Local Infix "<<<" := Apart (at level 70).
Local Infix "===" := Equal (at level 70).

Local Hint Constructors tree MapsTo In Bst Above Below.
Local Hint Unfold In0 Apart Ok Bst_Ok.
Local Hint Immediate F.eq_sym.
Local Hint Resolve F.eq_refl F.eq_trans F.lt_trans.
Local Hint Resolve
 AboveLt Above_not_In Above_trans
 BelowGt Below_not_In Below_trans.

Ltac chok := change Bst with Ok in *.
Ltac autok := chok; auto with typeclass_instances.
Ltac ok :=
 match goal with
   | H : Ok (Node _ _ _ _ _) |- _ => inversion_clear H; chok; ok
   | H : Above _ (Node _ _ _ _ _) |- _ => inversion_clear H; ok
   | H : Below _ (Node _ _ _ _ _) |- _ => inversion_clear H; ok
   | |- Ok (Node _ _ _ _ _) => constructor; autok; ok
   | |- Above _ (Node _ _ _ _ _) => constructor; ok
   | |- Below _ (Node _ _ _ _ _) => constructor; ok
   | _ => eauto with typeclass_instances
 end.

Ltac induct m :=
 induction m as [|c l IHl x' vx' r IHr]; simpl; intros;
 [|case K.compare_spec; intros; inv Ok; chok].

Ltac destmatch :=
 match goal with
 | |- context [match K.compare _ _ with _ => _ end] =>
   case K.compare_spec; destmatch
 | |- context [match ?x with _ => _ end] =>
   destruct x; destmatch
 | _ => idtac
 end.

Section Elt.
Variable elt : Type.
Implicit Types m : t elt.
Implicit Types k x y : key.
Implicit Types v vx vy : elt.

(** ** Singleton set *)

Lemma singleton_spec x y vx vy :
  MapsTo y vy (singleton x vx) <-> y == x /\ vy = vx.
Proof.
 unfold singleton; intuition_in. subst; auto.
Qed.

Global Instance singleton_ok x vx : Ok (singleton x vx).
Proof.
 unfold singleton. ok.
Qed.

(** ** makeBlack, MakeRed *)

Global Instance makeBlack_ok m `{!Ok m} : Ok (makeBlack m).
Proof.
 destruct m; simpl; ok.
Qed.

Global Instance makeRed_ok m `{!Ok m} : Ok (makeRed m).
Proof.
 destruct m; simpl; ok.
Qed.

Lemma makeBlack_in m x : In x (makeBlack m) <-> In x m.
Proof.
 destruct m; simpl; intuition_in.
Qed.

Lemma makeRed_in m x : In x (makeRed m) <-> In x m.
Proof.
 destruct m; simpl; intuition_in.
Qed.

Lemma makeBlack_mapsto m x v : MapsTo x v (makeBlack m) <-> MapsTo x v m.
Proof.
 destruct m; simpl; intuition_in.
Qed.

Lemma makeRed_mapsto m x v : MapsTo x v (makeRed m) <-> MapsTo x v m.
Proof.
 destruct m; simpl; intuition_in.
Qed.

Lemma makeBlack_find m : makeBlack m === m.
Proof.
 now destruct m.
Qed.

Lemma makeRed_find m : makeRed m === m.
Proof.
 now destruct m.
Qed.

(** ** Generic handling for red-matching and red-red-matching *)

Definition isblack m :=
 match m with Bk _ _ _ _ => True | _ => False end.

Definition notblack m :=
 match m with Bk _ _ _ _ => False | _ => True end.

Definition notred m :=
 match m with Rd _ _ _ _ => False | _ => True end.

Definition rcase {A} f g m : A :=
 match m with
 | Rd a x v b => f a x v b
 | _ => g m
 end.

Inductive rspec {A} f g : t elt -> A -> Prop :=
 | rred a x v b : rspec f g (Rd a x v b) (f a x v b)
 | relse t : notred t -> rspec f g t (g t).

Fact rmatch {A} f g m : rspec (A:=A) f g m (rcase f g m).
Proof.
unfold rcase. destmatch; now constructor.
Qed.

Definition rrcase {A} f g m : A :=
 match m with
 | Rd (Rd a x vx b) y vy c => f a x vx b y vy c
 | Rd a x vx (Rd b y vy c) => f a x vx  b y vy c
 | _ => g m
 end.

Notation notredred := (rrcase (fun _ _ _ _ _ _ _ => False) (fun _ => True)).

Inductive rrspec {A} f g : t elt -> A -> Prop :=
 | rrleft a x vx b y vy c :
     rrspec f g (Rd (Rd a x vx b) y vy c) (f a x vx b y vy c)
 | rrright a x vx b y vy c :
     rrspec f g (Rd a x vx (Rd b y vy c)) (f a x vx b y vy c)
 | rrelse m : notredred m -> rrspec f g m (g m).

Fact rrmatch {A} f g m : rrspec (A:=A) f g m (rrcase f g m).
Proof.
unfold rrcase. destmatch; now constructor.
Qed.

Definition rrcase' {A} f g m : A :=
 match m with
 | Rd a x vx (Rd b y vy c) => f a x vx b y vy c
 | Rd (Rd a x vx b) y vy c => f a x vx b y vy c
 | _ => g m
 end.

Fact rrmatch' {A} f g m : rrspec (A:=A) f g m (rrcase' f g m).
Proof.
unfold rrcase'. destmatch; now constructor.
Qed.

(** Balancing operations are instances of generic match *)

Fact lbal_match l k v r :
 rrspec
   (fun a x vx b y vy c => Rd (Bk a x vx b) y vy (Bk c k v r))
   (fun l => Bk l k v r)
   l
   (lbal l k v r).
Proof.
 exact (rrmatch _ _ _).
Qed.

Fact rbal_match l k v r :
 rrspec
   (fun a x vx b y vy c => Rd (Bk l k v a) x vx (Bk b y vy c))
   (fun r => Bk l k v r)
   r
   (rbal l k v r).
Proof.
 exact (rrmatch _ _ _).
Qed.

Fact rbal'_match l k v r :
 rrspec
   (fun a x vx b y vy c => Rd (Bk l k v a) x vx (Bk b y vy c))
   (fun r => Bk l k v r)
   r
   (rbal' l k v r).
Proof.
 exact (rrmatch' _ _ _).
Qed.

Fact lbalS_match l x vx r :
 rspec
  (fun a y vy b => Rd (Bk a y vy b) x vx r)
  (fun l =>
    match r with
    | Bk a y vy b => rbal' l x vx (Rd a y vy b)
    | Rd (Bk a y vy b) z vz c =>
      Rd (Bk l x vx a) y vy (rbal' b z vz (makeRed c))
    | _ => Rd l x vx r
    end)
  l
  (lbalS l x vx r).
Proof.
 exact (rmatch _ _ _).
Qed.

Fact rbalS_match l x vx r :
 rspec
  (fun a y vy b => Rd l x vx (Bk a y vy b))
  (fun r =>
    match l with
    | Bk a y vy b => lbal (Rd a y vy b) x vx r
    | Rd a y vy (Bk b z vz c) =>
      Rd (lbal (makeRed a) y vy b) z vz (Bk c x vx r)
    | _ => Rd l x vx r
    end)
  r
  (rbalS l x vx r).
Proof.
 exact (rmatch _ _ _).
Qed.

(** ** Balancing for insertion *)

Global Instance lbal_ok l x v r `(!Ok l, !Ok r, x >> l, x << r) :
 Ok (lbal l x v r).
Proof.
 destruct (lbal_match l x v r); ok.
Qed.

Lemma lbal_in l x v r y :
 In y (lbal l x v r) <-> K.eq y x \/ In y l \/ In y r.
Proof.
 case lbal_match; intuition_in.
Qed.

(** Note : Rd is arbitrary here and in all similar results below *)

Lemma lbal_mapsto l x vx r y vy :
 MapsTo y vy (lbal l x vx r) <-> MapsTo y vy (Rd l x vx r).
Proof.
 case lbal_match; intuition_in.
Qed.

Lemma lbal_find l x v r `{!Ok l, !Ok r} :
 x >> l -> x << r ->
 lbal l x v r === Rd l x v r.
Proof.
 intros. intro. apply find_mapsto_equiv; auto using lbal_mapsto; autok.
Qed.

Global Instance rbal_ok l x v r `(!Ok l, !Ok r, x >> l, x << r) :
 Ok (rbal l x v r).
Proof.
 destruct (rbal_match l x v r); ok.
Qed.

Lemma rbal_in l x v r y :
 In y (rbal l x v r) <-> K.eq y x \/ In y l \/ In y r.
Proof.
 case rbal_match; intuition_in.
Qed.

Lemma rbal_mapsto l x vx r y vy :
 MapsTo y vy (rbal l x vx r) <-> MapsTo y vy (Rd l x vx r).
Proof.
 case rbal_match; intuition_in.
Qed.

Lemma rbal_find l x v r `{!Ok l, !Ok r} :
 x >> l -> x << r ->
 rbal l x v r === Rd l x v r.
Proof.
 intros. intro. apply find_mapsto_equiv; auto using rbal_mapsto; autok.
Qed.

Global Instance rbal'_ok l x v r `(!Ok l, !Ok r, x >> l, x << r) :
 Ok (rbal' l x v r).
Proof.
 destruct (rbal'_match l x v r); ok.
Qed.

Lemma rbal'_in l x r v y :
 In y (rbal' l x v r) <-> K.eq y x \/ In y l \/ In y r.
Proof.
 case rbal'_match; intuition_in.
Qed.

Lemma rbal'_mapsto l x vx r y vy :
 MapsTo y vy (rbal' l x vx r) <-> MapsTo y vy (Rd l x vx r).
Proof.
 case rbal'_match; intuition_in.
Qed.

Lemma rbal'_find l x v r `{!Ok l, !Ok r} :
 x >> l -> x << r ->
 rbal' l x v r === Rd l x v r.
Proof.
 intros. intro. apply find_mapsto_equiv; auto using rbal'_mapsto; autok.
Qed.

Hint Rewrite (@In_node_iff elt)
 makeRed_in makeBlack_in lbal_in rbal_in rbal'_in : rb.

Ltac autorew := autorewrite with rb.
Tactic Notation "autorew" "in" ident(H) := autorewrite with rb in H.
Ltac treeorder :=
 rewrite ?below_alt, ?above_alt; try intro; autorew; intuition_in; order.

(** ** Insertion *)

Lemma ins_in m x v y :
 In y (ins x v m) <-> K.eq y x \/ In y m.
Proof.
 induct m; destmatch; autorew; rewrite ?IHl, ?IHr; intuition_in.
 setoid_replace y with x; eauto.
Qed.
Hint Rewrite ins_in : rb.

Lemma ins_above m x v y : y >> m -> x < y -> y >> ins x v m.
Proof.
 intros. treeorder.
Qed.

Lemma ins_below m x v y : y << m -> y < x -> y << ins x v m.
Proof.
 intros. treeorder.
Qed.
Hint Resolve ins_above ins_below.

Global Instance ins_ok m x v `{!Ok m} : Ok (ins x v m).
Proof.
 induct m; auto; destmatch;
 (eapply lbal_ok || eapply rbal_ok || ok); auto.
Qed.

Lemma ins_spec1 m x v `{!Ok m} : find x (ins x v m) = Some v.
Proof.
 induct m; simpl; destmatch;
  rewrite ?lbal_find, ?rbal_find by eauto with *;
  simpl; destmatch; auto; try order.
Qed.

Lemma ins_spec2 m x y v `{!Ok m} : ~ x == y ->
 find y (ins x v m) = find y m.
Proof.
 induct m; simpl; destmatch;
  rewrite ?lbal_find, ?rbal_find by eauto with *;
  simpl; destmatch; auto; try order.
Qed.

Lemma ins_find m x y v `{!Ok m} :
 find y (ins x v m) =
  match K.compare y x with Eq => Some v | _ => find y m end.
Proof.
 destmatch; intros E.
 - apply find_spec; autok. rewrite E. apply find_spec; autok.
   now apply ins_spec1.
 - apply ins_spec2; trivial; order.
 - apply ins_spec2; trivial; order.
Qed.

Global Instance add_ok m x v `{!Ok m} : Ok (add x v m).
Proof.
 unfold add; autok.
Qed.

Lemma add_in m x v y :
 In y (add x v m) <-> K.eq y x \/ In y m.
Proof.
 unfold add. now autorew.
Qed.
Hint Rewrite add_in : rb.

Lemma add_spec1 m x v `{!Ok m} : find x (add x v m) = Some v.
Proof.
unfold add. rewrite makeBlack_find. now apply ins_spec1.
Qed.

Lemma add_spec2 m x y v `{!Ok m} : ~ x == y ->
 find y (add x v m) = find y m.
Proof.
unfold add. rewrite makeBlack_find. now apply ins_spec2.
Qed.


(** ** Balancing for deletion *)

Lemma lbalS_in l x v r y :
  In y (lbalS l x v r) <-> K.eq y x \/ In y l \/ In y r.
Proof.
 case lbalS_match.
 - intros; autorew; intuition_in.
 - clear l. intros l _. destmatch; autorew; intuition_in.
Qed.

Global Instance lbalS_ok l x v r :
  forall `(!Ok l, !Ok r, x >> l, x << r), Ok (lbalS l x v r).
Proof.
 case lbalS_match; intros; destmatch; ok; try apply rbal'_ok; treeorder.
Qed.

Lemma lbalS_mapsto l x v r y vy :
  MapsTo y vy (lbalS l x v r) <-> MapsTo y vy (Rd l x v r).
Proof.
 case lbalS_match; intros.
 - intuition_in.
 - destmatch; intuition_in;
   rewrite ?rbal'_mapsto in *; intuition_in;
   rewrite ?makeRed_mapsto in *; intuition_in;
   apply MapsRight; rewrite rbal'_mapsto; intuition_in.
   apply MapsRight. now rewrite makeRed_mapsto.
Qed.

Lemma lbalS_find l x v r `{!Ok l, !Ok r} : x >> l -> x << r ->
  lbalS l x v r === Rd l x v r.
Proof.
 intros. intro. apply find_mapsto_equiv; auto using lbalS_mapsto; autok.
Qed.

Lemma rbalS_in l x r v y :
  In y (rbalS l x v r) <-> K.eq y x \/ In y l \/ In y r.
Proof.
 case rbalS_match.
 - intuition_in.
 - intros t _. destmatch; autorew; intuition_in.
Qed.

Global Instance rbalS_ok l x v r :
 forall `(!Ok l, !Ok r, x >> l, x << r), Ok (rbalS l x v r).
Proof.
 case rbalS_match; intros; destmatch; ok; try (apply lbal_ok); treeorder.
Qed.

Lemma rbalS_mapsto l x v r y vy :
  MapsTo y vy (rbalS l x v r) <-> MapsTo y vy (Rd l x v r).
Proof.
 case rbalS_match; intros.
 - intuition_in.
 - destmatch; intuition_in;
   rewrite ?lbal_mapsto in *; intuition_in;
   rewrite ?makeRed_mapsto in *; intuition_in;
   apply MapsLeft; rewrite lbal_mapsto; intuition_in.
   apply MapsLeft. now rewrite makeRed_mapsto.
Qed.

Lemma rbalS_find l x v r `{!Ok l, !Ok r} : x >> l -> x << r ->
  rbalS l x v r === Rd l x v r.
Proof.
 intros. intro. apply find_mapsto_equiv; auto using rbalS_mapsto; autok.
Qed.

Hint Rewrite lbalS_in rbalS_in : rb.

(** ** Append for deletion *)

Ltac append_tac l r :=
 induction l as [| lc ll _ lx lv lr IHlr];
 [intro r; simpl
 |induction r as [| rc rl IHrl rx rv rr _];
   [simpl
   |destruct lc, rc;
     [specialize (IHlr rl); clear IHrl
     |simpl;
      assert (Hr:notred (Bk rl rx rv rr)) by (simpl; trivial);
      set (r:=Bk rl rx rv rr) in *; clearbody r; clear IHrl rl rx rv rr;
      specialize (IHlr r)
     |change (append _ _) with (Rd (append (Bk ll lx lv lr) rl) rx rv rr);
      assert (Hl:notred (Bk ll lx lv lr)) by (simpl; trivial);
      set (l:=Bk ll lx lv lr) in *; clearbody l; clear IHlr ll lx lv lr
     |specialize (IHlr rl); clear IHrl]]].

Fact append_rr_match ll lx lv lr rl rx rv rr :
 rspec
  (fun a x v b => Rd (Rd ll lx lv a) x v (Rd b rx rv rr))
  (fun t => Rd ll lx lv (Rd t rx rv rr))
  (append lr rl)
  (append (Rd ll lx lv lr) (Rd rl rx rv rr)).
Proof.
 exact (rmatch _ _ _).
Qed.

Fact append_bb_match ll lx lv lr rl rx rv rr :
 rspec
  (fun a x v b => Rd (Bk ll lx lv a) x v (Bk b rx rv rr))
  (fun t => lbalS ll lx lv (Bk t rx rv rr))
  (append lr rl)
  (append (Bk ll lx lv lr) (Bk rl rx rv rr)).
Proof.
 exact (rmatch _ _ _).
Qed.

Lemma append_in l r x :
 In x (@append elt l r) <-> In x l \/ In x r.
Proof.
 revert r.
 append_tac l r; autorew; try (intuition_in; fail).
 - (* Red / Red *)
   revert IHlr; case append_rr_match;
    [intros a y v b | intros t Ht]; autorew; tauto.
 - (* Black / Black *)
   revert IHlr; case append_bb_match;
    [intros a y v b | intros t Ht]; autorew; tauto.
Qed.

Hint Rewrite append_in : rb.

Global Instance append_ok : forall l r `{!Ok l, !Ok r},
 l <<< r -> Ok (@append elt l r).
Proof.
 append_tac l r; trivial; intros OK OK' AP;
 rewrite ?apart_node_l, ?apart_node_r in AP;
 decompose [and] AP; clear AP; ok; try treeorder.
 - (* Rd / Rd *)
   assert (U : Ok (append lr rl)) by auto.
   assert (V : lx << append lr rl) by treeorder.
   assert (W : rx >> append lr rl) by treeorder.
   revert U V W; case append_rr_match; intros; ok.
 - (* Bk / Bk *)
   assert (U : Ok (append lr rl)) by auto.
   assert (V : lx << append lr rl) by treeorder.
   assert (W : rx >> append lr rl) by treeorder.
   revert U V W; case append_bb_match; intros; ok.
Qed.

Lemma append_mapsto l r y v :
  MapsTo y v (append l r) <-> MapsTo y v l \/ MapsTo y v r.
Proof.
 revert r.
 append_tac l r; try (intuition_in; fail).
 - (* Rd / Rd *)
   simpl; intros.
   destmatch; revert IHlr; rewrite !MapsTo_node_iff; intuition.
 - (* Bk / Bk *)
   simpl; intros.
   destmatch; revert IHlr;
    rewrite ?lbalS_mapsto, !MapsTo_node_iff; intuition.
Qed.

(** ** Deletion *)

Lemma del_in m x y `{!Ok m} :
 In y (del x m) <-> In y m /\ ~K.eq y x.
Proof.
induct m; destmatch; treeorder.
Qed.

Hint Rewrite del_in : rb.

Global Instance del_ok m x `{!Ok m} : Ok (del x m).
Proof.
induct m.
- trivial.
- eapply append_ok; eauto.
- assert (x' >> del x l) by treeorder.
  destmatch; ok.
- assert (x' << del x r) by treeorder.
  destmatch; ok.
Qed.

Lemma del_spec1 m x `{!Ok m} : find x (del x m) = None.
Proof.
apply not_find_iff; ok. rewrite del_in; treeorder.
Qed.

Lemma del_spec2 m x y `{!Ok m} : ~ x == y ->
 find y (del x m) = find y m.
Proof.
intros.
apply find_mapsto_equiv; ok.
induct m.
- easy.
- rewrite append_mapsto, MapsTo_node_iff. treeorder.
- destmatch.
  + simpl. intuition_in.
  + rewrite 2 MapsTo_node_iff. factornode l. now rewrite IHl by ok.
  + rewrite lbalS_mapsto, 2 MapsTo_node_iff. factornode l.
    now rewrite IHl by ok.
- destmatch.
  + simpl. intuition_in.
  + rewrite 2 MapsTo_node_iff. factornode r. now rewrite IHr by ok.
  + rewrite rbalS_mapsto, 2 MapsTo_node_iff. factornode r.
    now rewrite IHr by ok.
Qed.

Lemma remove_in m x y `{!Ok m} :
 In y (remove x m) <-> In y m /\ ~K.eq y x.
Proof.
unfold remove. now autorew.
Qed.

Hint Rewrite remove_in : rb.

Global Instance remove_ok m x `{!Ok m} : Ok (remove x m).
Proof.
unfold remove; ok.
Qed.

Lemma remove_spec1 m x `{!Ok m} : find x (remove x m) = None.
Proof.
unfold remove. rewrite makeBlack_find. now apply del_spec1.
Qed.

Lemma remove_spec2 m x y `{!Ok m} : ~ x == y ->
 find y (remove x m) = find y m.
Proof.
unfold remove. rewrite makeBlack_find. now apply del_spec2.
Qed.

(** ** Treeify *)

Local Notation ifpred p n := (if p then pred n else n%nat).
Local Notation treeify_t := (klist elt -> t elt * klist elt).

Definition treeify_invariant size (f:treeify_t) :=
 forall acc,
 size <= length acc ->
 let (m,acc') := f acc in
 cardinal m = size /\ acc = bindings m ++ acc'.

Lemma treeify_zero_spec : treeify_invariant 0 (@treeify_zero elt).
Proof.
 intro. simpl. auto.
Qed.

Lemma treeify_one_spec : treeify_invariant 1 (@treeify_one elt).
Proof.
 intros [|x acc]; simpl; auto. inversion 1.
 destruct x. simpl; auto.
Qed.

Lemma treeify_cont_spec f g size1 size2 size :
 treeify_invariant size1 f ->
 treeify_invariant size2 g ->
 size = S (size1 + size2) ->
 treeify_invariant size (treeify_cont f g).
Proof.
 intros Hf Hg EQ acc LE. unfold treeify_cont.
 specialize (Hf acc).
 destruct (f acc) as (t1,acc1).
 destruct Hf as (Hf1,Hf2).
  { transitivity size; trivial. subst. auto with arith. }
 destruct acc1 as [|x acc1].
  { exfalso. revert LE. apply Nat.lt_nge. subst.
    rewrite app_nil_r, <- bindings_cardinal; auto with arith. }
 specialize (Hg acc1).
 destruct (g acc1) as (t2,acc2).
 destruct Hg as (Hg1,Hg2).
  { revert LE. subst.
    rewrite app_length, <- bindings_cardinal. simpl.
    rewrite Nat.add_succ_r, <- Nat.succ_le_mono.
    apply Nat.add_le_mono_l. }
 destruct x; simpl.
 rewrite bindings_node_acc. subst; auto.
Qed.

Lemma treeify_aux_spec n (p:bool) :
 treeify_invariant (ifpred p (Pos.to_nat n)) (treeify_aux p n).
Proof.
 revert p.
 induction n as [n|n|]; intros p; simpl treeify_aux.
 - eapply treeify_cont_spec; [ apply (IHn false) | apply (IHn p) | ].
   rewrite Pos2Nat.inj_xI.
   assert (H := Pos2Nat.is_pos n). apply Nat.neq_0_lt_0 in H.
   destruct p; simpl; intros; rewrite Nat.add_0_r; trivial.
   now rewrite <- Nat.add_succ_r, Nat.succ_pred; trivial.
 - eapply treeify_cont_spec; [ apply (IHn p) | apply (IHn true) | ].
   rewrite Pos2Nat.inj_xO.
   assert (H := Pos2Nat.is_pos n). apply Nat.neq_0_lt_0 in H.
   rewrite <- Nat.add_succ_r, Nat.succ_pred by trivial.
   destruct p; simpl; intros; rewrite Nat.add_0_r; trivial.
   symmetry. now apply Nat.add_pred_l.
 - destruct p; [ apply treeify_zero_spec | apply treeify_one_spec ].
Qed.

Lemma plength_aux_spec l p :
  Pos.to_nat (@plength_aux elt l p) = length l + Pos.to_nat p.
Proof.
 revert p. induction l; trivial. simpl plength_aux.
 intros. now rewrite IHl, Pos2Nat.inj_succ, Nat.add_succ_r.
Qed.

Lemma plength_spec l : Pos.to_nat (@plength elt l) = S (length l).
Proof.
 unfold plength. rewrite plength_aux_spec. apply Nat.add_1_r.
Qed.

Lemma treeify_bindings l : bindings (@treeify elt l) = l.
Proof.
 assert (H := @treeify_aux_spec (plength l) true l).
 unfold treeify. destruct treeify_aux as (t,acc); simpl in *.
 destruct H as (H,H'). { now rewrite plength_spec. }
 subst l. rewrite plength_spec, app_length, <- bindings_cardinal in *.
 destruct acc.
 * now rewrite app_nil_r.
 * exfalso. revert H. simpl.
   rewrite Nat.add_succ_r, Nat.add_comm.
   apply Nat.succ_add_discr.
Qed.

Lemma treeify_mapsto x v l : MapsTo x v (treeify l) <-> InA O.eqke (x,v) l.
Proof.
 intros. now rewrite <- bindings_mapsto, treeify_bindings.
Qed.

(* Todo : migrate this section elsewhere someday... *)

Section MoreOnSortA.
Context {A} eqA `{Equivalence A eqA}.
Context ltA `{StrictOrder A ltA} `{!Proper (eqA==>eqA==>iff) ltA}.

Lemma SortA_app (l1 l2 : list A) :
 sort ltA (l1++l2) <->
 sort ltA l1 /\ sort ltA l2 /\
  forall a1 a2, List.In a1 l1 -> List.In a2 l2 -> ltA a1 a2.
Proof.
 split.
 { induction l1 as [|a1 l1 IHl1].
   - easy.
   - simpl. inversion_clear 1 as [ | ? ? Hs Hhd ].
     destruct (IHl1 Hs) as (H1 & H2 & H3); clear IHl1.
     repeat split.
     * constructor; auto.
       destruct l1; simpl in *; auto; inversion_clear Hhd; auto.
     * trivial.
     * intros b1 b2 [->|Hb1] Hb2; eauto.
       eapply SortA_InfA_InA with (eqA:=eqA)(l:=l1++l2); auto.
       rewrite InA_app_iff. right. apply In_InA; ok. }
 { intros (U & V & W); eapply SortA_app; eauto.
   intros x y. rewrite !InA_alt.
   intros (x' & -> & Hx) (y' & -> & Hy); auto. }
Qed.

End MoreOnSortA.

(** Apart predicate on lists *)

Section ApartList.
Context {A B : Type}.
Implicit Types lA : klist A.
Implicit Types lB : klist B.

Definition ApartL lA lB :=
 forall ka kb, List.In ka lA -> List.In kb lB -> ka#1 < kb#1.

Lemma ApartL_rev lA lB : ApartL (rev lA) lB <-> ApartL lA lB.
Proof.
 unfold ApartL. now setoid_rewrite <- in_rev.
Qed.

Lemma ApartL_appl lA lA' lB :
 ApartL (lA++lA') lB <-> ApartL lA lB /\ ApartL lA' lB.
Proof.
 unfold ApartL. setoid_rewrite in_app_iff; firstorder.
Qed.

Lemma ApartL_appr lA lB lB' :
 ApartL lA (lB++lB') <-> ApartL lA lB /\ ApartL lA lB'.
Proof.
 unfold ApartL. setoid_rewrite in_app_iff; firstorder.
Qed.

Lemma ApartL_consl ka lA lB :
 ApartL (ka::lA) lB <-> ApartL [ka] lB /\ ApartL lA lB.
Proof.
 apply (ApartL_appl [ka]).
Qed.

Lemma ApartL_consr kb lA lB :
 ApartL lA (kb::lB) <-> ApartL lA [kb] /\ ApartL lA lB.
Proof.
 apply (ApartL_appr lA [kb]).
Qed.

End ApartList.

Lemma ApartL_eqk_l {A B B'} (lA : klist A) (kb:key*B) (kb':key*B') :
 ApartL [kb] lA -> K.eq (kb#1) (kb'#1) -> ApartL [kb'] lA.
Proof.
 unfold ApartL. simpl. intros AP E (k,b') (k',a) [<-|[ ]] Hy; simpl.
 rewrite <-E. apply (AP kb (k',a)); auto.
Qed.

Lemma ApartL_ltk_l {A B B'} (lA : klist A) (kb:key*B) (kb':key*B') :
 ApartL [kb] lA -> K.lt (kb'#1) (kb#1) -> ApartL [kb'] lA.
Proof.
 unfold ApartL. simpl. intros AP LT (k,b') (k',a) [<-|[ ]] Hy; simpl.
 rewrite LT. apply (AP kb (k',a)); auto.
Qed.

Lemma ApartL_eqk_r {A B B'} (lA : klist A) (kb:key*B) (kb':key*B') :
 ApartL lA [kb] -> K.eq (kb#1) (kb'#1) -> ApartL lA [kb'].
Proof.
 unfold ApartL. simpl. intros AP E (k,a) (k',b') Hx [<-|[ ]]; simpl.
 rewrite <-E. apply (AP (k,a) kb); auto.
Qed.

Lemma ApartL_ltk_r {A B B'} (lA : klist A) (kb:key*B) (kb':key*B') :
 ApartL lA [kb] -> K.lt (kb#1) (kb'#1) -> ApartL lA [kb'].
Proof.
 unfold ApartL. simpl. intros AP LT (k,a) (k',b') Hx [<-|[ ]]; simpl.
 rewrite <-LT. apply (AP (k,a) kb); auto.
Qed.

Lemma sort_app_key (l l' : klist elt) :
 sort O.ltk (l++l') <-> sort O.ltk l /\ sort O.ltk l' /\ ApartL l l'.
Proof.
 apply SortA_app with (eqA:=O.eqk)(ltA:=O.ltk); ok.
Qed.

Lemma sort_cons_key p (l : klist elt) :
 sort O.ltk (p::l) <-> sort O.ltk l /\ ApartL [p] l.
Proof.
 rewrite (sort_app_key [p] l). firstorder.
Qed.

Lemma bindings_above x (e:elt) (m:t elt) :
  x >> m <-> ApartL (bindings m) [(x,e)].
Proof.
 rewrite above_alt. unfold ApartL. simpl. split.
 - intros H p q Hp [<-|[ ]]. simpl. apply H.
   rewrite <- In_alt. exists (p#2). rewrite <- bindings_mapsto.
   apply In_InA; ok. now destruct p.
 - intros H y. rewrite <-In_alt. intros (v,M).
   rewrite <- bindings_mapsto, InA_alt in M.
   destruct M as ((y',v') & (E,E') & IN). compute in E, E'.
   subst v'. rewrite E. apply (H (y',v) (x,e)); auto.
Qed.

Lemma bindings_below x (e:elt) (m:t elt) :
  x << m <-> ApartL [(x,e)] (bindings m).
Proof.
 rewrite below_alt. unfold ApartL. simpl. split.
 - intros H p q [<-|[ ]] Hq. simpl. apply H.
   rewrite <- In_alt. exists (q#2). rewrite <- bindings_mapsto.
   apply In_InA; ok. now destruct q.
 - intros H y. rewrite <-In_alt. intros (v,M).
   rewrite <- bindings_mapsto, InA_alt in M.
   destruct M as ((y',v') & (E,E') & IN). compute in E, E'.
   subst v'. rewrite E. apply (H (x,e) (y',v)); auto.
Qed.

Lemma bindings_sort_ok (m:t elt) : sort O.ltk (bindings m) <-> Ok m.
Proof.
 split; auto using bindings_sort.
 induction m as [|c l IHl x v r IHr].
 - unfold bindings. simpl. firstorder.
 - rewrite bindings_node.
   rewrite sort_app_key, sort_cons_key, ApartL_consr.
   rewrite <- bindings_above, <- bindings_below. intuition; ok.
Qed.

Instance treeify_ok l : sort O.ltk l -> Ok (@treeify elt l).
Proof.
 intros. apply bindings_sort_ok. rewrite treeify_bindings; auto.
Qed.

End Elt.

Definition Keqb x y :=
  match K.compare x y with
  | Eq => true
  | _ => false
  end.

Lemma Keqb_spec x y : reflect (K.eq x y) (Keqb x y).
Proof.
 unfold Keqb. destruct (K.compare x y) eqn:E; constructor.
 - revert E. now case K.compare_spec.
 - revert E. case K.compare_spec; easy || order.
 - revert E. case K.compare_spec; easy || order.
Qed.

Definition oelse {A} (o o' : option A) :=
 match o with
 | None => o'
 | _ => o
 end.

Definition obind {A B} (o:option A) (f:A->option B) :=
  match o with Some a => f a | None => None end.

Lemma findA_app {A B} (h:A->bool) (l l' : list (A*B)) :
  findA h (l++l') = oelse (findA h l) (findA h l').
Proof.
 induction l as [|(a,b) l IH]; simpl; auto.
 rewrite IH. destruct (h a); auto.
Qed.

Lemma findA_inA {elt} x e (l : klist elt) :
 findA (Keqb x) l = Some e -> InA O.eqke (x,e) l.
Proof.
 induction l as [|(k,v) l IH]; simpl; try easy.
 case Keqb_spec; intro E; auto. intros [= ->]; auto.
Qed.

Lemma findA_inA_iff {elt} x e (l : klist elt) : sort O.ltk l ->
 (findA (Keqb x) l = Some e <-> InA O.eqke (x,e) l).
Proof.
 intros Sl. split; [apply findA_inA| ]. revert Sl.
 induction l as [|(k,v) l IH]; simpl; try easy.
 inversion_clear 1. rewrite InA_cons. intros [(E,E')|IN].
 - compute in E, E'. subst.
   case Keqb_spec; intros; auto || order.
 - case Keqb_spec; intros; auto.
   assert (LT : O.ltk (k,v) (x,e))
     by (eapply SortA_InfA_InA with (eqA:=O.eqke); ok).
   compute in LT. order.
Qed.

Lemma findA_find {elt} x (m : t elt) `{!Ok m} :
 findA (Keqb x) (bindings m) = find x m.
Proof.
 apply eq_option_alt. intro e.
 rewrite findA_inA_iff by now apply bindings_sort.
 rewrite find_spec by auto.
 apply bindings_mapsto.
Qed.

Section Mapo.
Variable elt elt' : Type.
Variable f : key -> elt -> option elt'.

Lemma mapoL_sorted (l : klist elt) acc :
 sort O.ltk (rev l) -> sort O.ltk acc -> ApartL l acc ->
 sort O.ltk (mapoL f l acc).
Proof.
 revert acc.
 induction l as [|(k,e) l IH]; simpl; auto.
 intros acc Sl Sacc AP.
 rewrite sort_app_key in Sl; ok. destruct Sl as (Sl & _ & AP').
 rewrite ApartL_rev, ApartL_consr in AP'. destruct AP' as (AP1',AP').
 rewrite ApartL_consl in AP. destruct AP as (AP1,AP).
 apply IH; clear IH; simpl; auto; destruct (f k e); simpl; auto.
 - apply sort_cons_key. eauto using ApartL_eqk_l.
 - apply ApartL_consr. eauto using ApartL_eqk_r.
Qed.

Global Instance mapo_ok m `{!Ok m} : Ok (mapo f m).
Proof.
 unfold mapo. apply treeify_ok. apply mapoL_sorted; simpl; auto.
 - rewrite rev_bindings_rev, rev_involutive. now apply bindings_sort.
 - inversion 2.
Qed.

Lemma mapoL_find l acc x :
 sort O.ltk (rev l) ->
 exists y : K.t,
    y == x /\
    findA (Keqb x) (mapoL f l acc) =
     oelse (obind (findA (Keqb x) (rev l)) (f y)) (findA (Keqb x) acc).
Proof.
 revert acc.
 induction l as [|(k,e) l IH]; simpl; intros acc Sl.
 - now exists x.
 - rewrite sort_app_key in Sl. destruct Sl as (Sl & _ & AP).
   rewrite ApartL_rev in AP.
   destruct (IH (ocons k (f k e) acc) Sl) as (y & Hy & E). clear IH.
   setoid_rewrite findA_app. setoid_rewrite E. clear E.
   destruct (findA (Keqb x) (rev l)) eqn:El; simpl in *; auto.
   + exists y; split; auto.
     destruct (f y e0); simpl; auto.
     destruct (f k e); simpl; auto.
     case Keqb_spec; auto. intros.
     apply findA_inA in El. rewrite InA_rev in El.
     apply InA_alt in El.
     destruct El as ((x',e') & (Hx',_) & IN).
     compute in Hx'.
     enough (x' < k) by order.
     apply (AP (x',e') (k,e)); simpl; auto.
   + clear l Sl AP El.
     destruct (f k e) eqn:Fk; simpl.
     * case Keqb_spec; [exists k | exists y]; simpl; now rewrite ?Fk.
     * case Keqb_spec; [exists k | exists y]; simpl; now rewrite ?Fk.
Qed.

Lemma mapoL_mapsto l acc x v' :
 InA O.eqke (x,v') (mapoL f l acc) <->
 (exists y v, K.eq y x /\ List.In (y,v) l /\ f y v = Some v') \/
  InA O.eqke (x,v') acc.
Proof.
 revert acc.
 induction l as [|(k,e) l IH]; simpl; intros.
 - firstorder.
 - destruct (f k e) eqn:Hf; simpl in *; rewrite IH; clear IH; auto.
   rewrite ?InA_cons.
   + firstorder; try red in H; try red in H0; simpl in *; subst.
     * left. exists k, e; auto.
     * injection H0 as <- <-. right; left. compute; split; auto.
       congruence.
   + firstorder. injection H0 as <- <-. congruence.
Qed.

Lemma mapo_mapsto m x (v':elt') :
  MapsTo x v' (mapo f m) ->
   exists y v, K.eq y x /\ MapsTo x v m /\ f y v = Some v'.
Proof.
 unfold mapo.
 rewrite treeify_mapsto, mapoL_mapsto, InA_nil; auto.
 intros [(y & v & E & IN & Hf)|[ ]].
 rewrite rev_bindings_rev, <-In_rev in IN.
 exists y, v. repeat split; auto. apply bindings_mapsto.
 rewrite InA_alt. exists (y, v). split; auto.
Qed.

Lemma mapo_in m x :
 x ∈ (mapo f m) ->
  exists y d, K.eq y x /\ MapsTo x d m /\ f y d <> None.
Proof.
 rewrite <- In_alt. intros (v',H).
 apply mapo_mapsto in H. destruct H as (y & v & E & M & Hf).
 exists y, v; repeat split; congruence.
Qed.

Lemma mapo_find m x `{!Ok m} :
  exists y, K.eq y x /\
            find x (mapo f m) = obind (find x m) (f y).
Proof.
 assert (Ok (mapo f m)) by ok.
 destruct (@mapoL_find (rev_bindings m) nil x) as (y & Hy & EQ).
 - rewrite rev_bindings_rev, rev_involutive; now apply bindings_sort.
 - exists y; split; auto.
   unfold mapo in *. rewrite <- !findA_find; auto.
   rewrite treeify_bindings, EQ. simpl. clear EQ.
   rewrite rev_bindings_rev, rev_involutive. now destruct obind.
Qed.

End Mapo.

Section Merge.
Variable elt elt' elt'' : Type.
Implicit Type f : key -> option elt -> option elt' -> option elt''.

Lemma mergeL_sorted f l l' acc :
 sort O.ltk (rev l) -> sort O.ltk (rev l') -> sort O.ltk acc ->
 ApartL l acc -> ApartL l' acc ->
 sort O.ltk (mergeL f l l' acc).
Proof.
 revert l' acc.
 induction l as [|(x,e) l IHl].
 - simpl. intros. apply mapoL_sorted; auto.
 - induction l' as [|(x',e') l' IHl'].
   + intros. apply mapoL_sorted; auto.
   + intros acc Sl Sl' Sacc AP AP'.
     simpl; destmatch.
     * intros E.
       simpl in Sl, Sl'.
       apply sort_app_key in Sl. destruct Sl as (Sl & _ & APl).
       apply sort_app_key in Sl'. destruct Sl' as (Sl' & _ & APl').
       rewrite ApartL_rev in APl. rewrite ApartL_rev in APl'.
       rewrite ApartL_consl in AP. destruct AP as (AP1,AP).
       rewrite ApartL_consl in AP'. destruct AP' as (AP1',AP').
       apply IHl; clear IHl IHl'; auto; destruct f; simpl; auto.
       { apply sort_cons_key. eauto using ApartL_eqk_l. }
       { rewrite ApartL_consr. eauto using ApartL_eqk_r. }
       { rewrite ApartL_consr. eauto using ApartL_eqk_r. }
     * intros LT.
       change (Sorted O.ltk (mergeL f ((x,e)::l) l'
                             (ocons x' (f x' None (Some e')) acc))).
       simpl in Sl'.
       apply sort_app_key in Sl'. destruct Sl' as (Sl' & _ & APl').
       rewrite ApartL_rev in APl'.
       rewrite ApartL_consl in AP'. destruct AP' as (AP1',AP').
       apply IHl'; clear IHl IHl'; auto; destruct f; simpl; auto.
       { apply sort_cons_key. eauto using ApartL_eqk_l. }
       { rewrite ApartL_consr. split; auto.
         rewrite ApartL_consl. split.
         - intros (?,?) (?,?). compute. intuition congruence.
         - simpl in Sl. rewrite sort_app_key, ApartL_rev in Sl.
           destruct Sl as (_ & _ & ?). eauto using ApartL_ltk_r. }
       { rewrite ApartL_consr. eauto using ApartL_eqk_r. }
     * intros LT.
       simpl in Sl.
       apply sort_app_key in Sl. destruct Sl as (Sl & _ & APl).
       rewrite ApartL_rev in APl.
       rewrite ApartL_consl in AP. destruct AP as (AP1,AP).
       apply IHl; clear IHl IHl'; auto; destruct f; simpl; auto.
       { apply sort_cons_key. eauto using ApartL_eqk_l. }
       { rewrite ApartL_consr. eauto using ApartL_eqk_r. }
       { rewrite ApartL_consr. split; auto.
         rewrite ApartL_consl. split.
         - intros (?,?) (?,?). compute. intuition congruence.
         - simpl in Sl'. rewrite sort_app_key, ApartL_rev in Sl'.
           destruct Sl' as (_ & _ & ?). eauto using ApartL_ltk_r. }
Qed.

Global Instance merge_ok f m m' `{!Ok m, !Ok m'} : Ok (merge f m m').
Proof.
apply treeify_ok, mergeL_sorted; auto;
 rewrite ?rev_bindings_rev, ?rev_involutive;
 now apply bindings_sort || firstorder.
Qed.

Lemma mergeL_in f l l' acc x :
 (exists v, InA O.eqke (x,v) (mergeL f l l' acc)) ->
    (exists v, InA O.eqke (x,v) l) \/
    (exists v, InA O.eqke (x,v) l') \/
    (exists v, InA O.eqke (x,v) acc).
Proof.
 revert l' acc.
 induction l as [|(y,e) l IHl].
 - simpl. intros l' acc (v,H). right.
   apply mapoL_mapsto in H.
   destruct H as [(y & v' & E & IN & _)|H].
   + left; exists v'. rewrite InA_alt. exists (y,v'); split; auto.
   + firstorder.
 - induction l' as [|(y',e') l' IHl'].
   + intros acc (v,H). apply mapoL_mapsto in H; simpl in *.
     destruct H as [(y' & v' & E & [[= <- <-]|IN] & _)|H].
     * left. exists e; eauto.
     * left. exists v'. rewrite InA_cons. right. rewrite InA_alt.
       exists (y',v'); auto.
     * firstorder.
   + intros acc. simpl; destmatch.
     * intros E H. apply IHl in H; clear IHl IHl'.
       setoid_rewrite InA_cons.
       firstorder.
       destruct f; simpl in *; [ | firstorder].
       rewrite InA_cons in H; destruct H as [H|H]; [ | firstorder ].
       compute in H. destruct H as (H,_).
       left. exists e. now left.
     * intros LT H.
       change (exists v,
               InA O.eqke (x,v) (mergeL f ((y,e)::l) l'
                                  (ocons y' (f y' None (Some e')) acc)))
       in H.
       apply IHl' in H; clear IHl IHl'.
       setoid_rewrite InA_cons at 2.
       firstorder.
       destruct f; simpl in *; [ | firstorder].
       rewrite InA_cons in H; destruct H as [H|H]; [ | firstorder ].
       compute in H. destruct H as (H,_).
       right; left. exists e'. now left.
     * intros LT H.
       apply IHl in H; clear IHl IHl'.
       setoid_rewrite InA_cons at 1.
       firstorder.
       destruct f; simpl in *; [ | firstorder].
       rewrite InA_cons in H; destruct H as [H|H]; [ | firstorder ].
       compute in H. destruct H as (H,_).
       left. exists e. now left.
Qed.

Lemma merge_spec2 f m m' x :
  In x (merge f m m') -> In x m \/ In x m'.
Proof.
 unfold merge.
 rewrite <- !In_alt. unfold In0. setoid_rewrite treeify_mapsto.
 intros H. apply mergeL_in in H. destruct H as [(v,H)|[(v,H)|(v,H)]].
 - left. exists v. rewrite rev_bindings_rev, InA_rev in H.
   now apply bindings_mapsto.
 - right. exists v. rewrite rev_bindings_rev, InA_rev in H.
   now apply bindings_mapsto.
 - now rewrite InA_nil in H.
Qed.

Lemma mergeL_find f l l' acc x :
 (forall k, f k None None = None) ->
 sort O.ltk (rev l) ->
 sort O.ltk (rev l') ->
 exists y, K.eq y x /\
  findA (Keqb x) (mergeL f l l' acc) =
    oelse (f y (findA (Keqb x) (rev l)) (findA (Keqb x) (rev l')))
          (findA (Keqb x) acc).
Proof.
 intros Hf.
 revert l' acc.
 induction l as [|(y,e) l IHl].
 - simpl. intros l' acc _ Sl'.
   destruct (@mapoL_find _ _ (fun k v' => f k None (Some v')) l' acc x Sl')
     as (y & Hy & EQ).
   exists y; split; auto; rewrite EQ; clear EQ.
   destruct findA; simpl; rewrite ?Hf; auto.
 - induction l' as [|(y',e') l' IHl'].
   + intros acc Sl _. clear IHl.
     destruct (@mapoL_find _ _ (fun k v => f k (Some v) None) _ acc x Sl)
       as (z & Hz & EQ).
     exists z; split; auto. cbn - [mapoL]. rewrite EQ; clear EQ.
     simpl. destruct findA; simpl; rewrite ?Hf; auto.
   + intros acc Sl Sl'.
     simpl mergeL. destmatch; intro E.
     * simpl in Sl, Sl'. rewrite sort_app_key in Sl, Sl'.
       destruct Sl as (Sl & _ & AP). destruct Sl' as (Sl' & _ & AP').
       destruct (IHl l' (ocons y (f y (Some e) (Some e')) acc))
        as (z & Hz & EQ); auto.
       setoid_rewrite EQ. clear IHl IHl' EQ.
       simpl. setoid_rewrite findA_app; simpl.
       destruct findA eqn:INl.
       ** exists z; split; auto.
          assert (x < y).
          { apply findA_inA in INl. apply InA_alt in INl.
            destruct INl as ((x',e0') & (Hx',_) & INl).
            compute in Hx'. rewrite Hx'.
            apply (AP (x',e0') (y,e)); simpl; auto. }
          destruct (findA _ (rev l')) eqn:INl'; simpl.
          *** destruct (f z _ _); simpl; auto.
              destruct (f y _ _); simpl; auto.
              case Keqb_spec; auto || order.
          *** case Keqb_spec; auto; try order. intros.
              destruct (f z _ _); simpl; auto.
              destruct (f y _ _); simpl; auto.
              case Keqb_spec; auto || order.
       ** clear INl.
          destruct (findA _ (rev l')) eqn:INl'; simpl.
          *** exists z; split; auto.
              assert (x < y').
              { apply findA_inA in INl'. apply InA_alt in INl'.
                destruct INl' as ((x',e0') & (Hx',_) & INl').
                compute in Hx'. rewrite Hx'.
                apply (AP' (x',e0') (y',e')); simpl; auto. }
              case Keqb_spec; auto; try order. intros.
              destruct (f z _ _); simpl; auto.
              destruct (f y _ _); simpl; auto.
              case Keqb_spec; auto || order.
          *** clear INl'. rewrite Hf. simpl.
              destruct (f y _ _) eqn:Fy; simpl;
               case Keqb_spec; intros;
                case Keqb_spec; intros; try order;
                 try setoid_rewrite Hf; firstorder;
                 exists y; now rewrite Fy.
     * change
         (exists y0, y0 == x /\
           findA (Keqb x)
                 (mergeL f ((y,e)::l) l'
                   (ocons y' (f y' None (Some e')) acc)) =
           oelse
             (f y0 (findA (Keqb x) (rev ((y, e) :: l)))
                (findA (Keqb x) (rev ((y', e') :: l'))))
             (findA (Keqb x) acc)).
       simpl in Sl'. rewrite sort_app_key in Sl'.
       destruct Sl' as (Sl' & _ & AP').
       destruct (IHl' (ocons y' (f y' None (Some e')) acc))
        as (z & Hz & EQ); auto.
       setoid_rewrite EQ. clear IHl IHl' EQ.
       remember ((y,e)::l) as l0.
       simpl. setoid_rewrite findA_app.
       destruct findA eqn:INl.
       ** exists z; split; auto.
          assert (x < y').
          { apply findA_inA in INl. apply InA_alt in INl.
            destruct INl as ((x',e0') & (Hx',_) & INl).
            compute in Hx'. rewrite Hx'.
            rewrite Heql0 in *. simpl in *.
            rewrite sort_app_key in Sl.
            destruct Sl as (Sl & _ & AP).
            rewrite in_app_iff in INl. destruct INl.
            - rewrite <- E. apply (AP (x',e0') (y,e)); simpl; auto.
            - simpl in H. destruct H as [[= <- _]|[  ]]; auto. }
          destruct (findA _ (rev l')) eqn:INl'; simpl.
          *** destruct (f z _ _); simpl; auto.
              destruct (f y' _ _); simpl; auto.
              case Keqb_spec; auto || order.
          *** case Keqb_spec; auto; try order. intros.
              destruct (f z _ _); simpl; auto.
              destruct (f y' _ _); simpl; auto.
              case Keqb_spec; auto || order.
       ** clear INl.
          destruct (findA _ (rev l')) eqn:INl'; simpl.
          *** exists z; split; auto.
              assert (x < y').
              { apply findA_inA in INl'. apply InA_alt in INl'.
                destruct INl' as ((x',e0') & (Hx',_) & INl').
                compute in Hx'. rewrite Hx'.
                apply (AP' (x',e0') (y',e')); simpl; auto. }
              destruct (f z _ _); simpl; auto.
              destruct (f y' _ _); simpl; auto.
              case Keqb_spec; auto || order.
          *** clear INl'. rewrite Hf. simpl.
              destruct (f y' _ _) eqn:Fy'; simpl;
               case Keqb_spec; intros;
                 try setoid_rewrite Hf; firstorder;
                 exists y'; now rewrite Fy'.
     * simpl in Sl. rewrite sort_app_key in Sl.
       destruct Sl as (Sl & _ & AP).
       destruct (IHl ((y',e')::l') (ocons y (f y (Some e) None) acc))
        as (z & Hz & EQ); auto.
       setoid_rewrite EQ. clear IHl IHl' EQ.
       remember ((y',e')::l') as l0'.
       simpl. setoid_rewrite findA_app.
       destruct findA eqn:INl.
       ** exists z; split; auto.
          assert (x < y).
          { apply findA_inA in INl. apply InA_alt in INl.
            destruct INl as ((x',e0') & (Hx',_) & INl).
            compute in Hx'. rewrite Hx'.
            apply (AP (x',e0') (y,e)); simpl; auto. }
          destruct (findA _ (rev l0')) eqn:INl'; simpl.
          *** destruct (f z _ _); simpl; auto.
              destruct (f y _ _); simpl; auto.
              case Keqb_spec; auto || order.
          *** destruct (f z _ _); simpl; auto.
              destruct (f y _ _); simpl; auto.
              case Keqb_spec; auto || order.
       ** clear INl.
          destruct (findA _ (rev l0')) eqn:INl'; simpl.
          *** exists z; split; auto.
              assert (x < y).
              { apply findA_inA in INl'. apply InA_alt in INl'.
                destruct INl' as ((x',e0') & (Hx',_) & INl').
                compute in Hx'. rewrite Hx'.
                rewrite Heql0' in *. simpl in *.
                rewrite sort_app_key in Sl'.
                destruct Sl' as (Sl' & _ & AP').
                rewrite in_app_iff in INl'. destruct INl'.
                - rewrite <- E. apply (AP' (x',e0') (y',e')); simpl; auto.
                - simpl in H. destruct H as [[= <- _]|[  ]]; auto. }
              case Keqb_spec; auto; try order. intros.
              destruct (f z _ _); simpl; auto.
              destruct (f y _ _); simpl; auto.
              case Keqb_spec; auto || order.
          *** clear INl'. rewrite Hf. simpl.
              destruct (f y _ _) eqn:Fy; simpl;
               case Keqb_spec; intros;
                 try setoid_rewrite Hf; firstorder;
                 exists y; now rewrite Fy.
Qed.

Lemma merge_spec1n f m m' x `{!Ok m, !Ok m'} :
 (forall k, f k None None = None) ->
 exists y, K.eq y x /\
           find x (merge f m m') = f y (find x m) (find x m').
Proof.
 intros Hf.
 assert (Ok (merge f m m')) by ok.
 destruct (@mergeL_find f (rev_bindings m) (rev_bindings m') nil x)
   as (y & Hy & EQ); auto.
 - rewrite rev_bindings_rev, rev_involutive; now apply bindings_sort.
 - rewrite rev_bindings_rev, rev_involutive; now apply bindings_sort.
 - exists y; split; auto.
   unfold merge in *. rewrite <- !findA_find; auto.
   rewrite treeify_bindings, EQ. simpl. clear EQ.
   rewrite rev_bindings_rev, rev_involutive.
   rewrite rev_bindings_rev, rev_involutive.
   now destruct f.
Qed.

Lemma merge_spec1 f m m' x `{!Ok m, !Ok m'} :
 (In x m \/ In x m') ->
 exists y, K.eq y x /\
           find x (merge f m m') = f y (find x m) (find x m').
Proof.
 set (g := fun x o o' => match o,o' with None, None => None
                                        | _,_ => f x o o' end).
 destruct (@merge_spec1n g m m' x) as (y & Hy & EQ); auto.
 change (merge f) with (merge g).
 exists y; split; auto. rewrite EQ.
 destruct (find x m) eqn:F; simpl; auto.
 destruct (find x m') eqn:F'; simpl; auto.
 rewrite not_find_iff in F, F'; intuition.
Qed.

End Merge.
End Raw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of binary search trees. *)

Module Make (K: OrderedType) <: S K.

 Module Import Raw := Raw K.

 Record tree (elt:Type) :=
  Mk {this :> Raw.tree elt; is_ok : Ok this}.

 Existing Instance is_ok.
 Local Arguments Mk {elt} this {is_ok}.

 Definition t := tree.
 Definition key := K.t.

 Section Elt.
 Variable elt elt' elt'': Type.

 Implicit Types m : t elt.
 Implicit Types x y : key.
 Implicit Types e : elt.

 Definition empty : t elt := Mk (empty elt).
 Definition is_empty m : bool := is_empty m.
 Definition add x e m : t elt := Mk (add x e m).
 Definition remove x m : t elt := Mk (remove x m).
 Definition mem x m : bool := mem x m.
 Definition find x m : option elt := Raw.find x m.
 Definition map f m : t elt' := Mk (map f m).
 Definition mapi (f:key->elt->elt') m : t elt' := Mk (mapi f m).
 Definition merge f m (m':t elt') : t elt'' := Mk (merge f m m').
 Definition bindings m : list (key*elt) := bindings m.
 Definition cardinal m := cardinal m.
 Definition fold {A} (f:key->elt->A->A) m i := fold f m i.
 Definition equal cmp m m' : bool := equal cmp m m'.

 Definition MapsTo x e m : Prop := MapsTo x e m.
 Definition In x m : Prop := In0 x m.

 Definition eq_key : (key*elt) -> (key*elt) -> Prop := @O.eqk elt.
 Definition eq_key_elt : (key*elt) -> (key*elt) -> Prop := @O.eqke elt.
 Definition lt_key : (key*elt) -> (key*elt) -> Prop := @O.ltk elt.

 Instance MapsTo_compat :
   Proper (K.eq==>Logic.eq==>Logic.eq==>iff) MapsTo.
 Proof.
   intros k k' Hk e e' <- m m' <-. unfold MapsTo; simpl. now rewrite Hk.
 Qed.

 Lemma find_spec m x e : find x m = Some e <-> MapsTo x e m.
 Proof. apply find_spec; autok. Qed.

 Lemma mem_spec m x : mem x m = true <-> In x m.
 Proof. unfold In, mem; rewrite In_alt. apply mem_spec; autok. Qed.

 Lemma empty_spec x : find x empty = None.
 Proof. apply empty_spec. Qed.

 Lemma is_empty_spec m : is_empty m = true <-> forall x, find x m = None.
 Proof. apply is_empty_spec. Qed.

 Lemma add_spec1 m x e : find x (add x e m) = Some e.
 Proof. apply add_spec1; autok. Qed.
 Lemma add_spec2 m x y e : ~ K.eq x y -> find y (add x e m) = find y m.
 Proof. apply add_spec2; autok. Qed.

 Lemma remove_spec1 m x : find x (remove x m) = None.
 Proof. apply remove_spec1; autok. Qed.
 Lemma remove_spec2 m x y : ~K.eq x y -> find y (remove x m) = find y m.
 Proof. apply remove_spec2; autok. Qed.

 Lemma bindings_spec1 m x e :
   InA eq_key_elt (x,e) (bindings m) <-> MapsTo x e m.
 Proof. apply bindings_mapsto. Qed.

 Lemma bindings_spec2 m : sort lt_key (bindings m).
 Proof. apply bindings_sort; autok. Qed.

 Lemma bindings_spec2w m : NoDupA eq_key (bindings m).
 Proof. apply bindings_nodup; autok. Qed.

 Lemma fold_spec m {A} (i : A) (f : key -> elt -> A -> A) :
   fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
 Proof. apply fold_spec; autok. Qed.

 Lemma cardinal_spec m : cardinal m = length (bindings m).
 Proof. apply bindings_cardinal. Qed.

 Definition Equal m m' := forall y, find y m = find y m'.
 Definition Eqdom (m m':t elt) := forall y, In y m <-> In y m'.
 Definition Equiv (R:elt->elt->Prop) m m' :=
  Eqdom m m' /\ (forall k e e', MapsTo k e m -> MapsTo k e' m' -> R e e').
 Definition Equivb cmp := Equiv (Cmp cmp).

 Lemma Equivb_Equivb cmp m m' :
  Equivb cmp m m' <-> Raw.Equivb cmp m m'.
 Proof.
 unfold Equivb, Equiv, Raw.Equivb, In. intuition.
 intros k. rewrite <- !In_alt. apply H0.
 intros k. unfold In; rewrite !In_alt. apply H0.
 Qed.

 Lemma equal_spec m m' cmp :
   equal cmp m m' = true <-> Equivb cmp m m'.
 Proof. rewrite Equivb_Equivb. apply equal_Equivb; apply is_ok. Qed.

 End Elt.

 Lemma map_spec {elt elt'} (f:elt->elt') m x :
   find x (map f m) = option_map f (find x m).
 Proof. apply map_spec. Qed.

 Lemma mapi_spec {elt elt'} (f:key->elt->elt') m x :
   exists y:key, K.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).
 Proof. apply mapi_spec. Qed.

 Lemma merge_spec1 {elt elt' elt''}
       (f:key->option elt->option elt'->option elt'') m m' x :
   In x m \/ In x m' ->
   exists y:key, K.eq y x /\
                 find x (merge f m m') = f y (find x m) (find x m').
 Proof. unfold In. rewrite !In_alt. apply merge_spec1; autok. Qed.

 Lemma merge_spec2 {elt elt' elt''}
       (f:key -> option elt->option elt'->option elt'') m m' x :
   In x (merge f m m') -> In x m \/ In x m'.
 Proof. unfold In. rewrite !In_alt. apply merge_spec2; autok. Qed.

End Make.

Module Make_ord (K:OrderedType)(D:OrderedType) <: Sord K D.
  Module Import MapS := Make(K).
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
    destruct c; simpl; unfold flip; simpl; intros; case K.compare_spec;
      auto; try F.order.
    intros. right. split; auto. now symmetry.
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
   try case D.compare_spec; simpl; unfold flip; simpl; auto;
   case K.compare_spec; try R.F.order; auto.
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
   Cmp (compare m1 m2) (bindings m1) (bindings m2).
  Proof.
    destruct m1 as (s1,H1), m2 as (s2,H2).
    unfold compare; simpl.
    rewrite <- (app_nil_r (R.bindings s1)).
    replace (R.bindings s2) with (R.flatten_e (R.cons s2 (R.End _))) by
    (rewrite R.cons_1; simpl; rewrite app_nil_r; auto).
    auto using compare_cont_Cmp, compare_end_Cmp.
  Qed.

  Definition eq (m1 m2 : t) := LO.eq_list (bindings m1) (bindings m2).
  Definition lt (m1 m2 : t) := LO.lt_list (bindings m1) (bindings m2).

  Lemma compare_spec m1 m2 : CompSpec eq lt m1 m2 (compare m1 m2).
  Proof.
    assert (H := compare_Cmp m1 m2).
    unfold Cmp in H.
    destruct (compare m1 m2); auto.
  Qed.

  (* Proofs about [eq] and [lt] *)

  Definition sbindings (m1 : t) :=
   LO.MapS.Mk (@R.bindings_sort _ m1 _).

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
  rewrite Equivb_Equivb.
  rewrite R.Equivb_bindings. apply LO.eq_spec.
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

End Make_ord.
