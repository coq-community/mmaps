(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * Finite map library, "raw" version *)

(** This "raw" interface isn't meant for general use, see rather
    the [Interface] file for that. The "raw" version has two interests :

    - Internally, as an intermediate step during the implementations
      [WeakList] [OrdList], [AVL] and [RBT] proposed in this library;

    - For advanced users, access to a "raw" map datatype allows
      smaller memory footprint during Coq computations (no proof parts)
      and hence slightly faster operations, at the expense of more
      complex reasoning when proving properties later.

    Raw means here that among all inhabitant of the type of maps,
    we'll only consider these fulfilling some adequacy predicate
    [Ok] (think for instance of lists that are sorted or trees that
    are binary search trees). All operations here will have [Ok]
    pre-conditions, and all operations answering new maps will
    maintain this adequacy.

    A implementation of the usual [Interface.S] can then be obtained
    by restricting the type of maps, and then wrapping all operations.
    In functor [Raw2Maps] below, this is done via a record combining
    a map and a adequacy proof. [Raw2Maps] is used as the final step
    in [OrdList], [AVL] and [RBT].

    See [Interface] for the documentation of all these operations
    and extra explanations.
*)

From Coq Require Export Bool Equalities Orders SetoidList.
From MMaps Require Export Interface.
Set Implicit Arguments.
Unset Strict Implicit.

Definition Cmp {elt:Type}(cmp:elt->elt->bool) e1 e2 := cmp e1 e2 = true.

Module Type WS (K : DecidableType).

  Definition key := K.t.
  Hint Transparent key.

  Definition eq_key {elt} (p p':key*elt) := K.eq (fst p) (fst p').

  Definition eq_key_elt {elt} (p p':key*elt) :=
      K.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Parameter t : Type -> Type.
  (** the abstract type of maps *)

  (** Is a set well-formed or ill-formed ? *)

  Parameter IsOk : forall {elt}, t elt -> Prop.
  Class Ok {elt}(m:t elt) : Prop := ok : IsOk m.

  (** In order to be able to validate (at least some) particular sets as
      well-formed, we ask for a boolean function for (semi-)deciding
      predicate [Ok]. If [Ok] isn't decidable, [isok] may be the
      always-false function. *)
  Parameter isok : forall {elt}, t elt -> bool.
  Parameter isok_Ok : forall {elt} (m:t elt) `(isok m = true), Ok m.

  Section Ops.
  Parameter empty : forall {elt}, t elt.
  Variable elt:Type.
  Parameter is_empty : t elt -> bool.
  Parameter add : key -> elt -> t elt -> t elt.
  Parameter find : key -> t elt -> option elt.
  Parameter remove : key -> t elt -> t elt.
  Parameter mem : key -> t elt -> bool.
  Parameter bindings : t elt -> list (key*elt).
  Parameter cardinal : t elt -> nat.
  Parameter fold : forall A: Type, (key -> elt -> A -> A) -> t elt -> A -> A.
  Parameter equal : (elt -> elt -> bool) -> t elt -> t elt -> bool.
  Variable elt' elt'' : Type.
  Parameter map : (elt -> elt') -> t elt -> t elt'.
  Parameter mapi : (key -> elt -> elt') -> t elt -> t elt'.
  Parameter merge : (key -> option elt -> option elt' -> option elt'') ->
                      t elt -> t elt' ->  t elt''.
  End Ops.

  Declare Instance empty_ok {elt} : Ok (@empty elt).
  Declare Instance add_ok {elt} (m:t elt) x e `(!Ok m) :
    Ok (add x e m).
  Declare Instance remove_ok {elt} (m:t elt) x `(!Ok m) :
    Ok (remove x m).
  Declare Instance map_ok {elt elt'}(f:elt->elt') m `(!Ok m) :
    Ok (map f m).
  Declare Instance mapi_ok {elt elt'}(f:key->elt->elt') m `(!Ok m) :
    Ok (mapi f m).
  Declare Instance merge_ok {elt elt' elt''}
    (f:key -> option elt -> option elt' -> option elt'') m m'
    `(!Ok m, !Ok m') :
    Ok (merge f m m').

  Parameter MapsTo : forall {elt}, key -> elt -> t elt -> Prop.
  Definition In {elt}(k:key)(m: t elt) : Prop := exists e, MapsTo k e m.

  Section Specs.
  Context {elt elt' elt'' : Type}.
  Global Declare Instance MapsTo_compat :
      Proper (K.eq==>Logic.eq==>Logic.eq==>iff) (@MapsTo elt).

  Variable m m' : t elt.
  Variable x y : key.
  Variable e : elt.
  Parameter find_spec : forall `{!Ok m},
     find x m = Some e <-> MapsTo x e m.
  Parameter mem_spec : forall `{!Ok m}, mem x m = true <-> In x m.
  Parameter empty_spec : find x (@empty elt) = None.
  Parameter is_empty_spec :
     is_empty m = true <-> forall x, find x m = None.
  Parameter add_spec1 : forall `{!Ok m}, find x (add x e m) = Some e.
  Parameter add_spec2 : forall `{!Ok m},
    ~K.eq x y -> find y (add x e m) = find y m.
  Parameter remove_spec1 : forall `{!Ok m}, find x (remove x m) = None.
  Parameter remove_spec2 : forall `{!Ok m},
    ~K.eq x y -> find y (remove x m) = find y m.
  Parameter bindings_spec1 :
    InA eq_key_elt (x,e) (bindings m) <-> MapsTo x e m.
  Parameter bindings_spec2w : forall `{!Ok m},
    NoDupA eq_key (bindings m).
  Parameter cardinal_spec : cardinal m = length (bindings m).
  Parameter fold_spec :
    forall {A} (i : A) (f : key -> elt -> A -> A),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.

  Definition Equal (m m':t elt) := forall y, find y m = find y m'.
  Definition Eqdom (m m':t elt) := forall y, In y m <-> In y m'.
  Definition Equiv (R:elt->elt->Prop) m m' :=
   Eqdom m m' /\ (forall k e e', MapsTo k e m -> MapsTo k e' m' -> R e e').
  Definition Equivb (cmp: elt->elt->bool) := Equiv (Cmp cmp).

  Parameter equal_spec :
   forall (cmp : elt -> elt -> bool)`{!Ok m, !Ok m'},
    equal cmp m m' = true <-> Equivb cmp m m'.

  Parameter map_spec : forall (f:elt->elt') m x `{!Ok m},
    find x (map f m) = option_map f (find x m).
  Parameter mapi_spec : forall (f:key->elt->elt') m x `{!Ok m},
    exists y:key, K.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).

  Implicit Types f : key->option elt->option elt'->option elt''.

  Parameter merge_spec1 :
   forall f m m' x `{!Ok m, !Ok m'},
     In x m \/ In x m' ->
     exists y:key, K.eq y x /\
                   find x (merge f m m') = f y (find x m) (find x m').

  Parameter merge_spec2 :
    forall f m m' x `{!Ok m, !Ok m'},
      In x (merge f m m') -> In x m \/ In x m'.

  End Specs.
End WS.

(** ** Raw Maps on ordered keys. *)

Module Type S (K : OrderedType).
  Include WS K.

  Definition lt_key {elt} (p p':key*elt) := K.lt (fst p) (fst p').

  Parameter bindings_spec2 :
    forall {elt}(m : t elt)`{!Ok m}, sort lt_key (bindings m).
End S.

Module WRaw2Maps (K : DecidableType) (M : WS K) <: Interface.WS K.

 Import M.

 (** We avoid creating induction principles for the Record *)
 Local Unset Elimination Schemes.

 Record t_ (elt:Type) := Mkt {this :> M.t elt; is_ok : Ok this}.
 Definition t := t_.
 Definition key := K.t.

 Hint Unfold t.
 Existing Instance is_ok.
 Local Arguments Mkt {elt} this {is_ok}.

 Section Elt.
 Context {elt elt' elt'': Type}.

 Implicit Types m : t elt.
 Implicit Types x y : key.
 Implicit Types e : elt.

 Definition empty : t elt := Mkt (@empty elt).
 Definition is_empty m : bool := is_empty m.
 Definition add x e m : t elt := Mkt (add x e m).
 Definition remove x m : t elt := Mkt (remove x m).
 Definition mem x m : bool := mem x m.
 Definition find x m : option elt := find x m.
 Definition map f m : t elt' := Mkt (map f m).
 Definition mapi (f:key->elt->elt') m : t elt' := Mkt (mapi f m).
 Definition merge f m (m':t elt') : t elt'' := Mkt (merge f m m').
 Definition bindings m : list (key*elt) := bindings m.
 Definition cardinal m := cardinal m.
 Definition fold {A} (f:key->elt->A->A) m i := fold f m i.
 Definition equal cmp m m' : bool := equal cmp m m'.

 Definition MapsTo x e m : Prop := MapsTo x e m.
 Definition In x m : Prop := In x m.

 Definition eq_key {elt} (p p':key*elt) := K.eq (fst p) (fst p').

 Definition eq_key_elt {elt} (p p':key*elt) :=
  K.eq (fst p) (fst p') /\ (snd p) = (snd p').

 Instance MapsTo_compat :
   Proper (K.eq==>Logic.eq==>Logic.eq==>iff) MapsTo.
 Proof.
  intros k k' Hk e e' <- m m' <-. unfold MapsTo; simpl. now rewrite Hk.
 Qed.

 Lemma find_spec m x e : find x m = Some e <-> MapsTo x e m.
 Proof. apply find_spec, is_ok. Qed.

 Lemma mem_spec m x : mem x m = true <-> In x m.
 Proof. apply mem_spec, is_ok. Qed.

 Lemma empty_spec x : find x empty = None.
 Proof. apply empty_spec. Qed.

 Lemma is_empty_spec m : is_empty m = true <-> forall x, find x m = None.
 Proof. apply is_empty_spec. Qed.

 Lemma add_spec1 m x e : find x (add x e m) = Some e.
 Proof. apply add_spec1, is_ok. Qed.
 Lemma add_spec2 m x y e : ~ K.eq x y -> find y (add x e m) = find y m.
 Proof. apply add_spec2, is_ok. Qed.

 Lemma remove_spec1 m x : find x (remove x m) = None.
 Proof. apply remove_spec1, is_ok. Qed.
 Lemma remove_spec2 m x y : ~K.eq x y -> find y (remove x m) = find y m.
 Proof. apply remove_spec2, is_ok. Qed.

 Lemma bindings_spec1 m x e :
   InA eq_key_elt (x,e) (bindings m) <-> MapsTo x e m.
 Proof. apply bindings_spec1. Qed.

 Lemma bindings_spec2w m : NoDupA eq_key (bindings m).
 Proof. apply bindings_spec2w, is_ok. Qed.

 Lemma fold_spec m {A} (i : A) (f : key -> elt -> A -> A) :
   fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
 Proof. apply fold_spec. Qed.

 Lemma cardinal_spec m : cardinal m = length (bindings m).
 Proof. apply cardinal_spec. Qed.

 Definition Equal m m' := forall y, find y m = find y m'.
 Definition Eqdom (m m':t elt) := forall y, In y m <-> In y m'.
 Definition Equiv (R:elt->elt->Prop) m m' :=
  Eqdom m m' /\ (forall k e e', MapsTo k e m -> MapsTo k e' m' -> R e e').
 Definition Equivb cmp := Equiv (Cmp cmp).

 Lemma Equivb_Equivb cmp m m' :
  Equivb cmp m m' <-> M.Equivb cmp m m'.
 Proof.
 unfold Equivb, Equiv, M.Equivb, M.Equiv. intuition.
 Qed.

 Lemma equal_spec m m' cmp :
   equal cmp m m' = true <-> Equivb cmp m m'.
 Proof. rewrite Equivb_Equivb. apply equal_spec; apply is_ok. Qed.

 End Elt.

 Lemma map_spec {elt elt'} (f:elt->elt') m x :
   find x (map f m) = option_map f (find x m).
 Proof. apply map_spec, is_ok. Qed.

 Lemma mapi_spec {elt elt'} (f:key->elt->elt') m x :
   exists y:key, K.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).
 Proof. apply mapi_spec, is_ok. Qed.

 Lemma merge_spec1 {elt elt' elt''}
       (f:key->option elt->option elt'->option elt'') m m' x :
   In x m \/ In x m' ->
   exists y:key, K.eq y x /\
                 find x (merge f m m') = f y (find x m) (find x m').
 Proof. apply merge_spec1; apply is_ok. Qed.

 Lemma merge_spec2 {elt elt' elt''}
       (f:key -> option elt->option elt'->option elt'') m m' x :
   In x (merge f m m') -> In x m \/ In x m'.
 Proof. apply merge_spec2; apply is_ok. Qed.

End WRaw2Maps.

Module Raw2Maps (K : OrderedType) (M : S K) <: Interface.S K.
 Include WRaw2Maps K M.

 Definition lt_key {elt} (p p':key*elt) := K.lt (fst p) (fst p').

 Lemma bindings_spec2 {elt}(m : t elt) : sort lt_key (bindings m).
 Proof. apply M.bindings_spec2. Qed.

End Raw2Maps.
