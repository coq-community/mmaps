
(** * Finite Modular Maps : Main Interface *)

(** Author : Pierre Letouzey (Université de Paris - INRIA),
    adapted from earlier works in Coq Standard Library, see README.md.
    Licence : LGPL 2.1, see file LICENSE. *)

From Coq Require Export Bool Equalities Orders SetoidList.
Set Implicit Arguments.
Unset Strict Implicit.

(** When compared with Ocaml Map, this signature has been split in
    several parts :

 - The first part [WS] propose signatures for weak maps,
   which are maps with no ordering on the key type nor the
   data type. For obtaining an instance of this interface,
   a decidable equality on keys in enough (see for example
   [WeakList]). These signature contains the usual operators
   (add, find, ...). The only function that asks for more is
   [equal], whose first argument should be a comparison on data.

 - Then comes [S], that extends [WS] to the case where the key type
   is ordered. The main novelty is that [bindings] is required
   to produce sorted lists.

 - Finally, [Sord] extends [S] with a complete comparison function.
   For that, the data type should have a decidable total ordering
   as well.

 If unsure, what you're looking for is probably [S].

 Some additional differences with Ocaml:

 - no [iter] function, useless since Coq is purely functional
 - [option] types are used instead of [Not_found] exceptions.
   Said otherwise, [find] below is OCaml's [find_opt].

 Equality of maps

 Only one [equal] function on maps is provided, but several
 equivalence predicates on maps are considered, for different purposes.

 Predicate | On keys | On datas     | Decided by
 ----------------------------------------------------------------
 Equal     | K.eq    | Logic.eq     | equal eqb, if eqb decides (@Logic.eq elt)
 Equivb    | K.eq    | a test cmp   | equal cmp
 Equiv     | K.eq    | a relation R | equal cmp, if cmp decides R
 Eqdom     | K.eq    | True         | equal (fun _ _ => true)

 If [R] is an equivalence on datas, and [cmp] implements it, then we have
 [Eqdom m m' -> Equiv R m m' <-> Equivb cmp m m' -> Equal m m' -> m = m'].

 - In general, Leibniz equality on maps is not adequate here,
   since it is frequent that several maps may encode the same
   bindings, even when [K.eq] is Leibniz (think of tree re-balancing).

 - [Equal] is then the most precise predicate, and probably the most
   natural, corresponding to an observational equivalence : [Equal]
   maps will give equal results by [find] (or [MapsTo]).

 - [Equivb] and [Equiv] are somewhat ad-hoc, but necessary to fully
   specify the [equal] function. [Equivb] is parametrized by a boolean
   test [cmp] on datas, and its logical counterpart [Equiv] is parametrized
   by some relation on datas (possibly not an equivalence nor decidable).

 - [Eqdom] is only comparing the map domains. Said otherwise, it only
   considers the keys (via [K.eq]) but ignore datas altogether. Some
   properties are already shared amongst [Eqdom] maps, for instance
   they have the same cardinal.
*)

Definition Cmp {elt:Type}(cmp:elt->elt->bool) e1 e2 := cmp e1 e2 = true.

(** ** Weak signature for maps

    No requirements for an ordering on keys nor elements, only decidability
    of equality on keys. *)

Module Type WS (K : DecidableType).

  Definition key := K.t.

  Definition eq_key {elt} (p p':key*elt) := K.eq (fst p) (fst p').

  Definition eq_key_elt {elt} (p p':key*elt) :=
      K.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Parameter t : Type -> Type.
  (** the abstract type of maps *)

  Section Ops.

    Parameter empty : forall {elt}, t elt.
    (** The empty map. *)

    Variable elt:Type.

    Parameter is_empty : t elt -> bool.
    (** Test whether a map is empty or not. *)

    Parameter add : key -> elt -> t elt -> t elt.
    (** [add x y m] returns a map containing the same bindings as [m],
	plus a binding of [x] to [y]. If [x] was already bound in [m],
	its previous binding disappears. *)

    Parameter find : key -> t elt -> option elt.
    (** [find x m] returns the current binding of [x] in [m],
	or [None] if no such binding exists. *)

    Parameter remove : key -> t elt -> t elt.
    (** [remove x m] returns a map containing the same bindings as [m],
	except for [x] which is unbound in the returned map. *)

    Parameter mem : key -> t elt -> bool.
    (** [mem x m] returns [true] if [m] contains a binding for [x],
	and [false] otherwise. *)

    Parameter bindings : t elt -> list (key*elt).
    (** [bindings m] returns an assoc list corresponding to the bindings
        of [m], in any order. *)

    Parameter cardinal : t elt -> nat.
    (** [cardinal m] returns the number of bindings in [m]. *)

    Parameter fold : forall A: Type, (key -> elt -> A -> A) -> t elt -> A -> A.
    (** [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)],
	where [k1] ... [kN] are the keys of all bindings in [m]
	(in any order), and [d1] ... [dN] are the associated data. *)

    Parameter equal : (elt -> elt -> bool) -> t elt -> t elt -> bool.
    (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are equal,
      that is, contain equal keys and associate them with equal data.
      [cmp] is the equality predicate used to compare the data associated
      with the keys. *)

    Variable elt' elt'' : Type.

    Parameter map : (elt -> elt') -> t elt -> t elt'.
    (** [map f m] returns a map with same domain as [m], where the associated
	value a of all bindings of [m] has been replaced by the result of the
	application of [f] to [a]. Since Coq is purely functional, the order
        in which the bindings are passed to [f] is irrelevant. *)

    Parameter mapi : (key -> elt -> elt') -> t elt -> t elt'.
    (** Same as [map], but the function receives as arguments both the
	key and the associated value for each binding of the map. *)

    Parameter merge : (key -> option elt -> option elt' -> option elt'') ->
                      t elt -> t elt' ->  t elt''.
    (** [merge f m m'] creates a new map whose keys are a subset of keys of
        [m] and [m']. The presence of each such binding, and the corresponding
        value, is determined with the function [f]. More precisely, for
        a key [k], if its optional bindings [oe] in [m] and [oe'] in [m']
        are not both [None], then the presence and value of key [k] in
        the merged map is determined by [f k oe oe']. Note that
        [f k None None] will never be considered, and may differ from
        [None]. *)

  End Ops.
  Section Specs.

    Variable elt:Type.

    Parameter MapsTo : key -> elt -> t elt -> Prop.

    Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m.

    Global Declare Instance MapsTo_compat :
      Proper (K.eq==>Logic.eq==>Logic.eq==>iff) MapsTo.

    Variable m m' : t elt.
    Variable x y : key.
    Variable e : elt.

    Parameter find_spec : find x m = Some e <-> MapsTo x e m.
    Parameter mem_spec : mem x m = true <-> In x m.
    Parameter empty_spec : find x (@empty elt) = None.
    Parameter is_empty_spec : is_empty m = true <-> forall x, find x m = None.
    Parameter add_spec1 : find x (add x e m) = Some e.
    Parameter add_spec2 : ~K.eq x y -> find y (add x e m) = find y m.
    Parameter remove_spec1 : find x (remove x m) = None.
    Parameter remove_spec2 : ~K.eq x y -> find y (remove x m) = find y m.

    (** Specification of [bindings] *)
    Parameter bindings_spec1 :
      InA eq_key_elt (x,e) (bindings m) <-> MapsTo x e m.
    (** When compared with ordered maps, here comes the only
        property that is really weaker: *)
    Parameter bindings_spec2w : NoDupA eq_key (bindings m).

    (** Specification of [cardinal] *)
    Parameter cardinal_spec : cardinal m = length (bindings m).

    (** Specification of [fold] *)
    Parameter fold_spec :
      forall {A} (i : A) (f : key -> elt -> A -> A),
      fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.

    Definition Equal (m m':t elt) := forall y, find y m = find y m'.
    Definition Eqdom (m m':t elt) := forall y, In y m <-> In y m'.
    Definition Equiv (R:elt->elt->Prop) m m' :=
      Eqdom m m' /\ (forall k e e', MapsTo k e m -> MapsTo k e' m' -> R e e').
    Definition Equivb (cmp: elt->elt->bool) := Equiv (Cmp cmp).

    (** Specification of [equal] *)
    Parameter equal_spec : forall cmp : elt -> elt -> bool,
      equal cmp m m' = true <-> Equivb cmp m m'.

  End Specs.
  Section SpecMaps.

    Variables elt elt' elt'' : Type.

    Parameter map_spec : forall (f:elt->elt') m x,
      find x (map f m) = option_map f (find x m).

    (** Note : the specifications for [mapi] and [merge] below are
        general enough to work even when [f] is not a morphism w.r.t.
        [K.eq]. For [merge], we could also have [f k None None <> None].
        Alas, this leads to relatively awkward statements.
        See the [Properties] functor for more usual and pratical statements,
        for instance [merge_spec1mn]. *)

    Parameter mapi_spec : forall (f:key->elt->elt') m x,
      exists y:key, K.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).

    Parameter merge_spec1 :
      forall (f:key->option elt->option elt'->option elt'') m m' x,
      In x m \/ In x m' ->
      exists y:key, K.eq y x /\
                    find x (merge f m m') = f y (find x m) (find x m').

    Parameter merge_spec2 :
      forall (f:key -> option elt->option elt'->option elt'') m m' x,
      In x (merge f m m') -> In x m \/ In x m'.

  End SpecMaps.
End WS.


(** ** Maps on ordered keys. *)

Module Type S (K : OrderedType).
  Include WS K.

  Definition lt_key {elt} (p p':key*elt) := K.lt (fst p) (fst p').

  (** Additional specification of [bindings] *)

  Parameter bindings_spec2 : forall {elt}(m : t elt), sort lt_key (bindings m).

  (** Remark: since [fold] is specified via [bindings], this stronger
   specification of [bindings] has an indirect impact on [fold],
   which can now be proved to receive bindings in increasing order. *)

End S.


(** ** Maps with orderings both on keys and datas *)

Module Type Sord (K : OrderedType) (D : OrderedType).

  Declare Module MapS : S K.
  Import MapS.

  Definition t := MapS.t D.t.

  Include HasEq <+ HasLt <+ IsEq <+ IsStrOrder.

  Definition cmp e e' :=
    match D.compare e e' with Eq => true | _ => false end.

  Parameter eq_spec : forall m m', eq m m' <-> Equivb cmp m m'.

  Parameter compare : t -> t -> comparison.

  Parameter compare_spec : forall m1 m2, CompSpec eq lt m1 m2 (compare m1 m2).

End Sord.
