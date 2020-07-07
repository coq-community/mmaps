From Coq Require Import List SetoidList.
Import ListNotations.

Set Implicit Arguments.

(** * Some complements on lists *)

Definition option_bind {A B} o (f:A->option B) :=
 match o with
 | None => None
 | Some a => f a
 end.

(** An hybrid of [map] and [filter] *)

Fixpoint mapfilter {A B} (f:A->option B) l :=
 match l with
 | [] => []
 | a::l => match f a with
           | Some b => b::mapfilter f l
           | None => mapfilter f l
           end
 end.

Lemma mapfilter_app {A B} (f:A->option B) l l' :
  mapfilter f (l++l') = mapfilter f l ++ mapfilter f l'.
Proof.
induction l; simpl; auto.
destruct f; simpl; auto; f_equal; auto.
Qed.

Instance mapfilter_ext {A B} :
 Proper ((eq ==> eq) ==> eq ==> eq) (@mapfilter A B).
Proof.
 intros f f' E l l' <-.
 induction l; simpl; auto.
 rewrite <- (E a); auto. destruct f; auto. f_equal; auto.
Qed.

Lemma map_as_mapfilter {A B} (f:A->B) l :
 map f l = mapfilter (fun a => Some (f a)) l.
Proof.
induction l; simpl; f_equal; auto.
Qed.

Lemma filter_as_mapfilter {A} (f:A->bool) l :
 filter f l = mapfilter (fun a => if f a then Some a else None) l.
Proof.
induction l; simpl; auto. destruct f; simpl; auto. f_equal; auto.
Qed.

Lemma mapfilter_comp {A B C}(f:A->option B)(g:B->option C) l :
 mapfilter g (mapfilter f l) = mapfilter (fun a => option_bind (f a) g) l.
Proof.
induction l; simpl; auto.
destruct f; simpl; auto. destruct g; simpl; auto. f_equal; auto.
Qed.

Lemma mapfilter_map {A B C} (f:A->B)(g:B->option C) l :
 mapfilter g (map f l) = mapfilter (fun a => g (f a)) l.
Proof.
now rewrite map_as_mapfilter, mapfilter_comp.
Qed.

Lemma map_mapfilter {A B C} (f:A->option B)(g:B->C) l :
 map g (mapfilter f l) = mapfilter (fun a => option_map g (f a)) l.
Proof.
rewrite map_as_mapfilter, mapfilter_comp. f_equiv.
Qed.

(** Properties of [List.filter] *)

Lemma filter_app {A} (f:A->bool) l l' :
  filter f (l++l') = filter f l ++ filter f l'.
Proof.
induction l; simpl; auto. destruct (f a); simpl; f_equal; auto.
Qed.

Lemma filter_map {A B} (f:A->B)(h:B->bool) l :
  filter h (map f l) = map f (filter (fun x => h (f x)) l).
Proof.
induction l; simpl; auto. destruct (h (f a)); simpl; f_equal; auto.
Qed.

Instance filter_ext {A} : Proper ((eq==>eq)==>eq==>eq) (@filter A).
Proof.
intros f f' E l l' <-.
induction l; simpl; auto. rewrite <- (E a); auto.
destruct f; simpl; auto. f_equal; auto.
Qed.

(** [List.partition] via [List.filter] *)

Lemma partition_filter {A} (f:A->bool) l :
 partition f l = (filter f l, filter (fun a => negb (f a)) l).
Proof.
induction l; simpl; auto. rewrite IHl. now destruct f.
Qed.

(** More results about [List.forallb] and [List.existsb] *)

Lemma forallb_map {A B} (f:A->B)(h:B->bool) l:
 forallb h (map f l) = forallb (fun a => h (f a)) l.
Proof.
induction l; simpl; auto. destruct h; simpl; auto.
Qed.

Lemma existsb_map {A B} (f:A->B)(h:B->bool) l:
 existsb h (map f l) = existsb (fun a => h (f a)) l.
Proof.
induction l; simpl; auto. destruct h; simpl; auto.
Qed.

Instance forallb_ext {A} : Proper ((eq==>eq)==>eq==>eq) (@forallb A).
Proof.
intros f f' E l l' <-.
induction l; simpl; auto. rewrite <- (E a); auto.
destruct f; simpl; auto.
Qed.

Instance existsb_ext {A} : Proper ((eq==>eq)==>eq==>eq) (@existsb A).
Proof.
intros f f' E l l' <-.
induction l; simpl; auto. rewrite <- (E a); auto.
destruct f; simpl; auto.
Qed.


(** [SetoidList.SortA_app] written via a [iff] *)

Section MoreOnSortA.
Context {A} eqA `{Equivalence A eqA}.
Context ltA `{StrictOrder A ltA} `{!Proper (eqA==>eqA==>iff) ltA}.

Lemma SortA_app (l1 l2 : list A) :
 sort ltA (l1++l2) <->
 sort ltA l1 /\ sort ltA l2 /\
  forall a1 a2, In a1 l1 -> In a2 l2 -> ltA a1 a2.
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
       rewrite InA_app_iff. right. apply In_InA; auto with *. }
 { intros (U & V & W); eapply SortA_app; eauto.
   intros x y. rewrite !InA_alt.
   intros (x' & -> & Hx) (y' & -> & Hy); auto. }
Qed.

End MoreOnSortA.
