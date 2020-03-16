(*2.2.2 Booléens avec typage polymorphe *)

(*1*)
Definition pbool : Set := forall T : Set, T -> T -> T.
Definition ptr : pbool := fun T : Set => fun x : T => fun y : T => x.
Definition pfa :  pbool := fun T : Set => fun x : T => fun y : T => y.
Compute ptr.
Compute pfa.

(*2*)
Definition neg_bool_1 : pbool->pbool := fun b => fun T : Set => fun x y => b T y x.
Compute neg_bool_1 ptr.
Compute neg_bool_1 pfa.

Definition neg_bool_2 : pbool->pbool := fun b => fun T : Set => b(T->T->T)(fun x y => y)(fun x y => x).
Compute neg_bool_2 ptr.
Compute neg_bool_2 pfa.

(*3*)
(* Definition conj ???
Definition disj ????*)

(*4*)
Definition cond : pbool->nat := fun b : pbool => b nat 3 5.
Compute cond ptr.
Compute cond pfa.



