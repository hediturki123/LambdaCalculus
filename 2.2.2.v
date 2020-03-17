(*2.2.2 Booléens avec typage polymorphe *)

(*1*)
(* Définition des booléens *)
Definition pbool : Set := forall T : Set, T -> T -> T.
Definition ptr : pbool := fun T : Set => fun x : T => fun y : T => x.
Definition pfa :  pbool := fun T : Set => fun x : T => fun y : T => y.

Compute ptr.
Compute pfa.

(*2*)
(* Codage de la négation (Première version) *)
Definition neg_bool_1 : pbool->pbool := fun b => fun T : Set => fun x y => b T y x.
Compute neg_bool_1 ptr.
Compute neg_bool_1 pfa.

(* Codage de la négation (Deuxième version) *)
Definition neg_bool_2 : pbool->pbool := fun b => fun T : Set => b(T->T->T)(fun x y => y)(fun x y => x).
Compute neg_bool_2 ptr.
Compute neg_bool_2 pfa.

(*3*)
(* Definition de la conjonction *)
Definition conj : pbool-> pbool->pbool := fun a b => fun T:Set => fun x y  => a T (b T x y) y.
Compute conj ptr pfa.
Compute conj ptr ptr.
Compute conj pfa ptr.
Compute conj pfa pfa.

(* Definition de la disjonction *)
Definition disj : pbool->pbool->pbool := fun a b => fun T:Set => fun x y : T => a T x (b T x y).
Compute disj ptr pfa.
Compute disj pfa pfa.
Compute disj pfa ptr.
Compute disj ptr ptr.

(*4*)
(* Definition de la fonction pbool *)
Definition cond : pbool->nat := fun b : pbool => b nat 3 5.
Compute cond ptr.
Compute cond pfa.
Compute cond (neg_bool_1 ptr).
Compute cond (neg_bool_1 (neg_bool_2 ptr)).
Compute cond (conj ptr (neg_bool_1(neg_bool_2 ptr))).
Compute cond (disj ptr (neg_bool_1(neg_bool_2 pfa))).
Compute cond (disj pfa (neg_bool_1 ptr)).

(* 5 -- BONUS -- *)
(* Définition de la fonction qui rend un booléen appliqué à lui même *)
Definition id_bool: pbool->pbool := fun b => b pbool b b.
Compute id_bool ptr.
Compute id_bool pfa.

