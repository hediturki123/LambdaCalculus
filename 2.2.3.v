(*2.2.3 Structures de données : couples et choix *)

(*1*)
(* Défintion de pprod_nb (Permet de construire un couple avec un entier et un booléen)*) 
Definition pprod_nb : Set := forall T : Set, (nat->bool->T) -> T.
Definition pcpl_nb : nat->bool->pprod_nb := fun a b => fun T : Set => fun k : (nat->bool->T) =>k a b.
Compute pcpl_nb 3 true.
Compute pcpl_nb 5 false.
Compute pcpl_nb (450-250) true.

(*2*)
(* Définition de pprod_bn (Permet de construire un couple avec un booléen et un entier)*)
Definition pprod_bn : Set := forall T : Set, (bool->nat->T)->T.
Definition pcpl_bn : bool->nat->pprod_bn := fun a b => fun T : Set => fun k : (bool->nat->T) =>k a b.
Compute pcpl_bn true 3.
Compute pcpl_bn false 5.
Compute pcpl_bn true (450-250).

(*3*)
(* Définition de la fonction qui échange un entier avec un booléen d'un pprod_nb*)
Definition permutation_nat_bool : nat->bool->pprod_bn := fun a b => pcpl_bn b a.
Compute permutation_nat_bool 3 true.
Compute permutation_nat_bool (450-250) false.

(* Définition de la fonction qui construit le couple pprod_bn avec la permutation du couple pprod_nb*)
Definition echange : pprod_nb->pprod_bn := fun k => k pprod_bn(permutation_nat_bool).
Compute echange (pcpl_nb 3 true).
Compute echange (pcpl_nb 6 false).
Compute echange (pcpl_nb (450-250) true).

(*4*)
(* Définition d'une fonction qui créer un couple de n'importe quel type  *)
Definition pprod_1 : Set -> Set -> Set := fun A B => forall T:Set, (A->B->T)->T.
Definition pprod_2 (A B: Set) : Set := forall T:Set,(A->B->T)->T.
Definition pcpl (A B :Set): A->B->(pprod_2 A B) := fun (a : A) (b : B) => fun T => fun k :(A->B->T) => k a b.

Compute pcpl nat nat 1 2.
Compute pcpl bool nat true 1.
Compute pcpl nat bool 1 false.
Compute pcpl bool bool true false.


Definition psom (A B: Set) : Set := forall T:Set,(A->T)->(B->T)->T.
Definition inj1 (A B: Set) : A -> psom A B := fun u => fun T:Set => fun k => fun k'=>k u.
Definition inj2 (A B: Set) : B -> psom A B := fun v => fun T:Set => fun k => fun k'=>k' v.