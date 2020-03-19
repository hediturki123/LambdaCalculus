(*2.2.3 Structures de données : couples et choix *)

(*1*)
Definition pprod_nb : Set := forall T : Set, (nat->bool->T) -> T.
Definition pcpl_nb : nat->bool->pprod_nb := fun a b => fun T : Set => fun k : (nat->bool->T) =>k a b.
Compute pcpl_nb 3 true.

(*2*)
Definition pprod_bn : Set := forall T : Set, (bool->nat->T)->T.
Definition pcpl_bn : bool->nat->pprod_bn := fun a b => fun T : Set => fun k : (bool->nat->T) =>k a b.
Compute pcpl_bn true 3.

(*3*)
Definition permutation_nat_bool : nat->bool->pprod_bn := fun a b => pcpl_bn b a.
Compute permutation_nat_bool 3 true.

Definition echange : pprod_nb->pprod_bn := fun k => k pprod_bn(permutation_nat_bool).
Compute echange (pcpl_nb 3 true).
Compute echange (pcpl_nb 6 false).

(*4*)
Variable A B :Set. (* je ne sais pas comment enlever ce warning *)
Definition pprod_1 : Set -> Set -> Set := fun A B => forall T:Set, (A->B->T)->T.
Definition pprod_2 (A B: Set) : Set := forall T:Set,(A->B->T)->T.
Definition pcpl : A->B->(pprod_2 A B) := fun (a : A) (b : B) => fun T => fun k :(A->B->T) => k a b.

Compute pcpl nat nat 1 2.
Compute pcpl bool nat true 1.
Compute pcpl nat bool 1 false.
Compute pcpl bool bool true false.

Definition psom (A B: Set) : Set := forall T:Set,(A->T)->(B->T)->T.
Definition inj1 (A B: Set) : A -> psom A B := fun u => fun T:Set => fun k => fun k'=>k u.
Definition inj2 (A B: Set) : B -> psom A B := fun v => fun T:Set => fun k => fun k'=>k' v.
