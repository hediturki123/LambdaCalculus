(*2.2.3 Structures de données : couples et choix *)

Definition pprod_nb : Set := forall T : Set, (nat->bool->T) -> T.
Definition pcpl_nb : nat->bool->pprod_nb := fun a b => fun T : Set => fun k : (nat->bool->T) =>k a b.
Compute pcpl_nb 3 true.

Definition pprod_bn : Set := forall T : Set, (bool->nat->T)->T.
Definition pcpl_bn : bool->nat->pprod_bn := fun a b => fun T : Set => fun k : (bool->nat->T) =>k a b.
Compute pcpl_bn true 3.

Definition permutation_nat_bool : nat->bool->pprod_bn := fun a b => pcpl_bn b a.
Compute permutation_nat_bool 3 true.

Definition echange : pprod_nb->pprod_bn := fun k => k pprod_bn(permutation_nat_bool).
Compute echange (pcpl_nb 3 true).
Compute echange (pcpl_nb 6 false).


Definition pprod : Set -> Set -> Set := fun A B => forall T:Set, (A->B->T)->T.
Definition pprod' (A B: Set) : Set := forall T:Set,(A->B->T)->T.
Definition pcpl (A B : Set) := fun a b => fun T : Set =>fun k :(A->B->T) => k a b.
Compute pcpl.