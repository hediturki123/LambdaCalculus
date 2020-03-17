(*2.2.3 Structures de données : couples et choix *)

Definition pprod_nb : Set := forall T : Set, (nat->bool->T) -> T.
Definition pcpl_nb : nat->bool->pprod_nb := fun a b => fun T : Set => fun k : (nat->bool->T) =>k a b.
Compute pcpl_nb 3 true.

Definition pprod_bn : Set := forall T : Set, (bool->nat->T)->T.
Definition pcpl_bn : bool->nat->pprod_bn := fun a b => fun T : Set => fun k : (bool->nat->T) =>k a b.
Compute pcpl_bn true 3.

Definition echange : pprod_nb->pprod_bn : fun k => k 