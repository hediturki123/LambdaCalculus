(* 2.2.4 Entiers de Church avec typage polymorphe *)

Definition pnat : Set := forall T : Set, (T->T)->(T->T).

Definition p0 : pnat :=  fun T : Set =>fun f :(T->T) => fun x : T => x.
Compute p0.
Definition p1  : pnat :=  fun T : Set =>fun f :(T->T) => fun x : T => f x.
Compute p1.
Definition pS : pnat->pnat := fun n :pnat => fun T :Set => fun f x => f (n T f x).