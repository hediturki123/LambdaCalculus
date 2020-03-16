
(*2.2 Programmation de structures avancées en λ-calcul *)
(*2.2.1 Exemple simple : l’identité polymorphe *)

(*1*)
Definition tid : Set := forall T: Set, T -> T.
Definition id : tid := fun T:Set => fun x:T => x.

Compute id nat 3.
Compute id bool true.
Compute id bool false.

(*2*)
Definition nbtrue1 := fun b =>match b with
                      true => 1 | false => 0 end.
Definition id_bool : bool->nat := id (bool->nat) nbtrue1.
Compute id_bool true.
Compute id_bool false.

(*3*)
