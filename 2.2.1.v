
(*2.2 Programmation de structures avancées en λ-calcul *)
(*2.2.1 Exemple simple : l’identité polymorphe *)

(*1*)
(* -- Definition du tye identité -- *)
Definition tid : Set := forall T: Set, T -> T.

(* Définition de la fonction identitée *)
Definition id : tid := fun T:Set => fun x:T => x.

Compute id nat 3.
Compute id nat 50.
Compute id nat 10000. (* On peut voir qu'on se rapproche de la limite de la pile *)
Compute id bool true.
Compute id bool false.

(*2*)
(* Défintition de la fonction qui 1 lorsqu'elle à true 
et 0 lorsqu'elle à false *)
Definition nbtrue1 := fun b =>match b with
                      true => 1 | false => 0 end.

(* Définition de la fonction qui applique la fonction nbtrue1 *)
Definition id_bool : bool->nat := id (bool->nat) nbtrue1.
Compute id_bool true.
Compute id_bool false.

(*3*)
(* Application de la fonction id à elle même *)
Compute id tid id. (* retourne x donc elle peux 
                      s'appliquer à elle même *)
