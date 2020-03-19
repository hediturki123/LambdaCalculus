(*
Noel-Lardin Thomas
Turki Sanekli Hedi
*)
(*2.2.3 Structures de données : couples et choix *)
(*1*)
(* Définition de la construction d'un couple d'un entier et d'un booléen *)
Definition pprod_nb : Set := forall T : Set, (nat->bool->T) -> T.
Definition pcpl_nb : nat->bool->pprod_nb := fun a b => fun T : Set => fun k : (nat->bool->T) =>k a b.
Compute pcpl_nb 3 true.
Compute pcpl_nb 5 false.
Compute pcpl_nb (450-250) true.
Compute pcpl_nb (2+35) false.

(*2*)
(* Définition de la construction d'un couple d'un booléen et d'un entier *)
Definition pprod_bn : Set := forall T : Set, (bool->nat->T)->T.
Definition pcpl_bn : bool->nat->pprod_bn := fun a b => fun T : Set => fun k : (bool->nat->T) =>k a b.
Compute pcpl_bn true 3.
Compute pcpl_bn false 5.
Compute pcpl_bn true (450-250).
Compute pcpl_bn false (2+35).

(*3*)
(* Définition de la fonction d'échange d'un nat bool en bool nat*)
Definition permutation_nat_bool : nat->bool->pprod_bn := fun a b => pcpl_bn b a.
Compute permutation_nat_bool 3 true.
Compute permutation_nat_bool 5 false.
Compute permutation_nat_bool (5+3) true.

(* Définition de la fonction qui prend un pprod_nb et qui rend un pprod_bn en utilisant la fonction d'échange *)
Definition echange : pprod_nb->pprod_bn := fun k => k pprod_bn(permutation_nat_bool).
Compute echange (pcpl_nb 3 true).
Compute echange (pcpl_nb 6 false).
Compute echange (pcpl_nb (5+3) true).

(*4*)
(* Définition de la construction d'un couple de n'importe quel type *)
Definition pprod_1 : Set -> Set -> Set := fun A B => forall T:Set, (A->B->T)->T.
Definition pprod_2 (A B: Set) : Set := forall T:Set,(A->B->T)->T.
Definition pcpl (A B :Set): A->B->(pprod_2 A B) := fun (a : A) (b : B) => fun T => fun k :(A->B->T) => k a b.
Compute pcpl nat nat 1 2.
Compute pcpl bool nat true 1.
Compute pcpl nat bool 1 false.
Compute pcpl bool bool true false.

(* Définition de variable pour les fonctions inj1 et inj2 *)

Variable nat_Vers_nat : nat->nat.
Variable nat_vers_bool : nat->bool.
Variable bool_vers_nat : bool->nat.
Variable bool_vers_bool : bool->bool.

(* Définition des fonctions inj1 *)
(* Cette fonction va prendre un nat N et l'injecter dans la première fonction qui lui est donnée.
La fonction va être appliqué à N et inj1 va rendre le résultat de cette fonction. *)

Definition psom (A B: Set) : Set := forall T:Set,(A->T)->(B->T)->T.
Definition inj1 (A B: Set) : A -> psom A B := fun u => fun T:Set => fun k => fun k'=>k u.
Definition plus_un : nat->nat := fun n =>n+1.
Compute inj1 nat nat 2 nat plus_un nat_Vers_nat.
Compute inj1 nat bool 2 nat plus_un bool_vers_nat.
Compute inj1 bool nat true nat bool_vers_nat nat_Vers_nat.

(* Définition des fonctions inj2 *)
(* Pour cette fonction, elle va effectuer la même chose que inj1 sauf qu'au lieux de prendre la première fonction qui
lui est donnée, elle va prendre la deuxième. *)

Definition inj2 (A B: Set) : B -> psom A B := fun v => fun T:Set => fun k => fun k'=>k' v.
Compute inj2 nat nat 2 nat nat_Vers_nat plus_un.
Compute inj2 bool bool true bool bool_vers_bool bool_vers_bool.
Compute inj2 nat bool true bool nat_vers_bool bool_vers_bool.
