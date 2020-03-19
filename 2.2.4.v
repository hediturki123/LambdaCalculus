(*
Noel-Lardin Thomas
Turki Sanekli Hedi
*)
(* 2.2.4 Entiers de Church avec typage polymorphe *)

Definition pnat : Set := forall T : Set, (T->T)->(T->T).

(* Définition de l'entier 0 *)
Definition p0 : pnat :=  fun T : Set =>fun f :(T->T) => fun x : T => x.
Compute p0.

(* Définition du successeur *)
Definition pS : pnat->pnat := fun n :pnat => fun T :Set => fun f x => f (n T f x).

(* Définition d'autres entiers à l'aide du successeur *)
Definition p1 : pnat := pS p0.
Definition p2 : pnat := pS p1.
Definition p3 : pnat := pS p2.
Definition p4 : pnat := pS p3.
Compute p1.
Compute p2.
Compute p3.
Compute p4.

(*1*)
(* Définition de l'addition *)
Definition padd : pnat->pnat->pnat := fun n m => fun T => fun f x => n T f ( m T f x ).
Compute padd p1 p2.
Compute padd p4 p2.
Compute padd p2 p2.
Compute padd p2 (padd p4 p2).
Compute padd (padd p1 p2) (padd p1 p2). (* (1+2)+(1+2)=>6 *)

(* Définition de la multiplication *)
Definition pmult : pnat->pnat->pnat := fun n m => fun T => fun f => n T ( m T f ).
Compute pmult p0 p1.
Compute pmult p2 p2.
Compute pmult p3 p2.
Compute pmult (padd p1 p1) p3.
Compute pmult (padd p2 p2) (padd p1 p2).  (* (2+2)*(1+2)=> 12 *)


(* Définition des booléens *)
Definition pbool : Set := forall T : Set, T -> T -> T.
Definition ptr : pbool := fun T : Set => fun x : T => fun y : T => x.
Definition pfa :  pbool := fun T : Set => fun x : T => fun y : T => y.
Compute ptr.
Compute pfa.

(* Définition du test à 0*)
Definition pe0 : pnat->pbool := fun n => fun T => fun x y => n T (fun z => y) x.
Compute pe0 p0.
Compute pe0 p1.
Compute pe0 p2.

(*2 Bonus*)
(*pplus:pnat→pnat→pnat def = λn^pnat m^pnat.n pnat pS m.*)
Definition pplus : pnat->pnat->pnat := fun n m => n pnat pS m.
Compute pplus p1 p2.
Compute pplus p2 p3.
Compute pplus p4 p1.
Compute pplus (pmult p1 p2) (padd p3 p4). (* (1*2)+(3+4) => 9 *)
(* La fonction prend en argument n de type pnat, m de type pnat et calcule le successeur de m, n fois *)

(*3*)

(* Les couples *)
Definition pprod (A B: Set) : Set := forall T:Set,(A->B->T)->T.
(* Définition de la fonction qui construit un couple *)
Definition pcpl (A B :Set): A->B->(pprod A B) := fun (a : A) (b : B) => fun T => fun k :(A->B->T) => k a b.

(* Définition de la fonction qui renvoie le premier élément du couple *)
Definition frst (A B :Set) : (pprod A B) -> A:= fun p => p A (fun (x : A) (y : B) => x).
Compute frst pnat pnat (pcpl pnat pnat p3 p4).    (* (3,4) *)
Compute frst pbool pnat (pcpl pbool pnat ptr p4). (* (true,4) *)
Compute frst pnat pbool (pcpl pnat pbool p3 pfa). (* (3,false) *)

(* Définition de la fonction qui renvoie le deuxième élément du couple *)
Definition scnd (A B :Set) : (pprod A B) -> B:= fun p => p B (fun (x : A) (y : B) => y).
Compute scnd pnat pnat (pcpl pnat pnat p3 p4).    (* (3,4) *)
Compute scnd pbool pnat (pcpl pbool pnat ptr p4). (* (true,4) *)
Compute scnd pnat pbool (pcpl pnat pbool p3 pfa). (* (3,false) *)

(* Définition de fonction pour calculer le prédécésseur*)
(* Définition de la fonction qui prend le couple (A,B) et renvoie le couple (B,B+1) *)
(* Lorsqu'elle reçoit un couple, elle va prendre le deuxième élément du couple et le met dans le premier élément du couple
en construction. Ensuite, elle prend le deuxième élément du couple lui ajoute 1 puis le place dans le deuxième élément
du couple en construction et elle renvoie se couple *)
Definition pred1: (pprod pnat pnat)->(pprod pnat pnat):= fun c => pcpl pnat pnat (scnd pnat pnat c)(pS(scnd pnat pnat c)).
Compute pred1 (pcpl pnat pnat p3 p4).
Compute pred1 (pcpl pnat pnat p1 p2).

(* Définition de la fonction qui itère n fois la fonction pred1 est renvoie le prédécesseur de n *)
(* Pour cette fonction, on va faire n fois la fonction précédente.Cela va permettre de créer le couple (n-1,n).
Par exemple, si on veux le prédécesseur de 3, la fonction vas exécuter comme celà:
(0,0)-> 1ère itération (0,1)-> 2ème itération (1,2)-> 3ème itération (2,3)-> sélection du premier élément 2
-> renvoi de cet élément. *)
Definition pred: pnat->pnat := fun n => frst pnat pnat (n(pprod pnat pnat) pred1 (pcpl pnat pnat p0 p0)).
Compute pred p1.
Compute pred p2.
Compute pred p4.
Compute pred (pmult (padd p1 p2) (pmult p2 p3)). (* (1+2)*(2*3)=> 12-1=>11 *)



