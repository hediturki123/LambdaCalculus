(* 2.2.4 Entiers de Church avec typage polymorphe *)

Definition pnat : Set := forall T : Set, (T->T)->(T->T).

Definition p0 : pnat :=  fun T : Set =>fun f :(T->T) => fun x : T => x.
Compute p0.


Definition pS : pnat->pnat := fun n :pnat => fun T :Set => fun f x => f (n T f x).
Definition p1 : pnat := pS p0.
Definition p2 : pnat := pS p1.
Definition p3 : pnat := pS p2.
Definition p4 : pnat := pS p3.
Compute p1.
Compute p2.
Compute p3.
Compute p4.

(*1*)
Definition padd : pnat->pnat->pnat := fun n m => fun T => fun f x => n T f ( m T f x ).
Compute padd p1 p2.
Compute padd p4 p2.
Compute padd p2 p2.

Definition pmult : pnat->pnat->pnat := fun n m => fun T => fun f => n T ( m T f ).
Compute pmult p0 p1.
Compute pmult p2 p2.
Compute pmult p3 p2.

Definition pbool : Set := forall T : Set, T -> T -> T.
Definition ptr : pbool := fun T : Set => fun x : T => fun y : T => x.
Definition pfa :  pbool := fun T : Set => fun x : T => fun y : T => y.

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
(* La fonction prend en argument n de type pnat, m de type pnat et calcule le successeur de m, n fois *)


(*3*) 

Definition pprod (A B: Set) : Set := forall T:Set,(A->B->T)->T.
Definition pcpl (A B :Set): A->B->(pprod A B) := fun (a : A) (b : B) => fun T => fun k :(A->B->T) => k a b.
Definition frst (A B :Set) : (pprod A B) -> A:= fun p => p A (fun (x : A) (y : B) => x).
Compute frst pnat pnat (pcpl pnat pnat p3 p4).
Compute frst pbool pnat (pcpl pbool pnat ptr p4).
Compute frst pnat pbool (pcpl pnat pbool p3 pfa).

Definition scnd (A B :Set) : (pprod A B) -> B:= fun p => p B (fun (x : A) (y : B) => y).
Compute scnd pnat pnat (pcpl pnat pnat p3 p4).
Compute scnd pbool pnat (pcpl pbool pnat ptr p4).
Compute scnd pnat pbool (pcpl pnat pbool p3 pfa).
(*Definition cpred1 := \c· cpl (snd c) (csucc (snd c)).*)
(*Definition ppred1*)



