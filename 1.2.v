(*
Noel-Lardin Thomas
Turki Sanekli Hedi
*)

(**********************************************************
*                         Partie 1                        *
***********************************************************)

(* -------------- Lambda calcul simplement typé ----------------*)
Section type_booleen.
Variable T: Set.
Variable E F:T.
Definition cbool := T -> T -> T.
Definition cnat := (T->T) -> T->T.

(* # 1 #*)
(* Définition des Booléens *)
Definition ctr : cbool := fun x y => x. (* TRUE *)
Definition cfa : cbool := fun x y => y. (* FALSE *)
Compute ctr E F.
Compute cfa E F.

(* # 2 #*)
(* Définition de la contion if *)
Definition cif : cbool -> T -> T -> T := fun c : cbool => fun x y => c x y.
Compute (cif ctr E F).
Compute (cif cfa E F).

(* Définition de la négation *)
Definition cnot : cbool->cbool := fun b : cbool => fun x y => cif b y x.
Compute(cnot ctr).
Compute(cnot cfa).

(* Définition de la contion and *)
Definition cand : cbool-> cbool->cbool := fun a b : cbool=> fun x y : T => a (b x y) y.
Compute (cand ctr cfa).
Compute (cand ctr ctr).
Compute (cand cfa cfa).
Compute (cand cfa ctr).

(* Définition de la contion or *)
Definition cor : cbool->cbool->cbool := fun a b : cbool=> fun x y : T => a x (b x y).
Compute (cor ctr cfa).
Compute (cor ctr ctr).
Compute (cor cfa cfa).
Compute (cor cfa ctr).

(* # 2 # *)
Section type_entier.

(* Définition des constantes *)
Definition c0 : cnat := fun f x => x.
Definition c1 : cnat := fun f x => f x.
Definition c2 : cnat := fun f x => f (f x).
Definition c3 : cnat := fun f x => f (f (f x)). 
Compute (c0).
Compute (c1).
Compute (c2).
Compute (c3).

(* Définition de l'opération successeur *)
Definition csucc : cnat-> cnat := fun n => fun f => fun x => f(n f x).
Compute (csucc c0).
Compute (csucc c1).
Compute (csucc c2).
Compute (csucc c3).
Compute (csucc (csucc c3)).

(* Définition de l'opération addition *)
Definition cadd : cnat->cnat->cnat := fun n m f x => n f ( m f x ).
Compute(cadd c1 c2).
Compute (cadd c3 (csucc c3)).
Compute (cadd (csucc c2) (csucc c3)).

(* Définition de l'opération multiplication *)
Definition cmult: cnat->cnat->cnat := fun n m f => n ( m f ).
Compute(cmult c2 c3).
Compute (cmult (cadd c2 c3) (csucc c1)).

(* Définition du test à 0 *)
Definition ceq0: cnat->cbool := fun n => fun x y => n (fun z => y) x.
Compute (ceq0 c0).
Compute (ceq0 c1).
Compute (ceq0 (cmult c0 (cadd c3 (cmult c2 c3)))). (* Multiplication par 0 *)
Compute (ceq0 (cmult c3 (cadd c3 (cmult c2 c3)))).

End type_entier.
End type_booleen.

