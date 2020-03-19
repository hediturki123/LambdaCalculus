(*
Noel-Lardin Thomas
Turki Sanekli Hedi
*)

Require Import untypedLC.
(**********************************************************
*                         Partie 1                        *
***********************************************************)

(* -------------- Lambda calcul non typé ----------------*)
(* # 1 #*)

(* Définition des Booléens *)
Definition ctr := \x y · x.       (* TRUE *)
Definition cfa := \x y · y.       (* FALSE *)
Compute show_cbn ctr.
Compute show_cbn cfa.

(* Définition des opération de base *)

Definition cif := \b m n · b m n. (* Condition if *)
Compute (show_cbn (cif ctr t f)).
Compute (show_cbn (cif cfa t f)).


Definition cand := \a b · \x y · a (b x y) y. (* Condition and *)
Compute (show_cbn (cand ctr ctr)).
Compute (show_cbn (cand ctr cfa)).
Compute (show_cbn (cand cfa cfa)).
Compute (show_cbn (cand cfa ctr)).

Definition cor := \a b · \x y · a x (b x y). (* Condition or *)
Compute (show_cbn (cor cfa cfa)).
Compute (show_cbn (cor ctr cfa)).
Compute (show_cbn (cor cfa ctr)).
Compute (show_cbn (cor ctr ctr)).

Definition cor' := \a · a a.      (* Condition or (deuxième version) *)
Compute (show_cbn (cor' cfa cfa)).
Compute (show_cbn (cor' ctr cfa)).
Compute (show_cbn (cor' cfa ctr)).
Compute (show_cbn (cor' ctr ctr)).

Definition cor_cif := \a b · \ x y · cif a x (b x y).
Compute (show_cbn (cor_cif cfa cfa)).
Compute (show_cbn (cor_cif ctr cfa)).
Compute (show_cbn (cor_cif ctr ctr)).
Compute (show_cbn (cor_cif cfa ctr)).

Definition cnot := \b · cif b cfa ctr.  (* Négation *)
Compute (show_cbn (cnot cfa)).
Compute (show_cbn (cnot ctr)).
Compute (red_cbn (cnot (cand ctr cfa))).

(* # 2 #*)
(* Définition des constantes en entier de Church *)
Definition c0 := \f x·x.          (* 0 *)
Definition c1 := \f x·f x.        (* 1 *)
Definition c2 := \f x·f( f x ).   (* 2 *)
Definition c3 := \f x·f(f(f x)).  (* 3 *)

(* Définition de l'opération: successeur *)
Definition csucc := \n f x·f(n f x).
Compute ( show_cbn (csucc c0) ).
Compute ( show_cbn (csucc c1) ).
Compute ( red_cbn (csucc c2)).
Compute (red_cbn (csucc c3)).
Compute (red_cbn (csucc ((csucc c3)))). (* successeur de 4 *)

(* Définition de l'opération: addition *)
Definition cadd := \n m f x·n f ( m f x ).
Compute ( red_cbn (cadd c0 c1) ).
Compute ( red_cbn (cadd c1 c2) ).
Compute ( red_cbn (cadd c3 (csucc (csucc c3)))). (* 3+5 *)


(* Définition de l'opération: muliplication *)
Definition cmult := \n m f·n ( m f ).
Compute ( red_cbn (cmult c2 c3)).
Compute (red_cbn (cmult (csucc c3) (csucc c3))). (* 4*4 *)
Compute (red_cbn (cmult (cadd c2 (csucc c0)) (cmult c2 c2))). (* (2+1)*2*2 *)

(* Définition du test à 0*)
Definition ceq0 :=  \n·n (\z·cfa) ctr.
Compute ( red_cbn (ceq0 c0)).
Compute ( red_cbn (ceq0 c1)).
Compute ( red_cbn (ceq0 (cmult (cadd c2 (csucc c0)) (cmult c2 c2)))).            (* (2+1)*2*2 *)
Compute ( red_cbn (ceq0 (cmult (cmult (cadd c2 (csucc c0)) (cmult c2 c2)) c0))). (* 0*(2+1)*2*2 *)

(* # 3 #*)
(* Définition du couple *)
Definition cpl := \x y k·k x y.     (* Creer un couple de deux entier de Church *)
Definition fst := \p· p (\x y·x).   (* Renvoie le premier entier de Church du couple *)
Definition snd := \p·p (\x y·y).    (* Renvoie le deuxième entier de Church du couple *)
Compute (red_cbn (fst (cpl c1 c2))).
Compute (red_cbn (snd (cpl c1 c2))).
Compute (red_cbn (fst (cpl c1 (cpl c0 c2)))).
Compute (red_cbn (snd (snd (cpl c1 (cpl c0 c2))))).

(* Définition des deux entiers de Church d'un couple *)
Definition caddc := \c·c cadd.
Compute (red_cbn (caddc (cpl c1 c2))).
Compute (red_cbn (caddc (cpl c3 (cmult c3 c3)))).

(* # 4 # *)
(* Définition de structure *)
Definition inj1 := \x z y·z x.
Definition inj2 := \x z y·y x.
Compute (red_cbn (inj1 x f g) ).
Compute (red_cbn (inj2 x f g) ).

(* Définition des fonctions *)
Definition fonc1:=\n · cmult n c2.
Definition fonc2:=\n · cnot n.
Compute (red_cbn (fonc1 c2)).
Compute (red_cbn (fonc2 ctr)).
Compute (red_cbn (inj1 c2 fonc1 fonc2)).
Compute (red_cbn (inj2 ctr fonc1 fonc2)).

(* Donnée optionnel -- BONUS -- *)
Definition Some:= inj1.
Definition None:= cfa. (* FAUX *)
Definition f1:= \x ·csucc x.
Definition f2:= c0.
Definition osucc:= \n · Some(n f1 f2).
Compute (red_cbn(osucc(Some(c2)))).
Compute (red_cbn(osucc(None))).
Compute (red_cbn(osucc(Some(cadd(cmult c2 c2) (csucc c1))))). (* (2*2)+2 *)

(* Définition de l'itérateur *)
Definition iter := \n g x· n g x .
Compute (red_cbn (iter c1 csucc c0)).
Compute (red_cbn (iter c2 csucc c0)).
Compute (red_cbn (iter c3 csucc c0)).

(* # 5 # *)
(* Définition d'une fonction qui rend le couple (y y+1) *)
Definition cpred1 := \c· cpl (snd c) (csucc (snd c)).
Compute (red_cbn (cpred1 (cpl c1 c2))).
Compute (red_cbn (cpred1 (cpl c2 c3))).

(* Définition du prédécesseur *)
Definition cpred := \n·fst(iter n cpred1 (cpl c0 c0)).
Compute (red_cbn (cpred c2)).
Compute (red_cbn (cpred c3)).
Compute (red_cbn (cpred(cmult(cadd c2 c3) c2))).

(* Definition de cpredo -- BONUS -- *)
Definition cpredo:=\n · n osucc None (\x ·x) c0.
Compute(red_cbn(cpredo c2)).
Compute(red_cbn(cpredo c3)).
Compute(red_cbn(cpredo (cmult c2 c3))).

(* # 6 # -- BONUS -- *)
(* Définition du Combinateur de point fixe *)
Definition delta := \f·\x·f(x x).
Definition Y := \f·(delta f) (delta f).

(* Definition de la factorielle *)
Definition cfonc := \r·\n·cif (ceq0 n) c1 (cmult n (r (cpred n))). (* if(n==0)then c1 else cmult(n*cfonc (n-1)) *)
Definition cfact := Y cfonc.
Compute(red_cbn(cfact c0)).
Compute(red_cbn(cfact c1)).
Compute(red_cbn(cfact c2)).
Compute(red_cbn(cfact c3)).
Compute(red_cbn(cfact (csucc c3))).





