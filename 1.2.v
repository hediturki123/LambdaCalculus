(*lambda calcul simplement typé*)
(*1.2.1 booléens*)
Section type_boolean.
Variable T : Set.
Definition cbool := T->T->T.
Definition cnat := (T->T) -> T->T.
Definition ccond := T->T->T->T.
(*True*)
Definition ctr : cbool := fun x y => x.
Definition cfa : cbool := fun x y => y.
Compute (ctr).
Compute (cfa).


(*operations sur les booleens*)
(*Definition cnot : cbool := 

*)
(*Definition cand 
Definition cnot
Definition cor 
*)
(*1.2.2 entiers naturels*)
Definition c0 : cnat := fun f x => x.
Definition c0 : cnat := fun f (f x) => f x.
Compute c0.
Definition cif : ccond := fun x y w => y.
Compute (cif ctr t f).
Compute ((cif cfa t f)).




(*Definition mult : ccond :=

Compute(add 1 2).
Compute(mult 2 3).

Definition c0 : cnat := fun x => x.


Compute c0.
Compute c1.
Compute c2.
Compute c3.

Definition succ : cnat
Compute succ.*)
End type_boolean.