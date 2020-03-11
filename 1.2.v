(*lambda calcul simplement typé*)
(*1.2.1 booléens*)
Section type_boolean.
Variable T : Set.
Definition cbool := T->T->T.
Definition cnat := (T->T) -> T->T.
Definition ccond := T->T->T->T.
(*True*)
Definition ctr : cbool := fun x y :T => x.

Definition cfa : cbool := fun x y :T => y.
Definition cif : cbool -> cbool := fun b : cbool => fun x y : T => b x y.
Compute (cif ctr).
Compute (cif cfa).



(*operations sur les booleens*)
Definition cand : cbool -> cbool -> cbool := fun a b : cbool => fun x y : T => a (b x y) y.
Definition cor : cbool -> cbool -> cbool := fun a b : cbool => fun x y : T => a x (b x y).
Definition cnot : cbool -> cbool  := fun b : cbool => fun x y : T => b y x.

Compute (cand ctr cfa).
Compute (cand ctr ctr).
Compute (cand cfa ctr).
Compute (cand cfa cfa).

Compute (cor ctr ctr).
Compute (cor ctr cfa).
Compute (cor cfa ctr).
Compute (cor cfa cfa).

Compute (cnot ctr).
Compute (cnot cfa).



(*1.2.2 entiers naturels*)
Definition c0 : cnat := fun f x => x.
Definition c0 : cnat := fun f (f x) => f x.
Compute c0.
Definition cif : ccond := fun x y w => y.
Compute (cif ctr t f).
Compute ((cif cfa t f)).



End type_boolean.