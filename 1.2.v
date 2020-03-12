Section type_booleen.
Variable T: Set.
Definition cbool := T -> T -> T.
Definition cnat := (T->T) -> T->T.

Definition ctr : cbool := fun x y => x.

Definition cfa : cbool := fun x y => y.

Definition cif : cbool -> T -> T -> T := fun c : cbool => fun x y => c x y.
Variable E F:T.
Compute (cif ctr E F).
Compute (cif cfa E F).

Definition cnot : cbool->cbool := fun b : cbool => fun x y => cif b y x.
Compute(cnot ctr).
Compute(cnot cfa).

Definition cand : cbool-> cbool->cbool := fun a b : cbool=> fun x y : T => a (b x y) y.
Compute (cand ctr cfa).
Compute (cand ctr ctr).
Compute (cand cfa cfa).
Compute (cand cfa ctr).

Definition cor : cbool->cbool->cbool := fun a b : cbool=> fun x y : T => a x (b x y).
Compute (cor ctr cfa).
Compute (cor ctr ctr).
Compute (cor cfa cfa).
Compute (cor cfa ctr).

Section type_entier.

Definition c0 : cnat := fun f x => x.
Definition c1 : cnat := fun f x => f x.
Definition c2 : cnat := fun f x => f (f x).
Definition c3 : cnat := fun f x => f (f (f x)). 
Compute (c0).
Compute (c1).
Compute (c2).
Compute (c3).

Definition csucc : cnat-> cnat := fun n => fun f => fun x => f(n f x).
Compute (csucc c0).
Compute (csucc c1).
Compute (csucc c2).
Compute (csucc c3).

Definition cadd : cnat->cnat->cnat := fun n m f x => n f ( m f x ).
Compute(cadd c1 c2).

Definition cmult: cnat->cnat->cnat := fun n m f => n ( m f ).
Compute(cmult c2 c3).

Definition ceq0: cnat->cbool := fun n => fun x y => n (fun z => y) x.
Compute (ceq0 c0).
Compute (ceq0 c1).


End type_entier.
End type_booleen.

