Require Import untypedLC.
(*1.1.1*)
Definition ctr := \x y · x.
Definition cfa := \x y · y.
Definition cif := \b m n · b m n.


Compute show_cbn ctr.
Compute show_cbn cfa.
Compute (show_cbn (cif ctr t f)).
Compute (show_cbn (cif cfa t f)).


Definition cand := \a b · \x y · a (b x y) y.
Compute (show_cbn (cand ctr ctr)).
Compute (show_cbn (cand ctr cfa)).
Compute (show_cbn (cand cfa cfa)).
Compute (show_cbn (cand cfa ctr)).

Definition cor := \a b · \x y · a x (b x y).
Compute (show_cbn (cor cfa cfa)).
Compute (show_cbn (cor ctr cfa)).
Compute (show_cbn (cor cfa ctr)).
Compute (show_cbn (cor ctr ctr)).

Definition cor' := \a · a a.
Compute (show_cbn (cor' cfa cfa)).
Compute (show_cbn (cor' ctr cfa)).
Compute (show_cbn (cor' cfa ctr)).
Compute (show_cbn (cor' ctr ctr)).

Definition cor_cif := \a b · \ x y · cif a x (b x y).
Compute (show_cbn (cor_cif cfa cfa)).
Compute (show_cbn (cor_cif ctr cfa)).
Compute (show_cbn (cor_cif ctr ctr)).
Compute (show_cbn (cor_cif cfa ctr)).

Definition cnot := \b · cif b cfa ctr.
Compute (show_cbn (cnot cfa)).
Compute (show_cbn (cnot ctr)).

(*1.1.2*)
Definition c0 := \f x·x.
Definition c1 := \f x·f x.
Definition c2 := \f x·f( f x ).
Definition c3 := \f x·f(f(f x)).

Definition csucc := \n f x·f(n f x).

Compute ( show_cbn (csucc c0) ).
Compute ( show_cbn (csucc c1) ).

Definition cadd := \n m f x·n f ( m f x ).

Compute ( show_cbn (cadd c0 c1) ).
Compute ( show_cbn (cadd c1 c2) ).
Compute ( show_cbn (cadd ctr cfa )).
Compute ( show_cbn (cadd cfa ctr)).
Compute ( show_cbn (cadd c2 ctr)).
Compute ( show_cbn (cadd c2 cfa)).

Definition cmult := \n m f·n ( m f ).

Compute ( show_cbn (cmult c2 c3)).

Definition ceq0 :=  \n·n (\z·cfa) ctr.

Compute ( show_cbn (ceq0 c0)).
Compute ( show_cbn (ceq0 c1)).

Definition cpl := \x y k·k x y.
Definition fst := \p· p (\x y·x).
Definition snd := \p·p (\x y·y).

Compute (show_cbn (fst (cpl c1 c2))).

Definition caddc := \c·c cadd.

Compute (show_cbn (caddc (cpl c1 c2))).

Definition inj1 := \z y·z x.
Definition inj2 := \z y·y x.

Compute (show_cbn (inj1 f g) ).
Compute (show_cbn (inj2 f g) ).

Definition iter := \n g x· n g x .
Compute (show_cbn (iter c1 csucc c0)).
Compute (show_cbn (iter c2 csucc c0)).
Compute (show_cbn (iter c3 csucc c0)).

Definition cpred1 := \c· cpl (snd c) (csucc (snd c)).
Compute (red_cbn (cpred1 (cpl c1 c2))).
Compute (red_cbn (cpred1 (cpl c2 c3))).

Definition cpred := \n·fst(iter n cpred1 (cpl c0 c0)).
Compute (red_cbn (cpred c2)).
Compute (red_cbn (cpred c3)).

Definition delta := \f·\x·f(x x).
Definition Y := \f·(delta f) (delta f).


(*1.1.6 Factorielle*)
Definition cfonc := \r·\n·cif (ceq0 n) c1 (cmult n (r (cpred n))).
Definition cfact := Y cfonc.
Compute(red_cbn(cfact c3)).
Compute(red_cbn(cfact (csucc c3))).





