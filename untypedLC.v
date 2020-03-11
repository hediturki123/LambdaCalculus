Require Export Nat.
Require Export List.
Export ListNotations.

(* Deep embedding of untyped pure lambda-calculus
   The goal is to teach lambda-calculus and experiment with
   several reduction strategies and functions (extracting
   bound or free variables, redexes, checking (strong,
   weak, head) normal forms, etc.
   The implementation is not complete nor strictly correct *)


(* To alleviate the notations we use a fixed number of variables 
   defined as constructors *)

Inductive letter : Set :=
  | a    | b    | c    | d    | e    | f
  | g    | h    | i    | j    | k    | l
  | m    | n    | o    | p    | q    | r
  | s    | t    | u    | v    | w    | x
  | y    | z
  | a1   | b1   | c1   | d1   | e1   | f1
  | g1   | h1   | i1   | j1   | k1   | l1
  | m1   | n1   | o1   | p1   | q1   | r1
  | s1   | t1   | u1   | v1   | w1   | x1
  | y1   | z1
.

Definition nat_of_letter x :=
  match x with
  | a  =>  0  | b  =>  1  | c  =>  2  | d  =>  3  | e  =>  4  | f  =>  5
  | g  =>  6  | h  =>  7  | i  =>  8  | j  =>  9  | k  => 10  | l  => 11
  | m  => 12  | n  => 13  | o  => 14  | p  => 15  | q  => 16  | r  => 17
  | s  => 18  | t  => 19  | u  => 20  | v  => 21  | w  => 22  | x  => 23
  | y  => 24  | z  => 25
  | a1 => 26  | b1 => 27  | c1 => 28  | d1 => 29  | e1 => 30  | f1 => 31
  | g1 => 32  | h1 => 33  | i1 => 34  | j1 => 35  | k1 => 36  | l1 => 37
  | m1 => 38  | n1 => 39  | o1 => 40  | p1 => 41  | q1 => 42  | r1 => 43
  | s1 => 44  | t1 => 45  | u1 => 46  | v1 => 47  | w1 => 48  | x1 => 49
  | y1 => 50  | z1 => 51
  end.

Definition letter_of_nat nn :=
  match nn with
  |  0 =>  a  |  1 =>  b  |  2 =>  c  |  3 =>  d  |  4 =>  e  |  5 =>  f
  |  6 =>  g  |  7 =>  h  |  8 =>  i  |  9 =>  j  | 10 =>  k  | 11 =>  l
  | 12 =>  m  | 13 =>  n  | 14 =>  o  | 15 =>  p  | 16 =>  q  | 17 =>  r
  | 18 =>  s  | 19 =>  t  | 20 =>  u  | 21 =>  v  | 22 =>  w  | 23 =>  x
  | 24 =>  y  | 25 =>  z
  | 26 => a1  | 27 => b1  | 28 => c1  | 29 => d1  | 30 => e1  | 31 => f1
  | 32 => g1  | 33 => h1  | 34 => i1  | 35 => j1  | 36 => k1  | 37 => l1
  | 38 => m1  | 39 => n1  | 40 => o1  | 41 => p1  | 42 => q1  | 43 => r1
  | 44 => s1  | 45 => t1  | 46 => u1  | 47 => v1  | 48 => w1  | 49 => x1
  | 50 => y1  | 51 => z1
  | _ => a (* fake *)
  end.

Definition first_letter := a.
Definition card_letter := 52.

(* *)

Inductive Name : Set :=
| Lett : letter -> Name
| Prime : Name -> Name
.

Coercion Lett: letter >-> Name.

Notation "X °" := (Prime X) (at level 1, format "X °").

Fixpoint nat_of_Name nn :=
  match nn with
  | Lett xx => nat_of_letter xx
  | Prime nn => card_letter + nat_of_Name nn
  end.

Definition eqb_Name ax ay : bool := eqb (nat_of_Name ax) (nat_of_Name ay).

(* Fresh names *)

Definition rot_nat n :=
    if eqb (S n) card_letter then O else S n.

Definition rot_letter x := letter_of_nat (rot_nat (nat_of_letter x)).

Fixpoint next_name nn :=
  match nn with
  | Lett xx =>
    let rn := rot_nat (nat_of_letter xx) in
    match rn with
    | O => Prime first_letter
    | _ => Lett (letter_of_nat rn)
    end
  | Prime nn => Prime (next_name nn)
  end.

Fixpoint gen_names {A: Type} (ll : list A) n : list Name :=
  match ll with
  | [] => [n]
  | _ :: ll => n :: gen_names ll (next_name n)
  end.

(* Remove all ax in ll, returns None if ax not in ll *)

Fixpoint mayrem (ax:Name) (ll:list Name) : option (list Name) :=
  match ll with
  | [] => None
  | ax1 :: lls =>
    match mayrem ax lls with
    | None => if eqb_Name ax ax1 then Some lls else None
    | Some lls' => if eqb_Name ax ax1 then Some lls' else Some (ax1 :: lls')
    end
  end.

(* remove a name in a list of names *)

(* lavoid <= lstruct in some sense (size, or injection)
   result not in lavoid
*)
Fixpoint fresh_1 (cand:Name) (lavoid lstruct: list Name) : Name :=
  match lstruct with
  | [] => cand
  | _ :: lstruct' => match mayrem cand lavoid with
                     | None => cand
                     | Some lavoid' => fresh_1 (next_name cand) lavoid' lstruct'
                     end
  end.

Definition fresh (avoid:list Name) : Name := fresh_1 first_letter avoid avoid.

(* ------------------------------------------------------------ *)

(* Syntax of lambda expressions *)

Inductive lexp : Type :=
  | Var : Name -> lexp
  | Lam : Name -> lexp -> lexp
  | App : lexp -> lexp -> lexp.

(* Notations
   \x y.x y is written \x y:x y   *)

Notation "\ x .. y ~ M" := (Lam x .. (Lam y M) ..)
   (at level 30, x at level 0, y at level 0, right associativity).
Notation "\ x .. y · M" := (Lam x .. (Lam y M) ..)
   (at level 30, x at level 0, y at level 0, right associativity).
Notation "'λ' x .. y · M" := (Lam x .. (Lam y M) ..)
   (at level 30, x at level 0, y at level 0, right associativity).

Coercion Var: Name >-> lexp.

Coercion App: lexp >-> Funclass.

(*
Lemma Name_eq_dec : forall ax ay:Name, {ax = ay} + {ax <> ay}.
Proof.
intros. destruct ax; destruct ay; try (right; easy); left; easy.
Qed.

Definition eqb_Name ax ay : bool :=
match Name_eq_dec ax ay with
| left _  => true
| right _ => false
end.
*)

(* member function in list of names *)

Fixpoint mem (ax:Name) (xx:list Name) : bool :=
  match xx with
  | [] => false
  | ax1 :: xxs => if eqb_Name ax ax1 then true else mem ax xxs
  end.

(* remove a name in a list of names *)

Fixpoint rem (ax:Name) (xx:list Name) : list Name :=
  match xx with
  | [] => []
  | ax1 :: xx1 => if eqb_Name ax ax1 then rem ax xx1
                  else ax1 :: rem ax xx1
  end.

(* remove duplicates in a list of names *)

Fixpoint make_set xx : list Name :=
  match xx with
  | [] => []
  | ax :: xx1 => if mem ax xx1 then make_set xx1
                 else ax :: (make_set xx1)
  end.

(* intersection of two list of names *)

Fixpoint inter_1 xx yx : list Name :=
  match xx with
  | [] => []
  | ax :: xx1 => if mem ax yx then ax :: inter_1 xx1 yx
                 else inter_1 xx1 yx
  end.

Definition inter xx yx : list Name := inter_1 (make_set xx) yx.

(* returns all names used in a lexp *)

Fixpoint allvars ex : list Name :=
  match ex with
  | Var nx => [nx]
  | Lam nx ex => nx :: (allvars ex)
  | App ex1 ex2 => allvars ex1 ++ allvars ex2
  end.

Definition vars ex := make_set (allvars ex).

(* returns all variables with a free occurrence in a lexp *)

Fixpoint freevars ex : list Name :=
  match ex with
  | Var nx => [nx]
  | Lam nx ex => rem nx (freevars ex)
  | App ex1 ex2 => freevars ex1 ++ freevars ex2
  end.

Definition vlibres ex := make_set (freevars ex).

(* returns all variables with a bound occurrence in a lexp *)

Fixpoint boundvars ex : list Name :=
  match ex with
  | Var nx => []
  | Lam nx ex => if mem nx (freevars ex) then nx :: (boundvars ex)
                 else boundvars ex
  | App ex1 ex2 => boundvars ex1 ++ boundvars ex2
  end.

Definition vliees ex := make_set (boundvars ex).

Fixpoint declaredvars ex : list Name :=
  match ex with
  | Var nx => []
  | Lam nx ex => nx :: (declaredvars ex)
  | App ex1 ex2 => declaredvars ex1 ++ declaredvars ex2
  end.

Definition vdef ex := make_set (declaredvars ex).

(** Replace all free occurrences of [Var ny] by [Var nz] in [ex].
   Used with the hypothesis that [nz] does not occur in [ex]. *)

Fixpoint rename ny nz ex: lexp :=
  match ex with
  | Var nx      => if eqb_Name nx ny then Var nz else ex
  | Lam nx ex1  => if eqb_Name nx ny then ex else
                     Lam nx (rename ny nz ex1)
  | App ex1 ex2 => App (rename ny nz ex1) (rename ny nz ex2)
  end.

(** Change all bound occurrences of [Var ny] by [Var nz] in [ex].
   Used with the hypothesis that [nz] does not occur in [ex]. *)

Fixpoint alpha ny nz ex: lexp :=
  match ex with
  | Var nx      => Var nx
  | Lam nx ex1  => let ex2 := alpha ny nz ex1 in
                   if eqb_Name nx ny then Lam nz (rename nx nz ex2)
                   else Lam nx ex2
  | App ex1 ex2 => App (alpha ny nz ex1) (alpha ny nz ex2)
  end.

(* Renaming of all bound variable of a lexp which also occur in fv *)

(* (* Old buggy version which repeats the computation of the same fresh name *)
Fixpoint renaming fv all ex :=
match fv with
| [] => ex
| fx :: fvs => renaming fvs all (alpha fx (fresh all) ex)
end.
 *)

Fixpoint renaming fv avoid ex :=
  match fv with
  | [] => ex
  | fx :: fvs =>
    let freshname := fresh avoid in
    renaming fvs (freshname :: avoid) (alpha fx freshname ex)
  end.

(* straightforward substitution ex1[z:=ex2] *)

Fixpoint subst_1 nz ex2 ex1: lexp :=
  match ex1 with
  | Var nx        => if eqb_Name nx nz then ex2 else ex1
  | Lam nx ex     => if eqb_Name nx nz then ex1
                     else Lam nx (subst_1 nz ex2 ex)
  | App ex11 ex12 => App (subst_1 nz ex2 ex11) (subst_1 nz ex2 ex12)
  end.

(* substitution ex1[nx:=ex2] avoiding capture using prior renaming *)

Definition subst nx ex2 ex1 : lexp :=
  let vx := inter (vdef ex1) (vlibres ex2) in
  let avoid := allvars ex1 in
  subst_1 nx ex2 (renaming vx avoid ex1).

(* Return the list of redexes of an expression *)
(* JF : il faut en plus les repérer par leur lieu d'occurrence *)

Fixpoint redexes  ex : list lexp :=
  match ex with
  | Var nx             => []
  | App (Lam nx tx) rx => (App (Lam nx tx) rx) :: (redexes tx ++ redexes rx)
  | App lx rx          => redexes lx ++ redexes rx
  | Lam nx tx          => redexes tx
  end.

(* Occurrences *)
Inductive occ : Set :=
| Ici
| UL : occ -> occ (* sous Lam *)
| LA : occ -> occ (* Gauche App  *)
| RA : occ -> occ (* Droite App  *)
.

(* *)

Fixpoint no_UL oc : bool :=
  match oc with
  | Ici => true
  | UL _ => false
  | LA oc => no_UL oc
  | RA oc => no_UL oc
  end.

(* *)

(* Something at an occurrence *)
Definition smtg_occ chk oc ex : Prop :=
  (fix aux oc ex : Prop :=
     match oc, ex with
     | Ici, _ => chk ex
     | UL oc, Lam _ tx => aux oc tx
     | LA oc, App lx rx => aux oc lx
     | RA oc, App lx rx => aux oc rx
     | _, _ => False
     end) oc ex.

Definition anyterm (ex : lexp) := True.
(* redex at root *)
Definition rar (ex : lexp) :=
  match ex with
  | App (λ _ · _) _ => True
  | _ => False
  end.
(* free var at root *)
Definition fvr (nx: Name) (ex : lexp) :=
  match ex with
  | Var ny => if eqb_Name nx ny then True else False
  | _ => False
  end.

Definition has_occ := smtg_occ anyterm.
Definition has_red := smtg_occ rar.

Lemma has_occ_UL_LA {ex oc1 oc2} : has_occ (UL oc1) ex -> has_occ (LA oc2) ex -> False.
Proof. destruct ex; intros; assumption. Qed.

Lemma has_occ_UL_RA {ex oc1 oc2} : has_occ (UL oc1) ex -> has_occ (RA oc2) ex -> False.
Proof. destruct ex; intros; assumption. Qed.

Fixpoint subterm_at ex oc : has_occ oc ex -> lexp :=
     match oc, ex return has_occ oc ex -> lexp with
     | Ici, _ => fun oec => ex
     | UL oc, Lam _ tx => fun oec => subterm_at tx oc oec
     | LA oc, App lx rx => fun oec => subterm_at lx oc oec
     | RA oc, App lx rx => fun oec => subterm_at rx oc oec
     | _, _ => fun oec => match oec with end
     end.

Definition rewrite_at (chk : lexp -> Prop) (rewf: forall ex, chk ex -> lexp)
                      ex oc (oec : smtg_occ chk oc ex) : lexp :=
 (fix rew_at ex oc : smtg_occ chk oc ex -> lexp :=
     match oc, ex return smtg_occ chk oc ex -> lexp with
     | Ici, _ => fun oec => rewf ex oec
     | UL oc, Lam vx tx => fun oec => Lam vx (rew_at tx oc oec)
     | LA oc, App lx rx => fun oec => App (rew_at lx oc oec) rx
     | RA oc, App lx rx => fun oec => App lx (rew_at rx oc oec)
     | _, _ => fun oec => match oec with end
     end) ex oc oec.

(*
Definition rewrite_at (rewf: lexp -> lexp) ex oc (oec : has_occ oc ex) : lexp :=
 (fix rew_at ex oc : has_occ oc ex -> lexp :=
     match oc, ex return has_occ oc ex -> lexp with
     | Ici, _ => fun oec => rewf ex
     | UL oc, Lam vx tx => fun oec => Lam vx (rew_at tx oc oec)
     | LA oc, App lx rx => fun oec => App (rew_at lx oc oec) rx
     | RA oc, App lx rx => fun oec => App lx (rew_at rx oc oec)
     | _, _ => fun oec => match oec with end
     end) ex oc oec.
*)
(* Guarded occurences *)
Inductive gocc_of (chk : lexp -> Prop) ex : Set :=
  o_o : forall oc, smtg_occ chk oc ex -> gocc_of chk ex.
Definition occ_of := gocc_of anyterm.
Definition rocc_of := gocc_of rar.
Definition lift_test (f: occ -> bool) chk ex (go : gocc_of chk ex) : bool :=
  let (oc, _) := go in f oc.

(* *)
Lemma smtg_occ_impl (chk1 chk2 : lexp -> Prop) :
  (forall ex, chk1 ex -> chk2 ex) -> forall oc ex, smtg_occ chk1 oc ex -> smtg_occ chk2 oc ex.
Proof.
  intro chch.
  refine 
  (fix aux oc ex : _ :=
     match oc, ex with
     | Ici, _ => chch ex
     | UL oc, Lam _ tx => aux oc tx
     | LA oc, App lx rx => aux oc lx
     | RA oc, App lx rx => aux oc rx
     | _, _ => fun F => F
     end); simpl.
Defined.    

Lemma gocc_impl (chk1 chk2 : lexp -> Prop) :
  (forall ex, chk1 ex -> chk2 ex) -> forall ex, gocc_of chk1 ex -> gocc_of chk2 ex.
Proof.
  intros chch ex [oc Hoc]. exists oc. apply (smtg_occ_impl _ _ chch _ _ Hoc).
Defined.

Lemma rocc_occ {ex} : rocc_of ex -> occ_of ex.
Proof.
  apply (gocc_impl rar anyterm).
  clear ex. intros ex _. exact I.
Defined.

(* Term at a guarded occurence *)
Definition subterm_at_g ex (oe : occ_of ex) : lexp :=
  let (oc, oec) := oe in subterm_at ex oc oec.
Definition subterm_at_gr ex (oe : rocc_of ex) : lexp :=
  subterm_at_g ex (rocc_occ oe).

Definition rewrite_at_g chk rewf ex (oe : gocc_of chk ex) : lexp :=
  let (oc, oec) := oe in rewrite_at chk rewf ex oc oec.

Definition root_subst ex : rar ex -> lexp :=
  match ex with
  | App (λ nx · body) actualp => fun _ => subst nx actualp body
  | _ => fun F => match F with end
  end.

(* Applies a substitution at a (guaranteed) occurrence of a redex *)
Definition beta_at : forall ex, rocc_of ex -> lexp := rewrite_at_g rar root_subst.


(* *)


Definition lift1 (f: occ -> occ) (g: lexp -> lexp) :
  (forall oc ex, has_red oc ex -> has_red (f oc) (g ex)) ->
  (forall ex, rocc_of ex -> rocc_of (g ex)).
  intros transf ex [oc eoc].
  exists (f oc). apply (transf oc ex eoc).
Defined.

Definition same_eoc oc ex (eoc : has_red oc ex) := eoc.

Definition lift1_UL nx := lift1 UL (fun ex => λ nx· ex) same_eoc :
   forall ex, rocc_of ex -> rocc_of (λ nx· ex).
Definition lift1_LA rx := lift1 LA (fun lx => App lx rx) same_eoc :
   forall lx, rocc_of lx -> rocc_of (App lx rx).
Definition lift1_RA lx := lift1 RA (fun rx => App lx rx) same_eoc :
   forall rx, rocc_of rx -> rocc_of (App lx rx).

Fixpoint occredexes_of ex : list (rocc_of ex) :=
  match ex with
  | Var nx             => []
  | Lam nx tx          => map (lift1_UL nx tx) (occredexes_of tx)
  | App lx rx =>
    let orl := map (lift1_LA rx lx) (occredexes_of lx) in
    let orr := map (lift1_RA lx rx) (occredexes_of rx) in
    match lx return list (rocc_of (App lx rx)) -> _ with
    | (\nx· tx) => cons (o_o rar ((\nx· tx) rx) Ici I)
    | _ => fun olrx => olrx
    end (orl ++ orr)
  end.

(* For interactive use : pos_redexes, see_redex, red_beta *)

Definition map2 {A B C} (f: B -> C) : list (A*B) -> list (A*C) :=
   map (fun xy:A*B => let (x,y) := xy in (x, f y)).

(* Numbered occurrences *)
Fixpoint nbd_occ_of ex n : nat * list (nat * rocc_of ex) :=
  match ex with
  | Var nx             => (n, [])
  | Lam nx tx          =>
    let (n', l) := nbd_occ_of tx (S n) in 
    (n', map2 (lift1_UL nx tx) l)
  | App lx rx =>
    let (n1, l1) := nbd_occ_of lx n in
    let (n2, l2) := nbd_occ_of rx n1 in
    let orl := map2 (lift1_LA rx lx) l1 in
    let orr := map2 (lift1_RA lx rx) l2 in
    (n2, match lx return list (nat * rocc_of (App lx rx)) -> _ with
         | λ nx· tx => cons (n, o_o rar ((λ nx· tx) rx) Ici I)
         | _ => fun olrx => olrx
         end (orl ++ orr))
  end.

Definition nbd_occredexes_of ex : list (nat * rocc_of ex) :=
  let (_, l ) := nbd_occ_of ex 1 in l.

Definition lift_fct_nb {A} (f : occ -> A) ex (nro : nat * rocc_of ex) : A :=
  let (_ , ro) := nro in let (oc, _) := ro in
  f oc.                                                  

Definition lift_cmp_nb {A} (cmp : occ -> occ -> A) ex (nro1 nro2 : nat * rocc_of ex) : A :=
  let (_ , ro1) := nro1 in let (oc1, _) := ro1 in
  let (_ , ro2) := nro2 in let (oc2, _) := ro2 in
  cmp oc1 oc2.                                                  

Definition pos_redexes ex : list nat := map fst (nbd_occredexes_of ex).
Definition pos_redexes_noUL ex : list nat :=
  let nroex := nbd_occredexes_of ex in
  let nroex_noUL := filter (lift_fct_nb no_UL ex) nroex in
  map fst nroex_noUL.

Definition wrg_nb : lexp := (w r o n g) (n u m b e r).

Definition see_redex nn1 ex : lexp :=
  (fix loop lno := 
  match lno with
  | [] => wrg_nb
  | (nn2, ro) :: lno => if eqb nn1 nn2 then subterm_at_gr ex ro else loop lno
  end) (nbd_occredexes_of ex).

Definition red_beta nn1 ex : lexp :=
  (fix loop lno := 
  match lno with
  | [] => wrg_nb
  | (nn2, ro) :: lno => if eqb nn1 nn2 then beta_at ex ro else loop lno
  end) (nbd_occredexes_of ex).


(* ********************** Comparisons between redexes ********************** *)

Definition morph (f: occ -> occ) (R: occ -> occ -> Prop) : Prop :=
  forall oc1 oc2, R oc1 oc2 -> R (f oc1) (f oc2).

Inductive more_outer : occ -> occ -> Prop :=
| mo_Ici : forall oc, more_outer Ici oc
| mo_mUL : morph UL more_outer
| mo_mLA : morph LA more_outer
| mo_mRA : morph RA more_outer
.

Definition more_inner oc1 oc2 := more_outer oc2 oc1.

Lemma more_outer_refl : forall oc, more_outer oc oc.
Proof.
  induction oc as [ | ex Hex | ex Hex | ex Hex].
  - apply mo_Ici.
  - apply mo_mUL; apply Hex.
  - apply mo_mLA; apply Hex.
  - apply mo_mRA; apply Hex.
Qed.

(* transitive (then partial pre-order) *)
Lemma more_outer_trans :
  forall oc1 oc2 oc3,
  more_outer oc1 oc2 -> more_outer oc2 oc3 -> more_outer oc1 oc3.
Proof.
  intros * lo12. revert oc3.
  induction lo12 as [oc | oc1 oc2 lo12 Hlo12 | oc1 oc2 lo12 Hlo12 | oc1 oc2 lo12 Hlo12];
    intros oc3 lo13. 
  - inversion lo13; clear lo13; subst; apply mo_Ici.
  - inversion lo13; clear lo13; subst. apply mo_mUL. apply Hlo12; assumption.
  - inversion lo13; clear lo13; subst. apply mo_mLA. apply Hlo12; assumption.
  - inversion lo13; clear lo13; subst. apply mo_mRA. apply Hlo12; assumption.
Qed.

(* transitive (then partial pre-order) on occurrences of a given lexp *)
Lemma more_outer_trans_complicated :
  forall oc1 oc2 oc3 ex,
  has_occ oc1 ex -> has_occ oc2 ex -> has_occ oc3 ex ->
  more_outer oc1 oc2 -> more_outer oc2 oc3 -> more_outer oc1 oc3.
Proof.
  intros * ho1 ho2 ho3 lo12. revert oc3 ex ho1 ho2 ho3.
  induction lo12 as [oc | oc1 oc2 lo12 Hlo12 | oc1 oc2 lo12 Hlo12 | oc1 oc2 lo12 Hlo12];
    intros oc3 ex ho1 ho2 ho3 lo13.
  - inversion lo13; clear lo13; subst; apply mo_Ici.
  - inversion lo13; clear lo13; subst. apply mo_mUL.
    destruct ex as [ |nx ex | ]; try (case ho1).
    apply Hlo12 with (ex:=ex); assumption.
  - inversion lo13; clear lo13; subst. apply mo_mLA.
    destruct ex as [ |nx ex | ]; try (case ho1).
    apply Hlo12 with (ex:=ex1); assumption.
  - inversion lo13; clear lo13; subst. apply mo_mRA.
    destruct ex as [ |nx ex | ]; try (case ho1).
    apply Hlo12 with (ex:=ex2); assumption.
Qed.

(* Ad-hoc mais a l'air de marcher. Laissé pour le test mais À VIRER + tard *)
Fixpoint mlob oc1 oc2 : bool :=
  match oc1, oc2 with
  | Ici, LA (UL _) => true
  | LA _, Ici => true
  | LA _, RA _ => true
  | Ici, RA _ => true
  | Ici, UL _ => true
  | UL oc1, UL oc2 => mlob oc1 oc2
  | LA oc1, LA oc2 => mlob oc1 oc2
  | RA oc1, RA oc2 => mlob oc1 oc2
  |  _, _ => false
  end.

(* For partial ordering *)
Inductive pcomp : Set := Pe | Pl | Pg | Pn (* not comparable *).

(* outermost - innermost *)
Fixpoint oi oc1 oc2 : pcomp :=
  match oc1, oc2 with
  | Ici, Ici => Pe
  | Ici, _ => Pl
  | _, Ici => Pg
  | UL oc1, UL oc2 => oi oc1 oc2
  | LA oc1, LA oc2 => oi oc1 oc2
  | RA oc1, RA oc2 => oi oc1 oc2
  |  _, _ => Pn
  end.

(* leftmost - rightmost *)
Fixpoint lr oc1 oc2 : comparison :=
  match oc1, oc2 with
  | Ici, Ici => Eq
  | Ici, UL _ => Lt
  | UL _, Ici => Gt
  | UL oc1, UL oc2 => lr oc1 oc2
  | LA oc1, LA oc2 => lr oc1 oc2
  | RA oc1, RA oc2 => lr oc1 oc2
  | LA _, _ => Lt
  | _, LA _ => Gt
  | RA _, _ => Gt
  | _, RA _ => Lt
  end.

(* Pour l'honneur : sans discrminate *)
Lemma oi_eq : forall oc1 oc2, oi oc1 oc2 = Pe -> oc1 = oc2.
Proof.
  pose (discr (oc1 oc2 : occ) x := match x with Pe => oc2 | _ => oc1 end).
  exact (
      fix loop oc1 oc2 : _ :=
        match oc1, oc2 with
        | Ici, Ici => fun e => eq_refl
        | UL oc1, UL oc2 => fun e => f_equal UL (loop oc1 oc2 e)
        | LA oc1, LA oc2 => fun e => f_equal LA (loop oc1 oc2 e)
        | RA oc1, RA oc2 => fun e => f_equal RA (loop oc1 oc2 e)
        | oc1, oc2 => fun e => f_equal (discr oc1 oc2) e
        end).
Qed.

(* leftmore outermore (strict) *)
Definition strict_le_ou oc1 oc2 : bool :=
  match oi oc1 oc2 with
    | Pe => false
    | Pl => true
    | Pg => false
    | Pn => match lr oc1 oc2 with
              | Eq => false
              | Lt => true
              | Gt => false
            end
  end.

(* OK for the next : 
   problematic cases are meaningless for occurrences of redexes in an actual lexp *)
Lemma mlob_sameas_strict_le_ou :
  forall oc1 oc2 ex, has_red oc1 ex -> has_red oc2 ex -> mlob oc1 oc2 = strict_le_ou oc1 oc2.
Proof.
Abort. 

(* le_ou yields a total order ; anyway only different occurrences will be compared *)
(*
(* Direct version with an artificial excahnge of args in innermost *)
Definition horizontal_obsol := occ -> occ -> bool.
Definition vertical_obsol := horizontal_obsol -> occ -> occ -> bool.
Definition outermost_obsol : vertical_obsol := fun k oc1 oc2 =>
    match oi oc1 oc2 with
    | Pe => true
    | Pl => true
    | Pg => false
    | Pn => k oc1 oc2
    end.
Definition innermost_obsol : vertical_obsol :=
  fun k oc1 oc2 => outermost_obsol (fun oc2 oc1 => k oc1 oc2) oc2 oc1.

Definition leftmost_obsol : horizontal_obsol := fun oc1 oc2 =>
    match lr oc1 oc2 with
    | Eq => true
    | Lt => true
    | Gt => false
    end.

Definition rightmost_obsol : horizontal_obsol := fun oc1 oc2 => leftmost_obsol oc2 oc1.
                                        
Definition strategy (h: horizontal_obsol) (v: vertical_obsol) := v h.

Definition le_ou_obsol := strategy leftmost_obsol outermost_obsol.
Definition ri_ou_obsol := strategy rightmost_obsol outermost_obsol.
Definition le_in_obsol := strategy leftmost_obsol innermost_obsol.
Definition ri_in_obsol := strategy rightmost_obsol innermost_obsol.
*)

(* CPS version, with a unit -> to keep lazyness in cbv (pour l'honneur) *)
Definition horizontal := occ -> occ ->  ((unit -> bool) -> bool) -> bool.
Definition vertical := occ -> occ -> ((unit -> bool) -> bool).

Definition outermost : vertical := fun oc1 oc2 =>
    match oi oc1 oc2 with
    | Pe => fun _ => true
    | Pl => fun _ => true
    | Pg => fun _ => false
    | Pn => fun b => b tt
    end.

Definition leftmost : horizontal := fun oc1 oc2 =>
    fun k => k (fun _ =>
    (match lr oc1 oc2 with
    | Eq => true
    | Lt => true
    | Gt => false
    end)).

Definition le_ou oc1 oc2 := leftmost oc1 oc2 (outermost oc1 oc2).
Definition ri_ou oc1 oc2 := leftmost oc2 oc1 (outermost oc1 oc2).
Definition le_in oc1 oc2 := leftmost oc1 oc2 (outermost oc2 oc1).
Definition ri_in oc1 oc2 := leftmost oc2 oc1 (outermost oc2 oc1).

(*
(* The 2 versions are equivalent *)
Lemma verif_le_ou oc1 oc2 : le_ou oc1 oc2 = le_ou_obsol oc1 oc2.
Proof.
  unfold le_ou, le_ou_obsol. unfold strategy, outermost, outermost_obsol.
  destruct (oi oc1 oc2); reflexivity.
Qed.

Lemma verif_ri_ou oc1 oc2 : ri_ou oc1 oc2 = ri_ou_obsol oc1 oc2.
Proof.
  unfold ri_ou, ri_ou_obsol. unfold strategy, outermost, outermost_obsol.
  destruct (oi oc1 oc2); reflexivity.
Qed.

Lemma verif_ri_in oc1 oc2 : ri_in oc1 oc2 = ri_in_obsol oc1 oc2.
Proof.
  unfold ri_in, ri_in_obsol. unfold strategy, outermost, innermost_obsol, leftmost, outermost_obsol.
  destruct (oi oc2 oc1); reflexivity.
Qed.

Lemma verif_le_in oc1 oc2 : le_in oc1 oc2 = le_in_obsol oc1 oc2.
Proof.
  unfold le_in, le_in_obsol. unfold strategy, outermost, innermost_obsol, leftmost, outermost_obsol.
  destruct (oi oc2 oc1); reflexivity.
Qed.
 *)

(* *)

Definition min {A} (cmp : A -> A -> bool) x y := if cmp x y then x else y.

Fixpoint minlist1 {A} (cmp : A -> A -> bool) x l : A :=
  match l with
  | [] => x
  | x' :: l' => min cmp x (minlist1 cmp x' l')
  end.

Definition non_empty {A} (l: list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => True
  end.

Definition depres {A} (l: list A) : Type :=
  match l with
  | [] => list A
  | x' :: l' => A * list A
  end.

Definition minlistdep {A} (cmp : A -> A -> bool) l : depres l :=
  match l with
  | [] => l
  | x' :: l' => (minlist1 cmp x' l', l)
  end.

Definition hdtl {A} (l: list A) : non_empty l -> A * list A :=
  match l with
  | [] => fun F => match F with end
  | x' :: l' => fun _ => (x', l')
  end.

Definition minlist {A} (cmp : A -> A -> bool) l : non_empty l -> A :=
  match l with
  | [] => fun F => match F with end
  | x' :: l' => fun _ => minlist1 cmp x' l'
  end.

(* ********************** The different types of normal forms ********************** *)

(* Check if an expression is under (strong) normal form
   N :::= λx. N | x N1 N2 .. Nn *)

Fixpoint fnorm  ex : bool :=
  match ex with
  | Var nx             => true
  | App (Lam nx tx) rx => false
  | App lx rx          => (fnorm lx) && (fnorm rx)
  | Lam nx tx          => fnorm tx
  end.

(* Check if an expression is under weak normal form
   W :::= λx. e | x W1 W2 .. Wn *)

Fixpoint is_wnf  ex : bool :=
  match ex with
  | Var nx             => true
  | Lam nx tx          => true
  | App (Lam nx tx) rx => false
  | App lx rx          => (is_wnf lx) && (is_wnf rx)
  end.

(* Check if an expression is under head normal form
   H :::= λx. H | x e1 e2 .. en *)

Fixpoint is_hnf  ex : bool :=
  match ex with
  | Var nx             => true
  | App (Lam nx tx) rx => false
  | App lx rx          => is_hnf lx
  | Lam nx tx          => is_hnf tx
  end.

(* Check if an expression is under weak head normal form
   WH :::= λx. e | x e1 e2 .. en *)

Fixpoint is_whnf  ex : bool :=
  match ex with
  | Var nx             => true
  | Lam nx tx          => true
  | App (Lam nx tx) rx => false
  | App lx rx          => is_whnf lx
  end.

(* ****************** The different reduction strategies ******************* *)

(* One step leftmost outermost beta-reduction *)

Fixpoint red1_lo ex : option lexp :=
  match ex with
  | App (Lam nx ex1) ex2 => Some (subst nx ex2 ex1)
  | App ex1 ex2          => match (red1_lo ex1) with
                            | None => match (red1_lo ex2) with
                                      | None => None
                                      | Some ex2' => Some (App ex1 ex2')
                                      end
                            | Some ex1' => Some (App ex1' ex2)
                            end
  | Lam nx ex1          => match (red1_lo ex1) with
                           | None => None
                           | Some ex1' => Some (Lam nx ex1')
                           end
  | _ => None
  end.

(* One step weak leftmost outermost beta-reduction *)

Fixpoint red1_low ex : option lexp :=
  match ex with
  | App (Lam nx ex1) ex2 => Some (subst nx ex2 ex1)
  | App ex1 ex2          => match (red1_low ex1) with
                            | None =>  None
                            | Some ex1' => Some (App ex1' ex2)
                            end
  | _ => None
  end.

(* One step rightmost outermost beta-reduction *)

Fixpoint red1_ro ex : option lexp :=
  match ex with
  | App (Lam nx ex1) ex2 =>  match (red1_ro ex2) with
                             | None      => Some (subst nx ex2 ex1)
                             | Some ex2' => Some (App (Lam nx ex1) ex2')
                             end
                               
  | App ex1 ex2          => match (red1_ro ex2) with
                            | None => match (red1_ro ex1) with
                                      | None => None
                                      | Some ex1' => Some (App ex1' ex2)
                                      end
                            | Some ex2' => Some (App ex1 ex2')
                            end
  | Lam nx ex1          => match (red1_lo ex1) with
                           | None => None
                           | Some ex1' => Some (Lam nx ex1')
                           end
  | _ => None
  end.

(* One step weak rightmost outermost beta-reduction *)

Fixpoint red1_row ex : option lexp :=
  match ex with
  | App (Lam nx ex1) ex2 =>  match (red1_row ex2) with
                             | None      => Some (subst nx ex2 ex1)
                             | Some ex2' => Some (App (Lam nx ex1) ex2')
                             end
                               
  | App ex1 ex2          => match (red1_row ex2) with
                            | None => match (red1_row ex1) with
                                      | None => None
                                      | Some ex1' => Some (App ex1' ex2)
                                      end
                            | Some ex2' => Some (App ex1 ex2')
                            end
  | _ => None
  end.

(* One reduction step by the one step reduction function rs *)

Definition red1 rs ex : lexp :=
  match rs ex with
  | None => ex
  | Some ex' => ex'
  end.

(* Expression denoting an out of bound computation *)
Definition toolong := \a b o r t·(t o o) (l o n g).

(* Reduction by rs until normal form (bounded by nx steps) *)

Fixpoint redn rs nx ex : lexp :=
  match nx with
  | 0    => toolong
  | S nx => match rs ex with
         | None => ex
         | Some ex' => redn rs nx ex'
            end
  end.

(* ====================================================================== *)
(* Reduction sequences, represented by vide/step lists of
  - a lexp E
  - the list lr of occurrences of all redexes (number for readability) in E
  - the list lw of occurrences of weak redexes (number for readability) in E
  - a number chosen in lr (or lw), or 0 if non-significant
*)

Inductive llexp :=
 | vide : llexp
 | step : lexp * list nat * list nat * nat -> llexp -> llexp.

Notation " { x } " := (step x vide).

Notation " { x '--β->' y '--β->' .. '--β->' z } "
:= (step x (step y .. (step z vide) ..))
   (at level 200,
    format " '{'  x '//' '--β->'  y '//' '--β->'  .. '//' '--β->'  z '}' ").

(* Building the list of reductions by rs until normal form (bounded by nx steps) *)

(* Reductions sequences based on a directly programmed reduction strategy
  (last number is 0 -- not significant *)
Definition showstep ex := step (ex, pos_redexes ex, pos_redexes_noUL ex, 0).
Fixpoint shown rs nx ex :=
  match nx with
  | 0    => step (toolong, [], [], 0) vide
  | S nx => match rs ex with
            | None => showstep ex vide
            | Some ex' => showstep ex (shown rs nx ex')
            end
  end.

(* Reductions sequences based on explicit choice of a redex occurrence,
   strategy represented by a cmp function *)
Fixpoint showncmp (weak: bool) cmp nx ex :=
  match nx with
  | 0    => step (toolong, [], [], 0) vide
  | S nx =>
    let nroex := nbd_occredexes_of ex in
    let nroex_noUL := filter (lift_fct_nb no_UL ex) nroex in
    let actual_nroex := if weak then nroex_noUL else nroex in
    match actual_nroex with
    | [] => step (ex, map fst nroex, [], 0) vide
    | nro1 :: lnro =>
      let chosen := minlist1 (lift_cmp_nb cmp ex) nro1 lnro in
      let ex' := beta_at ex (snd chosen) in
      step (ex, map fst nroex, map fst nroex_noUL, fst chosen) (showncmp weak cmp nx ex')
    end
  end.

(* The reduction strategies *)

(* Strong call-by-name (normal order bounded by 5000 (or 100) reduction steps) *)

Definition red1_cbn ex := red1  red1_lo ex.
Definition red_cbn  ex := redn  red1_lo 5000 ex.
Definition show_cbn_0 ex := shown red1_lo 100 ex.  (* pour mémoire *)
Definition show_cbn_l ex := showncmp false le_ou 100 ex.
Definition show_cbn_r ex := showncmp false ri_ou 100 ex.
Definition show_wcbn_l ex := showncmp true le_ou 100 ex.
Definition show_wcbn_r ex := showncmp true ri_ou 100 ex.
Definition show_cbn := show_cbn_l.
Definition show_wcbn := show_wcbn_l.

(* Strong call-by-value  (bounded by 5000 (or 100) reduction steps) *)
Definition show_cbv_l ex := showncmp false le_in 100 ex.
Definition show_cbv_r ex := showncmp false ri_in 100 ex.
Definition show_cbv := show_cbv_r.

(* Weak call-by-name (normal order bounded by 5000 (or 100) reduction steps) *)
Definition show_wcbv_l ex := showncmp true le_in 100 ex.
Definition show_wcbv_r ex := showncmp true ri_in 100 ex.
Definition show_wcbv := show_wcbv_r.

(* Strong call-by-value  (bounded by 5000 (or 100) reduction steps) *)

Definition red1_cbv ex := red1  red1_ro ex.
Definition red_cbv  ex := redn  red1_ro 5000 ex.
Definition show_cbv_0 ex := shown red1_ro 100 ex. (* pour mémoire *)

(* Weak call-by-name (normal order bounded by 5000 (or 100) reduction steps) *)

Definition red1_wcbn ex := red1  red1_low ex.
Definition red_wcbn  ex := redn  red1_low 5000 ex.
Definition show_wcbn_0 ex := shown red1_low 100 ex. (* pour mémoire *)

(* Weak call-by-value  (bounded by 5000 (or 100) reduction steps) *)

Definition red1_wcbv ex := red1  red1_row ex.
Definition red_wcbv  ex := redn  red1_row 5000 ex.
Definition show_wcbv_0 ex := shown red1_row 100 ex. (* pour mémoire *)


(* Syntactic equality modulo alpha-conversion of lexps *)

Fixpoint eq_lexp tx1 tx2 :bool :=
  match tx1, tx2 with
  | Var nx1, Var nx2         => eqb_Name nx1 nx2
  | App lx1 rx1, App lx2 rx2 => (eq_lexp lx1 lx2) && (eq_lexp rx1 rx2)
  | Lam nx1 tx1, Lam nx2 tx2 => if eqb_Name nx1 nx2 then eq_lexp tx1 tx2
                                else eq_lexp tx1 (subst nx2 (Var nx1) tx2)
  | _, _                     => false
  end.

(* Equivalence (modulo alpha and beta conversion) of lexps *)

Definition equiv_lexp (e1 e2:lexp) := eq_lexp (red_cbn e1) (red_cbn e2).

Definition equiv_lexp_P (e1 e2:lexp) := equiv_lexp e1 e2.

Notation " x == y" := (equiv_lexp_P x y) (at level 10).


(* ------------------------------------------------------------------------------------------
(* Tests et exemples *)

(* x N1 ... Nn *)
Definition xN1Nn := x (\a· a) (\b· b).

(* x e1 .. en *)
Definition xe1en := x ((\a·a) (\b·b)).

(* \x.x N1 ... Nn *)
Definition lxxN1Nn := \x·x (λ a·a) (\b·b).

Print lxxN1Nn.


(* \x.x e1 ... en *)
Definition lxxe1en := \x·x ((\a·a) (\b·b)).

(* \x.e *)
Definition lxe := \x·(\a·a) (\b·b).

(* (\x.E)F *)
Definition lxef := (\a·a)(\b·b).

Definition test := lxe lxef lxe.

Definition testfn := λ x y· y.

Compute (vlibres xN1Nn).
(* [x] *)

Compute (vliees xN1Nn).
(* [a; b] *)

Compute (vars xN1Nn).
(* [x; a; b] *)

Compute (rename y a (\x·x y (\y· y x z))).
(* λ x · (x a) (λ y · (y x) z) *)

Compute (alpha x z1 (\x·x y (\y· y x z))).
(* λ z1 · (z1 y) (λ y · (y z1) z) *)

Definition tol := List.map Lett.

Compute (renaming (tol [y]) (tol [x;y;z]) (\x·x y (\y· y x z))).
(* λ x · (x y) (λ a · (a x) z) *)

Compute (subst x (\x·y) (x y (\y· y x z))).
(* (λ x · y) y (λ a · (a (λ x · y)) z) *)


Compute (pos_redexes (x ((\y·y) (\z·z)))).
(* [1] *)
Compute see_redex 1 (x ((\y·y) (\z·z))).
(* (λ y · y) (λ z · z) *)
Compute red_beta 1  (x ((\y·y) (\z·z))).
(* x (λ z · z) *)

Compute (pos_redexes (x (\y·y) (\z·z))).
(* [] *)

Definition deuxred := (\x y·x)  ((\y·y) (\z·z)).
Compute redexes deuxred.
(* [(λ x y · x) ((λ y · y) (λ z · z)); (λ y · y) (λ z · z) *)

Compute (pos_redexes deuxred). (* [1; 3] *)
Compute see_redex 1 deuxred.
(* (λ x y · x) ((λ y · y) (λ z · z)) *)
Compute red_beta 1 deuxred.
(* λ y · (λ y · y) (λ z · z) *)
Compute see_redex 3 deuxred.
(* (λ y · y) (λ z · z) *)
Compute red_beta 3 deuxred.
(* (λ x y · x) (λ z · z) *)

Definition septred := (deuxred u ((\x· deuxred) (\y·y y)) v deuxred).
Compute septred.
(* (λ x y · x) ((λ y · y) (λ z · z)) u ((λ x · (λ x y · x) ((λ y · y) (λ z · z))) (λ y · y y)) v
         ((λ x y · x) ((λ y · y) (λ z · z))) *)
Compute (pos_redexes septred). (* [1; 3; 5; 6; 8; 11; 13] *)
Compute see_redex 1 septred.
(* (λ x y · x) ((λ y · y) (λ z · z)) *)
Compute red_beta 1 septred.
(* (λ y · y) (λ z · z) u ((λ x · (λ x y · x) ((λ y · y) (λ z · z))) (λ y · y y)) v
         ((λ x y · x) ((λ y · y) (λ z · z))) *)
Compute subterm_at septred (LA (LA (RA Ici))) I.
Compute see_redex 5 septred.
(* (λ x · (λ x y · x) ((λ y · y) (λ z · z))) (λ y · y y) *)
Compute red_beta 5 septred.
(* (λ x y · x) ((λ y · y) (λ z · z)) u (λ y · y y) v ((λ x y · x) ((λ y · y) (λ z · z))) *)


Compute (fnorm xN1Nn).    (* true  *)
Compute (fnorm xe1en).    (* false *)
Compute (fnorm lxxN1Nn).  (* true  *)
Compute (fnorm lxxe1en).  (* false *)
Compute (fnorm lxe).      (* false *)
Compute (fnorm lxef).     (* false *)

Compute (is_wnf xN1Nn).   (* true  *)
Compute (is_wnf xe1en).   (* false *)
Compute (is_wnf lxxN1Nn). (* true  *)
Compute (is_wnf lxxe1en). (* true  *)
Compute (is_wnf lxe).     (* true  *)
Compute (is_wnf lxef).    (* false *)

Compute (is_hnf xN1Nn).   (* true  *)
Compute (is_hnf xe1en).   (* true  *)
Compute (is_hnf lxxN1Nn). (* true  *)
Compute (is_hnf lxxe1en). (* true  *)
Compute (is_hnf lxe).     (* false *)
Compute (is_hnf lxef).    (* false *)

Compute (is_whnf xN1Nn).   (* true  *)
Compute (is_whnf xe1en).   (* true  *)
Compute (is_whnf lxxN1Nn). (* true  *)
Compute (is_whnf lxxe1en). (* true  *)
Compute (is_whnf lxe).     (* true  *)
Compute (is_whnf lxef).    (* false *)

Compute (red1_cbn test).
(* (λ a · a) (λ b · b) (λ x · (λ a · a) (λ b · b)) *)
Compute (red_cbn  test).
(* λ x b · b *)
Compute (show_cbn test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 0)
--β-> ((λ a · a) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 4], [1], 0)
--β-> ((λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 3], [1], 0)
--β-> (λ x · (λ a · a) (λ b · b), [2], [], 0)
--β-> (λ x b · b, [], [], 0)}
*)
Compute (show_cbn_l test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 1)
--β-> ((λ a · a) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 4], [1], 1)
--β-> ((λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 3], [1], 1)
--β-> (λ x · (λ a · a) (λ b · b), [2], [], 2)
--β-> (λ x b · b, [], [], 0)}
*)
Compute (show_cbn_r test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 7)
--β-> ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x b · b), [1; 2; 4], [1; 4], 1)
--β-> ((λ a · a) (λ b · b) (λ x b · b), [1], [1], 1)
--β-> ((λ b · b) (λ x b · b), [1], [1], 1)
--β-> (λ x b · b, [], [], 0)}
*)
Compute (show_wcbn_r test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 1)
--β-> ((λ a · a) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 4], [1], 1)
--β-> ((λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 3], [1], 1)
--β-> (λ x · (λ a · a) (λ b · b), [2], [], 0)}
 *)

Compute (red1_cbv test).
(* (λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x b · b) *)
Compute (red_cbv  test).
(* λ x b · b *)
Compute (show_cbv test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 0)
--β-> ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x b · b), [1; 2; 4], [1; 4], 0)
--β-> ((λ x · (λ a · a) (λ b · b)) (λ b · b) (λ x b · b), [1; 2], [1], 0)
--β-> ((λ a · a) (λ b · b) (λ x b · b), [1], [1], 0)
--β-> ((λ b · b) (λ x b · b), [1], [1], 0)
--β-> (λ x b · b, [], [], 0)}
*)
Compute (show_cbv_r test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 7)
--β-> ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x b · b), [1; 2; 4], [1; 4], 4)
--β-> ((λ x · (λ a · a) (λ b · b)) (λ b · b) (λ x b · b), [1; 2], [1], 2)
--β-> ((λ x b · b) (λ b · b) (λ x b · b), [1], [1], 1)
--β-> ((λ b · b) (λ x b · b), [1], [1], 1)
--β-> (λ x b · b, [], [], 0)}
*)
Compute (show_cbv_l test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 2)
--β-> ((λ x b · b) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 3; 6], [1; 3], 3)
--β-> ((λ x b · b) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 5], [1], 1)
--β-> ((λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 3], [1], 3)
--β-> ((λ b · b) (λ x b · b), [1], [1], 1)
--β-> (λ x b · b, [], [], 0)}
*)

Compute (red1_wcbn test).
(* (λ a · a) (λ b · b) (λ x · (λ a · a) (λ b · b)) *)
Compute (red_wcbn  test).
(* λ x · (λ a · a) (λ b · b) *)
Compute (show_wcbn test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 0)
--β-> ((λ a · a) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 4], [1], 0)
--β-> ((λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 3], [1], 0)
--β-> (λ x · (λ a · a) (λ b · b), [2], [], 0)}
*)
Compute (show_wcbn_l test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 1)
--β-> ((λ a · a) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 4], [1], 1)
--β-> ((λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 3], [1], 1)
--β-> (λ x · (λ a · a) (λ b · b), [], [], 0)}
 *)

Compute (red1_wcbv test).
(* (λ x · (λ a · a) (λ b · b)) (λ b · b) (λ x · (λ a · a) (λ b · b)) *)
Compute (red_wcbv test).
(* λ x · (λ a · a) (λ b · b) *)
Compute (show_wcbv test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 0)
--β-> ((λ x · (λ a · a) (λ b · b)) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 2; 6], [1], 0)
--β-> ((λ a · a) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 4], [1], 0)
--β-> ((λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 3], [1], 0)
--β-> (λ x · (λ a · a) (λ b · b), [2], [], 0)}
*)
Compute (show_wcbv_r test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 4)
--β-> ((λ x · (λ a · a) (λ b · b)) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 2; 6], [1], 1)
--β-> ((λ a · a) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 4], [1], 1)
--β-> ((λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 3], [1], 1)
--β-> (λ x · (λ a · a) (λ b · b), [2], [], 0)}
*)
Compute (show_wcbv_l test).
(*   =  { ((λ x · (λ a · a) (λ b · b)) ((λ a · a) (λ b · b)) (λ x · (λ a · a) (λ b · b)), [1; 2; 4; 7], [1; 4], 4)
--β-> ((λ x · (λ a · a) (λ b · b)) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 2; 6], [1], 1)
--β-> ((λ a · a) (λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 4], [1], 1)
--β-> ((λ b · b) (λ x · (λ a · a) (λ b · b)), [1; 3], [1], 1)
--β-> (λ x · (λ a · a) (λ b · b), [2], [], 0)}
 *)

Compute (equiv_lexp test testfn).  (* true *)
Eval compute in (test == testfn).  (* true *)

*)
