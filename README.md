# LambdaCalculus 

##### 🛑 English

## 1.1 Untyped λ-calculus
For this part, add the following query to the beginning of your file:
`` ''
Require Import untypedLC.
`` ''
It allows to import the definitions of lexp expressions.

1. Booleans (coding of constants and basic operations)
2. Natural integers (coding of some constants, successor, addition and multiplication operations, and of the test at 0)
3. Couples
4. Choice structure (inj1, inj2)
5. Predecessor
6. Factorial

## 1.2 Simply typed λ-calculus
1. Booleans (coding of constants and basic operations)
2. Natural integers (coding of some constants, successor, addition and multiplication operations, and of the test at 0)

## 2.2 Programming of advanced structures in λ-calculus

### 2.2.1 The polymorphic identity
To use polymorphic typing, you have to launch Coq with the following command:
`` ''
$ coqide -impredicative-set
`` ''
* Identity: id def = ΛT.λx ^ T.x

### 2.2.2 Booleans with polymorphic typing
* Booleans: pbool def = ∀T. T → T → T
* True: ptr def = ΛT.λx ^ T y ^ T.x
* False: pfa def = ΛT.λx ^ T y ^ T.y

### 2.2.3 Data structures: couples and choices
* Couples: A × B def = ∀T, (A → B → T) → T.
* Choice: A + B def = ∀T, (A → T) → (B → T) → T.

### 2.2.4 Church integers with polymorphic typing
* Integers: pnat def = ∀T, (T → T) → (T → T)
1. Addition, multiplication and test operations at 0.
2. Calculation of the predecessor of an integer n.

##### 🛑 Français

## 1.1 λ-calcul non typé
Pour cette partie, il faut ajouter la requête suivante au début de votre fichier :
```
Require Import untypedLC.
```
Elle permet d'importer les définitions des expressions lexp.

1.  Booléens (codage des constantes et des opérations de base)
2.  Entiers naturels (codage de quelques constantes, des opérations successeur, addition et multiplica-tion, et du test à 0)
3.  Couples
4.  Structure de choix (inj1, inj2) 
5.  Prédécesseur
6.  Factorielle

## 1.2 λ-calcul simplement typé 
1.  Booléens (codage des constantes et des opérations de base)
2.  Entiers naturels (codage de quelques constantes, des opérations successeur, addition et multiplica-tion, et du test à 0) 

## 2.2  Programmation de structures avancées en λ-calcul

### 2.2.1 L’identité polymorphe 
Pour utliser le typage polymorphe, il faut lancer Coq avec la commande suivante : 
```
$ coqide -impredicative-set
```
* L'identité : id def= ΛT.λx^T.x

### 2.2.2  Booléens avec typage polymorphe 
* Booléens : pbool def= ∀T. T→T→T
* Vrai : ptr def= ΛT.λx^T y^T.x
* Faux : pfa def= ΛT.λx^T y^T.y

### 2.2.3  Structures de données : couples et choix
* Couples : A×B def= ∀T, (A→B→T)→T.
* Choix : A+B def = ∀T, (A→T)→(B→T)→T.

### 2.2.4  Entiers de Church avec typage polymorphe 
* Entiers : pnat def= ∀T, (T→T)→(T→T)
1.  Opérations d’addition, de multiplication et de test à 0.
2.  Calcul du prédécesseur d’un entier n.
