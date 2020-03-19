# lambda-calcul-projet
## 1.1 λ-calcul non typé
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

### 2.2.2  Booléens avec typage polymorphe 
* pbool def= ∀T. T→T→T

### 2.2.3  Structures de données : couples et choix
* Couples : A×B def= ∀T, (A→B→T)→T.
* Choix : A+B def = ∀T, (A→T)→(B→T)→T.

### 2.2.4  Entiers de Church avec typage polymorphe 
* pnat def= ∀T, (T→T)→(T→T)
1.  Opérations d’addition, de multiplication et de test à 0.
2.  Calcul du prédécesseur d’un entier n.
