# foundations-harper

Agda proofs for some of the theorems in Robert Harper's [Practical Foundations of Programming Languages][harper15]. Languages from the followings chapters of the book are defined:

* Ch 4. Statics: L{num str}.
* Ch 8. Function Definitions and Values: L{num str fun}.
* Ch 9. Gödel's T.
* Ch 10. Plotkin’s PCF
* Ch 20. Girard’s System F.

For each language, we basically define its typing rules, its small step semantics, and prove the subject reduction (preservation) and progress theorems.

The proofs represents terms in Arthur Charguéraud's [locally nameless style with cofinite quantification][charguéraud], with my own little variation: terms are indexed by number of bound variables. Terms are thus always locally closed. I found this made some proofs much easier.

[harper15]: http://www.cs.cmu.edu/~rwh/plbook/1sted-revised.pdf

[charguéraud]: http://www.chargueraud.org/softs/ln/
