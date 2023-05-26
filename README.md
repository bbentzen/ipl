# Verified completeness in Henkin-style for intuitionistic propositional logic

This repository presents a Lean formalization of the classical proof of completeness in Henkin-style originally developed by Troelstra and van Dalen [1] for full first-order intuitionistic logic with respect to Kripke models. The completeness proof incorporates their insights in a fresh and elegant manner that is better suited for mechanization. We formalize its propositional fragment, whose main ingredient is a model construction based on a consistent extension of sets of formulas achieved by going through all disjunctions of the language [1, Lemma 6.3]. To carry out this extension, they assume an enumeration of disjunctions with infinite repetitions, also remarking that an alternative approach in which at each stage we treat the first disjunction not yet treated (this variant appears in Van Dalen [2, Lemma 5.3.8]). Our implementation is based on a third variant of the consistent extension method, which we developed to better suit our needs of formalization. Each propositional formula is only listed once in the enumeration, but we carry out the extension for each of them infinitely many times. The formalization consists of roughly 800 lines of code and encompasses the syntax and semantics of intuitionistic propositional logic, along with the soundness and completeness theorems. 
 
## Lean Installation

See the following link for installation of Lean 3 and mathlib: https://leanprover-community.github.io/get_started.html

## References

[1] Troelstra, Anne, and Van Dalen, Dirk. Constructivism in Mathematics, Vol 1. Elsevier, 1988.

[2] Van Dalen, Dirk. Logic and structure. 4th ed. Berlin: Springer, 2008.
