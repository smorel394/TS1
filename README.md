# TS1

This is a formalization in Lean4 of the first 8 pages of the paper : https://alco.centre-mersenne.org/articles/10.5802/alco.66/ (including the prerequisites about abstract simplicial complexes and shellability).
The main file is TS1.lean, it calls auxiliary files in the directory TS1. The file TS1/leitfaden.jpg gives the dependencies of the auxiliary files. The file TS1.lean contains a proof of Corollary 4.8 of the paper; the file TS1/FiniteWeightedComplex.lean contains the definition of the weighted complex and a proof of its shellability (Theorem 4.3); the file TS1/FiniteCoxeterComplex.lean contains a proof of the shellability of the Coxeter complex of the symmetric group (Björner's theorem, Theorem 4.2 in the paper).
