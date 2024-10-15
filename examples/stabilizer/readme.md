# Formalism of the Stabilizer Theory 

Author: Chew-Yi <qiuyif@student.unimelb.edu.au>

This "Stabilizer" package is the formalism and verification of the quantum stabilizer theory.

## Introduction to Math Background

https://qubit.guide/7-stabilisers

## Build this Project

```bash
# install quantumlib
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-quantumlib.1.5.1

make # compile sqir
make stabilizer # compile this project
```

## Status

- Done: The single-qubit Pauli group.
- WIP: The n-qubit Pauli group
- WIP: Theorems of stabilizer theories. e.g. commute/anti-commute relations.