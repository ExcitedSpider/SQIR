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

# compile barebone project -- use no libs or frameworks
cd barebone
dune build

# compile mathcomp based project
cd mathcomp
dune build
```

## Status

- Done: The single-qubit Pauli group.
- Done: The n-qubit Pauli group
- Done: Theorems of stabilizer theories. e.g. commute/anti-commute relations.
- WIP: Stabilizer Theories using mathcomp formalism
- WIP: examples of proving larger QECC programs correct