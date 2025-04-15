# Formalism of the Stabilizer Theory 

Author: Chew-Yi <qiuyif@student.unimelb.edu.au>

This "Stabilizer" package is the formalism and verification of the quantum stabilizer theory.

## Introduction to Math Background

https://qubit.guide/7-stabilisers

## Build this Project

```bash
# clone the whole repo
git clone git@github.com:ExcitedSpider/SQIR.git

# install quantumlib
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-quantumlib.1.5.1

# install mathcomp 
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect.2.2.0
opam install coq-mathcomp-fingroup.2.2.0

# compile SQIR core
make 

# compile stabilizer
make stabilizer
```

## Structure Description

There are two packages in the project.
- barebone. Barebone is the initial attempt to formalize stabilizer using a from-scratch style. Only quantumLib is used in the project.
- mathcomp. As the name suggests, we later did the formalization again using mathcomp and ssreflect, quantum-lib. 

```
.
├── barebone 
│   ├── ExtraSpecs.v # extra properties
│   ├── Group.v # from-scratch group definition
│   ├── PauliList.v # Coq.List based n-qubit pauli string
│   ├── PauliString_vector.v # Coq.Vector-based n-qubit pauli string
│   ├── Pauli.v # inductively defined 1-qubit pauli operator
│   ├── Stablizer.v # quantum stabilizer theory
│   └── dune
├── mathcomp
│   ├── PauliGroup.v # Pauli group definition based on math-comp, and entry-point to the formalization
│   ├── P1Props.v # verified properties of 1-qubit pauli group
│   ├── PNProps.v # verified properties of n-qubit pauli group
│   ├── Action.v # definitions of group actions
│   ├── ExtraSpecs.v # definitions of other properties (TODO: replace with mathcomp)
│   ├── Stabilizer.v # quantum stabilizer theory
│   └── dune
└── readme.md
```

## Status

- Done: The single-qubit Pauli group.
- Done: The n-qubit Pauli group
- Done: Theorems of stabilizer theories. e.g. commute/anti-commute relations.
Windows Terminal- WIP: Stabilizer Theories using mathcomp formalism
- WIP: examples of proving larger QECC programs correct
