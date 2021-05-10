# Coinductive Trace-Based Semantics for While

[![CI][action-shield]][action-link]

[action-shield]: https://github.com/palmskog/coind-sem-while/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/palmskog/coind-sem-while/actions?query=workflow%3ACI




Four equivalent operational semantics, and Hoare logic, for the
While language in Coq. The semantics account for both terminating and non-terminating
program runs through coinductive traces. All semantic relations are impredicative, and
impredicativity is used to encode induction-recursion.

## Meta

- Author(s):
  - Keiko Nakata (initial)
  - Tarmo Uustalu (initial)
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.10 or later
- Additional dependencies: none
- Coq namespace: `CoindSemWhile`
- Related publication(s):
  - [A Hoare logic for the coinductive trace-based big-step semantics of While](https://arxiv.org/abs/1412.6579) doi:[10.2168/LMCS-11(1:1)2015](https://doi.org/10.2168/LMCS-11(1:1)2015)
  - [Trace-Based Coinductive Operational Semantics for While](http://cs.ioc.ee/~keiko/papers/tphols09.pdf) doi:[10.1007/978-3-642-03359-9_26](https://doi.org/10.1007/978-3-642-03359-9_26)

## Building instructions

``` shell
git clone https://github.com/palmskog/coind-sem-while
cd coind-sem-while
make   # or make -j <number-of-cores-on-your-machine>
```

## Documentation

- `Trace.v` defines traces and bisimilarity. It proves
  bisimilarity is reflexive, symmetric and transitive.
- `Language.v` defines the While language.
- `BigRel.v` defines the big-step relational semantics
  and proves that it is deterministic and a setoid predicate.
- `BigFunct.v` defines the big-step functional semantics and
  proves that the big-step relational and the big-step functional
  semantics are equivalent.
- `SmallRel.v` defines the small-step relational semantics
  and proves that it is deterministic and a setoid predicate.
- `SmallFunct.v` defines the small-step functional semantics
  and proves that the small-step relational and the small-step
  functional semantics are equivalent and that the small-step
  functional and the big-step functional semantics are equivalent.
- `Alternatives.v` gives the complete formalizations of the alternative
  big-step semantics considered in the accompanying paper.
- `Assert.v` defines the assertion language and properties of the assertions.
- `Hoare.v` defines the partial-correctness Hoare logic, embedding and projection.
- `HoareTotal.v` defines the total-correctness Hoare logic, embedding and projection.
- `Semax.v` defines the trace-based Hoare logic.
- `SemaxSound.v` defines and proves soundness for the trace-based Hoare logic.
- `SemaxComplete.v` defines and proves completeness for the trace-based Hoare logic.
- `Markov.v` defines an example inspired by Markov's principle.
- `Liveness.v` defines an example that demonstrates reasoning about liveness.
- `Weakbism.v` defines an example based on weak trace equivalence.
