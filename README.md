<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Hoare Logic for Coinductive Trace-Based Semantics of While

[![Docker CI][docker-action-shield]][docker-action-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/palmskog/coind-sem-while/workflows/Docker%20CI/badge.svg?branch=abyss
[docker-action-link]: https://github.com/palmskog/coind-sem-while/actions?query=workflow:"Docker%20CI"



[doi-shield]: https://zenodo.org/badge/DOI/10.2168/LMCS-11(1:1)2015.svg
[doi-link]: https://doi.org/10.2168/LMCS-11(1:1)2015

A Hoare logic in Coq for coinductive trace-based operational semantics for the
While language, using predicative definitions of relations.

## Meta

- Author(s):
  - Keiko Nakata (initial)
  - Tarmo Uustalu (initial)
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.10 or later
- Additional dependencies: none
- Coq namespace: `CoindHoareWhile`
- Related publication(s):
  - [A Hoare logic for the coinductive trace-based big-step semantics of While](https://arxiv.org/abs/1412.6579) doi:[10.2168/LMCS-11(1:1)2015](https://doi.org/10.2168/LMCS-11(1:1)2015)

## Building instructions

``` shell
git clone https://github.com/palmskog/coind-sem-while
cd coind-sem-while
git checkout abyss
make   # or make -j <number-of-cores-on-your-machine>
```

## Documentation

- `Assert.v`: the assertion language and properties of the assertions
- `Hoare.v`: the partial-correctness Hoare logic, embedding and projection
- `HoareTotal.v`: the total-correctness Hoare logic, embedding and projection
- `Semax.v`: the trace-based Hoare logic
- `Markov.v`: corresponds to Section 5.1
- `Liveness.v`: corresponds to Section 5.2
- `Weakbism.v`: corresponds to Section 5.3
