<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Resumptions, Weak Bisimilarity and Big-Step Semantics for While with Interactive I/O

[![Docker CI][docker-action-shield]][docker-action-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/palmskog/coind-sem-while/workflows/Docker%20CI/badge.svg?branch=sophie
[docker-action-link]: https://github.com/palmskog/coind-sem-while/actions?query=workflow:"Docker%20CI"



[doi-shield]: https://zenodo.org/badge/DOI/10.4204/EPTCS.32.5.svg
[doi-link]: https://doi.org/10.4204/EPTCS.32.5

Several big-step operational semantics for the While language in Coq with
interactive I/O, based on resumptions and termination-sensitive weak bisimilarity.

## Meta

- Author(s):
  - Keiko Nakata (initial)
  - Tarmo Uustalu (initial)
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.11 or later
- Additional dependencies: none
- Coq namespace: `CoindResumptionsWhile`
- Related publication(s):
  - [Resumptions, Weak Bisimilarity and Big-Step Semantics for While with Interactive I/O: An Exercise in Mixed Induction-Coinduction](https://arxiv.org/abs/1008.2112) doi:[10.4204/EPTCS.32.5](https://doi.org/10.4204/EPTCS.32.5)

## Building instructions

``` shell
git clone https://github.com/palmskog/coind-sem-while
cd coind-sem-while
git checkout sophie
make   # or make -j <number-of-cores-on-your-machine>
```


