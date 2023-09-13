<a href="https://www.logicng.org"><img src="https://github.com/booleworks/logicng-rs/blob/main/doc/logos/logicng_logo_ferris.png" alt="logo" width="400"></a>

[![CI](https://github.com/booleworks/logicng-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/booleworks/logicng-rs/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/booleworks/logicng-rs/graph/badge.svg?token=AMGWKMH7VM)](https://codecov.io/gh/booleworks/logicng-rs)
[![license](https://img.shields.io/badge/license-Apache--2.0_OR_MIT-blue?style=flat-square)]()
<a href="https://blog.rust-lang.org/2023/06/01/Rust-1.70.0.html"><img alt="Rustc Version 1.70.0+" src="https://img.shields.io/badge/rustc-1.70.0%2B-lightgrey.svg"/></a>

# A Library for Creating, Manipulating, and Solving Boolean Formulas

__THIS IS AN ALPHA VERSION! THE API MAY STILL CHANGE IN SIGNIFICANT WAYS! THE
PROGRAM IS NOT FULLY TESTED, DO NOT USE IN PRODUCTION!__

## Introduction

This is [LogicNG](https://logicng.org/) for Rust. The [original
version](https://github.com/logic-ng/LogicNG) of LogicNG is a Java Library for
creating, manipulating and solving Boolean and Pseudo-Boolean formulas.

Its main focus lies on memory-efficient data-structures for Boolean formulas
and efficient algorithms for manipulating and solving them. The library is
designed and most notably used in industrial systems which have to manipulate
and solve millions of formulas per day. The Java version of LogicNG is heavily
used by the German automotive industry to validate and optimize their product
documentation, support the configuration process of vehicles, and compute WLTP
values for emission and consumption.

## Implemented Algorithms

The Rust version of LogicNG currently provides -among others- the following key
functionalities:

- Support for Boolean formulas, cardinality constraints, and pseudo-Boolean
formulas
- Thread-safe formula factory (in contrast to the Java version)
- Parsing of Boolean formulas from strings or files
- Transformations of formulas, like
  - Normal-Forms NNF, DNF, or CNF with various configurable algorithms
  - Anonymization of formulas
  - Simplification of formulas via subsumption or backbones
- Encoding cardinality constraints and pseudo-Boolean formulas to purely
Boolean formulas with a majority of different algorithms
- Solving formulas with an integrated SAT Solver including
  - Fast backbone computation on the solver
  - Incremental/Decremental solver interface
  - Proof generation
  - Optimization with incremental cardinality constraints
- Optimizing formulas with a MaxSAT solver (integrated
[OpenWBO](https://github.com/sat-group/open-wbo))
- Knowledge compilation with BDDs or DNNFs

## Philosophy

The most important philosophy of the library is to avoid unnecessary object
creation. Therefore formulas can only be generated via formula factories. A
formula factory assures that a formula is only created once in memory. If
another instance of the same formula is created by the user, the already
existing one is returned by the factory. This leads to a small memory footprint
and fast execution of algorithms. Formulas can cache the results of algorithms
executed on them and since every formula is hold only once in memory it is
assured that the same algorithm on the same formula is also executed only once.

## Whitepaper

If you want a high-level overview of LogicNG and how it is used in many
applications in the area of product configuration, you can read our
[whitepaper](https://logicng.org/whitepaper/abstract/).

## Funding

LogicNG for Rust development is funded by the [SofDCar project](https://sofdcar.de/):

<a href="https://www.logicng.org"><img src="https://github.com/booleworks/logicng-rs/blob/main/doc/logos/bmwk.png" alt="logo" width="200"></a>
