# LogicNG - The Next Generation Logic Framework

__THIS IS AN ALPHA VERSION! THE API MAY STILL CHANGE IN SIGNIFICANT WAYS! THE
PROGRAM IS NOT FULLY TESTED, DO NOT USE IN PRODUCTION!__

## Introduction

This is [LogicNG](https://logicng.org/) for Rust. The original version of
LogicNG is a Java Library for creating, manipulating and solving Boolean and
Pseudo-Boolean formulas.

Its main focus lies on memory-efficient data-structures for Boolean formulas and
efficient algorithms for manipulating and solving them. The library is designed
to be used in industrial systems which have to manipulate and solve millions of
formulas per day.


## Philosophy

The most important philosophy of the library is to avoid unnecessary object
creation. Therefore formulas can only be generated via formula factories. A
formula factory assures that a formula is only created once in memory. If
another instance of the same formula is created by the user, the already
existing one is returned by the factory. This leads to a small memory footprint
and fast execution of algorithms. Formulas can cache the results of algorithms
executed on them and since every formula is hold only once in memory it is
assured that the same algorithm on the same formula is also executed only once.

If you want a high-level overview of LogicNG and how it is used in many
applications in the area of product configuration, you can read our
[whitepaper](https://logicng.org/whitepaper/abstract/).

