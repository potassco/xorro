# xorro

[![standard-readme compliant](https://img.shields.io/badge/readme%20style-standard-brightgreen.svg?style=flat-square)](https://github.com/potassco/xorro)

> A tool for solving ASP programs with XOR (parity) constraints towards generating (near-)uniform answer sets.
> A fully re-implemented and extended version of the original `xorro` prototype is presented. This new version is built under clingo 5 infrastructure with Python support.

## Description
`xorro` is a tool that takes the advantage of the flexible ASP infrastructure
by using the Python integration of `clingo` to solve XOR (parity) constraints from different approaches. </br>
These approaches are: </br>
- count      : Add count aggregates with a modulo 2 operation
- {list,tree}: Translate binary xor operators to rules in the form of a list or a tree
- countp     : Propagator simply counting assigned literals
- up         : Propagator implementing unit propagation
- gje        : Propagator implementing Gauss-Jordan Elimination

On the other hand, like its predecessor `xorro` also has the feature
to build random XOR constraints for sampling purposes. <br/>
The main idea of sampling is to use random XOR constraints on top of an ASP program
to cut through the search space towards near-uniformity solutions. <br/>
This consist of calculating a few answer sets representative for all the search space.
This is particularly useful if the computation of all answers is practically infeasible.<br/>


## Table of Contents

- [Requirements](#requirements)
- [Installation](#installation)
- [Input](#input)
- [Usage](#usage)
- [Examples](#examples)
- [Contributors](#contributors)
- [License](#license)


## Requirements

This second generation of `xorro` works with `clingo` version 5.3
and is tested under Unix systems using Travis for Linux and Mac with Python 2.7 and 3.6. </br>
The easiest way to obtain Python enabled clingo packages is using Anaconda.
Packages are available in the Potassco channel.
First install either Anaconda or Miniconda and then run: `conda install -c potassco clingo`.



## Installation

Either run `xorro` directly from source or install it by the usual means provided by Python. </br>
To install `xorro` run: `python setup.py install`.



## Input

To accommodate parity constraints in the input language, we use the Aggregates-like syntax,
using a semicolon to separate elements that are themselves terms conditioned by conjunctions of literals. </br>
For example, let us express the XOR constraints `p(1) ⊕ ⊥`, and `p(2) ⊕ p(3) ⊕ ⊤` from the domain of `p(1..3)` as:
```
 &odd{ 1:p(1) }.
&even{ X:p(X), X>1 }.
```
The first constraint aims at filtering stable models that do not contain p(1),
while the second requires that either none or both atoms p(2) and p(3) are true. </br>
The program obtained after running the XOR constraints with the choice rule ‘{p(1..3)}.’,
results in two stable models, viz. {p(1)} and {p(1), p(2), p(3)}. </br>

It is important to remark that the scope for the XOR constraints presented in this version of ’xorro’
corresponds to directive statements,
meaning they can neither occur in the body nor in the head of a rule
and thus act as meta statements instructing the ASP system to eliminate stable models violating the parity.



## Usage

To use `xorro` directly from source run `python -m xorro` from the project's root directory and
follow the standard-like clingo call:
`usage: xorro [number] [options] [files]`

 
```
xorro --help
xorro examples/test.lp --approach=count
```

To enable the sampling features of `xorro`
To use `xorro` directly from source run `python -m xorro` from the project's root directory and
follow the standard-like clingo call:
`usage: xorro [number] [options] [files]`

To enable the sampling features of `xorro`, run the full command:
```
xorro --help
xorro examples/test.lp --approach=count [--sampling --s=<n> --q<n>]
```

The sampling options of `xorro` are shown next:
| command | description |
|---|---|
| `--sampling` | Enable sampling features. |
| `--s=<n>` | Number of XOR constraints to generate. Default=0, calculated automatically by **log(#atoms)**. |
| `--q=<n>` | Calculate the density of each constraint. Values from 0.1 to 1. Default=0.5. |




## Examples

To solve parity constraints within an ASP program, lets consider an example program `examples/test.lp` with six parity constraints:
```
$ cat examples/test.lp 
{ p(1;2;3) }.
{ q(1,(2;3)); q(2,1); q(3,1) }.

&odd{ (X+10)-2 : p(X), q(X,Y) }.
&even{ Y : q(X,Y), Y<3 }.
&even{ 1,2 : not q(1,2) }.
&odd{ X: p(X) }.
&odd{ X,Y: q(X,Y) }.
&odd{ X : p(X), X!=2 }.
#show p/1.
#show q/2.

$ python -m xorro examples/test.lp 0
xorro version 1.0
Reading from examples/test.lp
Solving...
Answer: 1
p(3) q(1,2) q(1,3) q(3,1)
Answer: 2
p(3) q(1,2) q(2,1) q(3,1)
Answer: 3
p(1) q(1,2) q(1,3) q(2,1)
Answer: 4
p(1) q(1,2) q(1,3) q(3,1)
Answer: 5
p(1) q(1,2) q(2,1) q(3,1)
SATISFIABLE

Models       : 5
Calls        : 1
Time         : 0.006s (Solving: 0.00s 1st Model: 0.00s Unsat: 0.00s)
CPU Time     : 0.006s
```

To enable the sampling features, let use the same program without the parity constraints shown above. The sampling features allows `xorro` propose random XOR constraints and compute representative answer sets from the search space.
An example is shown below:
```
$ python -m xorro examples/test.lp 2 --sampling --s=4 --q=0.5
xorro version 1.0
Reading from examples/test.lp
Random XOR Constraints: 4
Solving...
Answer: 1
p(2)
Answer: 2
p(2) q(1,3)
Answer: 3
p(1) p(2) p(3) q(2,1) q(3,1)
Answer: 4
p(1) p(2) p(3) q(1,3) q(2,1) q(3,1)
Answer: 5
p(1) q(1,2) q(2,1)
Answer: 6
p(1) q(1,2) q(1,3) q(2,1)
Answer: 7
p(3) q(1,2) q(3,1)
Answer: 8
p(3) q(1,2) q(1,3) q(3,1)

Sampled Answer Set(s): 4, 7
Answer: 4
p(1) p(2) p(3) q(1,3) q(2,1) q(3,1)
Answer: 7
p(3) q(1,2) q(3,1)
SATISFIABLE

Models       : 8
Calls        : 1
Time         : 0.008s (Solving: 0.00s 1st Model: 0.00s Unsat: 0.00s)
CPU Time     : 0.008s
```

The random XOR constraints used in sampling, are stored in the file `examples/xors.lp`. 
```
$ cat examples/xors.lp 
&odd{ p(2):p(2) ; p(3):p(3) ; q(2,1):q(2,1) }. 

&even{ q(1,2):q(1,2) ; q(2,1):q(2,1) ; q(3,1):q(3,1) }. 

&even{ p(1):p(1) ; p(3):p(3) ; q(1,2):q(1,2) }. 

&even{ p(3):p(3) ; q(1,2):q(1,2) ; q(2,1):q(2,1) }.
```

From the eight answer sets remaining after solving the program with the  XOR constraints mentioned above, the sampled answer sets were the number 4th and the 7th.

The sampling feature of `xorro` asks for all the remaining models after applying XOR constraints. If the requested models by the user are less than the remaining models, `xorro` will pick randomly n answer sets.


## Contributors

* Flavio Everardo - Get help/report bugs via flavio.everardo@cs.uni-potsdam.de
The original prototype of `xorro` was implemented by Marius Lindauer.

## License

This project is licensed under the MIT License - see the [LICENSE.md](LICENSE.md) file for details
