Description
===========

GraphProver is a theorem prover for Propositional Minimal Logic. In current development it implements only the implication connective. 

Installation
============

GraphProver depends on the following libraries (listed with the versions I'm using):

* love (0.10.11)
* lpeg (1.0.0-1)
* lualogging (1.3.0-1)

Löve is a canvas for Lua game development that we use to build the prover user interface. It can be downloaded from [the project website](https://love2d.org/).

Lpeg is a pattern-matching library for Lua. We use lpeg to parse input formulae in our prover. It can be installed using [luarocks](http://luarocks.org/).

lualogging is used to register log messages. It also can be installed using [luarocks](http://luarocks.org/).

For PDF export (via LaTeX) you'll need at least the following packages
from CTAN:

* LKproof
* incgraph

For other export options, install graphviz.

Usage
=====

Inside SequentProver directory:

1. Run the prover graphical interface

`love .`

2. Follow commands in the graphical interface

Input formula example
=====================

Parentheses are required to the right side of every subformula. 

The formula A &rarr; (B &rarr; A) has to be entered as:

`A imp (B imp (A))`
