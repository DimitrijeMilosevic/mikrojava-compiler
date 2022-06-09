# Overview

*Mikrojava* is a relaxed version of the *Java* programming language. 
Compiler passes through 4 phases:
- Lexical analysis: Compiler parses an input file and tries to identify tokens based on the defined regular expressions representing keywords, punctuation symbols and identifier names. If no errors occur, compiler further processes the input file as an array of tokens.
- Syntax analysis: Based on the grammar of *Mikrojava*, compiler tries to identify code structures: statements, expressions, etc. If no errors occur, compiler creates an abstract syntax tree which represents the code.
- Semantic analysis: Compiler traverses the abstract syntax tree in order to check for semantic errors (for example, incompatible types in an assignment). If no errors occur, compiler proceeds to generate the code.
- Code generation: Compiler, yet again, traverses the abstract syntax tree, now generating executable assembly code for all class methods and functions, as well as allocating memory for global variables and constants in the data segment.

# Implementation Details 

- Compiler supports basic operators (assign, plus, minus, multiply, divide, ...), arrays, *if* statements, *do-while* loops, *switch* statements and classes (including inheritance, virtual function tables, method overriding and substitution - automatic conversion from an object of the derived type to an object of the base type).
- *JFlex* tool was used for lexical analysis.
- *AST_cup* tool was used for syntax analysis and generation of the abstract syntax tree.
