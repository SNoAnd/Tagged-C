# Tagged C
This is the development for Tagged C

## Overview

Tagged C is a variant of C that implements a *Tag-based Reference Monitor* to protect a program
with arbitrary security policies. That means that its semantics treats every value as a pair
of a value and a *metadata tag* that describes some relevant context or history. Metadata
might be information like "I belong to Bob," or "I am a valid pointer to object x."
At key points in the language semantics, tags are updated according to user-defined rules.
The rules collectively form a *policy*.

## Important Files

The Policy module type is defined in common/Tags.v.

Policy instantiations are kept in policies/

The formal semantics are in cfrontend/CSem.v.

The reference interpreter is in cfrontend/CExec.v.

## License
The Tagged C development is based on CompCert, under the non-commercial
license found in the file `LICENSE`. This development may be used
for evaluation, research, educational and personal purposes, and shared
or modified consistent with the original license.
