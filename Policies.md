## Adding Policies to Tagged C ##

This file documents how to add a new policy, using the example in policies/Example.v.

1. Create the file policies/Example.v (this has already been done for you)
2. In Example.v, there is a module Ex1_Gas, instantiating every field of the 
Policy module type (see also common/Tags.v)
3. In extraction/extraction.v, add the policy to the imports and the modules
to the extraction list
4. In the makefile, add Example.v to the POLICIES variable
5. At the bottom of driver/Frontend.ml, add:
   module WithGas = FrontendP (Example.Ex1_Gas) FLAllocator
   
   You have a choice of FLAllocator or ConcreteAllocator.
6. In driver/Driver.ml, add a policy option to the command line options
7. Add C test files to the test suite in /tests/ . Add invocations to the run-all-tests.py file

### Guidance for Policy Design ###
1. In this version of PIPE there is a tag on the value and one on byte memory. This is an abstraction of spliting them up to make reasoning easier. In hardware it is all together.
    For example on an (32-bit) int, there is 1 tag on the int's value and 4 location/memory tags, one per byte.
1. myTags inductive type includes the tags that go on the pc, memory, and locations. 
1. In TaggedC, the "extra state" of the policy is carried around in the pc tag. 
1. Indicate which is which, for the reader's sake & your own. L_ for 
location/memory tags, V_ for value tags, and PC_ for pc tags. N for the "not interesting" or "nonapplicable" or "uNit" tag is an exception. 
1. Use  two vertical bars, || to seperate the policy name from the failing condition and one vertical bar, |, to seperate the failing condition from the diagnostic tag list. If the policy is consumed by some diagnostic tool or automated service, this makes life much easier. 
