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
6. In driver/Driver.ml, add a policy option to the command line options
