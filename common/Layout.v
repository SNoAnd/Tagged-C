Require Import ZArith.

Module Type Layout.
  Parameter global_min : Z.
  Parameter global_max : Z.
  Parameter heap_min : Z.
  Parameter heap_max : Z.
  Parameter stack_min : Z.
  Parameter stack_max : Z.
End Layout.
