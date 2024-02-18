Require Import Tags Memory.
Require Import ExtLib.Structures.Monad.

Module ErrorMonads (P:Policy).
  Import P.
  
  Section Monad.

    Global Instance Monad_memres : Monad MemoryResult :=
      { ret := fun _ t => MemorySuccess t;
        bind :=  fun _ _ c f =>
                   match c with
                   | MemorySuccess t => f t
                   | MemoryFail msg failure => MemoryFail msg failure
                   end }.
    
    Global Instance Monad_polres : Monad PolicyResult :=
      { ret := fun _ t => Success t;
        bind :=  fun _ _ c f =>
                   match c with
                   | Success t => f t
                   | PolicyFail msg params => PolicyFail msg params
                   end }.

    Global Instance Monad_mpres : Monad (fun t => MemoryResult (PolicyResult t)) :=
      { ret := fun _ t => MemorySuccess (Success t);
        bind :=  fun _ _ c f =>
                   match c with
                   | MemorySuccess (Success t) => f t
                   | MemorySuccess (PolicyFail msg params) => MemorySuccess (PolicyFail msg params)
                   | MemoryFail msg failure => MemoryFail msg failure
                   end }.
    
  End Monad.
End ErrorMonads.
