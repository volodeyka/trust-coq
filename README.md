# TruSt
A Coq library with formalization of the Truly Stateless Concurrency Model Checker (TruSt) in Coq. 

Checkout the [paper](https://people.mpi-sws.org/~viktor/papers/popl2022-trust.pdf) about TruSt and my [blogpost](https://habr.com/ru/company/JetBrains-education/blog/589343/) (in Russian).

## Description of Files

- `src/lib` - common definitions, lemmas
- `src/basic` - definitions and lemmas about some common notions on semantics of concurrent programs 
- `src/models` - definitions of some weak memory models (RA, SCOH, TSO)
- `src/trust` - TruSt formalization, includes:

   - `Util.v` - miscellaneous 
   - `Path.v` - adaptation of mathcomp's [path](https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/path.v)
   - `TerminateGen.v` - lemmas for general relation termination
   - `Executions_Aux.v` - auxiliary lemmas about execution graphs
   - `Sem.v` - general program semantics for TruSt
   - `Alg.v` - TruSt definition, its simple properties and correctness 
   - `Termination.v` - TruSt termination
   - `Prev.v` - definition of reversed TruSt algorithm
   - `Complete.v` - TruSt completeness
   - `Oplimal.v` - TruSt optionality
   - `Models.v` - Instances of concrete memory models for TruSt (SC, RA, SCOH, TSO, RC11)
