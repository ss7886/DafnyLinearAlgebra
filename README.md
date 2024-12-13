# COS516 Final Project
## By Samuel Sanft

See publicly available [Github](https://github.com/ss7886/DafnyLinearAlgebra) repo.

LaTex files and pdfs are available for the project outline and project report as well as a PowerPoint file containing the presentation slides.

All Dafny code is in /code directory.
- `matrix.dfy` implements an abstract data type for matrices.
- `vector.dfy` implements an abstract data type for vectors.
- `vectorFunctions.dfy` implements functions to perform vector arithmetic.
- `matrixFunctions.dfy` implements various predicates for matrices, as well as a function to initialize a matrix using a given function.
- `matrixMultiplication.dfy` implements functions for matrix-vector and matrix-matrix multiplication.
- `proofs/vectorProofs.dfy` contains verified proofs about operations implemented in `vector.dfy`.
- `proofs/vectorFunctionProofs.dfy` contains verified proofs about operations implemented in `vectorFunctions.dfy`.
- `proofs/matrixFunctionProofs.dfy` contains verified proofs about operations implemented in `matrixFunctions.dfy`.
- `proofs/matrixMultiplicationProofs.dfy` contains verified proofs about operations implemented in `matrixMultiplication.fy`
- `proofs/normalEquations.dfy` contains a function which returns the solution to the normal equations and a verified proof that this solution is an optimal solution to the ordinary least square (OLS) optimization problem.