type Matrix = mat : (seq<seq<real>>, int, int) |
    0 <= mat.1
    && 0 <= mat.2
    &&|mat.0| == mat.1
    && forall i | 0 <= i < mat.1 :: |mat.0[i]| == mat.2
    witness *

function matNumRows (mat : Matrix) : int
ensures 0 <= matNumRows (mat)
{
    mat.1
}

function matNumCols (mat : Matrix) : int
ensures 0 <= matNumCols (mat) 
{
    mat.2
}

function matGet (mat : Matrix, i : int, j : int) : real
requires 0 <= i < matNumRows (mat)
requires 0 <= j < matNumCols (mat)
{
    mat.0[i][j]
}
